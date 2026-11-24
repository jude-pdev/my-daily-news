#!/usr/bin/env python3
"""
Daily News Digest
-----------------
Fetches RSS/Atom feeds, downloads each article's text and picture, and builds
a clean, ad-free news web app in ./site that a phone can install like an app.
Tapping a headline opens the article inside the app (no website visit).

Usage:
    python3 daily_news.py            # build site/index.html
    python3 daily_news.py --open     # build and open it in your browser

Needs Python 3.8+ and nothing else (standard library only).
Sources: the built-in list is DEFAULT_FEEDS below. Sites added or removed from
the app's Settings screen are saved in sources.json next to this script:
    {"added": [{"category": "Tech", "name": "Example", "url": "https://example.com"}],
     "removed": ["BBC Sport"]}
You can also edit that file by hand. The url can be a feed or just a website
address - the script will look for the site's feed itself.
"""

import argparse
import html
import json
import os
import re
import sys
import webbrowser
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import urljoin
from urllib.request import Request, urlopen
import xml.etree.ElementTree as ET

# ----------------------------------------------------------------------
# SETTINGS - edit these
# ----------------------------------------------------------------------
DEFAULT_FEEDS = {
    "Australia": {
        "ABC News": "https://www.abc.net.au/news/feed/51120/rss.xml",
        "Guardian Australia": "https://www.theguardian.com/australia-news/rss",
        "Sydney Morning Herald": "https://www.smh.com.au/rss/feed.xml",
    },
    "World": {
        "BBC World": "https://feeds.bbci.co.uk/news/world/rss.xml",
        "Guardian World": "https://www.theguardian.com/world/rss",
    },
    "Tech": {
        "BBC Tech": "https://feeds.bbci.co.uk/news/technology/rss.xml",
        "Ars Technica": "https://feeds.arstechnica.com/arstechnica/index",
        "The Verge": "https://www.theverge.com/rss/index.xml",
    },
    "Sports": {
        "Guardian Australia Sport": "https://www.theguardian.com/au/sport/rss",
        "SMH Sport": "https://www.smh.com.au/rss/sport.xml",
        "BBC Sport": "https://feeds.bbci.co.uk/sport/rss.xml",
    },
}

MAX_PER_SOURCE = 8        # headlines shown per source
MAX_AGE_HOURS = 48        # ignore anything older than this
SUMMARY_CHARS = 220       # summary length cut-off on the list
FULL_TEXT = True          # download full article text into the app
# Paywalled sources: don't try to download their article text (still fetches the picture)
FULL_TEXT_SKIP_SOURCES = {"Sydney Morning Herald", "SMH Sport"}
MIN_BODY_CHARS = 500      # shorter than this = treat as "couldn't get the article"
MAX_BODY_CHARS = 12000    # cap per article to keep the app light
OUTPUT_DIR = Path(__file__).with_name("site")
OUTPUT_FILE = OUTPUT_DIR / "index.html"
TIMEZONE_NAME = "Australia/Sydney"   # used for display times
# ----------------------------------------------------------------------

UA = ("Mozilla/5.0 (Linux; Android 13) AppleWebKit/537.36 (KHTML, like Gecko) "
      "Chrome/120.0 Mobile Safari/537.36")


# ---------------------------- helpers ---------------------------------

def load_sources():
    """Built-in feeds, minus anything removed, plus anything added in sources.json."""
    path = Path(__file__).with_name("sources.json")
    data = {}
    if path.exists():
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except ValueError:
            print("sources.json isn't valid JSON - ignoring it", file=sys.stderr)
    if not isinstance(data, dict):
        data = {}
    removed = {str(x) for x in (data.get("removed") or [])}
    out = []
    for cat, feeds in DEFAULT_FEEDS.items():
        for name, url in feeds.items():
            if name not in removed:
                out.append({"category": cat, "name": name, "url": url, "custom": False})
    for item in (data.get("added") or []):
        try:
            cat = str(item["category"]).strip() or "Other"
            name = str(item["name"]).strip()
            url = str(item["url"]).strip()
        except (KeyError, TypeError):
            continue
        if name and url.startswith(("http://", "https://")):
            out.append({"category": cat, "name": name, "url": url, "custom": True})
    return out


def local_name(tag):
    """Strip the XML namespace from a tag name."""
    return tag.rsplit("}", 1)[-1] if "}" in tag else tag


def clean_text(raw, limit=None):
    """Remove HTML tags/entities and tidy whitespace."""
    if not raw:
        return ""
    text = re.sub(r"<[^>]+>", " ", raw)
    text = html.unescape(text)
    text = re.sub(r"\s+", " ", text).strip()
    if limit and len(text) > limit:
        text = text[:limit].rsplit(" ", 1)[0].rstrip(".,;:") + "…"
    return text


def parse_date(raw):
    if not raw:
        return None
    raw = raw.strip()
    try:
        dt = parsedate_to_datetime(raw)  # RSS style
    except (TypeError, ValueError):
        try:
            dt = datetime.fromisoformat(raw.replace("Z", "+00:00"))  # Atom style
        except ValueError:
            return None
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt


def child_text(elem, *names):
    for child in elem:
        if local_name(child.tag) in names and (child.text or "").strip():
            return child.text
    return ""


def entry_link(elem):
    for child in elem:
        if local_name(child.tag) == "link":
            href = child.attrib.get("href")
            if href and child.attrib.get("rel", "alternate") == "alternate":
                return href
            if child.text and child.text.strip():
                return child.text.strip()
    return ""


def good_url(url, base=""):
    """Absolute https URL or ''."""
    url = (url or "").strip()
    if not url:
        return ""
    url = urljoin(base, url) if base else url
    if url.startswith("http://"):
        url = "https://" + url[len("http://"):]
    return url if url.startswith("https://") else ""


def http_get(url, timeout=15, limit=3_000_000):
    req = Request(url, headers={"User-Agent": UA, "Accept-Language": "en-AU,en;q=0.9"})
    with urlopen(req, timeout=timeout) as resp:
        data = resp.read(limit)
        charset = resp.headers.get_content_charset() or "utf-8"
    return data, charset


# ------------------------ article extraction ---------------------------

class ArticleParser(HTMLParser):
    """Collects text blocks, the og:image and any JSON-LD from an HTML page."""

    SKIP = {"script", "style", "nav", "footer", "aside", "header", "form",
            "figcaption", "noscript", "svg", "button", "select", "iframe"}
    BLOCK = {"p": "p", "li": "p", "h2": "h", "h3": "h"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.skip = 0
        self.art = 0
        self.cur = None
        self.buf = []
        self.blocks = []          # (kind, text, inside_article)
        self.og_image = ""
        self.ld = []
        self._in_ld = False
        self._ld_buf = []

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag == "meta" and a.get("property") == "og:image" and not self.og_image:
            self.og_image = a.get("content") or ""
        if tag == "script" and "ld+json" in (a.get("type") or ""):
            self._in_ld, self._ld_buf = True, []
            return
        if tag in self.SKIP:
            self.skip += 1
            return
        if tag in ("article", "main"):
            self.art += 1
        if self.skip == 0 and tag in self.BLOCK:
            self._flush()
            self.cur = self.BLOCK[tag]

    def handle_endtag(self, tag):
        if tag == "script" and self._in_ld:
            self.ld.append("".join(self._ld_buf))
            self._in_ld = False
            return
        if tag in self.SKIP:
            self.skip = max(0, self.skip - 1)
            return
        if tag in ("article", "main"):
            self.art = max(0, self.art - 1)
        if tag in self.BLOCK:
            self._flush()

    def handle_data(self, data):
        if self._in_ld:
            self._ld_buf.append(data)
        elif self.skip == 0 and self.cur:
            self.buf.append(data)

    def _flush(self):
        if self.cur:
            text = re.sub(r"\s+", " ", "".join(self.buf)).strip()
            if text:
                self.blocks.append((self.cur, text, self.art > 0))
        self.cur, self.buf = None, []


BOILERPLATE = re.compile(
    r"^(advertisement|sign up|subscribe|read more|related:|share this|"
    r"follow us|get our|listen to|watch:|copyright|©)", re.I)


def _ld_article_body(ld_list):
    def walk(o):
        if isinstance(o, dict):
            v = o.get("articleBody")
            if isinstance(v, str) and len(v) >= MIN_BODY_CHARS:
                return v
            for x in o.values():
                r = walk(x)
                if r:
                    return r
        elif isinstance(o, list):
            for x in o:
                r = walk(x)
                if r:
                    return r
        return None

    for raw in ld_list:
        try:
            r = walk(json.loads(raw))
        except ValueError:
            continue
        if r:
            text = html.unescape(re.sub(r"<[^>]+>", " ", r))
            parts = [re.sub(r"[ \t]+", " ", p).strip() for p in re.split(r"\n+", text)]
            parts = [p for p in parts if p]
            if len(parts) == 1 and len(parts[0]) > 800:  # one big blob: split by sentences
                sents = re.split(r"(?<=[.!?])\s+", parts[0])
                parts = [" ".join(sents[i:i + 4]) for i in range(0, len(sents), 4)]
            return [("p", p) for p in parts]
    return []


def _blocks_to_body(blocks):
    art = [b for b in blocks if b[2]]
    chosen = art if sum(1 for b in art if b[0] == "p") >= 3 else blocks
    out, seen = [], set()
    for kind, text, _ in chosen:
        if kind == "p" and len(text) < 40:
            continue
        if kind == "h" and len(text) < 3:
            continue
        if BOILERPLATE.match(text) or text in seen:
            continue
        seen.add(text)
        out.append((kind, text))
    # drop trailing headings
    while out and out[-1][0] == "h":
        out.pop()
    return out


def body_chars(body):
    return sum(len(t) for _, t in body)


def trim_body(body):
    out, total = [], 0
    for kind, text in body:
        total += len(text)
        if total > MAX_BODY_CHARS and out:
            break
        out.append((kind, text))
    return out


def html_to_body(raw_html):
    """Convert feed-supplied HTML (e.g. content:encoded) into body blocks."""
    p = ArticleParser()
    try:
        p.feed(raw_html)
        p.close()
        p._flush()
    except Exception:
        return []
    return [(k, t) for k, t, _ in p.blocks if (k == "h" or len(t) >= 25)]


def fetch_article(url):
    """Download an article page. Returns (body_blocks, og_image)."""
    data, charset = http_get(url)
    page = data.decode(charset, errors="replace")
    p = ArticleParser()
    try:
        p.feed(page)
        p.close()
        p._flush()
    except Exception:
        pass
    body = _ld_article_body(p.ld)
    if body_chars(body) < MIN_BODY_CHARS:
        body = _blocks_to_body(p.blocks)
    return body, good_url(p.og_image, url)


# ------------------------------ feeds ----------------------------------

def find_image(item, link):
    best, best_w = "", -1
    for child in item.iter():
        name = local_name(child.tag)
        url = ""
        if name in ("thumbnail", "content") and child.attrib.get("url"):
            typ = child.attrib.get("type", "")
            medium = child.attrib.get("medium", "")
            if (typ and not typ.startswith("image")) or medium in ("video", "audio"):
                continue
            url = child.attrib["url"]
        elif name == "enclosure" and child.attrib.get("type", "").startswith("image"):
            url = child.attrib.get("url", "")
        if url:
            try:
                w = int(child.attrib.get("width", 0))
            except ValueError:
                w = 0
            if w > best_w:
                best, best_w = url, w
    if not best:
        for raw in (child_text(item, "encoded", "content"), child_text(item, "description", "summary")):
            m = re.search(r"<img[^>]+src=[\"']([^\"']+)", raw or "", re.I)
            if m:
                best = html.unescape(m.group(1))
                break
    return good_url(best, link)


def is_feed(root):
    return local_name(root.tag) in ("rss", "feed", "RDF")


def discover_feed(page_url, page_html):
    """Given a normal web page, find that site's RSS/Atom feed."""
    candidates = []
    for m in re.finditer(r"<link\b[^>]*>", page_html, re.I):
        tag = m.group(0)
        if re.search(r"application/(rss|atom)\+xml", tag, re.I) and "alternate" in tag.lower():
            h = re.search(r"href=[\"']([^\"']+)", tag, re.I)
            if h:
                candidates.append(urljoin(page_url, html.unescape(h.group(1))))
    for path in ("/feed", "/rss", "/feed.xml", "/rss.xml", "/atom.xml", "/index.xml"):
        candidates.append(urljoin(page_url, path))
    tried = set()
    for cand in candidates:
        if cand in tried or len(tried) >= 8:
            continue
        tried.add(cand)
        try:
            data, _ = http_get(cand)
            root = ET.fromstring(data)
            if is_feed(root):
                return root
        except Exception:
            continue
    return None


def load_feed_root(url):
    data, charset = http_get(url)
    try:
        root = ET.fromstring(data)
        if is_feed(root):
            return root
    except ET.ParseError:
        pass
    root = discover_feed(url, data.decode(charset, errors="replace"))
    if root is None:
        raise ValueError("no news feed found at this address")
    return root


def fetch_feed(src):
    """Return (src, [articles], error_or_None)."""
    source, url = src["name"], src["url"]
    try:
        root = load_feed_root(url)
    except Exception as exc:  # network, HTTP or XML errors
        return src, [], f"{type(exc).__name__}: {exc}"

    items = [e for e in root.iter() if local_name(e.tag) in ("item", "entry")]
    articles = []
    for item in items:
        title = clean_text(child_text(item, "title"))
        link = entry_link(item)
        if not title or not link.startswith(("http://", "https://")):
            continue
        summary = clean_text(
            child_text(item, "description", "summary", "content"), SUMMARY_CHARS
        )
        if summary.lower().startswith(title.lower()[:40]):
            summary = ""  # avoid repeating the headline
        published = parse_date(child_text(item, "pubDate", "published", "updated", "date"))

        body = []
        feed_html = child_text(item, "encoded", "content")
        if feed_html and len(feed_html) > MIN_BODY_CHARS:
            candidate = html_to_body(feed_html)
            if body_chars(candidate) >= MIN_BODY_CHARS:
                body = candidate

        articles.append({
            "title": title, "link": link, "summary": summary,
            "published": published, "source": source,
            "image": find_image(item, link), "body": body,
        })
    return src, articles, None


def enrich(article):
    """Fetch the article page for full text and/or a picture, if still missing."""
    need_body = FULL_TEXT and not article["body"] and article["source"] not in FULL_TEXT_SKIP_SOURCES
    need_image = not article["image"]
    if not (need_body or need_image):
        return
    try:
        body, og_image = fetch_article(article["link"])
    except Exception:
        return
    if need_image and og_image:
        article["image"] = og_image
    if need_body and body_chars(body) >= MIN_BODY_CHARS:
        article["body"] = body


def local_time(dt):
    try:
        from zoneinfo import ZoneInfo
        return dt.astimezone(ZoneInfo(TIMEZONE_NAME))
    except Exception:
        return dt.astimezone()


def slug(text):
    return re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-") or "section"


def build_sections():
    cutoff = datetime.now(timezone.utc) - timedelta(hours=MAX_AGE_HOURS)
    sources = load_sources()

    with ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(fetch_feed, sources))

    epoch = datetime.min.replace(tzinfo=timezone.utc)
    sections, errors, info = {}, [], []
    for s in sources:
        sections.setdefault(s["category"], [])
    seen = set()
    for src, articles, err in results:
        row = {"name": src["name"], "category": src["category"], "url": src["url"],
               "custom": src["custom"], "n": 0, "err": bool(err)}
        info.append(row)
        if err:
            errors.append((src["name"], err))
            continue
        kept = 0
        for a in sorted(articles, key=lambda x: x["published"] or epoch, reverse=True):
            if a["published"] and a["published"] < cutoff:
                continue
            key = re.sub(r"\W+", "", a["title"].lower())
            if key in seen:
                continue
            seen.add(key)
            sections[src["category"]].append(a)
            kept += 1
            if kept >= MAX_PER_SOURCE:
                break
        row["n"] = kept

    for cat in sections:
        sections[cat].sort(key=lambda x: x["published"] or epoch, reverse=True)

    everything = [a for arts in sections.values() for a in arts]
    for i, a in enumerate(everything):
        a["id"] = i
    with ThreadPoolExecutor(max_workers=12) as pool:
        list(pool.map(enrich, everything))
    for a in everything:
        a["body"] = trim_body(a["body"])
    return sections, errors, info


# ------------------------------ page -----------------------------------

CSS = r"""
:root{--bg:#f6f5f1;--card:#fff;--text:#1c1c1e;--muted:#6b6b70;--accent:#b3261e;--line:#e4e2dc;
  --font:Georgia,'Times New Roman',serif;--ui:system-ui,-apple-system,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif}
@media(prefers-color-scheme:dark){:root:not([data-theme]){--bg:#141415;--card:#1e1e20;--text:#ececee;--muted:#9a9aa1;--accent:#ff8a80;--line:#2e2e32}}
:root[data-theme=light]{--bg:#f6f5f1;--card:#fff;--text:#1c1c1e;--muted:#6b6b70;--accent:#b3261e;--line:#e4e2dc}
:root[data-theme=dark]{--bg:#141415;--card:#1e1e20;--text:#ececee;--muted:#9a9aa1;--accent:#ff8a80;--line:#2e2e32}
:root[data-theme=sepia]{--bg:#f1e7d0;--card:#f8f0dc;--text:#433422;--muted:#7a6a55;--accent:#9a4a1a;--line:#dccfae}
:root[data-theme=black]{--bg:#000;--card:#0f0f0f;--text:#e8e8e8;--muted:#9b9b9b;--accent:#ff8a80;--line:#262626}
*{box-sizing:border-box}
[hidden]{display:none!important}
html{-webkit-text-size-adjust:100%}
body{margin:0;background:var(--bg);color:var(--text);font:1rem/1.5 var(--font)}
body.lock{overflow:hidden}
header,main,footer{max-width:760px;margin:0 auto;padding:0 18px}
header{padding-top:calc(32px + env(safe-area-inset-top,0px));padding-bottom:8px}
h1{margin:0;font-size:2rem;letter-spacing:-.5px}
.top{display:flex;justify-content:space-between;align-items:center;gap:12px}
.refresh,.btn,.mini,.rbar button,.rbar a{font:.875rem var(--ui);color:var(--text);background:var(--card);border:1px solid var(--line);
  border-radius:999px;padding:.45em .95em;cursor:pointer;text-decoration:none;display:inline-block}
.refresh:active,.btn:active,.mini:active{border-color:var(--accent)}
.mini{font-size:.78rem;padding:.3em .8em}
.iconbtn{width:2.6rem;height:2.6rem;display:inline-flex;align-items:center;justify-content:center;flex:none;color:var(--text);background:var(--card);border:1px solid var(--line);border-radius:50%;text-decoration:none}
.iconbtn:active,.iconbtn:hover{border-color:var(--accent);color:var(--accent)}
.date{color:var(--muted);font:.875rem var(--ui);margin-top:4px}
nav{position:sticky;top:0;background:var(--bg);padding:10px 0;margin:10px 0 0;border-bottom:1px solid var(--line);
    display:flex;gap:8px;flex-wrap:wrap;font:.875rem var(--ui)}
nav a{color:var(--text);text-decoration:none;padding:5px 12px;border:1px solid var(--line);border-radius:999px}
nav a:hover{border-color:var(--accent);color:var(--accent)}
h2{font:700 .8rem var(--ui);text-transform:uppercase;letter-spacing:1.5px;color:var(--accent);margin:34px 0 10px;scroll-margin-top:60px}
article.card{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:14px 16px;margin-bottom:10px;
    display:flex;gap:14px;align-items:flex-start;cursor:pointer}
.txt{flex:1;min-width:0}
article.card a.t{color:var(--text);text-decoration:none;font-size:1.05rem;font-weight:700;line-height:1.3;display:block}
article.card:hover a.t{color:var(--accent)}
.thumb{width:6.5rem;height:6.5rem;object-fit:cover;border-radius:8px;flex:none;background:var(--line)}
.meta{font:.75rem var(--ui);color:var(--muted);margin-top:4px}
.sum{margin:8px 0 0;color:var(--muted);font-size:.92rem}
.empty,.err,footer{color:var(--muted);font:.8rem var(--ui)}
footer{padding:30px 18px 50px}
@media(max-width:420px){.thumb{width:5.2rem;height:5.2rem}.sum{display:none}}

#reader,#settings{position:fixed;inset:0;z-index:100;background:var(--bg);overflow-y:auto;-webkit-overflow-scrolling:touch}
.rbar{position:sticky;top:0;z-index:2;background:var(--bg);border-bottom:1px solid var(--line);
    display:flex;justify-content:space-between;align-items:center;padding:10px 16px;
    padding-top:calc(10px + env(safe-area-inset-top,0px));font:.875rem var(--ui)}
.rbar .sp{width:5rem}
.rwrap{max-width:680px;margin:0 auto;padding:18px 18px 70px}
.hero{width:100%;max-height:360px;object-fit:cover;border-radius:10px;margin-bottom:14px;background:var(--line)}
.rmeta{font:.8rem var(--ui);color:var(--accent);font-weight:600}
.rtitle{font-size:1.7rem;line-height:1.2;margin:8px 0 18px}
.rbody p{font-size:1.1rem;line-height:1.7;margin:0 0 1.1em}
.rbody h3{font-size:1.2rem;margin:1.4em 0 .5em}
.note{font:.875rem var(--ui);color:var(--muted);background:var(--card);border:1px solid var(--line);border-radius:8px;padding:10px 12px}
.btn.wide{margin-top:14px}

.sets{font-family:var(--ui)}
.sets h3{font-size:.8rem;text-transform:uppercase;letter-spacing:1.5px;color:var(--accent);margin:30px 0 10px;padding-top:6px;border-top:1px solid var(--line)}
.sets h3:first-child{border-top:0;margin-top:6px}
.lbl{font-size:.85rem;color:var(--muted);margin:14px 0 6px}
.row{display:flex;gap:8px;flex-wrap:wrap}
.seg{display:flex;flex-wrap:wrap;gap:6px}
.seg button{font:inherit;font-size:.9rem;color:var(--text);background:var(--card);border:1px solid var(--line);border-radius:8px;padding:.5em .9em;cursor:pointer}
.seg button.on,#swatches .on{border-color:var(--accent);box-shadow:0 0 0 2px var(--accent)}
#swatches{display:flex;gap:10px;flex-wrap:wrap;align-items:center}
#swatches button,#swatches label{width:2.2rem;height:2.2rem;border-radius:50%;border:1px solid var(--line);cursor:pointer;padding:0;
  font-size:.6rem;color:var(--text);background:var(--card);display:inline-flex;align-items:center;justify-content:center;position:relative;overflow:hidden}
#swatches label input{position:absolute;inset:0;opacity:0;width:100%;height:100%;cursor:pointer}
#size{width:100%;accent-color:var(--accent)}
.sets input[type=text],.sets input[type=password],.sets select{width:100%;font:inherit;font-size:.95rem;color:var(--text);background:var(--card);
  border:1px solid var(--line);border-radius:8px;padding:.6em .7em;margin:0 0 8px}
.hint{font-size:.82rem;color:var(--muted);margin:8px 0}
.hint.bad{color:var(--accent);font-weight:600}
#srclist{list-style:none;margin:0 0 6px;padding:0}
#srclist li{display:flex;justify-content:space-between;align-items:center;gap:10px;padding:9px 0;border-bottom:1px solid var(--line)}
#srclist li div{min-width:0}
#srclist .hint{margin:2px 0 0}
details{margin-top:18px;background:var(--card);border:1px solid var(--line);border-radius:8px;padding:10px 12px}
summary{cursor:pointer;font-size:.92rem}
.steps{padding-left:1.2em;font-size:.88rem;color:var(--muted)}
.steps li{margin:4px 0}
.steps a{color:var(--accent)}
"""

PREFS_JS = r"""
(function(){
  var SANS="system-ui,-apple-system,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif";
  var HUM="'Trebuchet MS',Verdana,Tahoma,sans-serif";
  var MONO="ui-monospace,Menlo,Consolas,'Courier New',monospace";
  var FONTS={serif:["Georgia,'Times New Roman',serif",SANS],sans:[SANS,SANS],humanist:[HUM,HUM],mono:[MONO,MONO]};
  var NP={
    load:function(){try{return JSON.parse(localStorage.getItem('newsPrefs')||'{}')||{};}catch(e){return {};}},
    save:function(p){try{localStorage.setItem('newsPrefs',JSON.stringify(p));}catch(e){}},
    apply:function(p){
      try{
        var r=document.documentElement;
        if(p.theme&&p.theme!=='auto'){r.setAttribute('data-theme',p.theme);}else{r.removeAttribute('data-theme');}
        var f=FONTS[p.font]||FONTS.serif;
        r.style.setProperty('--font',f[0]);r.style.setProperty('--ui',f[1]);
        var s=parseInt(p.size,10);if(!(s>=80&&s<=160))s=100;
        r.style.fontSize=s+'%';
        if(p.accent){r.style.setProperty('--accent',p.accent);}else{r.style.removeProperty('--accent');}
        var m=document.querySelector('meta[name=theme-color]');
        if(m)m.setAttribute('content',p.accent||'#b3261e');
      }catch(e){}
    }
  };
  window.NewsPrefs=NP;
  NP.apply(NP.load());
})();
"""

JS = r"""
(function(){
  var $=function(id){return document.getElementById(id);};
  var cfg={};try{cfg=JSON.parse($('cfg').textContent);}catch(e){}
  var reader=$('reader'),content=$('rcontent'),orig=$('orig'),settings=$('settings');
  var P=window.NewsPrefs,prefs=P.load();

  /* ---------------- screens (reader / settings) ---------------- */
  function lock(on){document.body.classList.toggle('lock',on);}
  function showReader(id){
    var d=$('d-'+id);
    if(!d){closeAll();return;}
    content.innerHTML=d.innerHTML;
    orig.href=d.getAttribute('data-url');
    settings.hidden=true;reader.hidden=false;lock(true);reader.scrollTop=0;
  }
  function showSettings(){reader.hidden=true;content.innerHTML='';settings.hidden=false;lock(true);settings.scrollTop=0;}
  function closeAll(){reader.hidden=true;settings.hidden=true;content.innerHTML='';lock(false);}
  function sync(){
    var h=location.hash,m=h.match(/^#read-(\d+)$/);
    if(m){showReader(m[1]);}else if(h==='#settings'){showSettings();}else{closeAll();}
  }
  function goBack(){if(history.length>1){history.back();}else{location.hash='';}}
  document.addEventListener('click',function(e){
    var c=e.target.closest('article.card');
    if(!c)return;
    e.preventDefault();
    location.hash='read-'+c.getAttribute('data-id');
  });
  Array.prototype.forEach.call(document.querySelectorAll('.back'),function(b){b.addEventListener('click',goBack);});
  window.addEventListener('hashchange',sync);

  /* ---------------- appearance ---------------- */
  var DEF={theme:'auto',font:'serif'};
  function syncPrefUI(){
    Array.prototype.forEach.call(document.querySelectorAll('.seg[data-pref]'),function(seg){
      var k=seg.getAttribute('data-pref'),cur=prefs[k]||DEF[k];
      Array.prototype.forEach.call(seg.children,function(b){b.classList.toggle('on',b.getAttribute('data-v')===String(cur));});
    });
    var sz=prefs.size||100;
    $('size').value=sz;$('sizeval').textContent=sz+'%';
    Array.prototype.forEach.call(document.querySelectorAll('#swatches button'),function(b){
      b.classList.toggle('on',(b.getAttribute('data-c')||'')===(prefs.accent||''));
    });
  }
  function setPref(k,v){
    if(v===null||v===undefined||v===''){delete prefs[k];}else{prefs[k]=v;}
    P.save(prefs);P.apply(prefs);syncPrefUI();
  }
  settings.addEventListener('click',function(e){
    var b=e.target.closest('.seg button');
    if(b){setPref(b.parentNode.getAttribute('data-pref'),b.getAttribute('data-v'));return;}
    var s=e.target.closest('#swatches button');
    if(s){setPref('accent',s.getAttribute('data-c'));}
  });
  $('size').addEventListener('input',function(){setPref('size',parseInt(this.value,10));});
  $('accpick').addEventListener('input',function(){setPref('accent',this.value);});
  $('resetprefs').addEventListener('click',function(){prefs={};P.save(prefs);P.apply(prefs);syncPrefUI();});

  /* ---------------- GitHub helpers ---------------- */
  var repo=cfg.repo||(function(){
    var h=location.hostname;
    if(/\.github\.io$/.test(h)){var seg=location.pathname.split('/')[1];if(seg)return h.split('.')[0]+'/'+seg;}
    return '';
  })();
  function token(){try{return localStorage.getItem('ghToken')||'';}catch(e){return '';}}
  function setToken(t){try{if(t){localStorage.setItem('ghToken',t);}else{localStorage.removeItem('ghToken');}}catch(e){}}
  function msg(id,text,bad){var el=$(id);el.textContent=text;el.className='hint'+(bad?' bad':'');}
  function gh(path,opts){
    opts=opts||{};
    opts.headers={'Authorization':'Bearer '+token(),'Accept':'application/vnd.github+json','Content-Type':'application/json'};
    return fetch('https://api.github.com/repos/'+repo+path,opts);
  }
  function explain(r){
    if(r.status===401)return "GitHub rejected the token. Check it was copied in full, or make a new one.";
    if(r.status===403)return "The token doesn't have permission. It needs Contents: Read and write on this repository.";
    if(r.status===404)return "The token can't see the repository "+repo+". Make sure you selected it when creating the token.";
    if(r.status===409||r.status===422)return "The file changed while saving. Please try again.";
    return "GitHub returned an error ("+r.status+").";
  }
  function b64enc(s){var bytes=new TextEncoder().encode(s),bin='';bytes.forEach(function(c){bin+=String.fromCharCode(c);});return btoa(bin);}
  function b64dec(s){var bin=atob(s.replace(/\s/g,'')),arr=new Uint8Array(bin.length);for(var i=0;i<bin.length;i++)arr[i]=bin.charCodeAt(i);return new TextDecoder().decode(arr);}
  function openConnect(){$('connect').open=true;}

  async function readSources(){
    var r=await gh('/contents/sources.json');
    if(r.status===404)return {data:{added:[],removed:[]},sha:null};
    if(!r.ok)throw r;
    var j=await r.json(),data={};
    try{data=JSON.parse(b64dec(j.content));}catch(e){}
    if(!data||typeof data!=='object'||Array.isArray(data))data={};
    data.added=Array.isArray(data.added)?data.added:[];
    data.removed=Array.isArray(data.removed)?data.removed:[];
    return {data:data,sha:j.sha};
  }
  async function changeSources(mutate,okText){
    msg('srcmsg','Saving…');
    try{
      var f=await readSources();
      mutate(f.data);
      var body={message:'Update news sources',content:b64enc(JSON.stringify(f.data,null,2)+'\n')};
      if(f.sha)body.sha=f.sha;
      var r=await gh('/contents/sources.json',{method:'PUT',body:JSON.stringify(body)});
      if(!r.ok)throw r;
      msg('srcmsg',okText);return true;
    }catch(e){
      msg('srcmsg',(e&&e.status)?explain(e):"Couldn't reach GitHub. Check your connection.",true);return false;
    }
  }

  /* ---------------- news sources ---------------- */
  var pending=[];
  function renderSources(){
    var ul=$('srclist');ul.innerHTML='';
    (cfg.sources||[]).concat(pending).forEach(function(s){
      var li=document.createElement('li'),box=document.createElement('div'),n=document.createElement('strong'),m=document.createElement('div');
      n.textContent=s.name;m.className='hint';
      m.textContent=s.category+' · '+(s.pending?'appears after the next build':(s.err?"⚠ couldn't load":s.n+' articles'));
      box.appendChild(n);box.appendChild(m);li.appendChild(box);
      if(!s.pending){
        var x=document.createElement('button');x.textContent='Remove';x.className='mini';
        x.addEventListener('click',function(){removeSource(s);});li.appendChild(x);
      }
      ul.appendChild(li);
    });
  }
  async function removeSource(s){
    if(!token()){openConnect();msg('srcmsg','Connect GitHub below first, so the app can save the change.',true);return;}
    if(!confirm('Remove '+s.name+'?'))return;
    var ok=await changeSources(function(d){
      if(s.custom){d.added=d.added.filter(function(x){return !(x.name===s.name&&x.url===s.url);});}
      else if(d.removed.indexOf(s.name)<0){d.removed.push(s.name);}
    },'Removed. It disappears after the next build (a few minutes).');
    if(ok){cfg.sources=cfg.sources.filter(function(x){return x!==s;});renderSources();}
  }
  var sel=$('newcat');
  (cfg.categories||[]).forEach(function(c){var o=document.createElement('option');o.value=c;o.textContent=c;sel.appendChild(o);});
  var on=document.createElement('option');on.value='__new';on.textContent='New category…';sel.appendChild(on);
  sel.addEventListener('change',function(){$('newcatname').hidden=(this.value!=='__new');});

  $('addbtn').addEventListener('click',async function(){
    var url=$('newurl').value.trim(),name=$('newname').value.trim();
    var cat=sel.value==='__new'?$('newcatname').value.trim():sel.value;
    if(!url){msg('srcmsg','Enter the website or feed address.',true);return;}
    if(!/^https?:\/\//i.test(url))url='https://'+url;
    var u;try{u=new URL(url);}catch(e){msg('srcmsg',"That address doesn't look right.",true);return;}
    if(!cat){msg('srcmsg','Choose or type a category.',true);return;}
    if(!name)name=u.hostname.replace(/^www\./,'');
    if(!token()){openConnect();msg('srcmsg','Connect GitHub below first, so the app can save your sites.',true);return;}
    var ok=await changeSources(function(d){
      d.added=d.added.filter(function(x){return x.url!==url;});
      d.added.push({category:cat,name:name,url:url});
      d.removed=d.removed.filter(function(x){return x!==name;});
    },'Saved. The app rebuilds in a few minutes, then reopen it to see the new site.');
    if(ok){pending.push({name:name,category:cat,pending:true});renderSources();$('newurl').value='';$('newname').value='';}
  });

  /* ---------------- GitHub connection ---------------- */
  function renderConn(){var t=!!token();$('conn-on').hidden=!t;$('conn-off').hidden=t;}
  $('savetok').addEventListener('click',async function(){
    var t=$('tokin').value.trim();
    if(!t){msg('connmsg','Paste your token first.',true);return;}
    if(!repo){msg('connmsg',"Couldn't work out your repository name.",true);return;}
    setToken(t);msg('connmsg','Checking…');
    try{
      var r=await gh('');if(!r.ok)throw r;
      $('tokin').value='';msg('connmsg','Connected to '+repo+'.');
    }catch(e){
      setToken('');msg('connmsg',(e&&e.status)?explain(e):"Couldn't reach GitHub. Check your connection.",true);
    }
    renderConn();
  });
  $('disconnect').addEventListener('click',function(){setToken('');renderConn();msg('connmsg','Disconnected.');});

  /* ---------------- refresh ---------------- */
  $('reloadbtn').addEventListener('click',function(){location.reload();});
  $('fetchnow').addEventListener('click',async function(){
    if(!token()){openConnect();msg('rmsg','Connect GitHub (at the bottom of this screen) to use this.',true);return;}
    msg('rmsg','Asking GitHub to fetch the latest news…');
    try{
      var i=await gh('');if(!i.ok)throw i;
      var br=(await i.json()).default_branch||'main';
      var r=await gh('/actions/workflows/news.yml/dispatches',{method:'POST',body:JSON.stringify({ref:br})});
      if(r.status!==204)throw r;
      msg('rmsg','Started. Give it 2 to 3 minutes, then tap "Reload app".');
    }catch(e){
      var t="Couldn't reach GitHub. Check your connection.";
      if(e&&e.status===401)t=explain(e);
      else if(e&&e.status)t="GitHub refused. The token needs the Actions: Read and write permission.";
      msg('rmsg',t,true);
    }
  });

  /* ---------------- start ---------------- */
  $('built').textContent=cfg.built?('Last built: '+cfg.built+'.'):'';
  syncPrefUI();renderSources();renderConn();sync();
  if('serviceWorker' in navigator){navigator.serviceWorker.register('sw.js').catch(function(){});}
})();
"""

SETTINGS_HTML = """
<div id='settings' hidden>
<div class='rbar'><button class='back'>← Back</button><strong>Settings</strong><span class='sp'></span></div>
<div class='rwrap sets'>

<h3>Refresh</h3>
<div class='row'><button class='btn' id='reloadbtn'>Reload app</button><button class='btn' id='fetchnow'>Fetch latest news now</button></div>
<p class='hint' id='rmsg'>The news updates by itself every 3 hours. <span id='built'></span></p>

<h3>Appearance</h3>
<div class='lbl'>Theme</div>
<div class='seg' data-pref='theme'><button data-v='auto'>Auto</button><button data-v='light'>Light</button><button data-v='dark'>Dark</button><button data-v='sepia'>Sepia</button><button data-v='black'>Black</button></div>
<div class='lbl'>Font</div>
<div class='seg' data-pref='font'>
<button data-v='serif' style="font-family:Georgia,serif">Serif</button>
<button data-v='sans' style="font-family:system-ui,sans-serif">Sans</button>
<button data-v='humanist' style="font-family:'Trebuchet MS',Verdana,sans-serif">Clear</button>
<button data-v='mono' style="font-family:ui-monospace,Menlo,Consolas,monospace">Mono</button></div>
<div class='lbl'>Text size <span id='sizeval'></span></div>
<input type='range' id='size' min='80' max='160' step='5'>
<div class='lbl'>Accent colour</div>
<div id='swatches'>
<button data-c='' title='Default'>Auto</button>
<button data-c='#b3261e' style='background:#b3261e' aria-label='Red'></button>
<button data-c='#1a5fb4' style='background:#1a5fb4' aria-label='Blue'></button>
<button data-c='#2e7d32' style='background:#2e7d32' aria-label='Green'></button>
<button data-c='#7b3fa0' style='background:#7b3fa0' aria-label='Purple'></button>
<button data-c='#c75b00' style='background:#c75b00' aria-label='Orange'></button>
<button data-c='#00796b' style='background:#00796b' aria-label='Teal'></button>
<label title='Pick any colour'>Pick<input type='color' id='accpick' value='#b3261e'></label>
</div>
<p><button class='mini' id='resetprefs'>Reset appearance</button></p>

<h3>News sources</h3>
<ul id='srclist'></ul>
<div class='lbl'>Add a site</div>
<input id='newurl' type='text' inputmode='url' placeholder='Website or feed address, e.g. theguardian.com' autocapitalize='off' autocorrect='off' spellcheck='false'>
<input id='newname' type='text' placeholder='Name (optional)'>
<select id='newcat'></select>
<input id='newcatname' type='text' placeholder='New category name' hidden>
<button class='btn' id='addbtn'>Add site</button>
<p class='hint' id='srcmsg'></p>

<details id='connect'><summary>GitHub connection (needed to add or remove sites)</summary>
<div id='conn-off'>
<ol class='steps'>
<li>Open <a href='https://github.com/settings/personal-access-tokens/new' target='_blank' rel='noopener'>github.com/settings/personal-access-tokens/new</a>.</li>
<li>Name it "news app" and pick the longest expiry offered.</li>
<li>Under Repository access choose <b>Only select repositories</b> and pick your news repository.</li>
<li>Under Repository permissions set <b>Contents</b> to Read and write, and <b>Actions</b> to Read and write.</li>
<li>Tap Generate token, copy it, and paste it below.</li>
</ol>
<input id='tokin' type='password' placeholder='Paste token here' autocomplete='off'>
<button class='btn' id='savetok'>Save token</button>
<p class='hint'>The token is stored only in this browser on this device. It can only reach the one repository you chose.</p>
</div>
<div id='conn-on' hidden><p>✓ Connected. <button class='mini' id='disconnect'>Disconnect</button></p></div>
<p class='hint' id='connmsg'></p>
</details>

</div></div>
"""


def esc(s):
    return html.escape(s, quote=True)


def img_tag(url, cls):
    return (f"<img class='{cls}' src='{esc(url)}' alt='' loading='lazy' "
            "referrerpolicy='no-referrer' onerror='this.remove()'>")


def render_reader_data(a):
    when = local_time(a["published"]).strftime("%d %b, %I:%M %p").lstrip("0") if a["published"] else ""
    meta = esc(a["source"]) + (" · " + when if when else "")
    parts = [f"<section id='d-{a['id']}' data-url='{esc(a['link'])}' hidden><div class='rwrap'>"]
    if a["image"]:
        parts.append(img_tag(a["image"], "hero"))
    parts.append(f"<div class='rmeta'>{meta}</div><h1 class='rtitle'>{esc(a['title'])}</h1><div class='rbody'>")
    if a["body"]:
        for kind, text in a["body"]:
            tag = "h3" if kind == "h" else "p"
            parts.append(f"<{tag}>{esc(text)}</{tag}>")
    else:
        if a["summary"]:
            parts.append(f"<p>{esc(a['summary'])}</p>")
        parts.append("<p class='note'>The full article isn't available in the app "
                     "(it may be behind a paywall or blocked from automatic reading).</p>")
    parts.append(f"</div><a class='btn wide' href='{esc(a['link'])}' target='_blank' rel='noopener'>"
                 f"Read on {esc(a['source'])} ↗</a></div></section>")
    return "".join(parts)


def render(sections, errors, info):
    now = local_time(datetime.now(timezone.utc))
    built = now.strftime("%a %d %b, %I:%M %p").replace(" 0", " ")
    cats = list(sections)
    for c in DEFAULT_FEEDS:
        if c not in cats:
            cats.append(c)
    cfg = {"repo": os.environ.get("GITHUB_REPOSITORY", ""), "built": built,
           "categories": cats, "sources": info}
    cfg_json = json.dumps(cfg, ensure_ascii=False).replace("</", "<\\/").replace("<!--", "<\\!--")

    parts = [
        "<!DOCTYPE html><html lang='en'><head><meta charset='utf-8'>",
        "<meta name='viewport' content='width=device-width,initial-scale=1,viewport-fit=cover'>",
        "<title>Daily News</title>",
        "<link rel='manifest' href='manifest.webmanifest'>",
        "<meta name='theme-color' content='#b3261e'>",
        "<link rel='icon' href='icon-192.png'>",
        "<link rel='apple-touch-icon' href='icon-192.png'>",
        "<meta name='mobile-web-app-capable' content='yes'>",
        f"<script>{PREFS_JS}</script>",
        "<style>", CSS, "</style></head><body>",
        "<header><div class='top'><h1>Daily News</h1>",
        "<a class='iconbtn' href='#settings' aria-label='Settings' title='Settings'>",
        "<svg viewBox='0 0 24 24' width='22' height='22' fill='none' stroke='currentColor' stroke-width='2' "
        "stroke-linecap='round' stroke-linejoin='round' aria-hidden='true'><circle cx='12' cy='12' r='3'/>"
        "<path d='M19.4 15a1.65 1.65 0 0 0 .33 1.82l.06.06a2 2 0 0 1 0 2.83 2 2 0 0 1-2.83 0l-.06-.06a1.65 1.65 0 0 0-1.82-.33 "
        "1.65 1.65 0 0 0-1 1.51V21a2 2 0 0 1-2 2 2 2 0 0 1-2-2v-.09A1.65 1.65 0 0 0 9 19.4a1.65 1.65 0 0 0-1.82.33l-.06.06a2 2 0 0 1-2.83 0 "
        "2 2 0 0 1 0-2.83l.06-.06a1.65 1.65 0 0 0 .33-1.82 1.65 1.65 0 0 0-1.51-1H3a2 2 0 0 1-2-2 2 2 0 0 1 2-2h.09A1.65 1.65 0 0 0 4.6 9 "
        "1.65 1.65 0 0 0-.33-1.82l-.06-.06a2 2 0 0 1 0-2.83 2 2 0 0 1 2.83 0l.06.06a1.65 1.65 0 0 0 1.82.33H9a1.65 1.65 0 0 0 1-1.51V3a2 2 0 0 1 "
        "2-2 2 2 0 0 1 2 2v.09a1.65 1.65 0 0 0 1 1.51 1.65 1.65 0 0 0 1.82-.33l.06-.06a2 2 0 0 1 2.83 0 2 2 0 0 1 0 2.83l-.06.06a1.65 1.65 0 0 0-.33 1.82V9 "
        "a1.65 1.65 0 0 0 1.51 1H21a2 2 0 0 1 2 2 2 2 0 0 1-2 2h-.09a1.65 1.65 0 0 0-1.51 1z'/></svg></a></div>",
        f"<div class='date'>{now.strftime('%A %d %B %Y, %I:%M %p').replace(' 0', ' ')}</div></header>",
        "<main><nav>",
    ]
    for cat in sections:
        parts.append(f"<a href='#c-{slug(cat)}'>{esc(cat)}</a>")
    parts.append("</nav>")

    everything = []
    for cat, articles in sections.items():
        parts.append(f"<h2 id='c-{slug(cat)}'>{esc(cat)}</h2>")
        if not articles:
            parts.append("<p class='empty'>No recent articles found.</p>")
        for a in articles:
            everything.append(a)
            when = ""
            if a["published"]:
                when = " · " + local_time(a["published"]).strftime("%d %b, %I:%M %p").lstrip("0")
            parts.append(
                f"<article class='card' data-id='{a['id']}'><div class='txt'>"
                f"<a class='t' href='{esc(a['link'])}'>{esc(a['title'])}</a>"
                f"<div class='meta'>{esc(a['source'])}{when}</div>"
                + (f"<p class='sum'>{esc(a['summary'])}</p>" if a["summary"] else "")
                + "</div>"
                + (img_tag(a["image"], "thumb") if a["image"] else "")
                + "</article>"
            )
    parts.append("</main><footer>")
    if errors:
        parts.append("<p class='err'>Couldn't load: " + "; ".join(esc(s) for s, _ in errors) + "</p>")
    parts.append("Updated automatically every few hours.</footer>")

    parts.append(
        "<div id='reader' hidden><div class='rbar'><button class='back'>← Back</button>"
        "<a id='orig' target='_blank' rel='noopener'>Open original ↗</a></div>"
        "<div id='rcontent'></div></div>"
    )
    parts.append(SETTINGS_HTML)
    parts.append("<div id='readers' hidden>")
    parts.extend(render_reader_data(a) for a in everything)
    parts.append("</div>")
    parts.append(f"<script type='application/json' id='cfg'>{cfg_json}</script>")
    parts.append(f"<script>{JS}</script></body></html>")
    return "".join(parts)


# ----------------------------- app files -------------------------------

MANIFEST = """{
  "name": "Daily News",
  "short_name": "News",
  "start_url": "./",
  "scope": "./",
  "display": "standalone",
  "background_color": "#b3261e",
  "theme_color": "#b3261e",
  "icons": [
    {"src": "icon-192.png", "sizes": "192x192", "type": "image/png", "purpose": "any"},
    {"src": "icon-512.png", "sizes": "512x512", "type": "image/png", "purpose": "any"},
    {"src": "icon-512.png", "sizes": "512x512", "type": "image/png", "purpose": "maskable"}
  ]
}
"""

SERVICE_WORKER = """const CACHE = 'news-v3';
self.addEventListener('install', () => self.skipWaiting());
self.addEventListener('activate', (e) => {
  e.waitUntil(
    caches.keys()
      .then((keys) => Promise.all(keys.filter((k) => k !== CACHE).map((k) => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});
// Online: always fetch the freshest copy. Offline: fall back to the last saved copy
// (which includes the full text of every article, so you can read offline).
self.addEventListener('fetch', (e) => {
  if (e.request.method !== 'GET') return;
  if (new URL(e.request.url).origin !== location.origin) return;
  e.respondWith(
    fetch(e.request, { cache: 'no-cache' })
      .then((res) => {
        const copy = res.clone();
        caches.open(CACHE).then((c) => c.put(e.request, copy));
        return res;
      })
      .catch(() => caches.match(e.request).then((m) => m || caches.match('./')))
  );
});
"""


def make_icon(size):
    """Draw a simple 'headlines' icon (red square, white text lines) as a PNG."""
    import struct
    import zlib

    bg, fg = (179, 38, 30), (255, 255, 255)
    # (x0, x1, y0, y1) as fractions; kept inside the central 80% so it survives masking
    bars = [(0.22, 0.78, 0.26, 0.37), (0.22, 0.78, 0.47, 0.51),
            (0.22, 0.78, 0.59, 0.63), (0.22, 0.60, 0.71, 0.75)]
    raw = bytearray()
    for y in range(size):
        raw.append(0)
        fy = y / size
        for x in range(size):
            fx = x / size
            on = any(x0 <= fx <= x1 and y0 <= fy <= y1 for x0, x1, y0, y1 in bars)
            raw.extend(fg if on else bg)

    def chunk(kind, data):
        body = kind + data
        return struct.pack(">I", len(data)) + body + struct.pack(">I", zlib.crc32(body) & 0xFFFFFFFF)

    return (b"\x89PNG\r\n\x1a\n"
            + chunk(b"IHDR", struct.pack(">IIBBBBB", size, size, 8, 2, 0, 0, 0))
            + chunk(b"IDAT", zlib.compress(bytes(raw), 9))
            + chunk(b"IEND", b""))


def write_app_files():
    OUTPUT_DIR.mkdir(exist_ok=True)
    (OUTPUT_DIR / "manifest.webmanifest").write_text(MANIFEST, encoding="utf-8")
    (OUTPUT_DIR / "sw.js").write_text(SERVICE_WORKER, encoding="utf-8")
    for size in (192, 512):
        (OUTPUT_DIR / f"icon-{size}.png").write_bytes(make_icon(size))


def main():
    parser = argparse.ArgumentParser(description="Build a daily news digest.")
    parser.add_argument("--open", action="store_true", help="open the result in your browser")
    args = parser.parse_args()

    sections, errors, info = build_sections()
    write_app_files()
    OUTPUT_FILE.write_text(render(sections, errors, info), encoding="utf-8")

    arts = [a for v in sections.values() for a in v]
    print(f"Saved {len(arts)} articles to {OUTPUT_FILE} "
          f"({sum(1 for a in arts if a['body'])} with full text, "
          f"{sum(1 for a in arts if a['image'])} with pictures)")
    for source, err in errors:
        print(f"  ! {source} failed: {err}", file=sys.stderr)
    if args.open:
        webbrowser.open(OUTPUT_FILE.as_uri())


if __name__ == "__main__":
    main()
