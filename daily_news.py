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
Edit FEEDS and the settings below to customise.
"""

import argparse
import html
import json
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
FEEDS = {
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


def fetch_feed(source, url):
    """Return (source, [articles], error_or_None)."""
    try:
        data, _ = http_get(url)
        root = ET.fromstring(data)
    except Exception as exc:  # network, HTTP or XML errors
        return source, [], f"{type(exc).__name__}: {exc}"

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
    return source, articles, None


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


def build_sections():
    cutoff = datetime.now(timezone.utc) - timedelta(hours=MAX_AGE_HOURS)
    jobs = [(cat, src, url) for cat, srcs in FEEDS.items() for src, url in srcs.items()]

    with ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(lambda j: fetch_feed(j[1], j[2]), jobs))

    epoch = datetime.min.replace(tzinfo=timezone.utc)
    sections, errors = {cat: [] for cat in FEEDS}, []
    seen = set()
    for (cat, _, _), (source, articles, err) in zip(jobs, results):
        if err:
            errors.append((source, err))
            continue
        kept = 0
        for a in sorted(articles, key=lambda x: x["published"] or epoch, reverse=True):
            if a["published"] and a["published"] < cutoff:
                continue
            key = re.sub(r"\W+", "", a["title"].lower())
            if key in seen:
                continue
            seen.add(key)
            sections[cat].append(a)
            kept += 1
            if kept >= MAX_PER_SOURCE:
                break

    for cat in sections:
        sections[cat].sort(key=lambda x: x["published"] or epoch, reverse=True)

    everything = [a for arts in sections.values() for a in arts]
    for i, a in enumerate(everything):
        a["id"] = i
    with ThreadPoolExecutor(max_workers=12) as pool:
        list(pool.map(enrich, everything))
    for a in everything:
        a["body"] = trim_body(a["body"])
    return sections, errors


# ------------------------------ page -----------------------------------

CSS = """
:root{--bg:#f6f5f1;--card:#fff;--text:#1c1c1e;--muted:#6b6b70;--accent:#b3261e;--line:#e4e2dc}
@media(prefers-color-scheme:dark){:root{--bg:#141415;--card:#1e1e20;--text:#ececee;--muted:#9a9aa1;--accent:#ff8a80;--line:#2e2e32}}
*{box-sizing:border-box}
[hidden]{display:none!important}
body{margin:0;background:var(--bg);color:var(--text);font:16px/1.5 Georgia,'Times New Roman',serif}
body.lock{overflow:hidden}
header,main,footer{max-width:760px;margin:0 auto;padding:0 18px}
header{padding-top:32px;padding-bottom:8px}
h1{margin:0;font-size:2rem;letter-spacing:-.5px}
.top{display:flex;justify-content:space-between;align-items:center;gap:12px}
.refresh{font:14px system-ui,sans-serif;color:var(--text);background:var(--card);border:1px solid var(--line);border-radius:999px;padding:6px 14px;cursor:pointer}
.refresh:active{border-color:var(--accent)}
.date{color:var(--muted);font:14px system-ui,sans-serif;margin-top:4px}
nav{position:sticky;top:0;background:var(--bg);padding:10px 0;margin:10px 0 0;border-bottom:1px solid var(--line);
    display:flex;gap:8px;flex-wrap:wrap;font:14px system-ui,sans-serif}
nav a{color:var(--text);text-decoration:none;padding:5px 12px;border:1px solid var(--line);border-radius:999px}
nav a:hover{border-color:var(--accent);color:var(--accent)}
h2{font:700 13px system-ui,sans-serif;text-transform:uppercase;letter-spacing:1.5px;color:var(--accent);margin:34px 0 10px}
article.card{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:14px 16px;margin-bottom:10px;
    display:flex;gap:14px;align-items:flex-start;cursor:pointer}
.txt{flex:1;min-width:0}
article.card a.t{color:var(--text);text-decoration:none;font-size:1.05rem;font-weight:700;line-height:1.3;display:block}
article.card:hover a.t{color:var(--accent)}
.thumb{width:104px;height:104px;object-fit:cover;border-radius:8px;flex:none;background:var(--line)}
.meta{font:12px system-ui,sans-serif;color:var(--muted);margin-top:4px}
.sum{margin:8px 0 0;color:var(--muted);font-size:.92rem}
.empty,.err,footer{color:var(--muted);font:13px system-ui,sans-serif}
footer{padding:30px 18px 50px}
@media(max-width:420px){.thumb{width:84px;height:84px}.sum{display:none}}

#reader{position:fixed;inset:0;z-index:100;background:var(--bg);overflow-y:auto;-webkit-overflow-scrolling:touch}
.rbar{position:sticky;top:0;z-index:2;background:var(--bg);border-bottom:1px solid var(--line);
    display:flex;justify-content:space-between;align-items:center;padding:10px 16px;
    padding-top:calc(10px + env(safe-area-inset-top,0px));font:14px system-ui,sans-serif}
.rbar button,.rbar a,.btn{color:var(--text);background:var(--card);border:1px solid var(--line);border-radius:999px;
    padding:7px 14px;text-decoration:none;font:14px system-ui,sans-serif;cursor:pointer}
.rwrap{max-width:680px;margin:0 auto;padding:18px 18px 70px}
.hero{width:100%;max-height:360px;object-fit:cover;border-radius:10px;margin-bottom:14px;background:var(--line)}
.rmeta{font:13px system-ui,sans-serif;color:var(--accent);font-weight:600}
.rtitle{font-size:1.7rem;line-height:1.2;margin:8px 0 18px}
.rbody p{font-size:1.1rem;line-height:1.7;margin:0 0 1.1em}
.rbody h3{font-size:1.2rem;margin:1.4em 0 .5em}
.note{font:14px system-ui,sans-serif;color:var(--muted);background:var(--card);border:1px solid var(--line);border-radius:8px;padding:10px 12px}
.btn{display:inline-block;margin-top:14px}
"""

JS = """
(function(){
  var reader=document.getElementById('reader'),content=document.getElementById('rcontent'),orig=document.getElementById('orig');
  function show(id){
    var d=document.getElementById('d-'+id);
    if(!d){hide();return;}
    content.innerHTML=d.innerHTML;
    orig.href=d.getAttribute('data-url');
    reader.hidden=false;document.body.classList.add('lock');reader.scrollTop=0;
  }
  function hide(){reader.hidden=true;document.body.classList.remove('lock');content.innerHTML='';}
  function sync(){var m=location.hash.match(/^#read-(\\d+)$/);if(m){show(m[1]);}else{hide();}}
  document.addEventListener('click',function(e){
    var c=e.target.closest('article.card');
    if(!c)return;
    e.preventDefault();
    location.hash='read-'+c.getAttribute('data-id');
  });
  document.getElementById('back').addEventListener('click',function(){
    if(history.length>1){history.back();}else{location.hash='';}
  });
  window.addEventListener('hashchange',sync);
  sync();
  if('serviceWorker' in navigator){navigator.serviceWorker.register('sw.js').catch(function(){});}
})();
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
    parts.append(f"</div><a class='btn' href='{esc(a['link'])}' target='_blank' rel='noopener'>"
                 f"Read on {esc(a['source'])} ↗</a></div></section>")
    return "".join(parts)


def render(sections, errors):
    now = local_time(datetime.now(timezone.utc))
    parts = [
        "<!DOCTYPE html><html lang='en'><head><meta charset='utf-8'>",
        "<meta name='viewport' content='width=device-width,initial-scale=1,viewport-fit=cover'>",
        "<title>Daily News</title>",
        "<link rel='manifest' href='manifest.webmanifest'>",
        "<meta name='theme-color' content='#b3261e'>",
        "<link rel='icon' href='icon-192.png'>",
        "<link rel='apple-touch-icon' href='icon-192.png'>",
        "<meta name='mobile-web-app-capable' content='yes'>",
        "<style>", CSS, "</style></head><body>",
        "<header><div class='top'><h1>Daily News</h1>",
        "<button class='refresh' onclick='location.reload()' aria-label='Refresh'>Refresh</button></div>",
        f"<div class='date'>{now.strftime('%A %d %B %Y, %I:%M %p').replace(' 0', ' ')}</div></header>",
        "<main><nav>",
    ]
    for cat in sections:
        parts.append(f"<a href='#{cat.lower()}'>{esc(cat)}</a>")
    parts.append("</nav>")

    everything = []
    for cat, articles in sections.items():
        parts.append(f"<h2 id='{cat.lower()}'>{esc(cat)}</h2>")
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

    # reader overlay + hidden article data
    parts.append(
        "<div id='reader' hidden><div class='rbar'><button id='back'>← Back</button>"
        "<a id='orig' target='_blank' rel='noopener'>Open original ↗</a></div>"
        "<div id='rcontent'></div></div>"
    )
    parts.append("<div id='readers' hidden>")
    parts.extend(render_reader_data(a) for a in everything)
    parts.append("</div>")
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

SERVICE_WORKER = """const CACHE = 'news-v2';
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

    sections, errors = build_sections()
    write_app_files()
    OUTPUT_FILE.write_text(render(sections, errors), encoding="utf-8")

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
