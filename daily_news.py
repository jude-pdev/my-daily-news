#!/usr/bin/env python3
"""
Daily News Digest
-----------------
Fetches RSS/Atom feeds and builds a clean, ad-free news web app in ./site
(index.html plus the files that let a phone install it like a real app).

Usage:
    python3 daily_news.py            # build site/index.html
    python3 daily_news.py --open     # build and open it in your browser

Needs Python 3.8+ and nothing else (standard library only).
Edit the FEEDS dictionary below to add or remove sources.
"""

import argparse
import html
import re
import sys
import webbrowser
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path
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
SUMMARY_CHARS = 220       # summary length cut-off
OUTPUT_DIR = Path(__file__).with_name("site")
OUTPUT_FILE = OUTPUT_DIR / "index.html"
TIMEZONE_NAME = "Australia/Sydney"   # used for display times
# ----------------------------------------------------------------------


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


def fetch_feed(source, url):
    """Return (source, [articles], error_or_None)."""
    try:
        req = Request(url, headers={"User-Agent": "Mozilla/5.0 (DailyNewsDigest)"})
        with urlopen(req, timeout=15) as resp:
            data = resp.read()
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
        articles.append(
            {"title": title, "link": link, "summary": summary,
             "published": published, "source": source}
        )
    return source, articles, None


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

    sections, errors = {cat: [] for cat in FEEDS}, []
    seen = set()
    for (cat, _, _), (source, articles, err) in zip(jobs, results):
        if err:
            errors.append((source, err))
            continue
        kept = 0
        for a in sorted(articles, key=lambda x: x["published"] or datetime.min.replace(tzinfo=timezone.utc), reverse=True):
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

    epoch = datetime.min.replace(tzinfo=timezone.utc)
    for cat in sections:
        sections[cat].sort(key=lambda x: x["published"] or epoch, reverse=True)
    return sections, errors


CSS = """
:root{--bg:#f6f5f1;--card:#fff;--text:#1c1c1e;--muted:#6b6b70;--accent:#b3261e;--line:#e4e2dc}
@media(prefers-color-scheme:dark){:root{--bg:#141415;--card:#1e1e20;--text:#ececee;--muted:#9a9aa1;--accent:#ff8a80;--line:#2e2e32}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--text);font:16px/1.5 Georgia,'Times New Roman',serif}
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
article{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:14px 16px;margin-bottom:10px}
article a.t{color:var(--text);text-decoration:none;font-size:1.1rem;font-weight:700;line-height:1.3;display:block}
article a.t:hover{color:var(--accent)}
.meta{font:12px system-ui,sans-serif;color:var(--muted);margin-top:4px}
.sum{margin:8px 0 0;color:var(--muted);font-size:.95rem}
.empty,.err,footer{color:var(--muted);font:13px system-ui,sans-serif}
footer{padding:30px 18px 50px}
"""


def render(sections, errors):
    now = local_time(datetime.now(timezone.utc))
    parts = [
        "<!DOCTYPE html><html lang='en'><head><meta charset='utf-8'>",
        "<meta name='viewport' content='width=device-width,initial-scale=1'>",
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
        parts.append(f"<a href='#{cat.lower()}'>{html.escape(cat)}</a>")
    parts.append("</nav>")

    for cat, articles in sections.items():
        parts.append(f"<h2 id='{cat.lower()}'>{html.escape(cat)}</h2>")
        if not articles:
            parts.append("<p class='empty'>No recent articles found.</p>")
        for a in articles:
            when = ""
            if a["published"]:
                when = " · " + local_time(a["published"]).strftime("%d %b, %I:%M %p").lstrip("0")
            parts.append(
                "<article>"
                f"<a class='t' href='{html.escape(a['link'], quote=True)}' target='_blank' rel='noopener'>{html.escape(a['title'])}</a>"
                f"<div class='meta'>{html.escape(a['source'])}{when}</div>"
                + (f"<p class='sum'>{html.escape(a['summary'])}</p>" if a["summary"] else "")
                + "</article>"
            )
    parts.append("</main><footer>")
    if errors:
        parts.append("<p class='err'>Couldn't load: " + "; ".join(html.escape(s) for s, _ in errors) + "</p>")
    parts.append(
        "Updated automatically every few hours.</footer>"
        "<script>if('serviceWorker' in navigator){navigator.serviceWorker.register('sw.js').catch(function(){});}</script>"
        "</body></html>"
    )
    return "".join(parts)


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

SERVICE_WORKER = """const CACHE = 'news-v1';
self.addEventListener('install', () => self.skipWaiting());
self.addEventListener('activate', (e) => {
  e.waitUntil(
    caches.keys()
      .then((keys) => Promise.all(keys.filter((k) => k !== CACHE).map((k) => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});
// Online: always fetch the freshest copy. Offline: fall back to the last saved copy.
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

    total = sum(len(v) for v in sections.values())
    print(f"Saved {total} articles to {OUTPUT_FILE}")
    for source, err in errors:
        print(f"  ! {source} failed: {err}", file=sys.stderr)
    if args.open:
        webbrowser.open(OUTPUT_FILE.as_uri())


if __name__ == "__main__":
    main()
