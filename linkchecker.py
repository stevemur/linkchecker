#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["httpx>=0.27", "rich>=13"]
# ///
"""
linkchecker — crawl a website and report broken links.

Usage:
    uv run linkchecker.py https://example.com
    uv run linkchecker.py https://example.com --concurrency 20 --max-pages 200
    uv run linkchecker.py https://example.com --no-external
"""

from __future__ import annotations

import argparse
import asyncio
import csv
import ipaddress
import json
import re
import time
from collections import defaultdict, deque
from dataclasses import dataclass, field
from datetime import datetime
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import urldefrag, urljoin, urlparse

import httpx
from rich import box
from rich.align import Align
from rich.console import Console, Group
from rich.live import Live
from rich.panel import Panel
from rich.rule import Rule
from rich.table import Table
from rich.text import Text

console = Console()

USER_AGENT = (
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 14_0) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/130.0 Safari/537.36 linkchecker/1.0"
)

# Statuses that usually mean "a bot was blocked", not "the page is gone".
SOFT_FAIL = {401, 403, 405, 406, 429, 451, 999}

DEFAULT_EXCLUDES = [
    r"/wp-admin", r"/wp-login\.php", r"/xmlrpc\.php", r"[?&]replytocom=",
    r"/feed/?$", r"/wp-json", r"[?&]share=", r"/cdn-cgi/",
]

IMAGE_RE = re.compile(r"\.(jpe?g|png|gif|webp|avif|svg|bmp|ico|tiff?)(\?|$)", re.I)
ASSET_RE = re.compile(r"\.(jpe?g|png|gif|webp|avif|svg|bmp|ico|tiff?|pdf|zip|mp[34]|mov|webm|"
                      r"css|js|woff2?|ttf|eot)(\?|$)", re.I)

SKIP_SCHEMES = ("mailto:", "tel:", "javascript:", "data:", "sms:", "#", "about:")


# ───────────────────────────── HTML parsing ──────────────────────────────

class LinkExtractor(HTMLParser):
    """Collects (url, kind, text) from <a>, <img>, <link>, <script>, <iframe>, <source>."""

    ATTRS = {
        "a": ("href", "link"),
        "img": ("src", "image"),
        "link": ("href", "asset"),
        "script": ("src", "script"),
        "iframe": ("src", "iframe"),
        "source": ("src", "media"),
        "video": ("src", "media"),
        "audio": ("src", "media"),
    }

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.links: list[tuple[str, str, str]] = []
        self.base: str | None = None
        self.title: str = ""
        self._in_title = False
        self._a_index: int | None = None
        self._a_text: list[str] = []

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag == "title" and not self.title:
            self._in_title = True
            return
        if tag == "base" and a.get("href"):
            self.base = a["href"]
            return
        if tag == "link":
            rel = (a.get("rel") or "").lower()
            # Skip hints that are not real resources.
            if any(r in rel for r in ("preconnect", "dns-prefetch", "pingback", "profile")):
                return
        if tag == "meta":
            prop = (a.get("property") or a.get("name") or "").lower()
            if prop in ("og:image", "og:image:url", "twitter:image") and a.get("content"):
                self.links.append((a["content"].strip(), "image", f"[{prop}]"))
            return
        # Images: src, lazy-load variants, and every candidate in srcset.
        if tag in ("img", "source"):
            alt = a.get("alt") or ""
            for attr in ("src", "data-src", "data-lazy-src", "data-original"):
                if a.get(attr):
                    kind = "image" if tag == "img" else "media"
                    self.links.append((a[attr].strip(), kind, f"[alt: {alt}]" if alt else ""))
            for attr in ("srcset", "data-srcset", "data-lazy-srcset"):
                for cand in (a.get(attr) or "").split(","):
                    part = cand.strip().split(" ")[0]
                    if part:
                        self.links.append((part, "image", "[srcset]"))
            if tag == "img" and self._a_index is not None and alt:
                self._a_text.append(f"[img: {alt}]")
            return
        if tag in self.ATTRS:
            attr, kind = self.ATTRS[tag]
            val = a.get(attr)
            if val:
                if tag == "a" and IMAGE_RE.search(val):
                    kind = "image"
                self.links.append((val.strip(), kind, ""))
                if tag == "a":
                    self._a_index = len(self.links) - 1
                    self._a_text = []

    def handle_data(self, data):
        if self._in_title:
            self.title += data
        if self._a_index is not None:
            self._a_text.append(data)

    def handle_endtag(self, tag):
        if tag == "title":
            self._in_title = False
        if tag == "a" and self._a_index is not None:
            text = " ".join("".join(self._a_text).split())[:80]
            url, kind, _ = self.links[self._a_index]
            self.links[self._a_index] = (url, kind, text)
            self._a_index = None


# ──────────────────────────── Status meanings ────────────────────────────

def error_label(e: Exception) -> str:
    """Turn a network error into a short, plain label."""
    msg = str(e).lower()
    if isinstance(e, httpx.TimeoutException):
        return "TIMEOUT"
    if isinstance(e, httpx.TooManyRedirects):
        return "LOOP"
    if "ssl" in msg or "certificate" in msg:
        return "BAD SSL"
    if isinstance(e, httpx.ConnectError):
        if any(s in msg for s in ("nodename", "name or service", "name resolution",
                                  "no address associated", "getaddrinfo")):
            return "NO DOMAIN"
        return "NO SERVER"
    if isinstance(e, (httpx.RemoteProtocolError, httpx.ReadError)):
        return "NO REPLY"
    return "ERROR"


ERROR_MEANINGS = {
    "NO DOMAIN": "The domain name does not exist any more. It probably expired. The link is dead.",
    "NO SERVER": "The domain exists, but no server answered at its address. Often an old server that was shut down.",
    "TIMEOUT": "The server took too long to answer. It may be slow or down. Try it in a browser.",
    "BAD SSL": "The site's HTTPS certificate is wrong or expired. Browsers show a security warning.",
    "NO REPLY": "The server closed the connection without an answer.",
    "LOOP": "The URL redirects in a circle and never lands on a page.",
    "ERROR": "Some other network error.",
}

HTTP_MEANINGS = {
    400: "Bad request", 401: "Login required", 403: "Forbidden (often bot blocking)",
    404: "Not found", 405: "Method not allowed", 406: "Not acceptable",
    410: "Gone (removed on purpose)", 429: "Too many requests (rate limited)",
    451: "Blocked for legal reasons", 500: "Server error", 502: "Bad gateway",
    503: "Service unavailable", 504: "Gateway timeout",
    520: "Cloudflare: unknown error from the site", 521: "Cloudflare: the site's server is down",
    522: "Cloudflare: the site's server did not answer", 523: "Cloudflare: the site's server is unreachable",
    525: "Cloudflare: SSL handshake failed", 526: "Cloudflare: invalid SSL certificate",
    999: "LinkedIn's code for blocking bots",
}


def meaning(label: str) -> str:
    if label in ERROR_MEANINGS:
        return ERROR_MEANINGS[label]
    if label.isdigit():
        code = int(label)
        return HTTP_MEANINGS.get(code) or ("Server error" if code >= 500 else "Client error")
    return ""


def legend_rows(results) -> list[tuple[str, str]]:
    """One (label, meaning) row for each status that appears, numbers first."""
    labels = {r.label for r in results}
    return [(l, meaning(l)) for l in sorted(labels, key=lambda l: (not l.isdigit(), l))]


# ─────────────────────────────── Data types ──────────────────────────────

@dataclass
class Result:
    url: str
    status: int | None
    ok: bool
    soft: bool = False          # blocked / rate-limited / uncertain
    error: str = ""
    final_url: str = ""
    elapsed: float = 0.0

    @property
    def label(self) -> str:
        if self.status is not None:
            return str(self.status)
        return self.error or "ERR"


@dataclass
class Referrer:
    page: str
    text: str
    kind: str


@dataclass
class Stats:
    pages_crawled: int = 0
    links_found: int = 0
    checked: int = 0
    ok: int = 0
    broken: int = 0
    soft: int = 0
    redirects: int = 0
    started: float = field(default_factory=time.monotonic)


# ───────────────────────────── The checker ───────────────────────────────

class LinkChecker:
    def __init__(self, root: str, args: argparse.Namespace):
        self.root = root.rstrip("/") + "/"
        self.args = args
        host = urlparse(self.root).hostname or ""
        self.site_hosts = {host, host.removeprefix("www."), "www." + host.removeprefix("www.")}
        self.excludes = [re.compile(p) for p in DEFAULT_EXCLUDES + (args.exclude or [])]

        self.stats = Stats()
        self.results: dict[str, Result] = {}
        self.referrers: dict[str, list[Referrer]] = defaultdict(list)
        self.seen_pages: set[str] = set()
        self.titles: dict[str, str] = {}
        self.queued_checks: set[str] = set()
        self.page_queue: asyncio.Queue[str] = asyncio.Queue()
        self.check_queue: asyncio.Queue[str] = asyncio.Queue()
        self.host_limits: dict[str, asyncio.Semaphore] = {}
        self.recent_broken: deque[tuple[str, Result]] = deque(maxlen=8)
        self.active: dict[int, str] = {}
        self.phase = "Starting"
        self.stop = False

    # ── helpers ──
    def is_internal(self, url: str) -> bool:
        return (urlparse(url).hostname or "") in self.site_hosts

    def is_excluded(self, url: str) -> bool:
        return any(p.search(url) for p in self.excludes)

    def normalize(self, base: str, raw: str) -> str | None:
        raw = raw.strip()
        if not raw or raw.lower().startswith(SKIP_SCHEMES):
            return None
        try:
            url, _ = urldefrag(urljoin(base, raw))
        except ValueError:
            return None
        p = urlparse(url)
        if p.scheme not in ("http", "https") or not p.hostname:
            return None
        return url

    def host_sem(self, url: str) -> asyncio.Semaphore:
        host = urlparse(url).hostname or ""
        if host not in self.host_limits:
            limit = self.args.concurrency if self.is_internal(url) else 3
            self.host_limits[host] = asyncio.Semaphore(limit)
        return self.host_limits[host]

    def record(self, res: Result) -> None:
        self.results[res.url] = res
        self.stats.checked += 1
        if res.ok:
            self.stats.ok += 1
            if res.final_url and res.final_url.rstrip("/") != res.url.rstrip("/"):
                self.stats.redirects += 1
        elif res.soft:
            self.stats.soft += 1
        else:
            self.stats.broken += 1
            self.recent_broken.appendleft((res.url, res))

    def enqueue_page(self, url: str) -> None:
        if url in self.seen_pages or self.is_excluded(url):
            return
        if self.args.max_pages and len(self.seen_pages) >= self.args.max_pages:
            return
        self.seen_pages.add(url)
        self.page_queue.put_nowait(url)

    def enqueue_check(self, url: str) -> None:
        if url in self.queued_checks or self.is_excluded(url):
            return
        self.queued_checks.add(url)
        self.check_queue.put_nowait(url)

    # ── network ──
    async def fetch_check(self, client: httpx.AsyncClient, url: str) -> Result:
        """HEAD first, fall back to GET. Never downloads full bodies."""
        t0 = time.monotonic()
        last_err = ""
        for attempt in range(2):
            try:
                async with self.host_sem(url):
                    resp = await client.head(url)
                    if resp.status_code in (403, 404, 405, 406, 501) or resp.status_code >= 500:
                        async with client.stream("GET", url) as r:
                            resp = r
                code = resp.status_code
                soft = code in SOFT_FAIL
                return Result(url, code, ok=code < 400, soft=soft and code >= 400,
                              final_url=str(resp.url), elapsed=time.monotonic() - t0)
            except httpx.TooManyRedirects:
                return Result(url, None, ok=False, error="LOOP")
            except (httpx.HTTPError, ValueError) as e:
                last_err = error_label(e)
                if last_err in ("NO DOMAIN", "BAD SSL"):
                    break  # retrying will not help
            await asyncio.sleep(1.0)
        # Timeouts on third-party sites are uncertain, not proof of a dead link.
        soft = last_err == "TIMEOUT" and not self.is_internal(url)
        return Result(url, None, ok=False, soft=soft, error=last_err,
                      elapsed=time.monotonic() - t0)

    async def crawl_page(self, client: httpx.AsyncClient, url: str) -> None:
        t0 = time.monotonic()
        try:
            async with self.host_sem(url):
                resp = await client.get(url)
        except httpx.HTTPError as e:
            err = error_label(e)
            if url not in self.results:
                self.record(Result(url, None, ok=False, error=err))
            return

        code = resp.status_code
        if url not in self.results:
            self.record(Result(url, code, ok=code < 400, soft=code in SOFT_FAIL and code >= 400,
                               final_url=str(resp.url), elapsed=time.monotonic() - t0))
        self.queued_checks.add(url)
        self.stats.pages_crawled += 1

        final = str(resp.url)
        ctype = resp.headers.get("content-type", "")
        if code >= 400 or "html" not in ctype or not self.is_internal(final):
            return

        parser = LinkExtractor()
        try:
            parser.feed(resp.text)
        except Exception:
            return
        base = urljoin(final, parser.base) if parser.base else final
        if parser.title.strip():
            self.titles[url] = " ".join(parser.title.split())

        seen_here: set[str] = set()
        for raw, kind, text in parser.links:
            link = self.normalize(base, raw)
            if not link or link in seen_here:
                continue
            seen_here.add(link)
            self.stats.links_found += 1
            self.referrers[link].append(Referrer(url, text, kind))
            internal = self.is_internal(link)
            if internal and kind == "link" and not ASSET_RE.search(urlparse(link).path):
                self.enqueue_page(link)
                if link not in self.seen_pages:  # hit max-pages or excluded
                    self.enqueue_check(link)
            elif internal or self.args.external:
                self.enqueue_check(link)

    async def seed_from_sitemap(self, client: httpx.AsyncClient) -> int:
        """Pull page URLs from sitemap.xml (and nested sitemap indexes)."""
        todo = [urljoin(self.root, "sitemap.xml"), urljoin(self.root, "sitemap_index.xml"),
                urljoin(self.root, "wp-sitemap.xml")]
        done: set[str] = set()
        count = 0
        while todo and not self.stop:
            sm = todo.pop()
            if sm in done:
                continue
            done.add(sm)
            try:
                r = await client.get(sm)
            except httpx.HTTPError:
                continue
            if r.status_code != 200 or "<" not in r.text[:200]:
                continue
            for loc in re.findall(r"<loc>\s*(.*?)\s*</loc>", r.text, flags=re.S):
                loc = loc.replace("&amp;", "&")
                if not self.is_internal(loc):
                    continue
                if loc.endswith(".xml") or "sitemap" in loc.rsplit("/", 1)[-1]:
                    todo.append(loc)
                else:
                    before = len(self.seen_pages)
                    self.enqueue_page(loc)
                    count += len(self.seen_pages) - before
        return count

    # ── workers ──
    async def page_worker(self, client, wid: int):
        while not self.stop:
            url = await self.page_queue.get()
            self.active[wid] = url
            try:
                await self.crawl_page(client, url)
            finally:
                self.active.pop(wid, None)
                self.page_queue.task_done()

    async def check_worker(self, client, wid: int):
        while not self.stop:
            url = await self.check_queue.get()
            self.active[wid] = url
            try:
                if url not in self.results:
                    self.record(await self.fetch_check(client, url))
            finally:
                self.active.pop(wid, None)
                self.check_queue.task_done()

    async def run(self, live: Live) -> None:
        limits = httpx.Limits(max_connections=self.args.concurrency * 2,
                              max_keepalive_connections=self.args.concurrency)
        timeout = httpx.Timeout(self.args.timeout, connect=min(10, self.args.timeout))
        async with httpx.AsyncClient(
            headers={"User-Agent": USER_AGENT, "Accept": "text/html,*/*;q=0.8",
                     "Accept-Language": "en-US,en;q=0.9"},
            follow_redirects=True, timeout=timeout, limits=limits,
            max_redirects=10, http2=False,
        ) as client:
            self.enqueue_page(self.root)
            if self.args.sitemap:
                self.phase = "Reading sitemap"
                n = await self.seed_from_sitemap(client)
                self.sitemap_count = n
            self.phase = "Crawling"

            n = self.args.concurrency
            workers = [asyncio.create_task(self.page_worker(client, i)) for i in range(n)]
            workers += [asyncio.create_task(self.check_worker(client, 100 + i)) for i in range(n)]

            refresher = asyncio.create_task(self._refresh(live))
            try:
                # Pages spawn checks, so wait until both queues drain together.
                while True:
                    await self.page_queue.join()
                    self.phase = "Checking links"
                    await self.check_queue.join()
                    if self.page_queue.empty() and self.check_queue.empty():
                        break
                self.phase = "Done"
            finally:
                self.stop = True
                for w in workers:
                    w.cancel()
                refresher.cancel()
                await asyncio.gather(*workers, refresher, return_exceptions=True)
                live.update(self.render())

    async def _refresh(self, live: Live):
        while True:
            live.update(self.render())
            await asyncio.sleep(0.15)

    # ── live UI ──
    def render(self):
        s = self.stats
        elapsed = time.monotonic() - s.started
        rate = s.checked / elapsed if elapsed else 0
        pending = self.page_queue.qsize() + self.check_queue.qsize() + len(self.active)
        total = s.checked + pending
        frac = s.checked / total if total else 0

        # Stat tiles
        def tile(label, value, style):
            return Panel(Align.center(Text(f"{value:,}", style=f"bold {style}")),
                         title=label, title_align="center", border_style=style,
                         box=box.ROUNDED, padding=(0, 1))

        tiles = Table.grid(expand=True)
        for _ in range(6):
            tiles.add_column(ratio=1)
        tiles.add_row(
            tile("Pages", s.pages_crawled, "cyan"),
            tile("Links", s.links_found, "blue"),
            tile("Checked", s.checked, "white"),
            tile("OK", s.ok, "green"),
            tile("Broken", s.broken, "red"),
            tile("Blocked?", s.soft, "yellow"),
        )

        # Progress bar
        width = max(20, console.width - 40)
        filled = int(frac * width)
        bar = Text()
        bar.append("█" * filled, style="green")
        bar.append("░" * (width - filled), style="grey35")
        prog = Text.assemble(
            (f" {self.phase:<15}", "bold magenta"), bar,
            (f" {frac*100:5.1f}% ", "bold"),
        )
        meta = Text.assemble(
            ("  ⏱  ", ""), (f"{elapsed:6.1f}s", "bold"),
            ("   ⚡ ", ""), (f"{rate:5.1f} req/s", "bold"),
            ("   ⏳ ", ""), (f"{pending:,} pending", "bold"),
            ("   ↪ ", ""), (f"{s.redirects:,} redirects", "dim"),
        )

        # Active requests
        act = Table.grid(padding=(0, 1))
        act.add_column(style="dim")
        act.add_column(overflow="ellipsis", no_wrap=True)
        for url in list(self.active.values())[:5]:
            icon = "🌐" if not self.is_internal(url) else "📄"
            act.add_row(icon, Text(url, style="grey70"))
        if not self.active:
            act.add_row("  ", Text("idle", style="dim"))

        # Recent broken
        rb = Table(box=box.SIMPLE_HEAD, expand=True, show_edge=False, header_style="bold red")
        rb.add_column("Status", width=11)
        rb.add_column("Broken URL", overflow="ellipsis", no_wrap=True, ratio=3)
        rb.add_column("Found on", overflow="ellipsis", no_wrap=True, ratio=2, style="dim")
        for url, res in list(self.recent_broken):
            refs = self.referrers.get(url) or []
            where = short_path(refs[0].page) if refs else ""
            icon = "🖼 " if lc_is_image(self, url) else "🔗 "
            rb.add_row(Text(res.label, style="bold red"), icon + url, where)
        if not self.recent_broken:
            rb.add_row(Text("—", style="dim"), Text("No broken links yet 🎉", style="green"), "")

        body = Group(
            tiles,
            Text(),
            prog,
            meta,
            Rule(style="grey30"),
            Text(" In flight", style="bold"),
            act,
            Rule(style="grey30"),
            rb,
        )
        return Panel(body, title=f"[bold]🔗 linkchecker[/] [dim]·[/] [cyan]{self.root}[/]",
                     border_style="magenta", box=box.HEAVY, padding=(1, 2))


# ────────────────────────────── Reporting ────────────────────────────────

def short_path(url: str) -> str:
    p = urlparse(url)
    path = p.path or "/"
    return path + (f"?{p.query}" if p.query else "")


def is_ip_url(url: str) -> bool:
    try:
        ipaddress.ip_address(urlparse(url).hostname or "")
        return True
    except ValueError:
        return False


def ip_fix(lc: "LinkChecker", url: str) -> str:
    """Swap the IP address for the site's own scheme and domain."""
    site = urlparse(lc.root)
    return urlparse(url)._replace(scheme=site.scheme, netloc=site.netloc).geturl()


def lc_is_image(lc: "LinkChecker", url: str) -> bool:
    refs = lc.referrers.get(url) or []
    return any(r.kind == "image" for r in refs) or bool(IMAGE_RE.search(urlparse(url).path))


def status_style(res: Result) -> str:
    if res.status is None:
        return "bold white on red"
    if res.status == 404 or res.status == 410:
        return "bold red"
    if res.status >= 500:
        return "bold magenta"
    return "bold yellow"


def report(lc: LinkChecker, interrupted: bool) -> tuple[list, list]:
    broken = [r for r in lc.results.values() if not r.ok and not r.soft]
    soft = [r for r in lc.results.values() if r.soft]
    broken.sort(key=lambda r: (not lc.is_internal(r.url), r.label, r.url))
    soft.sort(key=lambda r: (r.label, r.url))

    console.print()
    if interrupted:
        console.print(Panel("[yellow]Interrupted — showing partial results.[/]", border_style="yellow"))

    def make_table(title, rows, style):
        t = Table(title=title, title_style=f"bold {style}", box=box.ROUNDED,
                  border_style=style, expand=True, show_lines=True)
        t.add_column("Status", justify="center", width=11)
        t.add_column("Link", overflow="fold", ratio=3)
        t.add_column("Found on", overflow="fold", ratio=3)
        for r in rows:
            refs = lc.referrers.get(r.url, [])
            where = Text()
            for ref in refs[:4]:
                where.append("• ", style="dim")
                where.append(short_path(ref.page), style="cyan")
                if ref.text:
                    where.append(f'  “{ref.text}”', style="italic grey62")
                elif ref.kind != "link":
                    where.append(f"  ({ref.kind})", style="grey62")
                where.append("\n")
            if len(refs) > 4:
                where.append(f"  …and {len(refs) - 4} more pages\n", style="dim")
            link = Text(r.url, style="white")
            link.append("\n" + ("internal" if lc.is_internal(r.url) else "external"),
                        style="dim green" if lc.is_internal(r.url) else "dim blue")
            where.rstrip()
            t.add_row(Text(r.label, style=status_style(r)), link, where if where.plain else Text("—", style="dim"))
        return t

    broken_images = [r for r in broken if lc_is_image(lc, r.url)]
    broken_links = [r for r in broken if not lc_is_image(lc, r.url)]
    if broken_images:
        console.print(make_table(f"🖼   {len(broken_images)} missing image(s)", broken_images, "magenta"))
        console.print()
    if broken_links:
        console.print(make_table(f"💔  {len(broken_links)} broken link(s)", broken_links, "red"))
    if not broken:
        console.print(Panel(Align.center("[bold green]✨ No broken links found! ✨[/]"),
                            border_style="green"))

    if soft and lc.args.show_blocked:
        console.print()
        console.print(make_table(
            f"🤔  {len(soft)} link(s) blocked, rate-limited, or timed out (check by hand)",
            soft, "yellow"))
    elif soft:
        console.print(f"[yellow]🤔 {len(soft)} link(s) were blocked or timed out "
                      f"(often bot protection). Use [bold]--show-blocked[/] to list them.[/]")

    # Legend: what each status in the tables means.
    shown = broken + (soft if lc.args.show_blocked else [])
    if shown:
        legend = Table.grid(padding=(0, 2))
        legend.add_column(justify="right", no_wrap=True)
        legend.add_column(style="grey70")
        for label, text in legend_rows(shown):
            style = status_style(next(r for r in shown if r.label == label))
            legend.add_row(Text(label, style=style), text)
        console.print()
        console.print(Panel(legend, title="🔎 What the statuses mean", border_style="grey50",
                            expand=False))

    # Summary
    s = lc.stats
    elapsed = time.monotonic() - s.started
    summary = Table.grid(padding=(0, 3))
    summary.add_column(justify="right", style="dim")
    summary.add_column(style="bold")
    summary.add_row("Pages crawled", f"{s.pages_crawled:,}")
    summary.add_row("Unique URLs checked", f"{s.checked:,}")
    summary.add_row("OK", f"[green]{s.ok:,}[/]")
    summary.add_row("Missing images", f"[magenta]{len(broken_images):,}[/]")
    summary.add_row("Broken links", f"[red]{len(broken_links):,}[/]")
    summary.add_row("Blocked / uncertain", f"[yellow]{len(soft):,}[/]")
    n_ip = sum(1 for u in lc.referrers if is_ip_url(u))
    summary.add_row("IP-address URLs", f"[{'bold red' if n_ip else 'green'}]{n_ip:,}[/]")
    summary.add_row("Time", f"{elapsed:.1f}s")
    console.print()
    console.print(Panel(summary, title="📊 Summary", border_style="cyan", expand=False))
    return broken, soft


def write_reports(lc: LinkChecker, broken, soft, out: Path) -> None:
    out.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    host = urlparse(lc.root).hostname or "site"
    csv_path = out / f"{host}-{stamp}.csv"
    json_path = out / f"{host}-{stamp}.json"

    rows = []
    for kind, items in (("broken", broken), ("blocked", soft)):
        for r in items:
            for ref in lc.referrers.get(r.url, []) or [Referrer("", "", "")]:
                rows.append({
                    "severity": kind, "status": r.label, "url": r.url,
                    "is_image": lc_is_image(lc, r.url),
                    "internal": lc.is_internal(r.url), "found_on": ref.page,
                    "link_text": ref.text, "element": ref.kind,
                })
    with csv_path.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["severity", "status", "url", "is_image", "internal",
                                          "found_on", "link_text", "element"])
        w.writeheader()
        w.writerows(rows)
    json_path.write_text(json.dumps({
        "site": lc.root, "generated": datetime.now().isoformat(),
        "pages_crawled": lc.stats.pages_crawled, "urls_checked": lc.stats.checked,
        "broken": [{"url": r.url, "status": r.label,
                    "found_on": [ref.page for ref in lc.referrers.get(r.url, [])]} for r in broken],
        "blocked": [{"url": r.url, "status": r.label,
                     "found_on": [ref.page for ref in lc.referrers.get(r.url, [])]} for r in soft],
    }, indent=2))
    md_path = out / f"{host}-{stamp}.mdown"
    md_path.write_text(markdown_report(lc, broken, soft))
    console.print(f"\n📁 Reports saved:\n   [bold cyan]{md_path}[/]  [dim]← checklist for Bear[/]"
                  f"\n   [cyan]{csv_path}[/]\n   [cyan]{json_path}[/]\n")


def md_escape(s: str) -> str:
    return re.sub(r"([\[\]\\*_`|<>])", r"\\\1", s)


def markdown_report(lc: LinkChecker, broken: list[Result], soft: list[Result]) -> str:
    """A to-do list grouped by the page you need to edit. Each fix is a checkbox."""
    host = urlparse(lc.root).hostname or "site"
    s = lc.stats
    n_img = sum(1 for r in broken if lc_is_image(lc, r.url))

    def describe(r: Result, ref: Referrer) -> str:
        what = "🖼 Missing image" if lc_is_image(lc, r.url) else "🔗 Broken link"
        text = ref.text.strip()
        label = md_escape(text or (short_path(r.url) if lc.is_internal(r.url) else r.url))
        line = f"- [ ] **{r.label}** {what}: [{label}]({r.url})"
        if text:  # the label hides the URL, so show it too
            line += f" — `{r.url}`"
        if ref.kind not in ("link", "image"):
            line += f" _({ref.kind})_"
        if is_ip_url(r.url):
            line += " ⚠️ _IP address_"
        return line

    def ip_section() -> list[str]:
        ip_urls = sorted(u for u in lc.referrers if is_ip_url(u))
        if not ip_urls:
            return []
        by_page: dict[str, list[tuple[str, Referrer]]] = defaultdict(list)
        for u in ip_urls:
            seen = set()
            for ref in lc.referrers[u]:
                if ref.page not in seen:
                    seen.add(ref.page)
                    by_page[ref.page].append((u, ref))
        lines = ["## Links that use an IP address", "",
                 f"These URLs use a bare IP address in place of `{urlparse(lc.root).hostname}`. "
                 "Even if they load today, they break when the server moves, and HTTPS "
                 "certificates do not match them. Change each one to the domain name.", ""]
        for page in sorted(by_page, key=lambda p: (-len(by_page[p]), p)):
            name = lc.titles.get(page) or short_path(page)
            lines += [f"### [{md_escape(name)}]({page})", f"`{short_path(page)}`", ""]
            for u, ref in sorted(by_page[page]):
                res = lc.results.get(u)
                status = res.label if res else "not checked"
                kind = "🖼 image" if lc_is_image(lc, u) else "🔗 link"
                lines.append(f"- [ ] **{status}** {kind}: `{u}`")
                lines.append(f"    - change to: `{ip_fix(lc, u)}`")
            lines.append("")
        return lines

    def section(title: str, results: list[Result], intro: str) -> list[str]:
        by_page: dict[str, list[tuple[Result, Referrer]]] = defaultdict(list)
        orphans: list[Result] = []
        for r in results:
            refs = lc.referrers.get(r.url) or []
            if not refs:
                orphans.append(r)
            seen = set()
            for ref in refs:
                if ref.page in seen:
                    continue
                seen.add(ref.page)
                by_page[ref.page].append((r, ref))
        lines = [f"## {title}", "", intro, ""]
        for page in sorted(by_page, key=lambda p: (-len(by_page[p]), p)):
            name = lc.titles.get(page) or short_path(page)
            lines.append(f"### [{md_escape(name)}]({page})")
            lines.append(f"`{short_path(page)}` · {len(by_page[page])} to fix")
            lines.append("")
            # Images first, then links.
            items = sorted(by_page[page], key=lambda x: (not lc_is_image(lc, x[0].url), x[0].url))
            lines += [describe(r, ref) for r, ref in items]
            lines.append("")
        if orphans:
            lines.append("### Not linked from a crawled page")
            lines.append("")
            lines += [f"- [ ] **{r.label}** [{md_escape(r.url)}]({r.url})" for r in orphans]
            lines.append("")
        return lines

    out = [
        f"# Broken links — {host}",
        "",
        f"Checked {datetime.now():%B %-d, %Y at %-I:%M %p}. "
        f"Crawled {s.pages_crawled:,} pages and checked {s.checked:,} unique URLs.",
        "",
        f"- **{n_img}** missing images",
        f"- **{len(broken) - n_img}** broken links",
        f"- **{len(soft)}** links to check by hand (blocked or timed out)",
        f"- **{sum(1 for u in lc.referrers if is_ip_url(u))}** URLs that use an IP address",
        "",
        "#linkchecker",
        "",
    ]
    if broken or soft:
        out += ["## What the statuses mean", "", "| Status | Meaning |", "| --- | --- |"]
        out += [f"| **{label}** | {text} |" for label, text in legend_rows(broken + soft)]
        out.append("")
    if broken:
        out += section("Fix these", broken,
                       "Each heading is a page on the site. Each checkbox is one fix on that page.")
    else:
        out += ["## Fix these", "", "Nothing broken. ✨", ""]
    out += ip_section()
    if soft:
        out += section("Check by hand", soft,
                       "These sites blocked the checker (401/403/429/999) or timed out. "
                       "Most work fine in a browser. Open each one to make sure.")
    return "\n".join(out).rstrip() + "\n"


# ──────────────────────────────── Main ───────────────────────────────────

def banner():
    art = Text(justify="center")
    title = "L I N K C H E C K E R"
    colors = ["#ff5f87", "#ff875f", "#ffaf5f", "#ffd75f", "#afff5f", "#5fffaf",
              "#5fd7ff", "#5fafff", "#875fff", "#af5fff", "#d75fff"]
    for i, ch in enumerate(title):
        art.append(ch, style=f"bold {colors[i % len(colors)]}")
    console.print(Panel(Group(Align.center(art),
                              Align.center(Text("find every broken link on your site 🔗", style="dim"))),
                  box=box.DOUBLE, border_style="magenta"))


def preflight(url: str) -> bool:
    """Make sure the site root answers before we start a full crawl."""
    with console.status(f"[cyan]Contacting {url} …"):
        try:
            r = httpx.get(url, headers={"User-Agent": USER_AGENT}, follow_redirects=True, timeout=20)
        except httpx.HTTPError as e:
            console.print(Panel(f"[bold red]Cannot reach {url}[/]\n{type(e).__name__}: {e}",
                                title="❌ Site unreachable", border_style="red"))
            return False
    if r.status_code < 400:
        console.print(f"[green]✔[/] {url} answered [bold]{r.status_code}[/] — starting crawl\n")
        return True
    msg = f"[bold red]{url} returned HTTP {r.status_code}.[/]\n"
    if r.status_code == 503 and "<title>Maintenance</title>" in r.text:
        msg += ("\nWordPress is in [bold]maintenance mode[/]. An update is running or got stuck.\n"
                "If it lasts more than a few minutes, delete the [cyan].maintenance[/] file "
                "in the WordPress root folder.")
    elif r.headers.get("retry-after"):
        msg += f"\nThe server asks to retry after {r.headers['retry-after']} seconds."
    console.print(Panel(msg, title="❌ Site not available", border_style="red"))
    return False


def main():
    ap = argparse.ArgumentParser(description="Crawl a website and report broken links.")
    ap.add_argument("url", help="site root to crawl, e.g. https://example.com")
    ap.add_argument("-c", "--concurrency", type=int, default=12, help="parallel requests (default 12)")
    ap.add_argument("-m", "--max-pages", type=int, default=0, help="stop after N pages (0 = no limit)")
    ap.add_argument("-t", "--timeout", type=float, default=20, help="per-request timeout in seconds")
    ap.add_argument("--no-external", dest="external", action="store_false",
                    help="only check links on the same site")
    ap.add_argument("--no-sitemap", dest="sitemap", action="store_false",
                    help="do not seed the crawl from sitemap.xml")
    ap.add_argument("-x", "--exclude", action="append", metavar="REGEX",
                    help="skip URLs that match this regex (repeatable)")
    ap.add_argument("--show-blocked", action="store_true",
                    help="also list links that returned 401/403/429 or timed out")
    ap.add_argument("-o", "--out", default="reports", help="folder for CSV/JSON reports")
    ap.add_argument("--no-report", dest="write", action="store_false", help="do not write report files")
    args = ap.parse_args()

    url = args.url if "://" in args.url else "https://" + args.url
    banner()
    if not preflight(url):
        raise SystemExit(2)
    lc = LinkChecker(url, args)

    interrupted = False
    with Live(lc.render(), console=console, refresh_per_second=8, transient=False) as live:
        try:
            asyncio.run(lc.run(live))
        except KeyboardInterrupt:
            interrupted = True

    broken, soft = report(lc, interrupted)
    if args.write and lc.results:
        write_reports(lc, broken, soft, Path(args.out))
    raise SystemExit(1 if broken else 0)


if __name__ == "__main__":
    main()
