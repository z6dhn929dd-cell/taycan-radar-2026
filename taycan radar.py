#!/usr/bin/env python3
"""
Taycan Radar Bot  ·  Version 2 (mit Markt-Dashboard)
-----------------------------------------------------
Liest regelmäßig deine gespeicherten Suchen (Kleinanzeigen, mobile.de,
AutoScout24, eBay) komplett ein (alle Ergebnisseiten) und erkennt:

  * NEU        – Inserat ist zum ersten Mal aufgetaucht  -> Push mit Link
  * VERKAUFT   – Inserat ist mehrere Läufe in Folge verschwunden
                 (verkauft, reserviert oder vom Verkäufer gelöscht)
  * PREIS      – Preis wurde gesenkt / erhöht           -> optional Push

Daraus schreibt er docs/data.json – die Datenquelle für das Dashboard
(docs/index.html), das über GitHub Pages als Webseite erreichbar ist.

Start:
    pip install requests beautifulsoup4
    python taycan_radar.py            # läuft dauerhaft (alle X Minuten)
    python taycan_radar.py --once     # ein Durchlauf (GitHub / Cronjob)
    python taycan_radar.py --test     # Test-Push senden

Bitte moderat abfragen (>= 10 Minuten) und nur privat nutzen.
"""
from __future__ import annotations

import argparse
import json
import logging
import os
import random
import re
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urljoin, urlsplit, urlunsplit

import requests
from bs4 import BeautifulSoup

try:
    from zoneinfo import ZoneInfo
except ImportError:  # Python < 3.9
    ZoneInfo = None

BASE_DIR = Path(__file__).resolve().parent
CONFIG_FILE = BASE_DIR / "config.json"
STATE_FILE = BASE_DIR / "state.json"
DOCS_DIR = BASE_DIR / "docs"

PLATFORM_NAMES = {
    "mobile": "mobile.de",
    "kleinanzeigen": "Kleinanzeigen",
    "autoscout": "AutoScout24",
    "ebay": "eBay",
}
# so oft muss ein Inserat fehlen, bevor es als "verkauft/offline" gilt
MISSES_UNTIL_REMOVED = 3
KEEP_REMOVED_DAYS = 60
KEEP_HISTORY_DAYS = 90

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/129.0 Safari/537.36"
)
HEADERS = {
    "User-Agent": USER_AGENT,
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "de-DE,de;q=0.9,en;q=0.6",
}

log = logging.getLogger("taycan")


# --------------------------------------------------------------------------
# Datenmodell
# --------------------------------------------------------------------------
@dataclass
class Listing:
    platform: str          # id: mobile / kleinanzeigen / autoscout / ebay
    id: str
    title: str
    url: str
    price: int | None = None
    year: int | None = None
    km: int | None = None
    image: str | None = None
    snippet: str | None = None

    @property
    def key(self) -> str:
        return f"{self.platform}:{self.id}"


def summary(rec: dict) -> str:
    parts = [(rec.get("title") or "Porsche Taycan").strip()[:90]]
    if rec.get("price"):
        parts.append(fmt_eur(rec["price"]))
    if rec.get("year"):
        parts.append(f"EZ {rec['year']}")
    if rec.get("km"):
        parts.append(f"{rec['km']:,} km".replace(",", "."))
    return " · ".join(parts)


def fmt_eur(v: int) -> str:
    return f"{v:,} €".replace(",", ".")


# --------------------------------------------------------------------------
# Hilfsfunktionen
# --------------------------------------------------------------------------
def to_int(text) -> int | None:
    if text is None:
        return None
    digits = re.sub(r"[^\d]", "", str(text))
    return int(digits) if digits else None


def find_year(text: str) -> int | None:
    m = re.search(r"\b(?:\d{1,2}[/.-])?(20[1-3]\d)\b", text or "")
    return int(m.group(1)) if m else None


def find_km(text: str) -> int | None:
    m = re.search(r"([\d.]+)\s*km\b", text or "", re.I)
    return to_int(m.group(1)) if m else None


def find_price(text: str) -> int | None:
    m = re.search(r"([\d.]{4,})(?:,\d{2})?\s*(?:€|EUR)", text or "")
    return to_int(m.group(1)) if m else None


def clean(text: str | None, limit: int = 220) -> str | None:
    if not text:
        return None
    t = re.sub(r"\s+", " ", text).strip()
    return (t[: limit - 1] + "…") if len(t) > limit else t


def img_src(el) -> str | None:
    if el is None:
        return None
    img = el if el.name == "img" else el.select_one("img")
    if img is None:
        return None
    for attr in ("data-src", "src", "data-imgsrc", "data-lazy"):
        v = img.get(attr)
        if v and not v.startswith("data:"):
            return v if v.startswith("http") else urljoin("https://", v)
    srcset = img.get("srcset") or img.get("data-srcset")
    if srcset:
        return srcset.split(",")[0].strip().split(" ")[0]
    return None


def now_utc() -> datetime:
    return datetime.now(timezone.utc).replace(microsecond=0)


def iso(dt: datetime) -> str:
    return dt.isoformat().replace("+00:00", "Z")


def parse_iso(s: str) -> datetime:
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


def local_date(dt: datetime, tz_name: str) -> str:
    if ZoneInfo:
        try:
            return dt.astimezone(ZoneInfo(tz_name)).date().isoformat()
        except Exception:
            pass
    return dt.date().isoformat()


# --------------------------------------------------------------------------
# Seiten-Links (Blättern)
# --------------------------------------------------------------------------
def set_query(url: str, **params) -> str:
    parts = urlsplit(url)
    q = dict(parse_qsl(parts.query, keep_blank_values=True))
    q.update({k: str(v) for k, v in params.items()})
    return urlunsplit(parts._replace(query=urlencode(q, safe=";:")))


def page_url(platform: str, url: str, n: int) -> str:
    if n == 1:
        return url
    if platform == "kleinanzeigen":
        parts = urlsplit(url)
        segs = [s for s in parts.path.split("/") if s and not s.startswith("seite:")]
        # .../s-autos/[preis::x/]<suchwort>/k0c216  ->  seite:N vor dem Suchwort
        insert_at = max(1, len(segs) - 2)
        segs.insert(insert_at, f"seite:{n}")
        return urlunsplit(parts._replace(path="/" + "/".join(segs)))
    if platform == "mobile":
        return set_query(url, pageNumber=n)
    if platform == "autoscout":
        return set_query(url, page=n)
    if platform == "ebay":
        return set_query(url, _pgn=n)
    return url


# --------------------------------------------------------------------------
# Parser je Plattform
# --------------------------------------------------------------------------
def parse_kleinanzeigen(html: str, base: str) -> list[Listing]:
    soup = BeautifulSoup(html, "html.parser")
    out: list[Listing] = []
    for art in soup.select("article.aditem, article[data-adid]"):
        ad_id = art.get("data-adid")
        a = art.select_one("a[href*='/s-anzeige/']")
        href = art.get("data-href") or (a.get("href") if a else None)
        if not ad_id or not href:
            continue
        title_el = art.select_one("h2, .ellipsis, .text-module-begin")
        desc_el = art.select_one(".aditem-main--middle--description, .aditem-main--middle p")
        text = art.get_text(" ", strip=True)
        out.append(Listing(
            platform="kleinanzeigen", id=ad_id,
            title=clean(title_el.get_text(" ", strip=True) if title_el else "Porsche Taycan", 140),
            url=urljoin("https://www.kleinanzeigen.de", href),
            price=find_price(text), year=find_year(text), km=find_km(text),
            image=img_src(art), snippet=clean(desc_el.get_text(" ", strip=True) if desc_el else text),
        ))
    return out or generic_links(html, base, "kleinanzeigen", r"/s-anzeige/[^\"'?#]+/(\d+)-")


def parse_mobile(html: str, base: str) -> list[Listing]:
    soup = BeautifulSoup(html, "html.parser")
    out: list[Listing] = []
    seen = set()
    for a in soup.select("a[href*='details.html?id='], a[href*='/fahrzeuge/details']"):
        m = re.search(r"id=(\d+)", a.get("href", ""))
        if not m or m.group(1) in seen:
            continue
        seen.add(m.group(1))
        card = a.find_parent(["article", "div"]) or a
        text = a.get_text(" ", strip=True)
        title_el = a.select_one("h2, h3, [data-testid*='title']")
        out.append(Listing(
            platform="mobile", id=m.group(1),
            title=clean(title_el.get_text(" ", strip=True) if title_el else text, 140) or "Porsche Taycan",
            url=f"https://suchen.mobile.de/fahrzeuge/details.html?id={m.group(1)}",
            price=find_price(text), year=find_year(text), km=find_km(text),
            image=img_src(a) or img_src(card), snippet=clean(text),
        ))
    return out


def parse_autoscout(html: str, base: str) -> list[Listing]:
    soup = BeautifulSoup(html, "html.parser")
    out: list[Listing] = []
    for art in soup.select("article[data-guid]"):
        guid = art.get("data-guid")
        a = art.select_one("a[href*='/angebote/']")
        if not guid or not a:
            continue
        title_el = art.select_one("h2")
        sub_el = art.select_one("[class*='subtitle'], h2 + span")
        text = art.get_text(" ", strip=True)
        out.append(Listing(
            platform="autoscout", id=guid,
            title=clean(title_el.get_text(" ", strip=True) if title_el else "Porsche Taycan", 140),
            url=urljoin("https://www.autoscout24.de", a["href"]),
            price=to_int(art.get("data-price")) or find_price(text),
            year=find_year(art.get("data-first-registration", "") or text),
            km=to_int(art.get("data-mileage")) or find_km(text),
            image=img_src(art), snippet=clean(sub_el.get_text(" ", strip=True) if sub_el else text),
        ))
    return out or generic_links(html, base, "autoscout", r"/angebote/[^\"'?#]*?-([0-9a-f]{8}-[0-9a-f-]{27})")


def parse_ebay(html: str, base: str) -> list[Listing]:
    soup = BeautifulSoup(html, "html.parser")
    out: list[Listing] = []
    seen = set()
    for li in soup.select("li.s-item, li.s-card, li[data-listingid]"):
        a = li.select_one("a[href*='/itm/']")
        if not a:
            continue
        m = re.search(r"/itm/(?:[^/]+/)?(\d{9,})", a["href"])
        if not m or m.group(1) in seen:
            continue
        seen.add(m.group(1))
        title_el = li.select_one(".s-item__title, .s-card__title, [role='heading']")
        title = title_el.get_text(" ", strip=True) if title_el else a.get_text(" ", strip=True)
        if title.lower().startswith("shop on ebay"):
            continue
        text = li.get_text(" ", strip=True)
        out.append(Listing(
            platform="ebay", id=m.group(1), title=clean(title, 140) or "Porsche Taycan",
            url=f"https://www.ebay.de/itm/{m.group(1)}",
            price=find_price(text), year=find_year(text), km=find_km(text),
            image=img_src(li), snippet=clean(text),
        ))
    return out or generic_links(html, base, "ebay", r"/itm/(?:[^/\"']+/)?(\d{9,})")


def generic_links(html: str, base: str, platform: str, pattern: str) -> list[Listing]:
    """Fallback: sammelt alle Links, die wie ein Inserat aussehen."""
    soup = BeautifulSoup(html, "html.parser")
    out, seen = [], set()
    rx = re.compile(pattern)
    for a in soup.find_all("a", href=True):
        m = rx.search(a["href"])
        if not m or m.group(1) in seen:
            continue
        seen.add(m.group(1))
        text = a.get_text(" ", strip=True)
        out.append(Listing(platform=platform, id=m.group(1), title=clean(text, 140) or "Porsche Taycan",
                           url=urljoin(base, a["href"]), price=find_price(text),
                           year=find_year(text), km=find_km(text), image=img_src(a), snippet=None))
    return out


PARSERS = {
    "kleinanzeigen": parse_kleinanzeigen,
    "mobile": parse_mobile,
    "autoscout": parse_autoscout,
    "ebay": parse_ebay,
}


# --------------------------------------------------------------------------
# Filter & Benachrichtigung
# --------------------------------------------------------------------------
def matches(rec: dict, cfg: dict) -> bool:
    title = (rec.get("title") or "").lower()
    for word in cfg.get("must_contain") or []:
        if word and word.lower() not in title:
            return False
    for word in cfg.get("exclude") or []:
        if word and word.lower() in title:
            return False
    if cfg.get("max_price") and rec.get("price") and rec["price"] > cfg["max_price"]:
        return False
    if cfg.get("min_year") and rec.get("year") and rec["year"] < cfg["min_year"]:
        return False
    if cfg.get("max_km") and rec.get("km") and rec["km"] > cfg["max_km"]:
        return False
    return True


def notify(cfg: dict, title: str, message: str, link: str | None = None, tags: str = "red_car") -> None:
    topic = cfg.get("ntfy_topic")
    if topic and not topic.startswith("taycan-HIER"):
        server = cfg.get("ntfy_server", "https://ntfy.sh").rstrip("/")
        headers = {"Title": title.encode("utf-8"), "Tags": tags, "Priority": "high"}
        if link:
            headers["Click"] = link
            headers["Actions"] = f"view, Inserat öffnen, {link}".encode("utf-8")
        try:
            requests.post(f"{server}/{topic}", data=message.encode("utf-8"),
                          headers=headers, timeout=15).raise_for_status()
        except requests.RequestException as e:
            log.error("ntfy fehlgeschlagen: %s", e)

    tg = cfg.get("telegram") or {}
    if tg.get("bot_token") and tg.get("chat_id"):
        text = f"*{title}*\n{message}" + (f"\n{link}" if link else "")
        try:
            requests.post(f"https://api.telegram.org/bot{tg['bot_token']}/sendMessage",
                          json={"chat_id": tg["chat_id"], "text": text, "parse_mode": "Markdown"},
                          timeout=15).raise_for_status()
        except requests.RequestException as e:
            log.error("Telegram fehlgeschlagen: %s", e)


# --------------------------------------------------------------------------
# Abruf (alle Seiten einer Suche)
# --------------------------------------------------------------------------
def fetch(session: requests.Session, url: str) -> tuple[str | None, str | None]:
    try:
        r = session.get(url, headers=HEADERS, timeout=25)
    except requests.RequestException as e:
        return None, f"Verbindung fehlgeschlagen ({e.__class__.__name__})"
    if r.status_code != 200:
        return None, f"HTTP {r.status_code} – Plattform blockt automatische Abrufe"
    return r.text, None


def crawl_search(session, search: dict, max_pages: int) -> tuple[list[Listing], str | None]:
    platform, url = search["platform"], search["url"]
    parser = PARSERS[platform]
    found: dict[str, Listing] = {}
    for n in range(1, max_pages + 1):
        html, err = fetch(session, page_url(platform, url, n))
        if html is None:
            if n == 1:
                return [], err
            break  # spätere Seite fehlt: bisheriges Ergebnis nehmen
        new_here = 0
        for l in parser(html, url):
            if l.key not in found:
                found[l.key] = l
                new_here += 1
        if new_here == 0:
            break
        time.sleep(random.uniform(2, 4))
    return list(found.values()), None


# --------------------------------------------------------------------------
# Zustand
# --------------------------------------------------------------------------
def load_state() -> dict | None:
    try:
        return json.loads(STATE_FILE.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError):
        return None


def save_json(path: Path, data) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(data, ensure_ascii=False, indent=1, sort_keys=True), encoding="utf-8")
    tmp.replace(path)


def new_state() -> dict:
    return {"version": 2, "listings": {}, "removed": {}, "history": {}, "platforms": {}}


def fingerprint(rec: dict) -> str | None:
    """Gleiches Auto auf mehreren Plattformen: gleiches Baujahr, Preis und ~km."""
    if rec.get("price") and rec.get("year") and rec.get("km"):
        return f"{rec['year']}|{rec['price']}|{round(rec['km'] / 1000)}"
    return None


# --------------------------------------------------------------------------
# Ein Durchlauf
# --------------------------------------------------------------------------
def run_once(cfg: dict, session: requests.Session) -> dict:
    state = load_state()
    first_run = state is None
    state = state or new_state()
    tz = cfg.get("timezone", "Europe/Berlin")
    now = now_utc()
    stamp = iso(now)
    max_pages = int(cfg.get("max_pages", 8))
    stats = {"new": 0, "removed": 0, "price": 0}
    status: dict[str, dict] = {}

    # Suchen nach Plattform gruppieren (mehrere Suchen pro Plattform möglich)
    by_platform: dict[str, list[dict]] = {}
    for s in cfg["searches"]:
        if s["platform"] in PARSERS:
            by_platform.setdefault(s["platform"], []).append(s)
        else:
            log.warning("Unbekannte Plattform '%s' – übersprungen", s["platform"])

    for pid, searches in by_platform.items():
        name = PLATFORM_NAMES.get(pid, pid)
        log.info("Prüfe %s …", name)
        found: dict[str, Listing] = {}
        error = None
        for s in searches:
            listings, err = crawl_search(session, s, max_pages)
            if err:
                error = err
                break
            for l in listings:
                found.setdefault(l.key, l)
            time.sleep(random.uniform(3, 6))

        pstate = state["platforms"].setdefault(pid, {"name": name})
        prev_count = pstate.get("count")
        count = len(found)
        plausible = error is None and (prev_count is None or prev_count < 5 or count >= 0.6 * prev_count)
        if error is None and not plausible:
            error = f"Nur {count} statt ~{prev_count} Inserate geladen – Lauf ignoriert"
        ok = error is None
        if pstate.get("ok") != ok:
            pstate["ok"], pstate["since"] = ok, stamp
        pstate["error"] = error
        status[pid] = {"ok": ok, "count": count if ok else prev_count, "error": error,
                       "since": pstate.get("since")}
        if not ok:
            log.warning("  %s", error)
            continue

        baseline = prev_count is None  # erste erfolgreiche Erfassung dieser Plattform
        pstate["count"] = count
        log.info("  %d Inserate im Bestand", count)

        # --- gefundene Inserate einarbeiten
        for key, l in found.items():
            data = {"title": l.title, "url": l.url, "price": l.price, "year": l.year,
                    "km": l.km, "image": l.image, "snippet": l.snippet}
            if key in state["removed"]:  # wieder aufgetaucht
                rec = state["removed"].pop(key)
                rec.pop("removed", None)
                state["listings"][key] = rec
            rec = state["listings"].get(key)
            if rec is None:
                rec = {"key": key, "platform": pid, "first_seen": stamp, "baseline": baseline,
                       "prices": [[stamp, l.price]] if l.price else []}
                rec.update({k: v for k, v in data.items() if v is not None})
                state["listings"][key] = rec
                if not baseline and matches(rec, cfg):
                    stats["new"] += 1
                    log.info("  NEU: %s  %s", summary(rec), rec["url"])
                    notify(cfg, f"Neuer Taycan · {name}", summary(rec), rec["url"])
                    time.sleep(1)
                continue
            # bekanntes Inserat aktualisieren
            rec.pop("misses", None)
            rec.pop("missing_since", None)
            old_price = rec.get("price")
            for k, v in data.items():
                if v is not None:
                    rec[k] = v
            if l.price and old_price and l.price != old_price:
                rec.setdefault("prices", []).append([stamp, l.price])
                stats["price"] += 1
                diff = l.price - old_price
                log.info("  PREIS %s: %s -> %s", key, fmt_eur(old_price), fmt_eur(l.price))
                if diff < 0 and cfg.get("notify_price_drop", True) and matches(rec, cfg):
                    notify(cfg, f"Preis gesenkt −{fmt_eur(-diff)} · {name}", summary(rec),
                           rec["url"], tags="chart_with_downwards_trend")

        # --- fehlende Inserate: nach MISSES_UNTIL_REMOVED Läufen als verkauft markieren
        for key in [k for k, r in state["listings"].items() if r["platform"] == pid and k not in found]:
            rec = state["listings"][key]
            rec["misses"] = rec.get("misses", 0) + 1
            rec.setdefault("missing_since", stamp)
            if rec["misses"] >= MISSES_UNTIL_REMOVED:
                rec["removed"] = rec.pop("missing_since")
                rec.pop("misses", None)
                state["removed"][key] = state["listings"].pop(key)
                stats["removed"] += 1
                log.info("  VERKAUFT/OFFLINE: %s", summary(rec))
                if cfg.get("notify_removed", False) and matches(rec, cfg):
                    notify(cfg, f"Verkauft/offline · {name}", summary(rec), rec.get("url"),
                           tags="checkered_flag")

    # --- aufräumen & Tagesverlauf
    cutoff = now - timedelta(days=KEEP_REMOVED_DAYS)
    state["removed"] = {k: r for k, r in state["removed"].items() if parse_iso(r["removed"]) >= cutoff}
    today = local_date(now, tz)
    day = state["history"].setdefault(today, {})
    for pid in by_platform:
        if status.get(pid, {}).get("ok"):
            day[pid] = sum(1 for r in state["listings"].values()
                           if r["platform"] == pid and matches(r, cfg))
    keep = sorted(state["history"])[-KEEP_HISTORY_DAYS:]
    state["history"] = {d: state["history"][d] for d in keep}

    save_json(STATE_FILE, state)
    write_dashboard(state, status, cfg, now)

    if first_run:
        notify(cfg, "Taycan Radar läuft 🚀",
               "Startbestand gespeichert – ab jetzt meldet der Bot nur neue Inserate.")
    log.info("Fertig – %d neu, %d verkauft/offline, %d Preisänderungen.",
             stats["new"], stats["removed"], stats["price"])
    return stats


# --------------------------------------------------------------------------
# Dashboard-Daten
# --------------------------------------------------------------------------
def write_dashboard(state: dict, status: dict, cfg: dict, now: datetime) -> None:
    def slim(r: dict) -> dict:
        keys = ("key", "platform", "title", "url", "price", "year", "km", "image", "snippet",
                "first_seen", "baseline", "prices", "removed")
        return {k: r[k] for k in keys if r.get(k) not in (None, [], False)}

    active = [r for r in state["listings"].values() if matches(r, cfg)]
    removed = [r for r in state["removed"].values() if matches(r, cfg)]

    # gleiches Auto auf mehreren Plattformen erkennen
    groups: dict[str, set] = {}
    for r in active:
        fp = fingerprint(r)
        if fp:
            groups.setdefault(fp, set()).add(r["platform"])
    out_active = []
    for r in active:
        s = slim(r)
        fp = fingerprint(r)
        also = sorted(groups.get(fp, set()) - {r["platform"]}) if fp else []
        if also:
            s["also"] = also
        out_active.append(s)

    data = {
        "version": 2,
        "platforms": [{"id": pid, "name": p.get("name", PLATFORM_NAMES.get(pid, pid))}
                      for pid, p in sorted(state["platforms"].items())],
        "active": sorted(out_active, key=lambda r: r["first_seen"], reverse=True),
        "removed": sorted((slim(r) for r in removed), key=lambda r: r["removed"], reverse=True),
        "history": state["history"],
        "filters": {k: cfg.get(k) for k in ("max_price", "min_year", "max_km")},
    }
    # data.json ändert sich nur bei echten Ereignissen (gut für Git)
    save_json(DOCS_DIR / "data.json", data)
    # status.json ändert sich jeden Lauf (wird nicht in Git gespeichert)
    save_json(DOCS_DIR / "status.json", {"updated": iso(now), "platforms": status})


# --------------------------------------------------------------------------
def main() -> None:
    ap = argparse.ArgumentParser(description="Taycan Radar Bot")
    ap.add_argument("--once", action="store_true", help="nur ein Durchlauf")
    ap.add_argument("--test", action="store_true", help="Test-Push senden")
    ap.add_argument("--config", default=str(CONFIG_FILE))
    args = ap.parse_args()

    logging.basicConfig(level=logging.INFO, format="%(asctime)s  %(message)s", datefmt="%H:%M:%S")
    try:
        cfg = json.loads(Path(args.config).read_text(encoding="utf-8"))
    except FileNotFoundError:
        sys.exit("config.json fehlt – kopiere config.example.json zu config.json "
                 "oder füge die Konfiguration aus der Web-App ein.")

    # In der Cloud (GitHub) kommen geheime Werte aus "Secrets", nicht aus der Datei
    if os.environ.get("NTFY_TOPIC"):
        cfg["ntfy_topic"] = os.environ["NTFY_TOPIC"].strip()
    if os.environ.get("TELEGRAM_BOT_TOKEN") and os.environ.get("TELEGRAM_CHAT_ID"):
        cfg["telegram"] = {"bot_token": os.environ["TELEGRAM_BOT_TOKEN"],
                           "chat_id": os.environ["TELEGRAM_CHAT_ID"]}

    if args.test:
        notify(cfg, "Taycan Radar ist verbunden ✅",
               "So sieht eine Meldung aus. Tippen öffnet das Inserat.",
               "https://www.autoscout24.de/lst/porsche/taycan?sort=age&desc=1")
        print("Test-Nachricht gesendet.")
        return

    session = requests.Session()
    interval = max(5, int(cfg.get("interval_minutes", 10)))
    while True:
        run_once(cfg, session)
        if args.once:
            break
        wait = interval * 60 + random.randint(-60, 60)
        log.info("Nächste Prüfung in ca. %d Minuten.", wait // 60)
        time.sleep(wait)


if __name__ == "__main__":
    main()
