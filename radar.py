#!/usr/bin/env python3
"""
Taycan Radar Bot  ·  Version 3 (Markt-Analyse)
==============================================
Sammelt ALLE Porsche-Taycan-Inserate so breit wie möglich ein (lieber zu viele
als zu wenige) und bereitet sie für die Web-App (docs/index.html) auf.

Ablauf pro Lauf (alle ~10 Minuten über GitHub):
  * Schnellscan: die ersten Ergebnisseiten jeder Suche (neueste zuerst)
    -> neue Autos werden sofort erkannt und per Push gemeldet.
  * Vollscan (ca. stündlich): alle Ergebnisseiten aller Suchen
    -> Bestand, Preisänderungen und verkaufte/offline Autos.
  * Detailseiten: jedes Auto wird einmal komplett gelesen
    -> genauer Titel, Modell, EZ, km, PS, Ausstattung, Approved, MwSt., Verkäufer.

Mehrere Wege, damit kein passendes Auto verloren geht:
  * mehrere Suchen pro Plattform (verschiedene Suchwörter, Baujahr-Abschnitte)
  * gesucht wird NICHT nach "approved" o. Ä. – gefiltert wird erst im Dashboard
  * Approved/MwSt. werden aus Titel, Beschreibung, Detailseite und Verkäufer
    erkannt, mit Stufen (ja / wahrscheinlich / unbekannt / nein)
  * ein Auto gilt erst als verkauft, wenn es in 2 Vollscans fehlt
    (oder seine Detailseite "gelöscht" meldet)

Start lokal:
    pip install requests beautifulsoup4
    python radar.py --once      # ein Durchlauf
    python radar.py --full      # Vollscan erzwingen
    python radar.py --test      # Test-Push senden
"""
from __future__ import annotations

import argparse
import hashlib
import json
import logging
import os
import random
import re
import sys
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import parse_qsl, unquote, urlencode, urljoin, urlsplit, urlunsplit

import requests
from bs4 import BeautifulSoup

try:
    from zoneinfo import ZoneInfo
except ImportError:  # pragma: no cover
    ZoneInfo = None

VERSION = 3
BASE_DIR = Path(__file__).resolve().parent
CONFIG_FILE = BASE_DIR / "config.json"
STATE_FILE = BASE_DIR / "state.json"
DOCS_DIR = BASE_DIR / "docs"
DEBUG_DIR = BASE_DIR / "debug"

PLATFORM_NAMES = {
    "mobile": "mobile.de",
    "autoscout": "AutoScout24",
    "kleinanzeigen": "Kleinanzeigen",
    "ebay": "eBay",
    "porsche": "Porsche Finder",
}
MISSES_UNTIL_REMOVED = 2          # Vollscans in Folge, die ein Auto fehlen muss
KEEP_REMOVED_DAYS = 120
KEEP_HISTORY_DAYS = 180
MIN_PLAUSIBLE_PRICE = 25000       # darunter: Leasingrate, Anzahlung o. Ä.

USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/129.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.5 Safari/605.1.15",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:131.0) Gecko/20100101 Firefox/131.0",
]

log = logging.getLogger("taycan")


# ==========================================================================
# Kleine Helfer
# ==========================================================================
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


def to_int(text) -> int | None:
    if text is None:
        return None
    digits = re.sub(r"[^\d]", "", str(text))
    return int(digits) if digits else None


def clean(text: str | None, limit: int = 400) -> str | None:
    if not text:
        return None
    t = re.sub(r"\s+", " ", str(text)).strip()
    return (t[: limit - 1] + "…") if len(t) > limit else t


def fmt_eur(v: int) -> str:
    return f"{v:,} €".replace(",", ".")


def fmt_km(v: int) -> str:
    return f"{v:,} km".replace(",", ".")


# ==========================================================================
# Erkennung: Jahr, km, Preis, PS
# ==========================================================================
MONTHS = {"jan": 1, "feb": 2, "mär": 3, "maer": 3, "mar": 3, "apr": 4, "mai": 5, "jun": 6, "jul": 7,
          "aug": 8, "sep": 9, "okt": 10, "oct": 10, "nov": 11, "dez": 12, "dec": 12}

RE_EZ = [
    re.compile(r"\bEZ\.?\s*:?\s*(?:(\d{1,2})\s*[/.\-]\s*)?(20[12]\d)\b", re.I),
    re.compile(r"erstzulassung\W{0,6}(?:(\d{1,2})\s*[/.\-]\s*|([a-zäöü]{3,9})\.?\s+)?(20[12]\d)\b", re.I),
    re.compile(r"first registration\W{0,6}(?:(\d{1,2})\s*[/.\-]\s*)?(20[12]\d)\b", re.I),
    re.compile(r"\bBj\.?\s*:?\s*(20[12]\d)\b", re.I),
    re.compile(r"baujahr\W{0,6}(20[12]\d)\b", re.I),
]


def find_year(text: str | None) -> int | None:
    """Nur eindeutige Angaben (EZ, Erstzulassung, Baujahr) – nie Datumsangaben
    wie das Einstelldatum oder 'Approved bis 11/2027'."""
    if not text:
        return None
    for rx in RE_EZ:
        m = rx.search(text)
        if m:
            y = int([g for g in m.groups() if g and g.isdigit() and len(g) == 4][-1])
            if 2019 <= y <= datetime.now().year + 1:
                return y
    return None


def find_km(text: str | None) -> int | None:
    if not text:
        return None
    m = re.search(r"(?:kilometerstand|laufleistung|km-stand|mileage)\W{0,6}(\d{1,3}(?:\.\d{3})+|\d{1,6})\s*km", text, re.I)
    if m:
        return to_int(m.group(1))
    for m in re.finditer(r"(?<![\d,.])(\d{1,3}(?:\.\d{3})+|\d{1,6})\s*km\b(?!\s*/\s*h)", text, re.I):
        before = text[max(0, m.start() - 16):m.start()].lower()
        if re.search(r"reichweite|wltp|range|bis zu|ca\.\s*$|laden|lade", before):
            continue
        v = to_int(m.group(1))
        if v is not None and v <= 600000:
            return v
    return None


def find_price(text: str | None) -> int | None:
    if not text:
        return None
    m = re.search(r"(\d{1,3}(?:\.\d{3})+|\d{4,7})(?:,\d{2}|,-)?\s*(?:€|EUR)", text)
    return to_int(m.group(1)) if m else None


def find_ps(text: str | None) -> int | None:
    if not text:
        return None
    m = re.search(r"(\d{3})\s*kW\s*\(\s*(\d{3})\s*PS\)", text, re.I) or re.search(r"\b(\d{3})\s*PS\b", text, re.I)
    if m:
        v = int(m.groups()[-1])
        if 300 <= v <= 1100:
            return v
    return None


# ==========================================================================
# Erkennung: Modell, Approved, MwSt., Verkäufer, Ausstattung
# ==========================================================================
OTHER_MODELS = r"panamera|cayenne|macan|911|boxster|cayman|718|carrera|e-?tron gt|rs ?e-?tron|tesla|bmw|mercedes|audi"


def is_taycan(title: str, text: str = "") -> bool:
    """Lieber zu viele als zu wenige:
    * Titel nennt zuerst ein anderes Modell (z. B. "Panamera … suche Taycan")  -> nein
    * Titel nennt Taycan                                                          -> ja
    * Titel nennt kein Modell, aber Beschreibung nennt Taycan                     -> ja"""
    t = (title or "").lower()
    m_t = re.search(r"taycan", t)
    m_o = re.search(OTHER_MODELS, t)
    if m_o and (not m_t or m_o.start() < m_t.start()):
        return False
    if m_t:
        return True
    return "taycan" in (text or "").lower()


RE_EXCLUDE_DEFAULT = r"\b(suche|gesucht|ankauf|wir kaufen|kaufe|vermietung|vermiete|zu vermieten|mieten|miete|hochzeitsauto|abo)\b"


def detect_model(text: str) -> tuple[str, str]:
    t = " " + (text or "").lower().replace("-", " ") + " "
    if re.search(r"cross\s*turismo|crossturismo|\bct\b|\bcross\b", t):
        body = "Cross Turismo"
    elif re.search(r"sport\s*turismo|sportturismo|\bst\b", t):
        body = "Sport Turismo"
    else:
        body = "Limousine"
    if re.search(r"turbo\s*gt", t):
        var = "Turbo GT"
    elif re.search(r"turbo\s*s\b|turbos\b", t):
        var = "Turbo S"
    elif re.search(r"\bturbo\b", t):
        var = "Turbo"
    elif re.search(r"\bgts\b", t):
        var = "GTS"
    elif re.search(r"\b4\s?s\b", t):
        var = "4S"
    elif re.search(r"taycan\s+4\b|\b4\s+cross|\b4\s+sport\s*turismo|\bt4\b", t):
        var = "4"
    elif body == "Cross Turismo":
        var = "4"           # Cross Turismo gibt es nicht ohne Allrad
    else:
        var = "Basis"
    return var, body


APPROVED_NO = re.compile(r"(kein|keine|ohne|nicht)\s+(mehr\s+)?(porsche\s+)?approved|approved\s+(ist\s+)?(abgelaufen|ausgelaufen|beendet)", re.I)
APPROVED_YES = re.compile(r"approved", re.I)
APPROVED_LIKELY = re.compile(
    r"porsche\s*zentrum|porsche\s*centre|porsche\s*center|porsche\s*niederlassung|porsche\s*inter\s*auto|"
    r"111[\s-]*punkte|porsche[\s-]*garantie|garantie\s+porsche|porsche\s*classic\s*partner", re.I)
APPROVED_UNTIL = re.compile(r"approved[^\d]{0,25}?(\d{1,2})\s*[/.\-]\s*(20\d{2}|\d{2})\b", re.I)

VAT_NO = re.compile(
    r"(mwst|ust|mehrwertsteuer)\.?\s*(ist\s+)?nicht\s*(ausweisbar|ausgewiesen)|differenzbesteuert|§\s*25\s*a|25a\s*ustg|"
    r"privatverkauf|von\s+privat|privater\s+(nutzer|anbieter|verkäufer)", re.I)
VAT_YES = re.compile(
    r"(mwst|ust|mehrwertsteuer)\.?\s*(ist\s+)?ausweisbar|mwst\.?\s*ausw|vat\s*(deductible|reclaimable)|"
    r"netto\s*[:€]?\s*\d|\d[\d.]*\s*€?\s*netto|zzgl\.?\s*(19\s*%\s*)?(mwst|ust)|inkl\.?\s*(19\s*%\s*)(mwst|ust)|"
    r"19\s*%\s*(mwst|ust)|exportpreis\s*netto|\|\s*mwst\.?\s*\||\bmwst\.?\s*$", re.I)

SELLER_DEALER = re.compile(r"gewerblich|händler|haendler|autohaus|gmbh|\bkg\b|\bag\b|e\.\s?k\.|porsche\s*zentrum|dealer|automobile\b", re.I)
SELLER_PRIVATE = re.compile(r"privater\s+nutzer|privatverkauf|privatanbieter|von\s+privat|private\s+seller|privatperson", re.I)

EQUIPMENT = [
    ("perf_batt", "Performancebatterie Plus", r"performance[\s-]*batterie\s*plus|performance[\s-]*battery\s*plus|performancebatterie\+|batterie\s*plus|93[,.]?4\s*kwh|\b93\s*kwh|\b105\s*kwh"),
    ("pano", "Panoramadach", r"panorama"),
    ("hal", "Hinterachslenkung", r"hinterachslenkung|ha[\s-]*lenkung|\bhal\b|rear[\s-]*axle\s*steer"),
    ("luft", "Luftfederung", r"luftfederung|luftfahrwerk|luftfw|air\s*suspension"),
    ("bose", "Bose", r"\bbose\b"),
    ("burmester", "Burmester", r"burmester"),
    ("hud", "Head-up-Display", r"head[\s-]*up|\bhud\b"),
    ("innodrive", "InnoDrive", r"innodrive|inno\s*drive"),
    ("matrix", "Matrix-LED", r"matrix|pdls\s*\+|pdls\+|pdls plus"),
    ("chrono", "Sport Chrono", r"sport[\s-]*chrono|\bchrono\b"),
    ("beifahrer", "Beifahrerdisplay", r"beifahrer[\s-]*display|passenger\s*display"),
    ("massage", "Massage", r"massage"),
    ("belueftung", "Sitzbelüftung", r"sitzbelüftung|sitzlüftung|belüftete\s*sitze|sitzklima"),
    ("ahk", "Anhängerkupplung", r"anhängerkupplung|\bahk\b"),
    ("lader22", "22-kW-Lader", r"22\s*kw|on[\s-]*board[\s-]*lader\s*22"),
    ("waermepumpe", "Wärmepumpe", r"wärmepumpe|waermepumpe|heat\s*pump"),
    ("kamera360", "360°-Kamera", r"360\s*°|360[\s-]*grad|360[\s-]*kamera|360[\s-]*view|surround\s*view|umgebungsansicht"),
    ("keramik", "Keramikbremse", r"\bpccb\b|keramik|ceramic"),
    ("sportdesign", "SportDesign", r"sport\s*design"),
    ("pdcc", "PDCC / Active Ride", r"\bpdcc\b|active\s*ride|wankstabilisierung"),
]
EQUIP_RX = [(k, lbl, re.compile(rx, re.I)) for k, lbl, rx in EQUIPMENT]


def analyse_text(title: str, body: str, platform: str, now: datetime) -> dict:
    """Wertet Titel + Beschreibung aus. Gibt nur gefundene Werte zurück."""
    full = f"{title or ''} \n {body or ''}"
    out: dict = {}
    var, bdy = detect_model(title)
    if var == "Basis" and body:          # Titel ohne Variante -> Anfang der Beschreibung prüfen
        v2, b2 = detect_model(body[:250])
        if v2 != "Basis" and is_taycan(body[:250]):
            var = v2
        if bdy == "Limousine" and b2 != "Limousine":
            bdy = b2
    out["model"], out["body"] = var, bdy

    # Approved
    if platform == "porsche":
        out["approved"] = "ja"
    elif APPROVED_NO.search(full):
        out["approved"] = "nein"
    elif APPROVED_YES.search(full):
        out["approved"] = "ja"
    elif APPROVED_LIKELY.search(full):
        out["approved"] = "wahrscheinlich"
    else:
        out["approved"] = "unbekannt"
    m = APPROVED_UNTIL.search(full)
    if m:
        mon, yr = int(m.group(1)), int(m.group(2))
        yr = yr + 2000 if yr < 100 else yr
        if 1 <= mon <= 12 and 2020 <= yr <= 2035:
            out["approved_until"] = f"{mon:02d}/{yr}"
            if (yr, mon) < (now.year, now.month) and out["approved"] == "ja":
                out["approved"] = "abgelaufen"

    # MwSt.
    if VAT_NO.search(full):
        out["vat"] = "nein"
    elif VAT_YES.search(full) or re.search(r"\bmwst\b", title or "", re.I):
        out["vat"] = "ja"
    elif out["approved"] in ("ja", "wahrscheinlich") and APPROVED_LIKELY.search(full):
        out["vat"] = "wahrscheinlich"    # Porsche Zentren verkaufen fast immer regelbesteuert
    else:
        out["vat"] = "unbekannt"

    # Verkäufer
    if SELLER_PRIVATE.search(full):
        out["seller"] = "privat"
    elif SELLER_DEALER.search(full):
        out["seller"] = "händler"

    # Ausstattung
    out["equip"] = sorted({k for k, _, rx in EQUIP_RX if rx.search(full)})

    # Zustand
    if re.search(r"unfallfrei|kein\s+unfall|accident[\s-]*free", full, re.I):
        out["damage"] = "unfallfrei"
    elif re.search(r"unfall(schaden|wagen|fahrzeug)|hagelschaden|vorschaden|instandgesetzt|repariert", full, re.I):
        out["damage"] = "vorschaden"
    m = re.search(r"(?:soh|state of health|batterie(?:zustand|gesundheit)?|battery|akku(?:zustand)?)\D{0,12}(\d{2,3})\s*%", full, re.I) \
        or re.search(r"(\d{2,3})\s*%\s*(?:soh|batterie|battery|akku)", full, re.I)
    if m and 60 <= int(m.group(1)) <= 100:
        out["soh"] = int(m.group(1))
    if re.search(r"\b(china|chinesisch|re-?import|eu-?import|import(fahrzeug|wagen)?|us-?fahrzeug|ausländisch)\b", full, re.I):
        out["import"] = True
    ps = find_ps(full)
    if ps:
        out["ps"] = ps
    return out


# ==========================================================================
# Seiten-Links (Blättern)
# ==========================================================================
def set_query(url: str, **params) -> str:
    parts = urlsplit(url)
    q = dict(parse_qsl(parts.query, keep_blank_values=True))
    q.update({k: str(v) for k, v in params.items()})
    return urlunsplit(parts._replace(query=urlencode(q, safe=";:,")))


def page_url(platform: str, url: str, n: int) -> str:
    if n == 1:
        return url
    if platform == "kleinanzeigen":
        parts = urlsplit(url)
        segs = [s for s in parts.path.split("/") if s and not s.startswith("seite:")]
        segs.insert(max(1, len(segs) - 2), f"seite:{n}")
        return urlunsplit(parts._replace(path="/" + "/".join(segs)))
    if platform == "mobile":
        return set_query(url, pageNumber=n)
    if platform == "autoscout":
        return set_query(url, page=n)
    if platform == "ebay":
        return set_query(url, _pgn=n)
    if platform == "porsche":
        return set_query(url, page=n)
    return url


# ==========================================================================
# Ergebnislisten lesen (je Plattform)
# Jede Funktion liefert dicts: id, title, url, price, year, km, image, snippet
# ==========================================================================
def _img(el) -> str | None:
    if el is None:
        return None
    img = el if getattr(el, "name", None) == "img" else el.select_one("img")
    if img is None:
        return None
    for attr in ("data-src", "src", "data-imgsrc", "data-lazy"):
        v = img.get(attr)
        if v and not v.startswith("data:"):
            return v if v.startswith("http") else urljoin("https://", v)
    srcset = img.get("srcset") or img.get("data-srcset")
    return srcset.split(",")[0].strip().split(" ")[0] if srcset else None


def slug_title(url: str) -> str:
    m = re.search(r"/s-anzeige/([^/]+)/", url) or re.search(r"/angebote/([^/?#]+?)-[0-9a-f]{8}-", url) \
        or re.search(r"/itm/([^/?#]+)/\d", url)
    if not m:
        return ""
    words = unquote(m.group(1)).replace("-", " ").split()
    return " ".join(w.upper() if w in ("gts", "hud", "led", "pdls", "mwst") else w.capitalize() for w in words)


def best_title(candidates: list[str], url: str) -> str:
    cands = [clean(c, 160) for c in candidates if c and clean(c, 160)]
    good = [c for c in cands if "taycan" in c.lower() and c.lower().strip() not in ("porsche taycan", "taycan")]
    if good:
        return max(good, key=len)
    st = slug_title(url)
    if st:
        return st
    return max(cands, key=len) if cands else "Porsche Taycan"


def parse_kleinanzeigen(html: str, base: str) -> list[dict]:
    soup = BeautifulSoup(html, "html.parser")
    out = []
    for art in soup.select("article.aditem, article[data-adid], li.ad-listitem article"):
        ad_id = art.get("data-adid")
        a = art.select_one("a[href*='/s-anzeige/']")
        href = art.get("data-href") or (a.get("href") if a else None)
        if not ad_id or not href:
            continue
        url = urljoin("https://www.kleinanzeigen.de", href)
        cands = [x.get_text(" ", strip=True) for x in art.select("a[href*='/s-anzeige/'], h2, h3, .ellipsis")]
        cands += [i.get("alt", "") for i in art.select("img")] + [i.get("title", "") for i in art.select("a[title]")]
        text = art.get_text(" ", strip=True)
        desc_el = art.select_one(".aditem-main--middle--description")
        out.append({
            "id": ad_id, "url": url, "title": best_title(cands, url),
            "price": find_price((art.select_one(".aditem-main--middle--price-shipping--price, [class*='price']") or art).get_text(" ")),
            "year": find_year(text), "km": find_km(text), "image": _img(art),
            "snippet": clean(desc_el.get_text(" ", strip=True) if desc_el else
                             re.sub(r"^.*?(\d{2}\.\d{2}\.\d{4}|Heute,?\s*\d{2}:\d{2}|Gestern,?\s*\d{2}:\d{2})\s*", "", text)),
        })
    return out or generic_links(html, base, r"/s-anzeige/[^\"'?#\s]+/(\d+)-\d+-\d+", "https://www.kleinanzeigen.de")


def _walk(obj):
    if isinstance(obj, dict):
        yield obj
        for v in obj.values():
            yield from _walk(v)
    elif isinstance(obj, list):
        for v in obj:
            yield from _walk(v)


def _json_blobs(soup) -> list:
    blobs = []
    for s in soup.select("script#__NEXT_DATA__, script[type='application/json'], script[type='application/ld+json']"):
        try:
            blobs.append(json.loads(s.string or s.get_text() or ""))
        except Exception:
            continue
    return blobs


def parse_autoscout(html: str, base: str) -> list[dict]:
    soup = BeautifulSoup(html, "html.parser")
    found: dict[str, dict] = {}
    # Weg 1: eingebettete Daten (__NEXT_DATA__)
    for blob in _json_blobs(soup):
        for d in _walk(blob):
            url = d.get("url") if isinstance(d.get("url"), str) else None
            if not url or "/angebote/" not in url and "/offers/" not in url:
                continue
            mu = re.search(r"([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})", url)
            lid = str(d.get("id") or (mu.group(1) if mu else ""))
            if not lid:
                continue
            veh = d.get("vehicle") or {}
            trk = d.get("tracking") or {}
            price = d.get("price") or {}
            title = " ".join(str(x) for x in (veh.get("make"), veh.get("model"), veh.get("modelVersionInput") or veh.get("variant")) if x) \
                or d.get("title") or ""
            imgs = d.get("images") or []
            img = imgs[0] if imgs and isinstance(imgs[0], str) else (imgs[0].get("url") if imgs and isinstance(imgs[0], dict) else None)
            seller = d.get("seller") or {}
            vat = d.get("vat") or (price.get("vat") if isinstance(price, dict) else None)
            found[lid] = {
                "id": lid, "url": urljoin("https://www.autoscout24.de", url),
                "title": clean(title, 160) or slug_title(url) or "Porsche Taycan",
                "price": to_int(trk.get("price")) or find_price(str(price.get("priceFormatted") if isinstance(price, dict) else price)),
                "year": find_year("EZ " + str(trk.get("firstRegistration") or veh.get("firstRegistration") or "")),
                "km": to_int(trk.get("mileage")) or find_km(str(veh.get("mileageInKm") or "")),
                "image": img,
                "snippet": clean(" · ".join(str(x) for x in (veh.get("subtitle"), seller.get("companyName"),
                                                             seller.get("type"), "MwSt. ausweisbar" if vat else None) if x)),
            }
    if found:
        return list(found.values())
    # Weg 2: HTML-Karten
    out = []
    for art in soup.select("article[data-guid], article[id]"):
        guid = art.get("data-guid") or art.get("id")
        a = art.select_one("a[href*='/angebote/']")
        if not guid or not a:
            continue
        text = art.get_text(" ", strip=True)
        url = urljoin("https://www.autoscout24.de", a["href"])
        out.append({
            "id": guid, "url": url,
            "title": best_title([x.get_text(" ", strip=True) for x in art.select("h2, h3")], url),
            "price": to_int(art.get("data-price")) or find_price(text),
            "year": find_year("EZ " + (art.get("data-first-registration") or "")) or find_year(text),
            "km": to_int(art.get("data-mileage")) or find_km(text), "image": _img(art), "snippet": clean(text),
        })
    # Weg 3: alle Inserats-Links im Quelltext
    return out or generic_links(html, base, r"/angebote/[^\"'?#\s]*?-([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})",
                                "https://www.autoscout24.de")


def parse_mobile(html: str, base: str) -> list[dict]:
    soup = BeautifulSoup(html, "html.parser")
    out, seen = [], set()
    for a in soup.select("a[href*='details.html?id='], a[href*='/fahrzeuge/details']"):
        m = re.search(r"id=(\d+)", a.get("href", ""))
        if not m or m.group(1) in seen:
            continue
        seen.add(m.group(1))
        text = a.get_text(" ", strip=True)
        url = f"https://suchen.mobile.de/fahrzeuge/details.html?id={m.group(1)}"
        out.append({"id": m.group(1), "url": url,
                    "title": best_title([x.get_text(" ", strip=True) for x in a.select("h2, h3, [data-testid*='title']")] + [text[:120]], url),
                    "price": find_price(text), "year": find_year(text), "km": find_km(text),
                    "image": _img(a), "snippet": clean(text)})
    return out


def parse_ebay(html: str, base: str) -> list[dict]:
    if html.lstrip().startswith("<?xml") or "<rss" in html[:500]:
        return parse_ebay_rss(html)
    soup = BeautifulSoup(html, "html.parser")
    out, seen = [], set()
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
        out.append({"id": m.group(1), "url": f"https://www.ebay.de/itm/{m.group(1)}", "title": clean(title, 160),
                    "price": find_price(text), "year": find_year(text), "km": find_km(text),
                    "image": _img(li), "snippet": clean(text)})
    return out or generic_links(html, base, r"/itm/(?:[^/\"']+/)?(\d{9,})", "https://www.ebay.de")


def parse_ebay_rss(xml: str) -> list[dict]:
    soup = BeautifulSoup(xml, "html.parser")
    out = []
    for it in soup.find_all("item"):
        link = (it.find("link").get_text(strip=True) if it.find("link") else "") or (it.find("guid").get_text(strip=True) if it.find("guid") else "")
        m = re.search(r"/itm/(?:[^/]+/)?(\d{9,})", link)
        if not m:
            continue
        title = it.find("title").get_text(strip=True) if it.find("title") else ""
        desc = BeautifulSoup(it.find("description").get_text() if it.find("description") else "", "html.parser")
        text = desc.get_text(" ", strip=True)
        out.append({"id": m.group(1), "url": f"https://www.ebay.de/itm/{m.group(1)}", "title": clean(title, 160),
                    "price": find_price(text), "year": find_year(text), "km": find_km(text),
                    "image": _img(desc), "snippet": clean(text)})
    return out


def parse_porsche(html: str, base: str) -> list[dict]:
    """Porsche Finder: alle Fahrzeuge sind Porsche Approved."""
    soup = BeautifulSoup(html, "html.parser")
    found: dict[str, dict] = {}
    for blob in _json_blobs(soup):
        for d in _walk(blob):
            url = next((d.get(k) for k in ("url", "href", "detailUrl", "link") if isinstance(d.get(k), str) and "/details/" in d.get(k)), None)
            if not url:
                continue
            m = re.search(r"/details/(?:[^/?#]+/)*?([A-Za-z0-9-]{6,})(?:[/?#]|$)", url)
            if not m:
                continue
            text = json.dumps(d, ensure_ascii=False)
            title = d.get("title") or d.get("name") or d.get("modelName") or "Porsche Taycan"
            found[m.group(1)] = {"id": m.group(1), "url": urljoin("https://finder.porsche.com", url),
                                 "title": clean(str(title), 160), "price": find_price(text) or to_int(d.get("price")),
                                 "year": find_year(text), "km": find_km(text), "image": None, "snippet": None}
    if found:
        return list(found.values())
    return generic_links(html, base, r"/details/[^\"'?#\s]*?([A-Za-z0-9]{6,}[A-Za-z0-9-]*)(?=[\"'?#])", "https://finder.porsche.com")


def generic_links(html: str, base: str, pattern: str, host: str) -> list[dict]:
    """Letzter Weg: sammelt alle Links im Quelltext, die wie ein Inserat aussehen."""
    out, seen = [], set()
    for m in re.finditer(r"(?:href=|\"url\":\s*)\"([^\"]+)\"", html):
        href = m.group(1).replace("\\u002F", "/").replace("\\/", "/")
        mm = re.search(pattern, href)
        if not mm or mm.group(1) in seen:
            continue
        seen.add(mm.group(1))
        url = urljoin(host, href)
        out.append({"id": mm.group(1), "url": url, "title": slug_title(url) or "Porsche Taycan",
                    "price": None, "year": None, "km": None, "image": None, "snippet": None})
    return out


PARSERS = {
    "kleinanzeigen": parse_kleinanzeigen,
    "autoscout": parse_autoscout,
    "mobile": parse_mobile,
    "ebay": parse_ebay,
    "porsche": parse_porsche,
}
PAGE_SIZE_HINT = {"kleinanzeigen": 25, "autoscout": 20, "mobile": 20, "ebay": 50, "porsche": 12}


# ==========================================================================
# Detailseite lesen
# ==========================================================================
def parse_detail(platform: str, html: str) -> dict:
    soup = BeautifulSoup(html, "html.parser")

    def meta(prop):
        el = soup.select_one(f"meta[property='{prop}'], meta[name='{prop}']")
        return el.get("content") if el and el.get("content") else None

    title = meta("og:title")
    image = meta("og:image")
    body = ""
    body_desc = None
    if platform == "kleinanzeigen":
        t = soup.select_one("#viewad-title")
        title = t.get_text(" ", strip=True) if t else title
        parts = [soup.select_one(sel) for sel in ("#viewad-price", "#viewad-details", ".addetailslist",
                                                  "#viewad-configuration", "#viewad-description-text", "#viewad-contact",
                                                  ".userprofile-vip", "#viewad-profile-box", ".iconlist-text")]
        body = " | ".join(p.get_text(" ", strip=True) for p in parts if p)
        if not body:
            main = soup.select_one("#viewad-main, main") or soup.body or soup
            body = main.get_text(" ", strip=True)[:20000]
        if re.search(r"privater\s+nutzer", soup.get_text(" ", strip=True)[:20000], re.I):
            body += " | Privater Nutzer"
        elif re.search(r"gewerblicher\s+nutzer|gewerblicher\s+anbieter", soup.get_text(" ", strip=True)[:20000], re.I):
            body += " | Gewerblicher Händler"
        price_el = soup.select_one("#viewad-price")
        price = find_price(price_el.get_text(" ") if price_el else "")
    else:
        detail_json, desc_txt = "", ""
        for blob in _json_blobs(soup):
            for d in _walk(blob):
                if isinstance(d, dict) and ("listingDetails" in d or "vehicleDetails" in d):
                    det = d.get("listingDetails") or d.get("vehicleDetails")
                    detail_json += readable(det)[:60000]
                    if isinstance(det, dict) and isinstance(det.get("description"), str):
                        desc_txt = html_text(det["description"])
                    break
        main = soup.select_one("main") or soup.body or soup
        for junk in main.select("script, style, nav, footer, [class*='similar'], [class*='recommend'], [data-testid*='similar']"):
            junk.decompose()
        body = (detail_json + " | " + main.get_text(" ", strip=True))[:60000]
        price = None
        if desc_txt:
            m = re.search(r"sonderausstattung(en)?\s*:?", desc_txt, re.I)
            nice = desc_txt[m.end():].strip() if m and len(desc_txt) - m.end() > 40 else desc_txt
            body_desc = nice
        else:
            body_desc = None
    gone = bool(re.search(r"anzeige\s+(ist\s+)?(nicht\s+mehr\s+verfügbar|wurde\s+gelöscht|deaktiviert)|"
                          r"dieses\s+angebot\s+ist\s+nicht\s+mehr|inserat\s+ist\s+nicht\s+mehr\s+verfügbar|"
                          r"fahrzeug\s+wurde\s+bereits\s+verkauft|listing\s+has\s+ended|dieses\s+angebot\s+wurde\s+beendet", body[:5000] + " " + (title or ""), re.I))
    desc = body_desc if platform != "kleinanzeigen" else None
    if platform == "kleinanzeigen":
        de = soup.select_one("#viewad-description-text")
        desc = de.get_text(" ", strip=True) if de else None
    return {"title": clean(title, 160), "image": image, "body": body, "price": price,
            "year": find_year(body), "km": find_km(body), "gone": gone,
            "description": clean(desc, 600) if desc and not desc.lstrip().startswith("{") else None}


def html_text(h: str) -> str:
    t = re.sub(r"\s+", " ", BeautifulSoup(h.replace("<li>", " · <li>").replace("<br", " · <br"), "html.parser").get_text(" "))
    t = re.sub(r"\s*:\s*", ": ", re.sub(r"(\s*·\s*)+", " · ", t))
    return t.strip(" ·")


def readable(obj, depth=0) -> str:
    """Wandelt eingebettete Daten in lesbaren Text um (keine Klammern/Anführungszeichen)."""
    if depth > 6:
        return ""
    if isinstance(obj, str):
        return html_text(obj) if "<" in obj else obj
    if isinstance(obj, dict):
        return " | ".join(t for t in (readable(v, depth + 1) for k, v in obj.items()
                                      if k not in ("id", "images", "url", "tracking", "searchResultType")) if t)
    if isinstance(obj, list):
        return " | ".join(t for t in (readable(v, depth + 1) for v in obj) if t)
    return ""


# ==========================================================================
# HTTP
# ==========================================================================
class Fetcher:
    def __init__(self):
        self.s = requests.Session()
        self.blocked: set[str] = set()

    def get(self, url: str, platform: str) -> tuple[int, str | None]:
        self.final_url = url
        if platform in self.blocked:
            return 403, None
        headers = {"User-Agent": random.choice(USER_AGENTS),
                   "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
                   "Accept-Language": "de-DE,de;q=0.9,en;q=0.6"}
        for attempt in range(2):
            try:
                r = self.s.get(url, headers=headers, timeout=25)
            except requests.RequestException as e:
                if attempt:
                    return 0, f"Verbindung fehlgeschlagen ({e.__class__.__name__})"
                time.sleep(3)
                continue
            if r.status_code in (403, 429) and attempt == 0:
                time.sleep(6)
                continue
            if r.status_code in (403, 429):
                self.blocked.add(platform)
            self.final_url = r.url
            return r.status_code, r.text
        return 0, None


# ==========================================================================
# Zustand
# ==========================================================================
def load_json(path: Path):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError):
        return None


def save_json(path: Path, data, compact=False) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    if compact:
        tmp.write_text(json.dumps(data, ensure_ascii=False, separators=(",", ":"), sort_keys=True), encoding="utf-8")
    else:
        tmp.write_text(json.dumps(data, ensure_ascii=False, indent=1, sort_keys=True), encoding="utf-8")
    tmp.replace(path)


def search_signature(cfg: dict) -> str:
    raw = json.dumps(sorted((s["platform"], s["url"]) for s in cfg["searches"]))
    return hashlib.sha1(raw.encode()).hexdigest()[:12]


def migrate(state: dict) -> dict:
    if state.get("version", 1) < 3:
        for r in list(state.get("listings", {}).values()) + list(state.get("removed", {}).values()):
            r.pop("detail_at", None)          # Detailseiten neu lesen
            r["src"] = []
            if r.get("platform") == "kleinanzeigen":
                r.pop("year", None)           # v2 las teils das Einstelldatum als Baujahr
                if r.get("snippet"):
                    r["snippet"] = re.sub(r"^.*?(\d{2}\.\d{2}\.\d{4}|Heute,?\s*\d{2}:\d{2}|Gestern,?\s*\d{2}:\d{2})\s*", "", r["snippet"])
            if (r.get("title") or "").strip().lower() == "porsche taycan":
                r["title"] = slug_title(r.get("url", "")) or r["title"]
        state["version"] = 3
    for k in ("listings", "removed", "history", "platforms", "searches"):
        state.setdefault(k, {})
    return state


# ==========================================================================
# Einarbeiten eines Inserats
# ==========================================================================
def excluded_reason(rec: dict, cfg: dict) -> str | None:
    title = rec.get("title") or ""
    if not is_taycan(title, (rec.get("snippet") or "") + " " + (rec.get("detail_text") or "")[:3000]):
        return "kein Taycan"
    rx = cfg.get("exclude_regex") or RE_EXCLUDE_DEFAULT
    if re.search(rx, title, re.I):
        return "Gesuch/Vermietung"
    return None


def refresh_derived(rec: dict, now: datetime, cfg: dict) -> None:
    info = analyse_text(rec.get("title") or "", (rec.get("snippet") or "") + " | " + (rec.get("detail_text") or ""),
                        rec["platform"], now)
    for k, v in info.items():
        if v not in (None, ""):
            rec[k] = v
    rec["price_odd"] = bool(rec.get("price") and rec["price"] < MIN_PLAUSIBLE_PRICE)
    reason = excluded_reason(rec, cfg)
    if reason:
        rec["excluded"] = reason
    else:
        rec.pop("excluded", None)


# ==========================================================================
# Ein Durchlauf
# ==========================================================================
def run_once(cfg: dict, force_full: bool = False) -> dict:
    now = now_utc()
    stamp = iso(now)
    tz = cfg.get("timezone", "Europe/Berlin")
    state = load_json(STATE_FILE)
    first_ever = state is None
    state = migrate(state or {"version": VERSION})
    fetch = Fetcher()

    sig = search_signature(cfg)
    sig_changed = state.get("search_sig") != sig
    last_full = state.get("last_full")
    full = force_full or sig_changed or not last_full or \
        (now - parse_iso(last_full)) >= timedelta(minutes=int(cfg.get("full_scan_minutes", 60)) - 3)
    baseline_run = first_ever or sig_changed      # neue/änderte Suchen: Funde zählen nicht als "neu"
    mode = "Vollscan" if full else "Schnellscan"
    log.info("%s%s", mode, " (Startbestand)" if baseline_run else "")

    max_pages = int(cfg.get("max_pages", 20)) if full else int(cfg.get("quick_pages", 2))
    stats = {"new": 0, "removed": 0, "price": 0, "excluded": 0}
    search_status: dict[str, dict] = {}
    found_by_platform: dict[str, dict[str, tuple[dict, str]]] = {}
    completed_ok: set[str] = set()

    # ---------- 1) Suchen abarbeiten
    for s in cfg["searches"]:
        pid, name, url = s["platform"], s.get("name") or s["platform"], s["url"]
        parser = PARSERS.get(pid)
        if not parser or s.get("disabled"):
            continue
        st = {"platform": pid, "pages": 0, "count": 0, "error": None, "limit": False}
        found = found_by_platform.setdefault(pid, {})
        page_hint = PAGE_SIZE_HINT.get(pid, 20)
        for n in range(1, max_pages + 1):
            code, html = fetch.get(page_url(pid, url, n), pid)
            if code != 200 or html is None:
                if n == 1:
                    st["error"] = f"HTTP {code} – Plattform blockt automatische Abrufe" if code in (403, 429) \
                        else (html if code == 0 and html else f"HTTP {code}")
                break
            items = parser(html, url)
            st["pages"] = n
            if n == 1 and not items:
                dump_debug(pid, name, html)
            new_here = 0
            for it in items:
                key = f"{pid}:{it['id']}"
                if key not in found:
                    found[key] = (it, name)
                    new_here += 1
                    st["count"] += 1
            if new_here == 0 or len(items) < max(5, page_hint // 2):
                break
            if n == max_pages and full:
                st["limit"] = True
            time.sleep(random.uniform(1.5, 3.5))
        if st["error"] is None and full and not st["limit"]:
            completed_ok.add(name)
        search_status[name] = st
        log.info("  %-34s %3d Inserate, %d Seite(n)%s%s", name, st["count"], st["pages"],
                 " – LIMIT ERREICHT" if st["limit"] else "", f" – {st['error']}" if st["error"] else "")
        time.sleep(random.uniform(1, 3))

    # ---------- 2) Funde einarbeiten
    platform_ok: dict[str, bool] = {}
    search_year = {(x.get("name") or x["platform"]): x.get("year") for x in cfg["searches"]}
    for pid, found in found_by_platform.items():
        names = [n for n, st in search_status.items() if st["platform"] == pid]
        ok_any = any(search_status[n]["error"] is None for n in names)
        platform_ok[pid] = ok_any
        pst = state["platforms"].setdefault(pid, {"name": PLATFORM_NAMES.get(pid, pid)})
        errs = [search_status[n]["error"] for n in names if search_status[n]["error"]]
        pst.update({"ok": ok_any, "error": errs[0] if errs and not ok_any else None, "checked": stamp})
        if not ok_any:
            continue
        platform_baseline = baseline_run or not pst.get("count")
        prev = pst.get("count") or 0
        suspicious = full and prev >= 10 and len(found) < 0.6 * prev
        if suspicious:
            pst["error"] = f"Nur {len(found)} statt ~{prev} Inserate geladen – Verkäufe in diesem Lauf nicht gewertet"
            log.warning("  %s: %s", pid, pst["error"])
        for key, (it, sname) in found.items():
            data = {k: it.get(k) for k in ("title", "url", "price", "year", "km", "image", "snippet")}
            if not data["year"] and search_year.get(sname):
                data["year"] = search_year[sname]         # Suche war auf ein Baujahr begrenzt
            if key in state["removed"]:                       # wieder aufgetaucht
                rec = state["removed"].pop(key)
                for k in ("removed", "gone_reason"):
                    rec.pop(k, None)
                state["listings"][key] = rec
            rec = state["listings"].get(key)
            if rec is None:
                rec = {"key": key, "platform": pid, "first_seen": stamp, "src": [sname],
                       "baseline": platform_baseline, "prices": []}
                rec.update({k: v for k, v in data.items() if v is not None})
                if rec.get("price"):
                    rec["prices"] = [[stamp, rec["price"]]]
                state["listings"][key] = rec
                refresh_derived(rec, now, cfg)
                if rec.get("excluded"):
                    stats["excluded"] += 1
                continue
            if sname not in rec.setdefault("src", []):
                rec["src"].append(sname)
            rec.pop("misses", None)
            rec.pop("missing_since", None)
            old_price = rec.get("price")
            for k, v in data.items():
                if v is None:
                    continue
                if k == "title" and rec.get("detail_at"):     # Detail-Titel ist genauer
                    continue
                if k in ("year", "km") and rec.get(k) and rec.get("detail_at"):
                    continue
                rec[k] = v
            if data.get("price") and old_price and data["price"] != old_price:
                rec.setdefault("prices", []).append([stamp, data["price"]])
                stats["price"] += 1
                rec["price_changed"] = stamp
                if data["price"] < old_price and not rec.get("excluded"):
                    rec["notify_drop"] = old_price - data["price"]
            refresh_derived(rec, now, cfg)
        if full and ok_any and not suspicious:
            pst["count"] = sum(1 for r in state["listings"].values() if r["platform"] == pid and not r.get("excluded"))

        # ---------- 3) fehlende Autos (nur im Vollscan, nur wenn alle Suchen des Autos vollständig liefen)
        if full and not suspicious:
            for key in [k for k, r in state["listings"].items() if r["platform"] == pid and k not in found]:
                rec = state["listings"][key]
                srcs = set(rec.get("src") or []) or set(names)
                if not srcs <= completed_ok:
                    continue
                rec["misses"] = rec.get("misses", 0) + 1
                rec.setdefault("missing_since", stamp)
                rec["recheck"] = True
                if rec["misses"] >= MISSES_UNTIL_REMOVED:
                    mark_removed(state, key, rec.pop("missing_since"), "nicht mehr in der Suche", stats, cfg)

    # ---------- 4) Detailseiten lesen (neue zuerst, dann verdächtige, dann Rest)
    budget = int(cfg.get("details_per_run", 40))
    todo = [r for r in state["listings"].values() if not r.get("excluded")]
    todo.sort(key=lambda r: (0 if not r.get("detail_at") and not r.get("baseline") else
                             1 if r.get("recheck") else
                             2 if not r.get("detail_at") else 3,
                             r.get("detail_at") or "", r["first_seen"]), reverse=False)
    for r in todo:
        if (r.get("description") or "").lstrip().startswith("{") or (r.get("detail_text") or "").lstrip().startswith("{"):
            r.pop("description", None)
            r["recheck"] = True                   # Rohdaten aus Version 3.0 neu lesen
    todo = [r for r in todo if not r.get("detail_at") or r.get("recheck") or
            (now - parse_iso(r["detail_at"])) > timedelta(days=int(cfg.get("detail_refresh_days", 7)))]
    detail_count = 0
    for rec in todo:
        if detail_count >= budget:
            break
        pid = rec["platform"]
        if pid in fetch.blocked or not platform_ok.get(pid, True):
            continue
        code, html = fetch.get(rec["url"], pid)
        detail_count += 1
        rec.pop("recheck", None)
        if code in (404, 410):
            mark_removed(state, rec["key"], stamp, "Inserat gelöscht", stats, cfg)
            continue
        if code != 200 or not html:
            rec["detail_failed"] = stamp
            continue
        d = parse_detail(pid, html)
        lid = rec["key"].split(":", 1)[1]
        if lid not in (fetch.final_url or "") and lid not in unquote(fetch.final_url or ""):
            d["gone"] = True                      # Weiterleitung auf eine andere Seite = Inserat weg
        if d["gone"]:
            mark_removed(state, rec["key"], stamp, "Inserat als verkauft/beendet markiert", stats, cfg)
            continue
        rec["detail_at"] = stamp
        rec.pop("detail_failed", None)
        if d["title"] and "taycan" in d["title"].lower():
            tt = re.sub(r"\s*(\||-|–)\s*(kleinanzeigen|autoscout24|mobile\.de|ebay|porsche finder)\b.*$", "", d["title"], flags=re.I)
            tt = re.sub(r"\s+(für|for)\s+[€\d.,\s]+(€|eur)?.*$|\s+(gebraucht\s+)?kaufen.*$|\s+in\s+[A-ZÄÖÜ][^|]*\|.*$", "", tt, flags=re.I).strip()
            if len(tt) >= 8:
                rec["title"] = tt
        for k in ("year", "km"):
            if d[k] and not rec.get(k):     # Werte aus der Ergebnisliste sind zuverlässiger
                rec[k] = d[k]
        if d["price"] and not rec.get("price"):
            rec["price"] = d["price"]
        if d["image"] and not rec.get("image"):
            rec["image"] = d["image"]
        rec["detail_text"] = d["body"][:6000]
        if d["description"]:
            rec["description"] = d["description"]
        else:
            rec.pop("description", None)
        refresh_derived(rec, now, cfg)
        time.sleep(random.uniform(1.2, 2.8))
    log.info("  %d Detailseiten gelesen", detail_count)

    # ---------- 5) Benachrichtigungen
    for rec in state["listings"].values():
        if rec.get("excluded") or rec.get("baseline"):
            continue
        ready = rec.get("detail_at") or rec.get("detail_failed") or rec["platform"] in fetch.blocked
        if not rec.get("notified") and ready:
            rec["notified"] = stamp
            if notify_match(rec, cfg):
                stats["new"] += 1
                notify(cfg, f"Neuer Taycan · {PLATFORM_NAMES.get(rec['platform'])}", summary(rec), rec["url"])
                time.sleep(1)
        if rec.get("notify_drop"):
            drop = rec.pop("notify_drop")
            if (cfg.get("notify") or {}).get("price_drop", True) and notify_match(rec, cfg):
                notify(cfg, f"Preis −{fmt_eur(drop)} · {PLATFORM_NAMES.get(rec['platform'])}", summary(rec), rec["url"],
                       tags="chart_with_downwards_trend")

    # ---------- 6) Aufräumen, Verlauf, Ausgabe
    cutoff = now - timedelta(days=KEEP_REMOVED_DAYS)
    state["removed"] = {k: r for k, r in state["removed"].items() if parse_iso(r["removed"]) >= cutoff}
    if full:
        day = state["history"].setdefault(local_date(now, tz), {})
        for pid, ok in platform_ok.items():
            if ok:
                day[pid] = sum(1 for r in state["listings"].values() if r["platform"] == pid and not r.get("excluded"))
        keep = sorted(state["history"])[-KEEP_HISTORY_DAYS:]
        state["history"] = {d: state["history"][d] for d in keep}
        state["last_full"] = stamp
        state["search_sig"] = sig
    names_now = {(x.get("name") or x["platform"]) for x in cfg["searches"]}
    state["searches"] = {n: v for n, v in {**state.get("searches", {}), **{n: {**st, "checked": stamp, "mode": mode}
                         for n, st in search_status.items()}}.items() if n in names_now}
    state["version"] = VERSION

    save_json(STATE_FILE, state, compact=True)
    write_outputs(state, now, mode, detail_count)
    if first_ever:
        notify(cfg, "Taycan Radar läuft 🚀", "Startbestand gespeichert – ab jetzt meldet der Bot neue Taycans.")
    log.info("Fertig (%s) – %d gemeldet, %d verkauft/offline, %d Preisänderungen, %d aussortiert.",
             mode, stats["new"], stats["removed"], stats["price"], stats["excluded"])
    return stats


def mark_removed(state, key, when, reason, stats, cfg):
    rec = state["listings"].pop(key, None)
    if not rec:
        return
    rec["removed"] = when
    rec["gone_reason"] = reason
    for k in ("misses", "missing_since", "recheck"):
        rec.pop(k, None)
    state["removed"][key] = rec
    if rec.get("excluded"):
        return
    stats["removed"] += 1
    log.info("  WEG: %s (%s)", summary(rec), reason)
    if (cfg.get("notify") or {}).get("removed", False) and notify_match(rec, cfg):
        notify(cfg, f"Verkauft/offline · {PLATFORM_NAMES.get(rec['platform'])}", summary(rec), rec.get("url"), tags="checkered_flag")


def summary(rec: dict) -> str:
    parts = [(rec.get("title") or "Porsche Taycan").strip()[:90]]
    if rec.get("price"):
        parts.append(fmt_eur(rec["price"]))
    if rec.get("year"):
        parts.append(f"EZ {rec['year']}")
    if rec.get("km") is not None:
        parts.append(fmt_km(rec["km"]))
    if rec.get("approved") in ("ja", "wahrscheinlich"):
        parts.append("Approved" + (" bis " + rec["approved_until"] if rec.get("approved_until") else "") +
                     ("?" if rec["approved"] == "wahrscheinlich" else ""))
    if rec.get("vat") == "ja":
        parts.append("MwSt.")
    return " · ".join(parts)


def notify_match(rec: dict, cfg: dict) -> bool:
    n = cfg.get("notify") or {}
    appr = n.get("approved", "ja_oder_wahrscheinlich")
    a = rec.get("approved", "unbekannt")
    if appr == "ja" and a != "ja":
        return False
    if appr == "ja_oder_wahrscheinlich" and a not in ("ja", "wahrscheinlich"):
        return False
    if appr == "nicht_nein" and a in ("nein", "abgelaufen"):
        return False
    vat = n.get("vat", "egal")
    v = rec.get("vat", "unbekannt")
    if vat == "ja" and v != "ja":
        return False
    if vat == "nicht_nein" and v == "nein":
        return False
    if n.get("max_price") and rec.get("price") and rec["price"] > n["max_price"]:
        return False
    if n.get("min_year") and rec.get("year") and rec["year"] < n["min_year"]:
        return False
    if n.get("max_km") and rec.get("km") and rec["km"] > n["max_km"]:
        return False
    if n.get("models") and rec.get("model") not in n["models"]:
        return False
    return True


def notify(cfg: dict, title: str, message: str, link: str | None = None, tags: str = "red_car") -> None:
    topic = cfg.get("ntfy_topic")
    if topic and not topic.startswith(("taycan-HIER", "wird-aus")):
        server = cfg.get("ntfy_server", "https://ntfy.sh").rstrip("/")
        headers = {"Title": title.encode("utf-8"), "Tags": tags, "Priority": "high"}
        if link:
            headers["Click"] = link
            headers["Actions"] = f"view, Inserat öffnen, {link}".encode("utf-8")
        try:
            requests.post(f"{server}/{topic}", data=message.encode("utf-8"), headers=headers, timeout=15).raise_for_status()
        except requests.RequestException as e:
            log.error("ntfy fehlgeschlagen: %s", e)
    tg = cfg.get("telegram") or {}
    if tg.get("bot_token") and tg.get("chat_id"):
        try:
            requests.post(f"https://api.telegram.org/bot{tg['bot_token']}/sendMessage",
                          json={"chat_id": tg["chat_id"], "text": f"*{title}*\n{message}" + (f"\n{link}" if link else ""),
                                "parse_mode": "Markdown"}, timeout=15).raise_for_status()
        except requests.RequestException as e:
            log.error("Telegram fehlgeschlagen: %s", e)


def dump_debug(pid: str, name: str, html: str) -> None:
    """Speichert die erste Ergebnisseite, wenn nichts erkannt wurde – zur Fehlersuche."""
    try:
        DEBUG_DIR.mkdir(exist_ok=True)
        safe = re.sub(r"[^a-z0-9]+", "-", name.lower()).strip("-")
        (DEBUG_DIR / f"{safe}.html").write_text(html[:800000], encoding="utf-8")
    except OSError:
        pass


# ==========================================================================
# Ausgabe für die Web-App
# ==========================================================================
PUBLIC_KEYS = ("key", "platform", "title", "url", "price", "year", "km", "ps", "image", "snippet", "description",
               "first_seen", "baseline", "prices", "removed", "gone_reason", "model", "body", "approved",
               "approved_until", "vat", "seller", "equip", "damage", "soh", "price_odd", "detail_at", "import")


def write_outputs(state: dict, now: datetime, mode: str, detail_count: int) -> None:
    def pub(r):
        o = {k: r[k] for k in PUBLIC_KEYS if r.get(k) not in (None, [], "", False)}
        if r.get("baseline"):
            o["baseline"] = True
        if o.get("description") and o.get("snippet") and o["description"][:60] == o["snippet"][:60]:
            o.pop("snippet")
        return o

    active = [pub(r) for r in state["listings"].values() if not r.get("excluded")]
    removed = [pub(r) for r in state["removed"].values() if not r.get("excluded")]
    excluded = [{"key": r["key"], "title": r.get("title"), "url": r.get("url"), "why": r.get("excluded")}
                for r in state["listings"].values() if r.get("excluded")]
    # gleiches Auto auf mehreren Plattformen
    fp: dict[str, set] = {}
    for r in active:
        if r.get("price") and r.get("year") and r.get("km") is not None:
            fp.setdefault(f"{r['year']}|{r['price']}|{round(r['km'] / 1000)}", set()).add(r["platform"])
    for r in active:
        if r.get("price") and r.get("year") and r.get("km") is not None:
            also = sorted(fp[f"{r['year']}|{r['price']}|{round(r['km'] / 1000)}"] - {r["platform"]})
            if also:
                r["also"] = also
    data = {
        "version": VERSION,
        "generated": iso(now),
        "platforms": [{"id": pid, "name": PLATFORM_NAMES.get(pid, pid)} for pid in PLATFORM_NAMES if pid in state["platforms"]],
        "equipment": {k: lbl for k, lbl, _ in EQUIPMENT},
        "active": sorted(active, key=lambda r: r["first_seen"], reverse=True),
        "removed": sorted(removed, key=lambda r: r["removed"], reverse=True),
        "excluded": excluded,
        "history": state["history"],
    }
    save_json(DOCS_DIR / "data.json", data, compact=True)
    status = {
        "updated": iso(now), "mode": mode, "last_full": state.get("last_full"), "details_read": detail_count,
        "platforms": {pid: {k: p.get(k) for k in ("ok", "error", "count", "checked")} for pid, p in state["platforms"].items()},
        "searches": state.get("searches", {}),
        "pending_details": sum(1 for r in state["listings"].values() if not r.get("detail_at") and not r.get("excluded")),
    }
    save_json(DOCS_DIR / "status.json", status)


# ==========================================================================
def main() -> None:
    ap = argparse.ArgumentParser(description="Taycan Radar Bot")
    ap.add_argument("--once", action="store_true", help="nur ein Durchlauf")
    ap.add_argument("--full", action="store_true", help="Vollscan erzwingen")
    ap.add_argument("--test", action="store_true", help="Test-Push senden")
    ap.add_argument("--config", default=str(CONFIG_FILE))
    args = ap.parse_args()
    logging.basicConfig(level=logging.INFO, format="%(asctime)s  %(message)s", datefmt="%H:%M:%S")
    try:
        cfg = json.loads(Path(args.config).read_text(encoding="utf-8"))
    except FileNotFoundError:
        sys.exit("config.json fehlt.")
    if os.environ.get("NTFY_TOPIC"):
        cfg["ntfy_topic"] = os.environ["NTFY_TOPIC"].strip()
    if os.environ.get("TELEGRAM_BOT_TOKEN") and os.environ.get("TELEGRAM_CHAT_ID"):
        cfg["telegram"] = {"bot_token": os.environ["TELEGRAM_BOT_TOKEN"], "chat_id": os.environ["TELEGRAM_CHAT_ID"]}
    if args.test:
        notify(cfg, "Taycan Radar ist verbunden ✅", "So sieht eine Meldung aus. Tippen öffnet das Inserat.",
               "https://www.autoscout24.de/lst/porsche/taycan?sort=age&desc=1")
        print("Test-Nachricht gesendet.")
        return
    interval = max(5, int(cfg.get("interval_minutes", 10)))
    while True:
        run_once(cfg, force_full=args.full)
        if args.once or args.full:
            break
        time.sleep(interval * 60 + random.randint(-60, 60))


if __name__ == "__main__":
    main()
