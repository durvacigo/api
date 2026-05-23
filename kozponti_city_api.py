from __future__ import annotations

import asyncio
import hashlib
import json
import os
import random
import re
import threading
import time
from datetime import datetime, timezone
from pathlib import Path
from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Optional, Tuple
from urllib.parse import urljoin, urlsplit, urlunsplit

import aiohttp
import requests
from flask import Flask, Response, jsonify, request

app = Flask(__name__)

# ============================================================
# KÖZPONTI FORRÁS API / RAW PROXY
# ============================================================
# Cél: a webappokban a KÜLSŐ API URL-eket lehessen átírni erre a szerverre.
# Ez nem alakítja át a válaszokat weboldal-formátumra, hanem ugyanazt adja vissza,
# amit az eredeti külső szolgáltató adna.
#
# Példák:
#   http://xmap.szkt.hu/Home/BusInLineIndex?lineCode=8&vehicleJournayRowId=5664274
#   -> http://127.0.0.1:8010/szeged/Home/BusInLineIndex?lineCode=8&vehicleJournayRowId=5664274
#
#   https://utas.hu/api/query/v1/ws/otp/api/where/vehicles-for-location.json?...
#   -> http://127.0.0.1:8010/volanbusz/utas/api/query/v1/ws/otp/api/where/vehicles-for-location.json?...
#
#   https://mavplusz.hu/otp2-backend/otp/routers/default/index/graphql
#   -> http://127.0.0.1:8010/volanbusz/mavplusz/otp2-backend/otp/routers/default/index/graphql
# ============================================================

HOST = os.environ.get("CENTRAL_API_HOST", "0.0.0.0")
PORT = int(os.environ.get("CENTRAL_API_PORT", "8010"))
TIMEOUT = float(os.environ.get("CENTRAL_API_TIMEOUT", "25"))

# GET cache: csak rövid ideig, hogy ne minden webapp ugyanazt kérje le külön.
# Ha teljesen nyers, cache nélküli működés kell: set CENTRAL_API_CACHE_SECONDS=0
CACHE_SECONDS = float(os.environ.get("CENTRAL_API_CACHE_SECONDS", "3"))
CACHE_MAX_ITEMS = int(os.environ.get("CENTRAL_API_CACHE_MAX_ITEMS", "500"))

# Szeged webappban ez eddig is külön FastAPI/local járműforrás volt, nem maga a webapp.
# Átírható, ha nálad máshol fut.
SZEGED_VEHICLES_URL = os.environ.get("SZEGED_VEHICLES_URL", "http://127.0.0.1:8006/vehicles")

# Külső bázisok
XMAP_BASE = os.environ.get("XMAP_BASE", "http://xmap.szkt.hu/")
MAVPLUSZ_BASE = os.environ.get("MAVPLUSZ_BASE", "https://mavplusz.hu/")
UTAS_BASE = os.environ.get("UTAS_BASE", "https://utas.hu/")
BKK_BASE = os.environ.get("BKK_BASE", "https://go.bkk.hu/")
DKV_BASE = os.environ.get("DKV_BASE", "https://mobilalkalmazas.dkv.hu/")
MVK_MOBIL_BASE = os.environ.get("MVK_MOBIL_BASE", "http://mobilalkalmazas.mvkzrt.hu:8080/")
MVK_VALOS_BASE = os.environ.get("MVK_VALOS_BASE", "http://valosidoben.mvkzrt.hu:8080/")
GTFS_KTI_BASE = os.environ.get("GTFS_KTI_BASE", "https://gtfs.kti.hu/")
SOFIA_HTTP_BASE = os.environ.get("SOFIA_HTTP_BASE", "https://api.livetransport.eu/")


# ============================================================
# SZEGED /vehicles - beépített XMap scanner az xmap_api_3.py alapján
# ============================================================
XMAP_LINEINDEX_URL = os.environ.get("XMAP_LINEINDEX_URL", "http://xmap.szkt.hu/Intercity/LineIndex")
XMAP_BUSINLINE_URL = os.environ.get("XMAP_BUSINLINE_URL", "http://xmap.szkt.hu/Home/BusInLineIndex")
XMAP_TRANSDETAIL_URL = os.environ.get("XMAP_TRANSDETAIL_URL", "http://xmap.szkt.hu/Intercity/TransDetailIndex")

ACTIVE_POLL_SECONDS = int(os.environ.get("SZEGED_ACTIVE_POLL_SECONDS", "20"))
VEHICLE_TTL_SECONDS = int(os.environ.get("SZEGED_VEHICLE_TTL_SECONDS", str(15 * 60)))
MAX_CONCURRENT_HTTP = int(os.environ.get("SZEGED_MAX_CONCURRENT_HTTP", "15"))
STOP_SCAN_DELAY_MIN = float(os.environ.get("SZEGED_STOP_SCAN_DELAY_MIN", "0.05"))
STOP_SCAN_DELAY_MAX = float(os.environ.get("SZEGED_STOP_SCAN_DELAY_MAX", "0.1"))
SZEGED_CACHE_DIR = Path(os.environ.get("SZEGED_XMAP_CACHE_DIR", "cache"))
SZEGED_VEHICLES_CACHE_FILE = SZEGED_CACHE_DIR / "vehicles_cache.json"
SZEGED_BUSLINEINDEX_CACHE_FILE = SZEGED_CACHE_DIR / "buslineindex_cache.json"

STOP_IDS: List[str] = [
    "4840", "4841", "4976", "4497", "4842", "4843", "2591", "4498", "2544", "4598", "4844", "4845", 
    "4499", "86", "2593", "4846", "106", "4545", "2702", "2684", "4460", "4461", "165", "166", "4847", 
    "2945", "4848", "1798", "4778", "4849", "4500", "240", "2594", "4850", "4501", "257", "4851", 
    "284", "2834", "2501", "289", "4502", "4852", "298", "301", "4853", "2801", "341", "4854", "346", 
    "9477", "2595", "2596", "2508", "4855", "375", "4856", "9365", "391", "4857", "410", "2597", "441", 
    "9501", "443", "2900", "4859", "9502", "2598", "2774", "4861", "4503", "529", "4862", "4555", 
    "2599", "534", "4863", "4689", "559", "4864", "2600", "2601", "4865", "4456", "607", "4866", 
    "2901", "2602", "4867", "4868", "3928", "4793", "2767", "659", "4869", "661", "4870", "669", 
    "2588", "698", "4871", "699", "725", "2841", "4457", "2604", "745", "4872", "753", "2690", "762", 
    "4873", "784", "4504", "786", "4874", "792", "805", "4875", "2587", "4876", "4877", "4462", 
    "2738", "816", "9503", "9504", "4880", "4881", "4882", "857", "4883", "865", "874", "4884", 
    "4505", "4506", "989", "4885", "992", "2844", "4886", "4507", "1000", "1001", "2846", "1008", 
    "2610", "1018", "4887", "4888", "4889", "4890", "4891", "4892", "9505", "2847", "1072", "4508", 
    "4894", "1075", "1093", "4895", "1111", "1112", "2641", "2642", "1126", "3313", "4808", "2502", 
    "9395", "1158", "1162", "1163", "1164", "1166", "1167", "1211", "2761", "1245", "1247", "4897", 
    "2616", "1250", "2617", "2618", "4509", "4898", "9396", "2503", "1285", "9506", "4900", "1321", 
    "4901", "2548", "2542", "4902", "1333", "2849", "1346", "4903", "4904", "4905", "2898", "1389", 
    "9507", "1404", "2547", "4546", "2546", "9508", "2533", "1411", "3980", "4908", "1528", "1529", 
    "4909", "4910", "1596", "2534", "2622", "4911", "2895", "1647", "2624", "9397", "1708", "4912", 
    "1713", "2185", "4510", "4913", "4914", "4794", "1784", "4915", "4916", "9536", "4522", "9398", 
    "4512", "1799", "2897", "1800", "4917", "2625", "1805", "2579", "4918", "2581", "9399", "9509", 
    "3310", "2205", "1845", "1852", "4920", "571", "4513", "1909", "2645", "4922", "1916", "2856", 
    "1924", "1929", "4923", "1935", "2857", "4924", "4556", "2537", "4925", "1989", "4514", "9510", 
    "1994", "4523", "4484", "2053", "2629", "9356", "3990", "2086", "2087", "2088", "2661", "2746", 
    "2176", "2177", "2186", "2771", "2196", "2631", "4951", "4952", "4953", "2692", "4954", "4955", 
    "4956", "4957", "2225", "2227", "2228", "2231", "4958", "2242", "4516", "4959", "4960", "9400", 
    "4548", "9512", "2585", "2586", "2529", "4962", "4963", "2633", "4549", "2344", "2345", "2348", 
    "2634", "2360", "2361", "2391", "2863", "2526", "2393", "2394", "4458", "2402", "2635", "9534", 
    "4530", "2902", "4517", "2549", "9513", "4966", "4967", "2590", "4531", "2432", "2865", "2433", 
    "2441", "4459", "4968", "2638", "4813", "4792"
]

SZEGED_BASE_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120 Safari/537.36",
    "Accept": "*/*",
    "Accept-Language": "hu-HU,hu;q=0.9,en-US;q=0.8,en;q=0.7",
    "Connection": "keep-alive",
}

_szeged_loop: asyncio.AbstractEventLoop | None = None
_szeged_thread: threading.Thread | None = None
_szeged_http_session: aiohttp.ClientSession | None = None
_szeged_http_sem: asyncio.Semaphore | None = None
_szeged_vehicles_lock: asyncio.Lock | None = None
_szeged_active_trips_lock: asyncio.Lock | None = None
_szeged_tracking_queue: asyncio.Queue | None = None
_szeged_started = False

_szeged_vehicles_state: Dict[str, Any] = {"ts": 0, "count": 0, "vehicles": [], "by_plate": {}}
_szeged_active_trips: Dict[str, Dict[str, Any]] = {}
_szeged_stats: Dict[str, int] = {"lineindex_scans": 0, "businline_calls": 0, "vehicles_found": 0}
_szeged_last_error: str | None = None


def _szeged_json_write(path: Path, data: Any) -> None:
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_suffix(path.suffix + ".tmp")
        tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
        tmp.replace(path)
    except Exception:
        pass


def _szeged_json_read(path: Path, default: Any) -> Any:
    try:
        if path.exists():
            return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        pass
    return default


def _szeged_utc_floor_to_hour_isoz(dt: datetime) -> str:
    d = dt.astimezone(timezone.utc).replace(minute=0, second=0, microsecond=0)
    return d.strftime("%Y-%m-%dT%H:%M:%S.000Z")


def _szeged_trip_key(line_code: str, row_id: str) -> str:
    return f"{line_code}|{row_id}"


def _szeged_html_text(s: str) -> str:
    s = re.sub(r"<br\s*/?>", " ", s or "", flags=re.I)
    s = re.sub(r"<[^>]+>", " ", s)
    s = s.replace("&nbsp;", " ").replace("&amp;", "&").replace("&lt;", "<").replace("&gt;", ">").replace("&#160;", " ")
    return re.sub(r"\s+", " ", s).strip()


def _szeged_parse_lineindex_rows(html: str) -> List[Dict[str, str]]:
    out: List[Dict[str, str]] = []
    pattern = r'''<tr[^>]*onclick="GetTransDetail\('(\d+)'\)"[^>]*>(.*?)</tr>'''
    for row_match in re.finditer(pattern, html or "", flags=re.I | re.S):
        jid = (row_match.group(1) or "").strip()
        row_html = row_match.group(2) or ""
        cells = re.findall(r'''<td([^>]*)>(.*?)</td>''', row_html, flags=re.I | re.S)
        delay_text, line_text = "", ""
        for attrs, inner_html in cells:
            attrs_l = attrs.lower()
            txt = _szeged_html_text(inner_html)
            if not txt:
                continue
            if 'class="line' in attrs_l or "class='line" in attrs_l or re.search(r"\bline\b", attrs_l):
                if not line_text:
                    line_text = txt
            if 'class="delay' in attrs_l or "class='delay" in attrs_l or re.search(r"\bdelay\b|\bkeses\b|\bkésés\b", attrs_l):
                if not delay_text:
                    delay_text = txt
        if not delay_text and len(cells) >= 3:
            candidate = _szeged_html_text(cells[2][1])
            if candidate and not re.search(r"cél|irány|destination", candidate, flags=re.I):
                delay_text = candidate
        if not line_text and len(cells) >= 2:
            line_text = _szeged_html_text(cells[1][1])
        if jid and line_text:
            out.append({"line": line_text, "row_id": jid, "delay_text": delay_text, "delay_present": bool(delay_text.strip())})
    return out


async def _szeged_fetch_get(url: str) -> Tuple[Optional[str], Optional[int]]:
    global _szeged_last_error
    if _szeged_http_session is None or _szeged_http_sem is None:
        return None, None
    try:
        async with _szeged_http_sem:
            async with _szeged_http_session.get(url) as r:
                text = await r.text(errors="ignore")
                if r.status == 200 and text:
                    return text, r.status
                _szeged_last_error = f"GET {url} -> HTTP {r.status}"
    except Exception as e:
        _szeged_last_error = repr(e)
    return None, None


async def _szeged_fetch_post_form(url: str, data: Dict[str, str]) -> Tuple[Optional[str], Optional[int]]:
    global _szeged_last_error
    if _szeged_http_session is None or _szeged_http_sem is None:
        return None, None
    try:
        async with _szeged_http_sem:
            async with _szeged_http_session.post(url, data=data, headers={**SZEGED_BASE_HEADERS, "Content-Type": "application/x-www-form-urlencoded"}) as r:
                text = await r.text(errors="ignore")
                if r.status == 200 and text:
                    return text, r.status
                _szeged_last_error = f"POST {url} -> HTTP {r.status}"
    except Exception as e:
        _szeged_last_error = repr(e)
    return None, None


def _szeged_normalize_vehicle(item: Dict[str, Any], line_code: str, row_id: str) -> Dict[str, Any]:
    plate = ""
    for key in ["VehicleRegistrationNumber", "RegistrationNumber", "LicensePlate", "Plate", "plate", "VehicleName", "VehicleId", "VehicleID"]:
        if item.get(key):
            plate = str(item.get(key)).strip().upper()
            break
    raw = dict(item)
    raw["lineCode"] = line_code
    raw["id"] = row_id
    return {"id": plate or _szeged_trip_key(line_code, row_id), "plate": plate, "line": line_code, "trip_id": row_id, "last_seen_ts": int(time.time()), "raw": raw}


def _szeged_to_legacy_vehicle(v: Dict[str, Any]) -> Dict[str, Any]:
    return v.get("raw") or {}


async def _szeged_save_vehicles_cache() -> None:
    if _szeged_vehicles_lock is None:
        return
    async with _szeged_vehicles_lock:
        payload = {"ts": _szeged_vehicles_state["ts"], "count": _szeged_vehicles_state["count"], "vehicles": _szeged_vehicles_state["vehicles"]}
    _szeged_json_write(SZEGED_VEHICLES_CACHE_FILE, payload)


async def _szeged_upsert_seen_vehicles(vehicles: List[Dict[str, Any]]) -> None:
    if _szeged_vehicles_lock is None:
        return
    now_ts = int(time.time())
    async with _szeged_vehicles_lock:
        by_plate = dict(_szeged_vehicles_state.get("by_plate") or {})
        for v in vehicles:
            plate = str(v.get("plate") or v.get("id") or "").strip().upper()
            if not plate:
                continue
            old = by_plate.get(plate) or {}
            merged = dict(old)
            merged.update(v)
            merged["last_seen_ts"] = now_ts
            by_plate[plate] = merged
        by_plate = {k: v for k, v in by_plate.items() if now_ts - int(v.get("last_seen_ts") or 0) <= VEHICLE_TTL_SECONDS}
        _szeged_vehicles_state["by_plate"] = by_plate
        _szeged_vehicles_state["vehicles"] = sorted(by_plate.values(), key=lambda x: x.get("last_seen_ts") or 0, reverse=True)
        _szeged_vehicles_state["count"] = len(by_plate)
        _szeged_vehicles_state["ts"] = now_ts
    await _szeged_save_vehicles_cache()


async def _szeged_load_active_trips() -> None:
    global _szeged_active_trips
    data = _szeged_json_read(SZEGED_BUSLINEINDEX_CACHE_FILE, {})
    if isinstance(data, dict):
        _szeged_active_trips = data


async def _szeged_save_active_trips() -> None:
    if _szeged_active_trips_lock is None:
        return
    async with _szeged_active_trips_lock:
        data = dict(_szeged_active_trips)
    _szeged_json_write(SZEGED_BUSLINEINDEX_CACHE_FILE, data)


async def _szeged_cache_saver_loop() -> None:
    while True:
        await asyncio.sleep(15)
        await _szeged_save_active_trips()


async def _szeged_stop_scanner_loop() -> None:
    while True:
        used_date = _szeged_utc_floor_to_hour_isoz(datetime.now(timezone.utc))
        for stop_id in STOP_IDS:
            body = {"Target": str(stop_id), "IsArrival": "false", "StopPointSearchDate": used_date, "StopPointDateHour": "0", "StopPointDateMinute": "0"}
            _szeged_stats["lineindex_scans"] += 1
            text, status = await _szeged_fetch_post_form(XMAP_LINEINDEX_URL, body)
            if text and status == 200:
                rows = _szeged_parse_lineindex_rows(text)
                now_ts = int(time.time())
                if _szeged_active_trips_lock is not None:
                    async with _szeged_active_trips_lock:
                        for row in rows:
                            if row.get("delay_present"):
                                line, row_id = row["line"], row["row_id"]
                                t_key = _szeged_trip_key(line, row_id)
                                if t_key not in _szeged_active_trips:
                                    _szeged_active_trips[t_key] = {"line": line, "row_id": row_id, "last_poll_ts": 0, "last_seen_in_index": now_ts}
                                else:
                                    _szeged_active_trips[t_key]["last_seen_in_index"] = now_ts
            await asyncio.sleep(random.uniform(STOP_SCAN_DELAY_MIN, STOP_SCAN_DELAY_MAX))


async def _szeged_poller_producer_loop() -> None:
    while True:
        now_ts = int(time.time())
        to_poll = []
        stale_keys = []
        if _szeged_active_trips_lock is not None:
            async with _szeged_active_trips_lock:
                for t_key, trip in list(_szeged_active_trips.items()):
                    if now_ts - int(trip.get("last_seen_in_index") or 0) > 7200:
                        stale_keys.append(t_key)
                        continue
                    if now_ts - int(trip.get("last_poll_ts") or 0) >= ACTIVE_POLL_SECONDS:
                        trip["last_poll_ts"] = now_ts
                        to_poll.append(dict(trip))
                for k in stale_keys:
                    _szeged_active_trips.pop(k, None)
        if _szeged_tracking_queue is not None:
            for trip in to_poll:
                await _szeged_tracking_queue.put(trip)
        await asyncio.sleep(1)


async def _szeged_vehicle_poller_worker(worker_id: int) -> None:
    if _szeged_tracking_queue is None:
        return
    from urllib.parse import urlencode
    while True:
        trip = await _szeged_tracking_queue.get()
        line_code = str(trip.get("line") or "")
        row_id = str(trip.get("row_id") or "")
        t_key = _szeged_trip_key(line_code, row_id)
        url = XMAP_BUSINLINE_URL + "?" + urlencode({"lineCode": line_code, "vehicleJournayRowId": row_id})
        _szeged_stats["businline_calls"] += 1
        txt, status = await _szeged_fetch_get(url)
        if txt and status == 200:
            try:
                arr = json.loads(txt.strip())
                if isinstance(arr, list):
                    if len(arr) == 0:
                        if _szeged_active_trips_lock is not None:
                            async with _szeged_active_trips_lock:
                                _szeged_active_trips.pop(t_key, None)
                    else:
                        normalized = [_szeged_normalize_vehicle(x, line_code, row_id) for x in arr if isinstance(x, dict)]
                        normalized = [x for x in normalized if x.get("plate") or x.get("id")]
                        if normalized:
                            _szeged_stats["vehicles_found"] += len(normalized)
                            await _szeged_upsert_seen_vehicles(normalized)
            except Exception as e:
                global _szeged_last_error
                _szeged_last_error = repr(e)
        _szeged_tracking_queue.task_done()


async def _szeged_scanner_main() -> None:
    global _szeged_http_session, _szeged_http_sem, _szeged_vehicles_lock, _szeged_active_trips_lock, _szeged_tracking_queue, _szeged_last_error
    SZEGED_CACHE_DIR.mkdir(parents=True, exist_ok=True)
    _szeged_http_sem = asyncio.Semaphore(MAX_CONCURRENT_HTTP)
    _szeged_vehicles_lock = asyncio.Lock()
    _szeged_active_trips_lock = asyncio.Lock()
    _szeged_tracking_queue = asyncio.Queue()
    await _szeged_load_active_trips()
    timeout = aiohttp.ClientTimeout(total=12, connect=6, sock_read=8)
    connector = aiohttp.TCPConnector(limit=MAX_CONCURRENT_HTTP, ttl_dns_cache=300)
    _szeged_http_session = aiohttp.ClientSession(headers=SZEGED_BASE_HEADERS, timeout=timeout, connector=connector)
    tasks = [
        asyncio.create_task(_szeged_stop_scanner_loop(), name="szeged_scanner"),
        asyncio.create_task(_szeged_poller_producer_loop(), name="szeged_poller_producer"),
        asyncio.create_task(_szeged_cache_saver_loop(), name="szeged_cache_saver"),
    ] + [asyncio.create_task(_szeged_vehicle_poller_worker(i), name=f"szeged_worker_{i}") for i in range(10)]
    try:
        await asyncio.gather(*tasks)
    except asyncio.CancelledError:
        pass
    except Exception as e:
        _szeged_last_error = repr(e)
    finally:
        await _szeged_save_active_trips()
        if _szeged_http_session is not None:
            await _szeged_http_session.close()


def _run_szeged_loop() -> None:
    global _szeged_loop
    _szeged_loop = asyncio.new_event_loop()
    asyncio.set_event_loop(_szeged_loop)
    _szeged_loop.run_until_complete(_szeged_scanner_main())


def _ensure_szeged_scanner_started() -> None:
    global _szeged_started, _szeged_thread
    if _szeged_started:
        return
    _szeged_started = True
    _szeged_thread = threading.Thread(target=_run_szeged_loop, name="szeged-xmap-scanner", daemon=True)
    _szeged_thread.start()


HOP_BY_HOP_HEADERS = {
    "connection", "keep-alive", "proxy-authenticate", "proxy-authorization",
    "te", "trailers", "transfer-encoding", "upgrade", "host", "content-length",
    "accept-encoding",  # requests bontsa ki, Flask majd visszaküldi normál bodyként
}

PASS_RESPONSE_HEADERS = {
    "content-type", "cache-control", "expires", "last-modified", "etag",
    "content-disposition", "location",
}

@dataclass
class CacheItem:
    ts: float
    status: int
    headers: Dict[str, str]
    body: bytes

_CACHE: Dict[str, CacheItem] = {}


def _clean_subpath(path: str) -> str:
    path = (path or "").lstrip("/")
    # nagyon egyszerű védelem path traversal ellen
    parts = []
    for p in path.split("/"):
        if p in ("", "."):
            continue
        if p == "..":
            continue
        parts.append(p)
    return "/".join(parts)


def _join_url(base: str, subpath: str) -> str:
    base = base.rstrip("/") + "/"
    subpath = _clean_subpath(subpath)
    return urljoin(base, subpath)


def _target_origin(url: str) -> str:
    p = urlsplit(url)
    return urlunsplit((p.scheme, p.netloc, "", "", ""))


def _make_forward_headers(target_url: str) -> Dict[str, str]:
    out: Dict[str, str] = {}
    for k, v in request.headers.items():
        lk = k.lower()
        if lk in HOP_BY_HOP_HEADERS:
            continue
        # A saját hostra mutató origin/referer ne menjen tovább más domainre.
        if lk in {"origin", "referer"}:
            continue
        out[k] = v

    origin = _target_origin(target_url)
    host = urlsplit(target_url).netloc.lower()

    if "utas.hu" in host:
        out.setdefault("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36")
        out["Origin"] = "https://utas.hu"
        out["Referer"] = "https://utas.hu/"
        out.setdefault("Accept", "application/json, text/plain, */*")
    elif "mavplusz.hu" in host:
        out.setdefault("User-Agent", "Mozilla/5.0")
        out["Origin"] = "https://mavplusz.hu"
        out["Referer"] = "https://mavplusz.hu/"
        out.setdefault("Accept", "application/json, text/plain, */*")
    elif "xmap.szkt.hu" in host:
        out.setdefault("User-Agent", "Mozilla/5.0")
        out["Origin"] = "http://xmap.szkt.hu"
        out["Referer"] = "http://xmap.szkt.hu/"
        out.setdefault("Accept", "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8")
    elif "go.bkk.hu" in host:
        out.setdefault("User-Agent", "bkk-realtime-map/4.6")
        out.setdefault("Accept", "application/json, text/plain, */*")
    else:
        out.setdefault("User-Agent", "Mozilla/5.0")
        out.setdefault("Accept", "*/*")

    return out


def _cache_key(method: str, url: str, body: bytes) -> str:
    h = hashlib.sha256()
    h.update(method.upper().encode("utf-8"))
    h.update(b"\0")
    h.update(url.encode("utf-8"))
    h.update(b"\0")
    h.update(body or b"")
    return h.hexdigest()


def _get_cached(key: str) -> Optional[Response]:
    if CACHE_SECONDS <= 0:
        return None
    item = _CACHE.get(key)
    if not item:
        return None
    if time.time() - item.ts > CACHE_SECONDS:
        _CACHE.pop(key, None)
        return None
    return _make_response(item.body, item.status, item.headers, from_cache=True)


def _store_cache(key: str, status: int, headers: Dict[str, str], body: bytes) -> None:
    if CACHE_SECONDS <= 0:
        return
    if request.method.upper() not in {"GET", "POST"}:
        return
    # Hibákat csak rövidebb ideig is lehetne, most ugyanúgy cache-eljük pár mp-ig.
    if len(_CACHE) >= CACHE_MAX_ITEMS:
        # legrégebbi törlése
        oldest = min(_CACHE.items(), key=lambda kv: kv[1].ts)[0]
        _CACHE.pop(oldest, None)
    _CACHE[key] = CacheItem(time.time(), status, headers, body)


def _response_headers(resp: requests.Response) -> Dict[str, str]:
    out: Dict[str, str] = {}
    for k, v in resp.headers.items():
        if k.lower() in PASS_RESPONSE_HEADERS:
            out[k] = v
    return out


def _make_response(body: bytes, status: int, headers: Dict[str, str], from_cache: bool = False) -> Response:
    r = Response(body, status=status)
    for k, v in headers.items():
        if k.lower() in HOP_BY_HOP_HEADERS:
            continue
        r.headers[k] = v
    r.headers["Access-Control-Allow-Origin"] = "*"
    r.headers["Access-Control-Allow-Methods"] = "GET, POST, PUT, PATCH, DELETE, OPTIONS, HEAD"
    r.headers["Access-Control-Allow-Headers"] = "Content-Type, Authorization, X-Requested-With, Accept, Origin, Referer"
    r.headers["X-Central-API-Cache"] = "HIT" if from_cache else "MISS"
    return r


def _proxy_to(target_url: str, *, use_query: bool = True, allow_cache: bool = True) -> Response:
    if request.method == "OPTIONS":
        return _make_response(b"", 204, {"Content-Type": "text/plain; charset=utf-8"})

    params = request.query_string.decode("utf-8", errors="ignore") if use_query else ""
    if params:
        sep = "&" if "?" in target_url else "?"
        target_url = target_url + sep + params

    body = request.get_data() or b""
    key = _cache_key(request.method, target_url, body)
    if allow_cache:
        cached = _get_cached(key)
        if cached is not None:
            return cached

    try:
        resp = requests.request(
            method=request.method,
            url=target_url,
            headers=_make_forward_headers(target_url),
            data=body if request.method.upper() not in {"GET", "HEAD"} else None,
            timeout=TIMEOUT,
            allow_redirects=False,
        )
        headers = _response_headers(resp)
        out = _make_response(resp.content, resp.status_code, headers)
        if allow_cache and resp.status_code < 500:
            _store_cache(key, resp.status_code, headers, resp.content)
        return out
    except Exception as e:
        return jsonify({
            "ok": False,
            "error": repr(e),
            "target": target_url,
        }), 502


@app.after_request
def _after(resp: Response):
    # CORS minden válaszra, hogy a webapp külön portról is kérhesse.
    resp.headers.setdefault("Access-Control-Allow-Origin", "*")
    resp.headers.setdefault("Access-Control-Allow-Methods", "GET, POST, PUT, PATCH, DELETE, OPTIONS, HEAD")
    resp.headers.setdefault("Access-Control-Allow-Headers", "Content-Type, Authorization, X-Requested-With, Accept, Origin, Referer")
    return resp


@app.get("/")
def index():
    return jsonify({
        "ok": True,
        "name": "kozponti_forras_api",
        "port": PORT,
        "cache_seconds": CACHE_SECONDS,
        "examples": [
            "/szeged/Home/BusInLineIndex?lineCode=8&vehicleJournayRowId=5664274",
            "/szeged/Intercity/LineIndex",
            "/szeged/Intercity/TransDetailIndex?vehicleJournayRowId=5664274",
            "/volanbusz/utas/api/query/v1/ws/otp/api/where/vehicles-for-location.json?lat=47.1&lon=19.0&latSpan=0.1&lonSpan=0.1&key=ride-web&version=5&appVersion=4.0.0&locale=hu",
            "/volanbusz/mavplusz/otp2-backend/otp/auth/get-jwt",
            "/volanbusz/mavplusz/otp2-backend/otp/routers/default/index/graphql",
        ],
    })


@app.get("/health")
def health():
    return jsonify({"ok": True, "ts": int(time.time())})


# ============================================================
# SZEGED
# ============================================================
# XMap: pontosan a path maradjon meg helyben is:
#   /szeged/Home/BusInLineIndex?...       -> http://xmap.szkt.hu/Home/BusInLineIndex?...
#   /szeged/Intercity/LineIndex           -> http://xmap.szkt.hu/Intercity/LineIndex
#   /szeged/Intercity/TransDetailIndex?...-> http://xmap.szkt.hu/Intercity/TransDetailIndex?...
@app.route("/szeged/Home/<path:subpath>", methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD"])
def szeged_xmap_home(subpath: str):
    return _proxy_to(_join_url(XMAP_BASE, f"Home/{subpath}"))


@app.route("/szeged/Intercity/<path:subpath>", methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD"])
def szeged_xmap_intercity(subpath: str):
    return _proxy_to(_join_url(XMAP_BASE, f"Intercity/{subpath}"))


# Ha a webappban rövidebbre akarod írni: /szeged/xmap/Intercity/LineIndex
@app.route("/szeged/xmap/<path:subpath>", methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD"])
def szeged_xmap_any(subpath: str):
    return _proxy_to(_join_url(XMAP_BASE, subpath))


# Szeged beépített járműforrása az xmap_api_3.py alapján.
# Ugyanazt a legacy JSON formátumot adja vissza, mint a külön xmap_api_3.py /vehicles végpontja.
@app.route("/szeged/vehicles", methods=["GET", "OPTIONS", "HEAD"])
@app.route("/szeged/api/vehicles", methods=["GET", "OPTIONS", "HEAD"])
def szeged_vehicles_raw():
    if request.method == "OPTIONS":
        return _make_response(b"", 204, {"Content-Type": "text/plain; charset=utf-8"})
    _ensure_szeged_scanner_started()
    ts = int(_szeged_vehicles_state.get("ts") or 0)
    vehicles = [_szeged_to_legacy_vehicle(v) for v in list(_szeged_vehicles_state.get("vehicles") or [])]
    count = int(_szeged_vehicles_state.get("count") or len(vehicles))
    return jsonify({
        "vehicles": vehicles,
        "age_sec": max(0, int(time.time()) - ts) if ts else 0,
        "count": count,
        "ts": ts,
    })


@app.route("/szeged/vehicle/<plate>", methods=["GET", "OPTIONS", "HEAD"])
@app.route("/szeged/api/vehicle/<plate>", methods=["GET", "OPTIONS", "HEAD"])
def szeged_vehicle_one(plate: str):
    if request.method == "OPTIONS":
        return _make_response(b"", 204, {"Content-Type": "text/plain; charset=utf-8"})
    _ensure_szeged_scanner_started()
    p = str(plate or "").strip().upper()
    obj = (_szeged_vehicles_state.get("by_plate") or {}).get(p)
    if not obj:
        return jsonify({"ok": False, "error": f"Nem találom: {p}"}), 404
    return jsonify({"ts": int(time.time()), "vehicle": _szeged_to_legacy_vehicle(obj)})


@app.route("/szeged/status", methods=["GET", "OPTIONS", "HEAD"])
@app.route("/szeged/api/status", methods=["GET", "OPTIONS", "HEAD"])
def szeged_scanner_status():
    if request.method == "OPTIONS":
        return _make_response(b"", 204, {"Content-Type": "text/plain; charset=utf-8"})
    _ensure_szeged_scanner_started()
    qsize = _szeged_tracking_queue.qsize() if _szeged_tracking_queue is not None else 0
    return jsonify({
        "ok": True,
        "started": _szeged_started,
        "active_vehicles": int(_szeged_vehicles_state.get("count") or 0),
        "cached_active_trips": len(_szeged_active_trips),
        "tracking_queue_size": qsize,
        "stats": _szeged_stats,
        "tracked_stops_count": len(STOP_IDS),
        "last_error": _szeged_last_error,
        "ts": int(_szeged_vehicles_state.get("ts") or 0),
    })


# Szeged MÁV+ fallback / tripplanner jellegű GraphQL hívásokhoz.
@app.route("/szeged/mavplusz/<path:subpath>", methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD"])
def szeged_mavplusz(subpath: str):
    return _proxy_to(_join_url(MAVPLUSZ_BASE, subpath), allow_cache=False)


# ============================================================
# VOLÁNBUSZ
# ============================================================
# Utas.hu pozíciós API:
#   /volanbusz/utas/api/query/v1/ws/otp/api/where/vehicles-for-location.json?...
# -> https://utas.hu/api/query/v1/ws/otp/api/where/vehicles-for-location.json?...
@app.route("/volanbusz/utas/<path:subpath>", methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD"])
def volan_utas(subpath: str):
    return _proxy_to(_join_url(UTAS_BASE, subpath))


# Kényelmi alias, hogy akár /volanbusz/api/query/... is működjön utas.hu-ként.
@app.route("/volanbusz/api/query/<path:subpath>", methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD"])
def volan_utas_alias(subpath: str):
    return _proxy_to(_join_url(UTAS_BASE, f"api/query/{subpath}"))


# MÁV+ JWT és GraphQL:
#   /volanbusz/mavplusz/otp2-backend/otp/auth/get-jwt
#   /volanbusz/mavplusz/otp2-backend/otp/routers/default/index/graphql
@app.route("/volanbusz/mavplusz/<path:subpath>", methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD"])
def volan_mavplusz(subpath: str):
    # GraphQL/JWT ne legyen cache-elve, nehogy token vagy POST válasz keveredjen.
    return _proxy_to(_join_url(MAVPLUSZ_BASE, subpath), allow_cache=False)


# Kényelmi alias, ha a webappban csak a domain lett lecserélve /volanbusz-ra:
# /volanbusz/otp2-backend/... -> https://mavplusz.hu/otp2-backend/...
@app.route("/volanbusz/otp2-backend/<path:subpath>", methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD"])
def volan_mavplusz_alias(subpath: str):
    return _proxy_to(_join_url(MAVPLUSZ_BASE, f"otp2-backend/{subpath}"), allow_cache=False)


# Volán GTFS zip / statikus forrás:
@app.route("/volanbusz/gtfs/<path:subpath>", methods=["GET", "OPTIONS", "HEAD"])
def volan_gtfs(subpath: str):
    return _proxy_to(_join_url(GTFS_KTI_BASE, subpath), allow_cache=True)


# ============================================================
# BUDAPEST / BKK
# ============================================================
@app.route("/budapest/go/<path:subpath>", methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD"])
def budapest_go(subpath: str):
    return _proxy_to(_join_url(BKK_BASE, subpath))


# Alias a BKK API-path megtartásával.
@app.route("/budapest/api/query/<path:subpath>", methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD"])
def budapest_bkk_api_alias(subpath: str):
    return _proxy_to(_join_url(BKK_BASE, f"api/query/{subpath}"))


@app.route("/budapest/api/static/<path:subpath>", methods=["GET", "OPTIONS", "HEAD"])
def budapest_bkk_static_alias(subpath: str):
    return _proxy_to(_join_url(BKK_BASE, f"api/static/{subpath}"), allow_cache=True)


# ============================================================
# DEBRECEN / DKV
# ============================================================
@app.route("/debrecen/mobilapp/<path:subpath>", methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD"])
def debrecen_mobilapp(subpath: str):
    return _proxy_to(_join_url(DKV_BASE, f"mobilapp/{subpath}"))


@app.route("/debrecen/GTFS/<path:subpath>", methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD"])
def debrecen_gtfs_short(subpath: str):
    return _proxy_to(_join_url(DKV_BASE, f"mobilapp/GTFS/{subpath}"))


# ============================================================
# MISKOLC / MVK
# ============================================================
@app.route("/miskolc/GTFS/<path:subpath>", methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD"])
def miskolc_gtfs(subpath: str):
    return _proxy_to(_join_url(MVK_MOBIL_BASE, f"GTFS/{subpath}"))


@app.route("/miskolc/php/<path:subpath>", methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD"])
def miskolc_valos_php(subpath: str):
    return _proxy_to(_join_url(MVK_VALOS_BASE, f"php/{subpath}"), allow_cache=False)


# ============================================================
# SZÓFIA
# ============================================================
# A webapp websocketet használ. Normál Flask HTTP proxy nem tud websocketet átlátszóan továbbítani.
# Ez információs endpoint; ha HTTP végpontot is használsz Szófiához, ide lehet bekötni.
@app.get("/szofia/ws-info")
@app.get("/szófia/ws-info")
def szofia_ws_info():
    return jsonify({
        "ok": True,
        "note": "A szófiai forrás websocket: wss://api.livetransport.eu/sofia. Ezt a böngészőben közvetlenül vagy külön websocket proxyval kell kezelni.",
        "websocket_url": "wss://api.livetransport.eu/sofia",
    })


@app.route("/szofia/http/<path:subpath>", methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD"])
@app.route("/szófia/http/<path:subpath>", methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD"])
def szofia_http(subpath: str):
    return _proxy_to(_join_url(SOFIA_HTTP_BASE, subpath), allow_cache=False)


# ============================================================
# Debug / cache
# ============================================================
@app.get("/debug/cache")
def debug_cache():
    now = time.time()
    items = []
    for k, v in list(_CACHE.items())[:50]:
        items.append({"key": k[:16], "age": round(now - v.ts, 3), "status": v.status, "bytes": len(v.body)})
    return jsonify({"ok": True, "count": len(_CACHE), "items": items})


@app.post("/debug/cache/clear")
def clear_cache():
    _CACHE.clear()
    return jsonify({"ok": True, "cleared": True})


if __name__ == "__main__":
    _ensure_szeged_scanner_started()
    app.run(host=HOST, port=PORT, debug=False, threaded=True)
