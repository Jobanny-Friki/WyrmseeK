#!/usr/bin/python
"""
+------------+
|  LINDWYRM  |
+------------+

"Here be dragons. Handled."
"""

import json
import logging
import logging.handlers
import os
import subprocess
import zlib
from bisect import bisect_right
from collections import OrderedDict
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
from contextlib import suppress
from fnmatch import fnmatch
from functools import lru_cache
from heapq import heappush, heappushpop
from select import select
from shlex import split as shlex_split
from shutil import which
from signal import SIGINT, SIGTERM, signal
from sys import intern
from threading import Lock
from time import time
from typing import Any, NamedTuple
from urllib.parse import quote_from_bytes

import dbus.service
from dbus.mainloop.glib import DBusGMainLoop
from gi.repository import Gio, GLib  # type: ignore[missing-module-attribute]

try:
	import tomllib
except ModuleNotFoundError:
	import tomli as tomllib


logger = logging.getLogger("lindwyrm")
logger.setLevel(logging.INFO)

try:
    addr = next(p for p in ("/dev/log", "/var/run/syslog") if os.path.exists(p))
    handler = logging.handlers.SysLogHandler(addr)
    fmt = 'lindwyrm[%(process)d]: %(levelname)s - %(message)s'
except (OSError, FileNotFoundError, StopIteration):
    handler = logging.StreamHandler()
    fmt = '%(asctime)s - lindwyrm - %(levelname)s - %(message)s'

handler.setFormatter(logging.Formatter(fmt))
logger.addHandler(handler)

def read_config(path: str) -> dict[str, Any]:
	try:
		fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
		st = os.fstat(fd)
		if (st.st_mode & 0o777) not in (0o400, 0o600) or st.st_uid != os.getuid():
			os.close(fd)
			logger.warning(f"Config file has incorrect permissions or ownership: {path}")
			return {}

		with os.fdopen(fd, "rb") as f:
			data = tomllib.load(f)

		return {**data, **data.get("settings", {})}
	except (OSError, ValueError, tomllib.TOMLDecodeError):
		logger.exception(f"Failed to load config from {path}")
		return {}


DBUS_BUSNAME = "org.kde.lindwyrm"
PROG_DIRNAME = "lindwyrm"
IFACE_KRUNNER = "org.kde.krunner1"

CONFIG_FILE = os.path.join(GLib.get_user_config_dir(), PROG_DIRNAME, "config.toml")
CACHE_FILE = os.path.join(GLib.get_user_cache_dir(), PROG_DIRNAME, "cache.json.zlib")
_GLOBAL_CFG = read_config(CONFIG_FILE)

CACHE_MED = int(_GLOBAL_CFG.get("cache_med", 4096))
CACHE_BIG = int(_GLOBAL_CFG.get("cache_big", 8192))

IO_CHUNK_SIZE = 131072
MAX_TOTAL_RESULTS = 800

ICON_UNKNOWN = intern("unknown")
TYPE_FILE = intern("FILE")
TYPE_FOLDER = intern("FOLDER")
TYPE_OCTET = intern("OCTET-STREAM")

MIME_URI = "text/uri-list"
MIME_TEXT = "text/plain"
MAGICMIME = False

with suppress(ModuleNotFoundError):
	from magic import from_file as magic_from_file
	MAGICMIME = True

CLIPBOARD_PROVIDERS = {
	MIME_URI: [
		("wl-copy", "--type", MIME_URI),
		("xclip", "-selection", "clipboard", "-t", MIME_URI),
	],
	MIME_TEXT: [
		("wl-copy",),
		("xclip", "-selection", "clipboard", "-in"),
		("xsel", "--clipboard", "--input"),
	],
}


class LightResult(NamedTuple):
	path: str
	icon: str
	subtext: str
	score: float


class RelevanceWeights(NamedTuple):
	half_life: float
	mod_time: float
	depth: float
	exec_bonus: float
	dir_bonus: float


def intern_pair(a: str, b: str) -> tuple[str, str]:
	return intern(a), intern(b)


def validate_str(text: str | bytes) -> str | None:
	if isinstance(text, bytes):
		try:
			text = os.fsdecode(text)
		except (UnicodeDecodeError, ValueError):
			return None

	return None if "\x00" in text else text


def _find_command(*candidates: str) -> str | None:
	for cmd in candidates:
		if found := which(cmd):
			return found

	return None


def _spawn(cmd: list[str]) -> None:
	with suppress(OSError, subprocess.SubprocessError):
		subprocess.Popen(
			cmd,
			stdout=subprocess.DEVNULL,
			stderr=subprocess.DEVNULL,
			stdin=subprocess.DEVNULL,
			start_new_session=True,
		)


def _run_subprocess_input(cmd: list[str], text_input: str) -> bool:
	try:
		subprocess.run(
			cmd,
			input=text_input.encode("utf-8", errors="surrogateescape"),
			check=True,
			capture_output=True,
			timeout=2,
		)
		return True
	except (subprocess.TimeoutExpired, subprocess.CalledProcessError, OSError, UnicodeEncodeError):
		return False


_TIME_TH = [60, 3600, 86400, 604800, 2629746, 31556952]
_TIME_UN = ["minute", "hour", "day", "week", "month", "year"]
_SIZE_TH = [1, 1024, 1048576, 1073741824, 1099511627776]
_SIZE_UN = ["B", "KiB", "MiB", "GiB", "TiB"]


def human_readable_size(size: int) -> str:
	if size == 0:
		return "0 B"

	idx = bisect_right(_SIZE_TH, size) - 1
	return f"{size / _SIZE_TH[idx]:.1f} {_SIZE_UN[idx]}"


def human_readable_time(mtime: float | None, now: float) -> str:
	if mtime is None:
		return ""

	if (d := max(0, now - mtime)) < 60:
		return "Just now"

	idx = bisect_right(_TIME_TH, d) - 1
	return f"{(v := d / _TIME_TH[idx]):.1f} {_TIME_UN[idx]}{'s' * (v >= 2)} ago"


@lru_cache(maxsize=CACHE_BIG)
def get_raw_stat(path: str) -> tuple[bool, float | None, int, int]:
	try:
		stat_info = os.stat(path, follow_symlinks=True)
		return ((stat_info.st_mode & 0o170000) == 0o040000, stat_info.st_mtime, stat_info.st_size, stat_info.st_mode)
	except (FileNotFoundError, PermissionError, OSError, ValueError):
		return False, None, 0, 0


@lru_cache(maxsize=CACHE_MED)
def get_display_metadata(path: str) -> tuple[str, str]:
	is_dir, mtime, size, _ = get_raw_stat(path)
	if mtime is None and size == 0:
		return "", ""

	return ("" if is_dir else human_readable_size(size), human_readable_time(mtime, time()))


@lru_cache(maxsize=CACHE_BIG)
def cached_magic_mime(path: str) -> tuple[str, str]:
	try:
		mime = magic_from_file(path, mime=True)
		return intern_pair(mime.replace("/", "-"), mime)
	except (OSError, ValueError):
		return intern_pair(ICON_UNKNOWN, TYPE_FILE)


@lru_cache(maxsize=CACHE_MED)
def get_icon_for_extension(filename: str) -> tuple[str, str]:
	try:
		guessed, _ = Gio.content_type_guess(filename, None)
		if guessed == "application/octet-stream" and "." in filename:
			_, ext = os.path.splitext(filename)
			return intern_pair(ICON_UNKNOWN, ext[1:].upper() or TYPE_OCTET)

		icon_theme = Gio.content_type_get_icon(guessed)
		name = icon_theme.get_names()[0] if (icon_theme and icon_theme.get_names()) else ICON_UNKNOWN
		return intern_pair(name, guessed)
	except (GLib.GError, TypeError, AttributeError):
		return intern_pair(ICON_UNKNOWN, TYPE_FILE)


@lru_cache(maxsize=CACHE_MED)
def get_icon_and_subtext(path: str) -> tuple[str, str]:
	is_dir, _, _, _ = get_raw_stat(path)
	nice_size, nice_date = get_display_metadata(path)
	if is_dir:
		subtext = f"{TYPE_FOLDER} * {nice_date}" if nice_date else TYPE_FOLDER
		return intern_pair("folder", subtext)

	icon, type_str = get_icon_for_extension(os.path.basename(path))
	if type_str == TYPE_OCTET and MAGICMIME:
		m_icon, m_type = cached_magic_mime(path)
		if m_icon != ICON_UNKNOWN:
			icon, type_str = m_icon, m_type

	parts = [type_str.split("/")[-1].upper()]
	parts.extend(filter(None, [nice_size, nice_date]))
	return icon, " * ".join(parts)


class RelevanceScorer:
	def __init__(self, rules: tuple, weights: RelevanceWeights) -> None:
		self.rules = rules
		self.w = weights
		self.mod_time_half_life = max(1.0, weights.half_life) * 86400.0

	def calculate(self, path: str, path_lower: str, words: tuple[str, ...], now: float) -> float:
		is_dir, mtime, size, mode = get_raw_stat(path)
		if not is_dir and size == 0:
			return 0.0

		score = 0.0
		if self.rules:
			for patterns, action in self.rules:
				if any(fnmatch(path_lower, p) for p in patterns):
					score += action

		score -= min(path.count("/"), 12) * self.w.depth
		name_lower = os.path.basename(path_lower)
		n = max(1, len(name_lower))
		if matches := [
			1.75 * 2.7183 ** (-0.8 * (i / n)) * ((len(w) / n) ** 0.7) for w in words if 1 + (i := name_lower.find(w))
		]:
			score += max(matches) + (m := len(matches)) * 0.7 / (m + 2.5)

		if is_dir:
			score += self.w.dir_bonus
		else:
			if mode & 0o111:
				score += self.w.exec_bonus

			if mtime and mtime <= now:
				logit = max(0.0, now - mtime) / self.mod_time_half_life
				if logit < 7:
					score += self.w.mod_time if logit <= 0.001 else self.w.mod_time * 2.7183 ** (-logit)

		if score <= -7:
			return 0.0

		if score >= 7:
			return 1.0

		return 1.0 / (1.0 + 2.7183 ** (-score))


_CATEG_TH = [5, 20, 40, 60, 85]
_CATEG_MR = [0, 10, 30, 50, 70, 100]


def build_dbus_response(results: list[LightResult]) -> list:
	return [
		(
			r.path,
			x[:n] or x if 1 + (n := (x := os.path.basename(r.path)).rfind(".")) else x,
			r.icon,
			_CATEG_MR[bisect_right(_CATEG_TH, r.score * 100)],
			r.score,
			{"subtext": r.subtext},
		)
		for r in results[:MAX_TOTAL_RESULTS]
	]


class Runner(dbus.service.Object):
	def __init__(self) -> None:
		super().__init__(dbus.service.BusName(DBUS_BUSNAME, dbus.SessionBus()), "/runner")
		self.cfg = _GLOBAL_CFG

		def get_val(key: str, default: Any, type_fn: Callable = str) -> Any:
			try:
				return type_fn(self.cfg.get(key, default))
			except (TypeError, ValueError):
				return default

		def get_cmd_list(key: str, default: list[str]) -> list[str]:
			val = self.cfg.get(key)
			if val is None:
				return [found] if (found := _find_command(*default)) else []

			return val if isinstance(val, list) else shlex_split(str(val))

		self.binary = _find_command(get_val("binary", "plocate"), "locate") or ""

		opts = self.cfg.get("opts", "-i")
		self.opts = tuple(opts if isinstance(opts, list) else shlex_split(str(opts)))
		if not any(x in self.opts for x in ("-l", "--limit")):
			self.opts += ("-l", "200")

		self.opener = get_cmd_list("opener", ["mimeo", "handlr", "xdg-open"])
		self.clipboard_cmd = get_cmd_list("clipboard_cmd", [])
		self.min_len = max(1, get_val("min_len", 2, int))
		self.debounce_ms = get_val("debounce_ms", 180, int)
		self.process_timeout = get_val("process_timeout", 6.0, float)
		self.max_cached = get_val("history_size", 800, int)

		logger.info(f"Runner initialized - binary: {self.binary}, min_len: {self.min_len}, debounce: {self.debounce_ms}ms")

		weights = RelevanceWeights(
			half_life=get_val("mod_time_half_life_days", 30.0, float),
			mod_time=get_val("mod_time_weight", 0.60, float),
			depth=get_val("depth_penalty", 0.015, float),
			exec_bonus=get_val("executable_bonus", 0.18, float),
			dir_bonus=get_val("directory_bonus", 0.35, float),
		)

		self.scorer = RelevanceScorer(self._parse_rules(), weights)
		self.search_results = self._load_cache()
		self._current_query_norm: str | None = None
		self._query_lock = Lock()
		self.executor = ThreadPoolExecutor(max_workers=1)
		self._debounce_timer = None

	def _parse_rules(self) -> tuple:
		rules = []
		for item in self.cfg.get("rules", []):
			if not isinstance(item, dict):
				continue

			p = item.get("patterns")
			s = item.get("score")
			if p is None or s is None:
				continue

			pat = [p] if isinstance(p, str) else p
			try:
				rules.append((tuple(intern(x.strip().lower()) for x in pat), float(s)))
			except (ValueError, TypeError):
				continue

		logger.debug(f"Parsed {len(rules)} scoring rules from configuration")
		return tuple(rules)

	def _load_cache(self) -> OrderedDict:
		try:
			fd = os.open(CACHE_FILE, os.O_RDONLY | os.O_NOFOLLOW)
			st = os.fstat(fd)
			if (st.st_mode & 0o777) != 0o600 or st.st_uid != os.getuid():
				os.close(fd)
				logger.warning("Cache file has incorrect permissions or ownership")
				return OrderedDict()

			with os.fdopen(fd, "rb") as f:
				raw = json.loads(zlib.decompress(f.read()))

			validated = OrderedDict()
			for k, v in raw.items():
				if isinstance(k, str) and isinstance(v, list):
					items = [LightResult(p, i, t, float(s)) for p, i, t, s in v if isinstance(p, str)]
					if items:
						validated[k] = tuple(items)

			while len(validated) > self.max_cached:
				validated.popitem(last=False)

			logger.info(f"Cache loaded successfully with {len(validated)} entries")
			return validated
		except (FileNotFoundError, json.JSONDecodeError, zlib.error, OSError, ValueError):
			logger.exception("Failed to load cache")
			return OrderedDict()

	def save_cache(self) -> None:
		try:
			serializable = {
				k: [(r.path, r.icon, r.subtext, r.score) for r in v] for k, v in self.search_results.items()
			}
			os.makedirs(os.path.dirname(CACHE_FILE), mode=0o700, exist_ok=True)
			fd = os.open(CACHE_FILE, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
			with os.fdopen(fd, "wb") as f:
				f.write(zlib.compress(json.dumps(serializable, ensure_ascii=False).encode("utf-8"), level=6))
			logger.info(f"Cache saved successfully with {len(self.search_results)} entries")
		except (OSError, ValueError):
			logger.exception("Cache save failed")

	def _is_query_stale(self, query: str) -> bool:
		with self._query_lock:
			return self._current_query_norm != query

	def _run_locate_job(self, norm_query: str, words: tuple[str, ...]) -> None:
		if self._is_query_stale(norm_query) or not self.binary:
			return

		proc = None
		try:
			proc = subprocess.Popen(
				[self.binary, *self.opts, *words],
				stdout=subprocess.PIPE,
				stderr=subprocess.DEVNULL,
				bufsize=IO_CHUNK_SIZE,
				start_new_session=True,
			)
			fd = proc.stdout.fileno()
			os.set_blocking(fd, False)
			top_k_heap, now, paths_seen, read_buffer = [], time(), 0, b""
			start_time = now
			while True:
				if self._is_query_stale(norm_query) or (time() - start_time > self.process_timeout):
					break

				ready, _, _ = select([fd], [], [], 0.05)
				if fd in ready:
					chunk = proc.stdout.read(IO_CHUNK_SIZE)
					if not chunk:
						break

					read_buffer += chunk
					while b"\n" in read_buffer:
						line_bytes, read_buffer = read_buffer.split(b"\n", 1)
						if not (path := validate_str(line_bytes)):
							continue

						paths_seen += 1
						if paths_seen > MAX_TOTAL_RESULTS * 3:
							read_buffer = b""
							break

						score = self.scorer.calculate(path, path.lower(), words, now)
						if score <= 0.01:
							continue

						entry = (score, path)
						if len(top_k_heap) < MAX_TOTAL_RESULTS:
							heappush(top_k_heap, entry)
						elif score > top_k_heap[0][0]:
							heappushpop(top_k_heap, entry)

					if paths_seen > MAX_TOTAL_RESULTS * 3:
						break
				elif proc.poll() is not None:
					break
		except (OSError, subprocess.SubprocessError):
			pass
		finally:
			if proc:
				with suppress(Exception):
					if proc.poll() is None:
						proc.terminate()
						try:
							proc.wait(timeout=1.0)
						except subprocess.TimeoutExpired:
							proc.kill()
							with suppress(subprocess.TimeoutExpired):
								proc.wait(timeout=2.0)

					if proc.stdout:
						proc.stdout.close()

		if not self._is_query_stale(norm_query):
			final = sorted(top_k_heap, reverse=True)
			results = tuple(LightResult(p, *get_icon_and_subtext(p), s) for s, p in final)
			GLib.idle_add(self._on_search_finished, norm_query, results)

	def _on_search_finished(self, query: str, results: tuple[LightResult, ...]) -> bool:
		if not self._is_query_stale(query):
			self.search_results[query] = results
			if len(self.search_results) > self.max_cached:
				self.search_results.popitem(last=False)

		return False

	@dbus.service.method(IFACE_KRUNNER, in_signature="s", out_signature="a(sssida{sv})")
	def Match(self, query: str) -> list:
		stripped = query.strip()
		if len(stripped) < self.min_len:
			return []

		try:
			words = tuple(w.lower() for w in shlex_split(stripped))
			norm = " ".join(words)
		except (ValueError, AttributeError):
			norm = " ".join(words := tuple(stripped.lower().split()))

		if norm in self.search_results:
			self.search_results.move_to_end(norm)
			return build_dbus_response(list(self.search_results[norm]))

		if self._debounce_timer:
			GLib.source_remove(self._debounce_timer)

		with self._query_lock:
			self._current_query_norm = norm

		self._debounce_timer = GLib.timeout_add(self.debounce_ms, self._debounce_callback, norm, words)
		for key, res in reversed(self.search_results.items()):
			is_safe_prefix = norm.startswith(key) and len(key) >= max(2, len(norm) - 6)
			if is_safe_prefix and len(res) < MAX_TOTAL_RESULTS:
				filtered = [r for r in res if all(w in r.path.lower() for w in words)]
				return build_dbus_response(filtered)

		return []

	def _debounce_callback(self, norm: str, words: tuple) -> bool:
		self._debounce_timer = None
		self.executor.submit(self._run_locate_job, norm, words)
		return False

	@dbus.service.method(IFACE_KRUNNER, out_signature="a(sss)")
	def Actions(self) -> list:
		return [
			("open", "Open File", "document-open"),
			("parent", "Open Parent Folder", "inode-directory"),
			("copy", "Copy Path", "edit-copy"),
			("copy-uri", "Copy File (Paste Ready)", "edit-copy-path"),
		]

	@dbus.service.method(IFACE_KRUNNER, in_signature="ss")
	def Run(self, data: str, action_id: str) -> None:
		if not (safe_path := validate_str(os.path.realpath(data))):
			logger.warning(f"Invalid path received in Run: {data}")
			return

		action = action_id or "open"
		logger.info(f"Running action '{action}' on path: {safe_path}")
		if action == "open" and self.opener:
			_spawn([*self.opener, safe_path])
		elif action == "parent" and self.opener:
			_spawn([*self.opener, os.path.dirname(safe_path)])
		elif action == "copy":
			self._exec_clipboard(safe_path, MIME_TEXT)
		elif action == "copy-uri":
			self._exec_clipboard("file://" + quote_from_bytes(os.fsencode(safe_path)) + "\r\n", MIME_URI)

	def _exec_clipboard(self, data: str, mime: str) -> bool:
		if not validate_str(data):
			logger.warning("Invalid data for clipboard operation")
			return False

		if mime == MIME_TEXT and self.clipboard_cmd and _run_subprocess_input(self.clipboard_cmd, data[:8192]):
			return True

		success = any(
			which(cmd[0]) and _run_subprocess_input(list(cmd), data[:8192]) for cmd in CLIPBOARD_PROVIDERS.get(mime, [])
		)
		if not success:
			logger.warning(f"Clipboard operation failed for mime type: {mime}")
		return success


if __name__ == "__main__":
	logger.info("Starting Lindwyrm runner")
	DBusGMainLoop(set_as_default=True)
	runner = Runner()
	loop = GLib.MainLoop()

	def quit_handler(*_: Any) -> None:
		logger.info("Received shutdown signal, saving cache and exiting")
		runner.save_cache()
		loop.quit()

	signal(SIGINT, quit_handler)
	signal(SIGTERM, quit_handler)
	with suppress(KeyboardInterrupt):
		loop.run()
