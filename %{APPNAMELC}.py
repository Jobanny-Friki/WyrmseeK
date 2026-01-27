#!/usr/bin/python

import os
import re
import select
import subprocess
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor
from contextlib import suppress
from fnmatch import fnmatch
from functools import lru_cache
from operator import itemgetter
from shlex import split as shlex_split
from shutil import which
from signal import SIG_DFL, SIGINT, signal
from sys import intern
from threading import Lock
from time import time
from typing import Any, NamedTuple
from urllib.parse import quote_from_bytes

try:
	import tomllib
except ModuleNotFoundError:
	import tomli as tomllib

import dbus.service
from dbus.mainloop.glib import DBusGMainLoop
from gi.repository import Gio, GLib  # type: ignore[missing-module-attribute]

MAX_TOTAL_RESULTS = 500
MAX_PARTIAL_RESULTS = 200
IFACE_KRUNNER = "org.kde.krunner1"
ICON_UNKNOWN = intern("unknown")
TYPE_FILE = intern("FILE")
TYPE_FOLDER = intern("FOLDER")
TYPE_OCTET = intern("OCTET-STREAM")
IO_CHUNK_SIZE = 65536
MIME_URI = "text/uri-list"
MIME_TEXT = "text/plain"
CONFIG_DIR = GLib.get_user_config_dir()
CONFIG_FILE = os.path.join(CONFIG_DIR, "locate-krunner", "config.toml")

try:
	from magic import from_file as magic_from_file

	MAGICMIME = True
except ModuleNotFoundError:
	MAGICMIME = False


def read_config(path: str) -> dict[str, Any]:
	try:
		with open(path, "rb") as f:
			data = tomllib.load(f)

		settings = data.get("settings", {})
		if isinstance(settings, dict):
			data.update(settings)

		return data
	except (FileNotFoundError, PermissionError, tomllib.TOMLDecodeError, OSError, ValueError):
		return {}


_GLOBAL_CFG = read_config(CONFIG_FILE)
CACHE_BIG = int(_GLOBAL_CFG.get("cache_big", 4096))
CACHE_MED = int(_GLOBAL_CFG.get("cache_med", 2048))


class LightResult(NamedTuple):
	path: str
	icon: str
	score: float
	subtext: str


def intern_pair(a: str, b: str) -> tuple[str, str]:
	return intern(a), intern(b)


def human_readable_size(size: int) -> str:
	if size == 0:
		return "0 B"

	for unit in ['B', 'KB', 'MB', 'GB']:
		if size < 1024.0:
			return f"{size:.1f} {unit}"

		size /= 1024.0

	return f"{size:.1f} TB"


def human_readable_time(mtime: float | None, now: float) -> str:
	if not mtime:
		return ""

	diff = now - mtime
	if diff < 0:
		return ""

	intervals = [
		(60, "Just now"),
		(3600, "min"),
		(86400, "hr"),
		(604800, "days"),
		(2629746, "weeks"),
		(31556952, "months"),
		(float('inf'), "years"),
	]

	prev_limit = 1
	for limit, unit in intervals:
		if diff < limit:
			return unit if unit == "Just now" else f"{int(diff // prev_limit)} {unit} ago"

		prev_limit = limit

	return "Old"


def _spawn(cmd: list[str]) -> None:
	with suppress(OSError, subprocess.SubprocessError):
		subprocess.Popen(
			cmd,
			stdout=subprocess.DEVNULL,
			stderr=subprocess.DEVNULL,
			start_new_session=True,
		)


def _find_command(*candidates: str) -> str | None:
	for cmd in candidates:
		if found := which(cmd):
			return found

	return None


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


@lru_cache(maxsize=CACHE_BIG)
def cached_path_metadata(path: str) -> tuple[bool, float | None, int, int, str, str]:
	try:
		stat_info = os.stat(path, follow_symlinks=True)
		is_dir = (stat_info.st_mode & 0o170000) == 0o040000
		now = time()
		nice_size = "" if is_dir else human_readable_size(stat_info.st_size)
		nice_date = human_readable_time(stat_info.st_mtime, now)
		return is_dir, stat_info.st_mtime, stat_info.st_size, stat_info.st_mode, nice_size, nice_date
	except (FileNotFoundError, PermissionError, OSError, ValueError):
		return False, None, 0, 0, "", ""


@lru_cache(maxsize=CACHE_BIG)
def cached_magic_mime(path: str) -> tuple[str, str]:
	try:
		mime_type = magic_from_file(path, mime=True)
		return intern_pair(mime_type.replace("/", "-"), mime_type)
	except (PermissionError, OSError, FileNotFoundError, ValueError, TypeError, AttributeError):
		return intern_pair(ICON_UNKNOWN, TYPE_FILE)


@lru_cache(maxsize=CACHE_MED)
def get_icon_for_extension(filename: str) -> tuple[str, str]:
	try:
		guessed_type, _ = Gio.content_type_guess(filename, None)
		if guessed_type == "application/octet-stream" and "." in filename:
			_, ext = os.path.splitext(filename)
			return intern_pair(ICON_UNKNOWN, ext[1:].upper() or TYPE_OCTET)

		icon_theme = Gio.content_type_get_icon(guessed_type)
		icon_name = icon_theme.get_names()[0] if (icon_theme and icon_theme.get_names()) else ICON_UNKNOWN
		return intern_pair(icon_name, guessed_type)
	except (TypeError, AttributeError, ValueError, IndexError):
		return intern_pair(ICON_UNKNOWN, TYPE_FILE)


@lru_cache(maxsize=CACHE_MED)
def get_icon_and_subtext(path: str) -> tuple[str, str]:
	is_dir, _, _, _, nice_size, nice_date = cached_path_metadata(path)
	if is_dir:
		subtext = f"{TYPE_FOLDER} • {nice_date}" if (nice_date and nice_date != "Old") else TYPE_FOLDER
		return intern_pair("folder", subtext)

	icon, type_str = get_icon_for_extension(os.path.basename(path))
	if type_str == TYPE_OCTET and MAGICMIME:
		magic_icon, magic_type = cached_magic_mime(path)
		if magic_icon != ICON_UNKNOWN:
			icon, type_str = magic_icon, magic_type

	parts = [type_str.split("/")[-1].upper()]
	if nice_size:
		parts.append(nice_size)

	if nice_date and nice_date != "Old":
		parts.append(nice_date)

	return icon, " • ".join(parts)


class RelevanceScorer:
	def __init__(
		self,
		rules: tuple,
		half_life_days: float,
		mod_time_weight: float,
		depth_penalty: float,
		exec_bonus: float,
		dir_bonus: float,
		sigmoid_steepness: float,
	) -> None:
		self.rules = rules
		self.mod_time_half_life = max(1.0, half_life_days) * 86400.0
		self.mod_time_weight = mod_time_weight
		self.depth_penalty = depth_penalty
		self.exec_bonus = exec_bonus
		self.dir_bonus = dir_bonus
		self.sigmoid_steepness = sigmoid_steepness

	def calculate(self, path: str, path_lower: str, words: tuple[str, ...], now: float) -> float:
		is_dir, mtime, size, mode, _, _ = cached_path_metadata(path)
		if not is_dir and size == 0:
			return 0.0

		score = 0.0
		if self.rules:
			for patterns, action in self.rules:
				for p in patterns:
					if fnmatch(path_lower, p):
						score += action

		score -= min(path.count("/"), 12) * self.depth_penalty
		name_lower = os.path.basename(path_lower)
		name_len = max(1, len(name_lower))
		match_sum = 0.0
		for w in words:
			idx = name_lower.find(w)
			if idx != -1:
				pos_factor = 1.0 if idx == 0 else (1.0 - (idx / name_len))
				match_sum += (pos_factor * 0.6) + ((len(w) / name_len) * 0.3)

		if match_sum > 0:
			score += match_sum * 3.0 + len(words) * 0.1

		if is_dir:
			score += self.dir_bonus
		else:
			if mode & 0o111:
				score += self.exec_bonus

			if mtime and mtime <= now:
				logit = max(0.0, now - mtime) / self.mod_time_half_life
				if logit < 9.2:
					bonus = self.mod_time_weight if logit <= 0.001 else self.mod_time_weight * 2.7183 ** (-logit)
					score += bonus

		logit = score * self.sigmoid_steepness
		if logit <= -8.8:
			return 0.0

		if logit >= 8.8:
			return 1.0

		return 1.0 / (1.0 + 2.718281828459045 ** (-logit))

	def quick_score(self, path: str, words: tuple[str, ...]) -> float:
		path_lower = path.lower()
		score = sum(1.0 for w in words if w in path_lower)
		return max(0.0, score - path.count("/") * 0.01) if score else 0.0


def build_dbus_response(results: list[LightResult]) -> list:
	return [(r.path, os.path.basename(r.path), r.icon, 100, r.score, {"subtext": r.subtext}) for r in results[:MAX_TOTAL_RESULTS]]


@lru_cache(maxsize=CACHE_MED)
def _compile_filter_regex(words: tuple[str, ...]) -> re.Pattern | None:
	try:
		pattern_str = "".join(f"(?=.*{re.escape(w)})" for w in words)
		return re.compile(pattern_str, re.IGNORECASE)
	except re.error:
		return None


def filter_existing_results(results: tuple[LightResult, ...], words: tuple[str, ...]) -> list:
	if not words:
		return build_dbus_response(list(results))

	regex = _compile_filter_regex(words)
	filtered = [r for r in results if regex.search(r.path)] if regex else [r for r in results if all(w in r.path.lower() for w in words)]
	return build_dbus_response(filtered)


def normalize_and_parse(query: str) -> tuple[str, tuple[str, ...]]:
	words = tuple(w.lower() for w in shlex_split(query))
	return " ".join(words), words


def parse_rules(config: dict) -> tuple:
	rules_list = config.get("rules", [])
	if not isinstance(rules_list, list):
		return ()

	parsed = []
	for item in rules_list:
		if not isinstance(item, dict):
			continue

		patterns = item.get("patterns")
		score = item.get("score")
		if patterns is None or score is None:
			continue

		if isinstance(patterns, str):
			patterns = [patterns]

		pat_tuple = tuple(intern(p.strip().lower()) for p in patterns)
		try:
			parsed.append((pat_tuple, float(score)))
		except (ValueError, TypeError):
			continue

	return tuple(parsed)


class Runner(dbus.service.Object):
	def __init__(self) -> None:
		super().__init__(dbus.service.BusName("org.kde.locate", dbus.SessionBus()), "/runner")
		cfg = _GLOBAL_CFG

		def _get_list(key: str, defaults: list[str]) -> list[str]:
			val = cfg.get(key)
			if val is None:
				found = _find_command(*defaults)
				return [found] if found else []

			return val if isinstance(val, list) else shlex_split(str(val))

		self.binary = _find_command(str(cfg.get("binary") or "plocate"), "locate") or ""
		opts = cfg.get("opts", "-i -l 25")
		self.opts = tuple(opts if isinstance(opts, list) else shlex_split(str(opts)))
		if not any(x in self.opts for x in ("-l", "--limit")):
			self.opts += ("-l", "25")

		self.opener = _get_list("opener", ["mimeo", "handlr", "xdg-open"])
		self.clipboard_cmd = _get_list("clipboard_cmd", [])
		self.min_len = max(1, int(cfg.get("min_len", 3)))
		self.debounce_ms = int(cfg.get("debounce_ms", 250))
		self.process_timeout = float(cfg.get("process_timeout", 2.5))
		self.max_cached_queries = int(cfg.get("history_size", 500))
		self.scorer = RelevanceScorer(
			rules=parse_rules(cfg),
			half_life_days=float(cfg.get("mod_time_half_life_days", 20.0)),
			mod_time_weight=float(cfg.get("mod_time_weight", 0.25)),
			depth_penalty=float(cfg.get("depth_penalty", 0.02)),
			exec_bonus=float(cfg.get("executable_bonus", 0.1)),
			dir_bonus=float(cfg.get("directory_bonus", 0.2)),
			sigmoid_steepness=float(cfg.get("sigmoid_steepness", 3.0)),
		)
		self.search_results = OrderedDict()
		self._current_query_norm: str | None = None
		self._query_lock = Lock()
		self.executor = ThreadPoolExecutor(max_workers=1)
		self._debounce_timer = None

	@dbus.service.signal(IFACE_KRUNNER, signature="sa(sssida{sv})")
	def MatchesChanged(self, query: str, results: list) -> None:
		pass

	def _is_query_stale(self, query: str) -> bool:
		with self._query_lock:
			return self._current_query_norm != query

	def _hydrated_results(self, raw_candidates: list[tuple[str, float]]) -> list[LightResult]:
		hydrated = []
		for path, score in raw_candidates:
			icon, subtext = get_icon_and_subtext(path)
			hydrated.append(LightResult(path, icon, score, subtext))

		return hydrated

	def _run_locate_job(self, norm_query: str, words: tuple[str, ...]) -> None:
		if self._is_query_stale(norm_query) or not self.binary:
			return

		cmd = [self.binary, *self.opts, "--", *words]
		proc = None
		try:
			proc = subprocess.Popen(
				cmd,
				stdout=subprocess.PIPE,
				stderr=subprocess.DEVNULL,
				bufsize=IO_CHUNK_SIZE,
				start_new_session=True,
			)

			fd = proc.stdout.fileno()
			os.set_blocking(fd, False)

			raw_results = []
			start_time = time()
			now = time()
			paths_seen = total_processed = 0
			last_emitted_count = 0

			read_buffer = b""

			while True:
				if self._is_query_stale(norm_query):
					proc.terminate()
					return

				if time() - start_time > self.process_timeout:
					proc.terminate()
					break

				ready, _, _ = select.select([fd], [], [], 0.05)

				if fd in ready:
					chunk = proc.stdout.read(IO_CHUNK_SIZE)
					if not chunk:
						break

					read_buffer += chunk

					while b"\n" in read_buffer:
						line_bytes, read_buffer = read_buffer.split(b"\n", 1)

						try:
							raw = os.fsdecode(line_bytes)
							if "\x00" in raw:
								continue
							path = raw
						except (UnicodeDecodeError, ValueError):
							continue

						paths_seen += 1
						if paths_seen > MAX_TOTAL_RESULTS * 2:
							read_buffer = b""
							proc.terminate()
							break

						if paths_seen > 100 and len(raw_results) >= MAX_PARTIAL_RESULTS and self.scorer.quick_score(path, words) < 0.3:
							continue

						path_lower = path.lower()
						score = self.scorer.calculate(path, path_lower, words, now)
						if score > 0.01:
							raw_results.append((path, score))
							total_processed += 1
							if total_processed % 50 == 0 and total_processed <= MAX_PARTIAL_RESULTS and not self._is_query_stale(norm_query):
								raw_results.sort(key=itemgetter(1), reverse=True)
								partial_view = raw_results[:MAX_PARTIAL_RESULTS]
								final_objs = self._hydrated_results(partial_view)
								last_emitted_count = len(final_objs)
								GLib.idle_add(self.MatchesChanged, norm_query, build_dbus_response(final_objs))

				elif proc.poll() is not None:
					break

				if paths_seen > MAX_TOTAL_RESULTS * 2:
					break

		except (OSError, subprocess.SubprocessError, ValueError, UnicodeError):
			return
		finally:
			if proc:
				with suppress(Exception):
					if proc.poll() is None:
						proc.terminate()
						try:
							proc.wait(timeout=1.0)
						except subprocess.TimeoutExpired:
							proc.kill()
							proc.wait()
					proc.stdout.close()

		if self._is_query_stale(norm_query):
			return

		raw_results.sort(key=itemgetter(1), reverse=True)
		top_raw = raw_results[:MAX_TOTAL_RESULTS]
		final_results = tuple(self._hydrated_results(top_raw))

		GLib.idle_add(self._on_search_finished, norm_query, final_results, last_emitted_count)

	def _on_search_finished(self, query: str, results: tuple[LightResult, ...], last_emitted_count: int) -> bool:
		if not self._is_query_stale(query):
			self.search_results[query] = results
			if len(self.search_results) > self.max_cached_queries:
				self.search_results.popitem(last=False)

			if len(results) != last_emitted_count:
				GLib.idle_add(self.MatchesChanged, query, build_dbus_response(list(results)))

		return False

	@dbus.service.method(IFACE_KRUNNER, in_signature="s", out_signature="a(sssida{sv})")
	def Match(self, query: str):
		stripped = query.strip()
		if len(stripped) < self.min_len:
			return []

		try:
			norm, words = normalize_and_parse(stripped)
		except (ValueError, UnicodeDecodeError, UnicodeEncodeError, AttributeError):
			norm = " ".join(w.lower() for w in shlex_split(stripped))
			words = tuple(norm.split())

		if norm in self.search_results:
			self.search_results.move_to_end(norm)
			return build_dbus_response(list(self.search_results[norm]))

		if self._debounce_timer:
			GLib.source_remove(self._debounce_timer)

		with self._query_lock:
			self._current_query_norm = norm

		self._debounce_timer = GLib.timeout_add(self.debounce_ms, self._debounce_callback, norm, words)
		for key, res in reversed(self.search_results.items()):
			is_prefix = norm.startswith(key) and len(key) >= max(2, len(norm) - 4)
			is_complete_set = len(res) < MAX_TOTAL_RESULTS
			if is_prefix and is_complete_set:
				return filter_existing_results(res, words)

		return []

	def _debounce_callback(self, norm: str, words: tuple) -> bool:
		self._debounce_timer = None
		self.executor.submit(self._run_locate_job, norm, words)
		return False

	@dbus.service.method(IFACE_KRUNNER, out_signature="a(sss)")
	def Actions(self):
		return [
			("open", "Open File", "document-open"),
			("parent", "Open Parent Folder", "inode-directory"),
			("copy", "Copy Path", "edit-copy"),
			("copy-uri", "Copy File (Paste Ready)", "edit-copy-path"),
		]

	@dbus.service.method(IFACE_KRUNNER, in_signature="ss")
	def Run(self, data: str, action_id: str) -> None:
		if not data or "\x00" in data:
			return

		safe_path = os.path.normpath(data)
		if not action_id or action_id == "open":
			if self.opener:
				_spawn([*self.opener, safe_path])
		elif action_id == "parent":
			if self.opener:
				_spawn([*self.opener, os.path.dirname(safe_path)])
		elif action_id == "copy":
			self._exec_clipboard(safe_path, MIME_TEXT)
		elif action_id == "copy-uri":
			uri = "file://" + quote_from_bytes(os.fsencode(safe_path)) + "\r\n"
			self._exec_clipboard(uri, MIME_URI)

	def _exec_clipboard(self, data: str, mime_type: str) -> bool:
		if mime_type == MIME_TEXT and self.clipboard_cmd and _run_subprocess_input(self.clipboard_cmd, data):
			return True

		candidates = []
		if mime_type == MIME_URI:
			candidates.extend([("wl-copy", "--type", mime_type), ("xclip", "-selection", "clipboard", "-t", mime_type)])
		else:
			candidates.extend([("wl-copy",), ("xclip", "-selection", "clipboard", "-in"), ("xsel", "--clipboard", "--input")])

		return any(which(cmd[0]) and _run_subprocess_input(list(cmd), data) for cmd in candidates)


if __name__ == "__main__":
	DBusGMainLoop(set_as_default=True)
	signal(SIGINT, SIG_DFL)
	Runner()
	loop = GLib.MainLoop()
	with suppress(KeyboardInterrupt):
		loop.run()
