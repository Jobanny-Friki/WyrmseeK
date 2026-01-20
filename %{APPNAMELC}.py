#!/usr/bin/python
# flake8: noqa: PLR2004

"""
╔════════════╗
║  WYRMSEEK  ║
╚════════════╝

┄┄┄Overview

A lightweight, high-performance KRunner plugin that integrates
locate / plocate to provide fast file searching in KDE Plasma,
with intelligent scoring, caching, and debounced asynchronous
execution.

┄┄┄Core Features

• Uses locate / plocate for instant filesystem-wide search
• Asynchronous execution to keep KRunner responsive
• Debouncing to avoid spawning processes on every keystroke
• LRU query cache with prefix-based reuse
• Progressive result updates via MatchesChanged
• Relevance scoring based on:

  • filename matching
  • directory depth
  • modification time
  • executability
  • user-defined scoring rules

• MIME-aware icons (GIO, optional python-magic)

• Actions:

  • Open file
  • Open parent folder
  • Copy full path to clipboard

══════════════════════════════════════════════════════════════

┄┄┄Requirements

• Python 3.10+
• plocate or locate
• Python packages:

  • dbus-python
  • PyGObject
  • python-magic (optional)

══════════════════════════════════════════════════════════════

┄┄┄Configuration

Config file:

───────────────────────────────────
~/.config/locate-krunner/config.ini
───────────────────────────────────

Example:

╭───────────────────────────────────────╮
│ [Settings]                            │
│                                       │
│ binary = plocate                      │
│ cache_big = 4096                      │
│ cache_med = 2048                      │
│ clipboard_cmd = wl-copy               │
│ debounce_ms = 200                     │
│ depth_penalty = 0.02                  │
│ executable_bonus = 0.1                │
│ history_size = 500                    │
│ min_len = 3                           │
│ mod_time_half_life_days = 50          │
│ mod_time_weight = 0.3                 │
│ opener = handlr open                  │
│ opts = -i -l 25                       │
│ process_timeout = 3.0                 │
│ sigmoid_steepness = 5.0               │
│                                       │
│ scoring_rule_1 = *.mp4 | *.png :  0.2 │
│ scoring_rule_2 = */.cache/*    : -0.4 │
╰───────────────────────────────────────╯

══════════════════════════════════════════════════════════════

┄┄┄How It Works (High Level)

 1. User types a query in KRunner
 2. Query is normalized and debounced
 3. Cached results are returned immediately if available
 4. locate runs asynchronously after debounce
 5. Results are scored and sorted incrementally
 6. Partial results are emitted via MatchesChanged
 7. Final results are cached and returned

══════════════════════════════════════════════════════════════

┄┄┄DBus Interface

Implements org.kde.krunner1:

• Match(query) → results
• Actions() → open / parent / copy
• Run(data, action_id)
• MatchesChanged(query, results) for live updates

══════════════════════════════════════════════════════════════

┄┄┄Performance Notes

• Single worker thread prevents CPU saturation
• Cached filesystem metadata avoids repeated stat() calls
• Prefix-based cache reuse enables instant refinement
• Old searches are canceled cooperatively

"""

import math
import os
import re
import shutil
import signal
import subprocess
import sys
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor
from configparser import ConfigParser
from contextlib import suppress
from fnmatch import fnmatch
from functools import lru_cache
from operator import attrgetter
from shlex import split as shlex_split
from time import time as time_time
from threading import Lock as threading_Lock
from typing import NamedTuple
import dbus.service
from dbus.mainloop.glib import DBusGMainLoop
from gi.repository import Gio, GLib  # type: ignore

# Configuración de constantes y límites
MAX_TOTAL_RESULTS = 500
MAX_PARTIAL_RESULTS = 200

# Setup DBus Loop
DBusGMainLoop(set_as_default=True)

# Constantes internadas
IFACE_KRUNNER = "org.kde.krunner1"
ICON_UNKNOWN = sys.intern("unknown")
TYPE_FILE = sys.intern("FILE")
TYPE_FOLDER = sys.intern("FOLDER")
TYPE_OCTET = sys.intern("OCTET-STREAM")


def read_config(path: str) -> dict[str, str]:
	config = ConfigParser()
	if not config.read(path):
		return {}
	if "Settings" in config:
		return dict(config["Settings"])
	return dict(config["DEFAULT"])


CONFIG_DIR = GLib.get_user_config_dir()
CONFIG_FILE = os.path.join(CONFIG_DIR, "locate-krunner", "config.ini")
_GLOBAL_CFG = read_config(CONFIG_FILE)

CACHE_BIG = int(_GLOBAL_CFG.get("cache_big", "4096"))
CACHE_MED = int(_GLOBAL_CFG.get("cache_med", "2048"))

try:
	from magic import from_file as magic_from_file

	MAGICMIME = True
except ModuleNotFoundError:
	MAGICMIME = False


class LightResult(NamedTuple):
	path: str
	icon: str
	score: float
	subtext: str


# --- Helpers DRY ---


def intern_pair(a: str, b: str) -> tuple[str, str]:
	"""Helper to intern a tuple of strings."""
	return sys.intern(a), sys.intern(b)


def _spawn(cmd: list[str]) -> None:
	with suppress(OSError, subprocess.SubprocessError):
		subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)


def _find_command(*candidates: str) -> str:
	for cmd in candidates:
		if found := shutil.which(cmd):
			return found
	return candidates[-1] if candidates else ""


def _run_subprocess_input(cmd: list[str], text_input: str) -> bool:
	try:
		subprocess.run(cmd, input=text_input.encode('utf-8'), check=True, capture_output=True, timeout=2)
	except (subprocess.SubprocessError, OSError):
		return False
	else:
		return True


# --- Helpers de Metadatos e Iconos ---


@lru_cache(maxsize=CACHE_BIG)
def cached_path_metadata(path: str) -> tuple[bool, float | None, int, int]:
	try:
		stat_info = os.stat(path)
	except (OSError, FileNotFoundError):
		return False, None, 0, 0
	is_dir = (stat_info.st_mode & 0o170000) == 0o040000
	return is_dir, stat_info.st_mtime, stat_info.st_size, stat_info.st_mode


@lru_cache(maxsize=CACHE_BIG)
def cached_magic_mime(path: str) -> tuple[str, str]:
	try:
		mime_type = magic_from_file(path, mime=True)
		return intern_pair(mime_type.replace("/", "-"), mime_type.split("/")[-1].upper())
	except (OSError, ValueError, TypeError):
		return intern_pair(ICON_UNKNOWN, TYPE_FILE)


@lru_cache(maxsize=CACHE_MED)
def get_icon_for_extension(filename: str) -> tuple[str, str]:
	try:
		guessed_type, _ = Gio.content_type_guess(filename, None)
		if guessed_type == "application/octet-stream" and "." in filename:
			_, ext = os.path.splitext(filename)
			subtext = ext[1:].upper() or TYPE_OCTET
			return intern_pair(ICON_UNKNOWN, subtext)
		icon_theme = Gio.content_type_get_icon(guessed_type)
		icon_name = icon_theme.get_names()[0] if (icon_theme and icon_theme.get_names()) else ICON_UNKNOWN
		subtext = guessed_type.split("/")[-1].upper()
		return intern_pair(icon_name, subtext)
	except (TypeError, AttributeError, ValueError):
		return intern_pair(ICON_UNKNOWN, TYPE_FILE)


@lru_cache(maxsize=CACHE_MED)
def get_icon_and_subtext(path: str) -> tuple[str, str]:
	is_dir, _, _, _ = cached_path_metadata(path)
	if is_dir:
		return intern_pair("folder", TYPE_FOLDER)
	basename = os.path.basename(path)
	icon, subtext = get_icon_for_extension(basename)
	if subtext == TYPE_OCTET and MAGICMIME:
		return cached_magic_mime(path)
	return icon, subtext


# --- Lógica de Scoring ---


class RelevanceScorer:
	def __init__(
		self, rules: tuple, half_life_days: float, mod_time_weight: float, depth_penalty: float, exec_bonus: float, sigmoid_steepness: float
	) -> None:
		self.rules = rules
		self.mod_time_half_life = max(1.0, half_life_days) * 86400.0
		self.mod_time_weight = mod_time_weight
		self.depth_penalty = depth_penalty
		self.exec_bonus = exec_bonus
		self.sigmoid_steepness = sigmoid_steepness

	def _get_static_score(self, path: str, path_lower: str) -> float:
		score = 0.0
		if self.rules:
			for patterns, action in self.rules:
				for p in patterns:
					if fnmatch(path_lower, p):
						score += action
		score -= path.count(os.sep) * self.depth_penalty
		return score

	def _modification_bonus(self, mtime: float | None, now: float) -> float:
		if not mtime:
			return 0.0
		age = max(0.0, now - mtime)
		return self.mod_time_weight * math.exp(-age / self.mod_time_half_life)

	def calculate(self, path: str, path_lower: str, words: tuple[str, ...], now: float) -> float:
		is_dir, mtime, size, mode = cached_path_metadata(path)
		if not is_dir and size == 0:
			return 0.0

		score = self._get_static_score(path, path_lower)
		name_lower = os.path.basename(path_lower)
		name_len = len(name_lower)

		matches = [
			math.pow(math.exp(-2.5 * name_lower.find(w) / name_len) * math.pow(len(w) / name_len, 0.7), 1.2) * 2.0 for w in words if w in name_lower
		]
		if matches:
			score += max(matches) + math.log1p(len(matches)) * 0.20
		if not is_dir:
			if mode & 0o111:
				score += self.exec_bonus
			score += self._modification_bonus(mtime, now)

		try:
			return 1.0 / (1.0 + math.exp(-score * self.sigmoid_steepness))
		except OverflowError:
			return 1.0 if score > 0 else 0.0

	def quick_score(self, path: str, words: tuple[str, ...]) -> float:
		path_lower = path.lower()
		basename = os.path.basename(path_lower)
		score = sum(1.0 for w in words if w in basename)
		if not score:
			return 0.0
		score -= path.count(os.sep) * 0.01
		return max(0.0, score)


# --- Funciones de Utilidad ---


def build_dbus_response(results: list[LightResult]) -> list:
	return [(r.path, r.path, r.icon, 100, r.score, {"subtext": r.subtext}) for r in results[:MAX_TOTAL_RESULTS]]


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


def parse_rules(config: dict, prefix: str) -> tuple:
	rules = []
	for k, v in config.items():
		if k.startswith(prefix) and ":" in v:
			with suppress(ValueError):
				pat, sc = v.rsplit(":", 1)
				rules.append((tuple(sys.intern(p.strip().lower()) for p in pat.split("|")), float(sc.strip())))
	return tuple(rules)


# --- Clase Principal del Servicio ---


class Runner(dbus.service.Object):
	def __init__(self) -> None:
		bus_name = dbus.service.BusName("org.kde.locate", dbus.SessionBus())
		super().__init__(bus_name, "/runner")
		cfg = _GLOBAL_CFG

		# Helper to clean up config loading
		def _get_list_from_cfg(key: str, defaults: list[str]) -> list[str]:
			val = cfg.get(key)
			if val:
				return shlex_split(val)
			return [_find_command(*defaults)] if defaults else []

		self.binary = _find_command(cfg.get("binary") or "plocate", "locate")

		opts_str = cfg.get("opts", "-i -l 25")
		if "-l" not in opts_str and "--limit" not in opts_str:
			opts_str += " -l 25"
		self.opts = tuple(shlex_split(opts_str))

		self.opener = _get_list_from_cfg("opener", ["mimeo", "handlr", "xdg-open"])
		self.clipboard_cmd = _get_list_from_cfg("clipboard_cmd", [])

		self.min_len = max(1, int(cfg.get("min_len", "3")))
		self.debounce_ms = int(cfg.get("debounce_ms", "200"))
		self.process_timeout = float(cfg.get("process_timeout", "3.0"))
		self.max_cached_queries = int(cfg.get("history_size", "500"))

		self.scorer = RelevanceScorer(
			rules=parse_rules(cfg, "scoring_rule_"),
			half_life_days=float(cfg.get("mod_time_half_life_days", "50")),
			mod_time_weight=float(cfg.get("mod_time_weight", "0.3")),
			depth_penalty=float(cfg.get("depth_penalty", "0.02")),
			exec_bonus=float(cfg.get("executable_bonus", "0.1")),
			sigmoid_steepness=float(cfg.get("sigmoid_steepness", "5.0")),
		)

		self.search_results = OrderedDict()
		self._current_query_norm: str | None = None
		self._query_lock = threading_Lock()
		self.executor = ThreadPoolExecutor(max_workers=1)
		self._debounce_timer = None
		self._last_emitted_count = 0

	@dbus.service.signal(IFACE_KRUNNER, signature="sa(sssida{sv})")
	def MatchesChanged(self, query: str, results: list) -> None:
		pass

	def _is_query_stale(self, query: str) -> bool:
		"""Thread-safe check if the query has changed."""
		with self._query_lock:
			return self._current_query_norm != query

	def _run_locate_job(self, norm_query: str, words: tuple[str, ...]) -> None:
		if self._is_query_stale(norm_query):
			return

		cmd = [self.binary, *self.opts, *words]
		proc = None
		try:
			proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, bufsize=1, text=False, start_new_session=True)
			processed_results = []
			start_time = time_time()
			now = time_time()
			self._last_emitted_count = 0
			paths_seen = 0

			for i, line in enumerate(proc.stdout):
				# Verificación periódica de staleness
				if i % 10 == 0 and self._is_query_stale(norm_query):
					proc.terminate()
					return

				# Timeout duro del proceso
				if time_time() - start_time > self.process_timeout:
					proc.terminate()
					break

				try:
					raw = line.decode("utf-8", errors="surrogateescape").rstrip("\n")
					path = os.fsdecode(raw.encode('utf-8', 'surrogateescape'))
				except Exception:
					continue

				paths_seen += 1
				if paths_seen > MAX_TOTAL_RESULTS * 2:
					break

				if paths_seen > 100 and len(processed_results) >= MAX_PARTIAL_RESULTS and self.scorer.quick_score(path, words) < 0.3:
					continue

				path_lower = path.lower()
				score = self.scorer.calculate(path, path_lower, words, now)
				if score <= 0.01:
					continue

				icon, subtext = get_icon_and_subtext(path)
				processed_results.append(LightResult(path, icon, score, subtext))

				if (
					len(processed_results) > self._last_emitted_count
					and len(processed_results) <= MAX_PARTIAL_RESULTS
					and len(processed_results) % 50 == 0
					and not self._is_query_stale(norm_query)
				):
					partial = sorted(processed_results, key=attrgetter("score"), reverse=True)
					self._last_emitted_count = len(partial)
					GLib.idle_add(self.MatchesChanged, norm_query, build_dbus_response(partial))

		except Exception:
			return
		finally:
			if proc:
				with suppress(Exception):
					if proc.poll() is None:
						proc.terminate()
						proc.wait(timeout=0.2)
					proc.stdout.close()

		processed_results.sort(key=attrgetter('score'), reverse=True)
		GLib.idle_add(self._on_search_finished, norm_query, tuple(processed_results[:MAX_TOTAL_RESULTS]))

	def _on_search_finished(self, query: str, results: tuple[LightResult, ...]) -> bool:
		if not self._is_query_stale(query):
			self.search_results[query] = results
			if len(results) != self._last_emitted_count:
				GLib.idle_add(self.MatchesChanged, query, build_dbus_response(list(results)))
		return False

	@dbus.service.method(IFACE_KRUNNER, in_signature="s", out_signature="a(sssida{sv})")
	def Match(self, query: str):
		stripped = query.strip()
		if len(stripped) < self.min_len:
			return []
		
		try:
			norm, words = normalize_and_parse(stripped)
		except ValueError:
			norm = " ".join(w.lower() for w in shlex_split(stripped))
			words = tuple(norm.split())

		if norm in self.search_results:
			self.search_results.move_to_end(norm)
			return build_dbus_response(self.search_results[norm])

		if self._debounce_timer:
			GLib.source_remove(self._debounce_timer)
		with self._query_lock:
			self._current_query_norm = norm
		self._debounce_timer = GLib.timeout_add(self.debounce_ms, self._debounce_callback, norm, words)

		# Filtro de caché con lógica de longitud mejorada
		for key, res in reversed(self.search_results.items()):
			if norm.startswith(key) and len(key) >= max(2, len(norm) - 4):
				return filter_existing_results(res, words)
		return []

	def _debounce_callback(self, norm_query: str, words: tuple[str, ...]) -> bool:
		self._debounce_timer = None
		self.executor.submit(self._run_locate_job, norm_query, words)
		return False

	@dbus.service.method(IFACE_KRUNNER, out_signature="a(sss)")
	def Actions(self):
		return [("open", "Open File", "document-open"), ("parent", "Open Parent Folder", "inode-directory"), ("copy", "Copy Path", "edit-copy")]

	@dbus.service.method(IFACE_KRUNNER, in_signature="ss")
	def Run(self, data: str, action_id: str) -> None:
		if not action_id or action_id == "open":
			_spawn([*self.opener, data])
		elif action_id == "parent":
			_spawn([*self.opener, os.path.dirname(data)])
		elif action_id == "copy":
			# Try configured clipboard command first
			if self.clipboard_cmd and _run_subprocess_input(self.clipboard_cmd, data):
				return
			# Fallback commands
			fallbacks = [
				["wl-copy"],
				["xclip", "-selection", "clipboard", "-in"],
				["xsel", "--clipboard", "--input"],
			]
			for cmd in fallbacks:
				if shutil.which(cmd[0]) and _run_subprocess_input(cmd, data):
					return


if __name__ == "__main__":
	signal.signal(signal.SIGINT, signal.SIG_DFL)
	Runner()
	loop = GLib.MainLoop()
	with suppress(KeyboardInterrupt):
		loop.run()
