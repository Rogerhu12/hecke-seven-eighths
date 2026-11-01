#!/usr/bin/env python3
"""Diagnostic-only GDB parent/Lean child sampler; never acceptance evidence.

Invoke under `lake env python3 ... --input COPY.lean --output /tmp/UNIQUE
--evidence DIR`. No attachment to an existing process, installation, privilege
change, target-function call, kernel bypass, or Lean heartbeat/async override.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import selectors
import shutil
import signal
import subprocess
import sys
import time


READY_MARKER = "A2_D_LITERAL_F499_DIAGNOSTIC AFTER_ORIGINAL_IMPORTS"
MARKER_PREFIX = "A2_D_LITERAL_F499_DIAGNOSTIC "
EXPECTED_ORIGINAL_SHA256 = "f49992a4d96d0e86c404cb0e0138d613d30100b8405e1964b9258349ad4daee0"
EXPECTED_INPUT_SHA256 = "681461a728f500718a1557fe523721a1dd91d6645d95509d21946c7af76ccd4e"
LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
SAMPLE_OFFSETS = (60.0, 100.0)
HARD_SECONDS = 150.0
READY_SECONDS = 60.0
COMMAND_SECONDS = 6.0
CLEANUP_SECONDS = 10.0
ABORT_REQUESTED = False


class DiagnosticError(RuntimeError):
    pass


def request_abort(signum, _frame):
    global ABORT_REQUESTED
    ABORT_REQUESTED = True


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def proc_identity(pid: int) -> dict | None:
    """Read identity only; never read environment, memory, or unrelated PIDs."""
    try:
        root = Path("/proc") / str(pid)
        stat = (root / "stat").read_text()
        fields = stat.rsplit(")", 1)[1].split()
        return {
            "pid": pid, "state": fields[0], "ppid": int(fields[1]),
            "start_ticks": fields[19], "uid": root.stat().st_uid,
            "executable": str((root / "exe").resolve()),
        }
    except (OSError, ValueError, IndexError):
        return None


def same_live_identity(now: dict | None, owned: dict | None) -> bool:
    return bool(now and owned and now["state"] != "Z"
                and all(now[k] == owned[k] for k in ("pid", "uid", "start_ticks")))


def stream_text(line: str) -> str:
    if line[:1] in {"~", "@", "&"} and line[1:2] == '"':
        try:
            value = ast.literal_eval(line[1:])
            return value if isinstance(value, str) else line
        except (SyntaxError, ValueError):
            return line
    return line


def parse_exit_code(value: str | None) -> int | None:
    if value is None:
        return None
    try:
        return int(value, 8 if re.fullmatch(r"0[0-7]+", value) else 0)
    except ValueError:
        try:
            return int(value, 10)
        except ValueError:
            return None


class MIDriver:
    def __init__(self, argv: list[str], evidence: Path, started: float):
        self.started = started
        self.deadline = started + HARD_SECONDS
        self.evidence = evidence
        child_env = os.environ.copy()
        child_env["DEBUGINFOD_URLS"] = ""
        self.proc = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT, bufsize=0, env=child_env)
        assert self.proc.stdin is not None and self.proc.stdout is not None
        os.set_blocking(self.proc.stdout.fileno(), False)
        self.selector = selectors.DefaultSelector()
        self.selector.register(self.proc.stdout, selectors.EVENT_READ)
        self.raw_log = (evidence / "gdb-mi.log").open("wb")
        self.buffer = b""
        self.token = 0
        self.results: dict[str, str] = {}
        self.console: list[str] = []
        self.phase_markers: list[dict] = []
        self.ready_at: float | None = None
        self.running = False
        self.stop_serial = 0
        self.last_stop: str | None = None
        self.inferior_exited = False
        self.exit_code_raw: str | None = None
        self.exit_code: int | None = None
        self.exit_signal: str | None = None
        self.owned_inferior: dict | None = None
        self.cleanup_mode = False
        self.cleanup_log: list[dict] = []

    def elapsed(self) -> float:
        return time.monotonic() - self.started

    def consume(self, line: str) -> None:
        text = stream_text(line)
        self.console.append(text)
        for part in text.splitlines():
            if part.strip() == READY_MARKER and self.ready_at is None:
                self.ready_at = time.monotonic()
            if part.startswith(MARKER_PREFIX):
                self.phase_markers.append({"elapsed_seconds": self.elapsed(), "text": part})
        result = re.match(r"^(\d+)\^(.*)$", line)
        if result:
            self.results[result[1]] = result[2]
        if line.startswith("=thread-group-started,"):
            match = re.search(r'(?:^|,)pid="(\d+)"', line)
            if match:
                identity = proc_identity(int(match[1]))
                if identity is not None:
                    if identity["ppid"] != self.proc.pid or identity["uid"] != os.getuid():
                        raise DiagnosticError("GDB inferior is not this GDB's same-user direct child")
                    if self.owned_inferior and identity["pid"] != self.owned_inferior["pid"]:
                        raise DiagnosticError("Unexpected second inferior; refusing broader process sampling")
                    self.owned_inferior = identity
                    (self.evidence / "owned-processes.json").write_text(json.dumps({
                        "gdb_pid": self.proc.pid, "inferior": identity,
                        "scope": "Only this newly launched diagnostic process",
                    }, indent=2) + "\n")
        if line.startswith("*running,"):
            self.running = True
        if line.startswith("*stopped,"):
            self.running = False
            self.stop_serial += 1
            self.last_stop = line
            if 'reason="exited-normally"' in line:
                self.inferior_exited = True
                self.exit_code = 0
            elif 'reason="exited"' in line or 'reason="exited-signalled"' in line:
                self.inferior_exited = True
            match = re.search(r'(?:^|,)signal-name="([^"]+)"', line)
            if match and self.inferior_exited:
                self.exit_signal = match[1]
        if line.startswith("=thread-group-exited,"):
            self.inferior_exited = True
            self.running = False
        if self.inferior_exited:
            match = re.search(r'(?:^|,)exit-code="([^"]+)"', line)
            if match:
                self.exit_code_raw = match[1]
                self.exit_code = parse_exit_code(match[1])

    def pump(self, seconds: float = 0.2) -> None:
        if not self.cleanup_mode:
            if ABORT_REQUESTED:
                raise DiagnosticError("Diagnostic supervisor received a termination signal")
            if time.monotonic() >= self.deadline:
                raise DiagnosticError("Diagnostic hard wall deadline reached")
        for key, _ in self.selector.select(max(0.0, min(seconds, 0.2))):
            chunk = os.read(key.fd, 65536)
            if not chunk:
                self.selector.unregister(key.fileobj)
                if self.buffer:
                    self.consume(self.buffer.decode("utf-8", "replace"))
                    self.buffer = b""
                continue
            self.raw_log.write(chunk)
            self.raw_log.flush()
            self.buffer += chunk
            while b"\n" in self.buffer:
                line, self.buffer = self.buffer.split(b"\n", 1)
                self.consume(line.rstrip(b"\r").decode("utf-8", "replace"))

    def request(self, command: str, seconds: float = COMMAND_SECONDS,
                allowed: tuple[str, ...] = ("done",)) -> str:
        self.token += 1
        token = str(self.token)
        payload = (token + command + "\n").encode()
        self.raw_log.write(b">>> " + payload)
        self.raw_log.flush()
        assert self.proc.stdin is not None
        self.proc.stdin.write(payload)
        self.proc.stdin.flush()
        deadline = time.monotonic() + seconds
        while token not in self.results:
            if time.monotonic() >= deadline:
                raise DiagnosticError("GDB MI command timed out: " + command.split()[0])
            if self.proc.poll() is not None:
                raise DiagnosticError("GDB exited before replying to MI command")
            self.pump()
        result = self.results.pop(token)
        if result.split(",", 1)[0] not in allowed:
            raise DiagnosticError("GDB MI rejected " + command.split()[0] + ": " + result)
        return result

    def wait_stopped(self, previous: int, seconds: float = COMMAND_SECONDS) -> None:
        deadline = time.monotonic() + seconds
        while self.stop_serial <= previous and not self.inferior_exited:
            if time.monotonic() >= deadline:
                raise DiagnosticError("GDB did not report the requested inferior stop")
            self.pump()

    def snapshot(self, number: int, lean_binary: Path) -> dict:
        identity = proc_identity(self.owned_inferior["pid"]) if self.owned_inferior else None
        if not same_live_identity(identity, self.owned_inferior):
            raise DiagnosticError("No live owned Lean inferior available to sample")
        assert identity is not None
        if identity["ppid"] != self.proc.pid or Path(identity["executable"]) != lean_binary:
            raise DiagnosticError("Inferior identity or actual compiler executable changed")
        previous = self.stop_serial
        self.request("-exec-interrupt --all")
        self.wait_stopped(previous)
        if self.inferior_exited:
            raise DiagnosticError("Inferior exited before requested stack snapshot")
        mark = len(self.console)
        self.request('-interpreter-exec console "thread apply all bt 256"', seconds=12.0)
        stack = "\n".join(self.console[mark:]) + "\n"
        stack_path = self.evidence / f"stack-{number:02d}.txt"
        stack_path.write_text(stack)
        result = {
            "number": number,
            "elapsed_seconds": self.elapsed(),
            "seconds_after_imports_ready": time.monotonic() - self.ready_at if self.ready_at else None,
            "owned_inferior_pid": identity["pid"],
            "gdb_stop_record": self.last_stop,
            "stack_file": stack_path.name,
            "last_observed_phase_marker": self.phase_markers[-1] if self.phase_markers else None,
            "scope": "Momentary all-thread stack; no theorem completion inference",
        }
        self.request("-exec-continue --all", allowed=("running", "done"))
        return result

    def cleanup(self) -> bool:
        """Bounded cleanup; signals are restricted to the PID/start identity we created."""
        self.cleanup_mode = True
        end = time.monotonic() + CLEANUP_SECONDS
        if self.proc.poll() is None and not self.inferior_exited:
            try:
                if self.running:
                    previous = self.stop_serial
                    self.request("-exec-interrupt --all", seconds=1.0)
                    self.wait_stopped(previous, seconds=1.0)
                self.request('-interpreter-exec console "kill"', seconds=1.5)
                self.cleanup_log.append({"action": "kill_own_inferior_through_gdb", "ok": True})
            except (DiagnosticError, OSError, BrokenPipeError) as exc:
                self.cleanup_log.append({"action": "gdb_cleanup", "error": str(exc)})
        if self.owned_inferior:
            now = proc_identity(self.owned_inferior["pid"])
            if same_live_identity(now, self.owned_inferior):
                try:
                    os.kill(self.owned_inferior["pid"], signal.SIGKILL)
                    self.cleanup_log.append({"action": "kill_verified_owned_pid", "ok": True})
                except ProcessLookupError:
                    pass
                except OSError as exc:
                    self.cleanup_log.append({"action": "kill_verified_owned_pid", "error": str(exc)})
        if self.proc.poll() is None:
            try:
                self.request("-gdb-exit", seconds=1.5, allowed=("exit",))
            except (DiagnosticError, OSError, BrokenPipeError):
                pass
        if self.proc.poll() is None:
            self.proc.terminate()
            try:
                self.proc.wait(timeout=max(0.1, min(1.5, end - time.monotonic())))
            except subprocess.TimeoutExpired:
                self.proc.kill()
                self.proc.wait(timeout=1.5)
        # Give the debugger/init a brief chance to reap a terminated inferior.
        while self.owned_inferior and time.monotonic() < end:
            if not same_live_identity(proc_identity(self.owned_inferior["pid"]), self.owned_inferior):
                break
            time.sleep(0.05)
        remaining = bool(self.owned_inferior and same_live_identity(
            proc_identity(self.owned_inferior["pid"]), self.owned_inferior))
        self.selector.close()
        self.raw_log.close()
        return self.proc.poll() is not None and not remaining


def metadata_command(argv: list[str]) -> str:
    result = subprocess.run(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, timeout=6, check=True)
    return result.stdout.strip()


def run(args: argparse.Namespace) -> int:
    started = time.monotonic()
    evidence = args.evidence.resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    result = {
        "scope": "Diagnostic-only GDB parent / new Lean child; never original native acceptance",
        "complete_target_module_compiled": False,
        "complete_module_within_five_minutes": False,
        "acceptance_evidence": False,
        "default_lean_async_preserved": True,
        "heartbeat_override": None,
        "profiler_override": None,
        "stderr_option_override": False,
        "stack_frame_limit_per_thread": 256,
        "stack_command_timeout_seconds": 12.0,
        "original_module_acceptance": False,
        "full_task_acceptance": False,
        "compiler_outputs_can_be_restored_as_project_cache": False,
        "sample_offsets_after_imports_seconds": list(SAMPLE_OFFSETS),
        "maximum_main_seconds": HARD_SECONDS,
        "maximum_cleanup_seconds": CLEANUP_SECONDS,
        "snapshots": [],
        "attached_existing_process": False,
        "privilege_or_security_settings_changed": False,
    }
    driver: MIDriver | None = None
    source: Path | None = None
    exit_status = 4
    try:
        gdb = shutil.which("gdb")
        if gdb is None:
            result["status"] = "missing_gdb"
            raise DiagnosticError("gdb is unavailable; no installation or privilege fallback is attempted")
        scope_path = Path("/proc/sys/kernel/yama/ptrace_scope")
        scope = scope_path.read_text().strip() if scope_path.exists() else None
        result["observed_ptrace_scope"] = scope
        if scope in {"2", "3"}:
            result["status"] = "unprivileged_ptrace_unavailable"
            raise DiagnosticError("Host policy disallows this unprivileged debugger launch; policy is unchanged")
        if os.environ.get("LEAN_NUM_THREADS") != "2":
            raise DiagnosticError("LEAN_NUM_THREADS must already equal 2 in the inherited Lake environment")
        source = args.input.resolve(strict=True)
        if sha256(source) != EXPECTED_INPUT_SHA256:
            raise DiagnosticError("Input is not the frozen full D f499 source plus 46 reversible markers")
        original = Path("HeckeSkeleton/Moments/MOM_ENGINE_STEP/OrdinaryLiteralExceptionalLeaf.lean")
        if sha256(original) != EXPECTED_ORIGINAL_SHA256:
            raise DiagnosticError("Checkout D literal source differs from the frozen f499 source")
        result["original_source_sha256"] = sha256(original)
        output = args.output.resolve()
        if source.suffix != ".lean" or not output.is_relative_to(Path("/tmp")):
            raise DiagnosticError("Input must be a Lean file and compiler output must be in a unique /tmp directory")
        output.mkdir(parents=True, exist_ok=True)
        olean, ilean = output / (source.stem + ".olean"), output / (source.stem + ".ilean")
        if olean.exists() or ilean.exists():
            raise DiagnosticError("Refusing to overwrite previous compiler outputs")
        prefix = Path(metadata_command(["lean", "--print-prefix"]))
        lean_binary = (prefix / "bin/lean").resolve(strict=True)
        version = metadata_command([str(lean_binary), "--version"])
        if "4.35.0-rc3" not in version or LEAN_COMMIT not in version:
            raise DiagnosticError("Resolved compiler does not match the pinned Lean version and commit")
        gdb_version = metadata_command([gdb, "--version"]).splitlines()[0]
        native_args = [str(lean_binary), "-j2", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                       "-DstderrAsMessages=false",
                       "-o", str(olean), "-i", str(ilean), str(source)]
        command = [gdb, "--quiet", "--nx", "--interpreter=mi2", "--args", *native_args]
        result.update({
            "gdb_version": gdb_version, "lean_version": version,
            "lean_binary": str(lean_binary), "lean_binary_sha256": sha256(lean_binary),
            "input_path": str(source), "input_sha256_before": sha256(source),
            "compiler_output_directory": str(output), "command": command,
            "environment_dumped": False,
        })
        driver = MIDriver(command, evidence, started)
        for setting in ["pagination off", "confirm off", "debuginfod enabled off", "mi-async on", "startup-with-shell off",
                        "disable-randomization off", "print frame-arguments none"]:
            driver.request("-gdb-set " + setting)
        driver.request("-exec-run", allowed=("running", "done"))
        ready_deadline = min(driver.deadline, time.monotonic() + READY_SECONDS)
        while driver.ready_at is None and not driver.inferior_exited:
            if time.monotonic() >= ready_deadline:
                raise DiagnosticError("Imports-ready marker was not observed within 60 seconds")
            driver.pump()
        if driver.inferior_exited:
            result["status"] = "inferior_exited_before_requested_samples"
            exit_status = 3
        else:
            assert driver.ready_at is not None
            result["imports_ready_elapsed_seconds"] = driver.ready_at - started
            for number, offset in enumerate(SAMPLE_OFFSETS, 1):
                due = driver.ready_at + offset
                while time.monotonic() < due and not driver.inferior_exited:
                    driver.pump()
                if driver.inferior_exited:
                    result["status"] = "inferior_exited_before_requested_samples"
                    exit_status = 3
                    break
                result["snapshots"].append(driver.snapshot(number, lean_binary))
                (evidence / f"snapshot-{number:02d}.json").write_text(
                    json.dumps(result["snapshots"][-1], indent=2) + "\n")
            else:
                result["status"] = "two_snapshots_collected_diagnostic_will_be_terminated"
                exit_status = 0
        result["input_sha256_after"] = sha256(source)
        if result["input_sha256_after"] != result["input_sha256_before"]:
            raise DiagnosticError("The diagnostic input file changed during sampling")
    except (DiagnosticError, OSError, ValueError, subprocess.SubprocessError) as exc:
        result.setdefault("status", "diagnostic_error")
        result["error"] = str(exc)
        exit_status = 2 if driver is None else 4
    finally:
        if source is not None and "input_sha256_before" in result:
            try:
                result["input_sha256_after"] = sha256(source)
                result["diagnostic_input_unchanged"] = (
                    result["input_sha256_after"] == result["input_sha256_before"])
            except OSError:
                result["diagnostic_input_unchanged"] = False
            if not result["diagnostic_input_unchanged"]:
                exit_status = 4
                result["status"] = "diagnostic_input_changed"
        if driver is not None:
            result["inferior_exit_code_before_cleanup"] = driver.exit_code
            result["inferior_exit_code_raw_before_cleanup"] = driver.exit_code_raw
            result["inferior_exit_signal_before_cleanup"] = driver.exit_signal
            result["last_stop_before_cleanup"] = driver.last_stop
            result["phase_markers"] = driver.phase_markers
            result["owned_inferior"] = driver.owned_inferior
            try:
                cleaned = driver.cleanup()
            except Exception as exc:
                cleaned = False
                result["cleanup_exception"] = str(exc)
            result["cleanup_complete"] = cleaned
            result["cleanup_actions"] = driver.cleanup_log
            result["gdb_exit_code"] = driver.proc.poll()
            if not cleaned:
                exit_status = 5
                result["status"] = "diagnostic_cleanup_failed"
        else:
            result["cleanup_complete"] = True
        result["elapsed_seconds"] = time.monotonic() - started
        result["snapshot_count"] = len(result["snapshots"])
        result["driver_exit_code"] = exit_status
        (evidence / "stack-result.json").write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps(result), flush=True)
    return exit_status


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--evidence", required=True, type=Path)
    args = parser.parse_args()
    signal.signal(signal.SIGTERM, request_abort)
    signal.signal(signal.SIGINT, request_abort)
    return run(args)


if __name__ == "__main__":
    raise SystemExit(main())
