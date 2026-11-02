#!/usr/bin/env python3
"""Compile every V2 module and audit each group whose proofs are complete.

The skeleton permits proof placeholders only in groups marked unproved.
Lake is the build authority; the fresh Lean audit checks every loaded V2
declaration, including private and generated declarations, recursively.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import signal
import subprocess
import sys
import threading
import time

ROOT = Path.cwd()
TASK = ROOT / "HeckeSkeleton/Moments/MOM_ENGINE_STEP_V2"
EVIDENCE = ROOT / "v2-build"
PREFIX = "HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2"
NAMESPACE = "HeckeSkeleton.Moments.EngineStepV2"
ALLOWED = ["propext", "Classical.choice", "Quot.sound"]
MODULE_TIMEOUT_SECONDS = 600
WATCH_INTERVAL_SECONDS = 15
WATCHDOG_RESULTS: dict[str, dict] = {}
TASK_BRANCH_PREFIX = "cloud/mom-v2-"
BASE_BRANCH = "cloud/mom-engine-step-v2"


def code_only(text: str) -> str:
    result = []
    depth = 0
    quoted = False
    i = 0
    while i < len(text):
        char, pair = text[i], text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                result.append("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                result.append("  ")
                i += 2
            else:
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif quoted:
            if char == "\\" and i + 1 < len(text):
                result.append("  ")
                i += 2
            else:
                if char == '"':
                    quoted = False
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            result.append("  ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            result.append(" " * (end - i))
            i = end
        else:
            quoted = char == '"'
            result.append(" " if quoted else char)
            i += 1
    return "".join(result)


def lean_processes(root_pid: int) -> list[dict]:
    """Read only Lean descendants of the current Lake/audit command."""
    completed = subprocess.run(
        ["ps", "-ww", "-eo", "pid=,ppid=,etimes=,rss=,args="],
        capture_output=True, text=True, check=True, timeout=5)
    rows = []
    parents = {}
    for line in completed.stdout.splitlines():
        parts = line.split(None, 4)
        if len(parts) != 5:
            continue
        pid, parent, elapsed, rss = map(int, parts[:4])
        parents[pid] = parent
        rows.append((pid, elapsed, rss, parts[4]))

    def descendant(pid: int) -> bool:
        seen = set()
        while pid not in seen:
            if pid == root_pid:
                return True
            seen.add(pid)
            if pid not in parents:
                return False
            pid = parents[pid]
        return False

    found = []
    for pid, elapsed, rss, command in rows:
        if not descendant(pid):
            continue
        try:
            argv = shlex.split(command)
        except ValueError:
            continue
        if not argv or Path(argv[0]).name != "lean":
            continue
        filename = next((arg for arg in argv[1:] if arg.endswith(".lean")), None)
        if filename is None:
            continue
        path = Path(filename).absolute()
        try:
            filename = str(path.relative_to(ROOT))
        except ValueError:
            filename = str(path)
        module = (filename[:-5].replace("/", ".")
                  if filename.startswith("HeckeSkeleton/") else filename)
        found.append({"pid": pid, "source": filename, "module": module,
                      "elapsed_seconds": elapsed, "rss_kib": rss})
    return found


class Watcher(threading.Thread):
    """Adapt the probe Watcher's process monitoring, without changing sources."""
    def __init__(self, root_pid: int, stage: str):
        super().__init__(daemon=True)
        self.root_pid = root_pid
        self.stage = stage
        self.done = threading.Event()
        self.max_elapsed: dict[str, int] = {}
        self.max_rss: dict[str, int] = {}
        self.killed: list[dict] = []
        self.errors: list[str] = []
        self.snapshot_path = EVIDENCE / (Path(stage).stem + "_watchdog.json")
        self.log_path = EVIDENCE / (Path(stage).stem + "_watchdog.log")

    def report(self) -> dict:
        return {"limit_seconds": MODULE_TIMEOUT_SECONDS,
                "poll_seconds": WATCH_INTERVAL_SECONDS,
                "max_elapsed_seconds": self.max_elapsed,
                "max_rss_kib": self.max_rss,
                "killed": self.killed, "monitor_errors": self.errors}

    def run(self):
        # A thread exception must be visible to the main gate, even if opening
        # or writing the monitor's own evidence file is what failed.
        try:
            self.monitor()
        except Exception as error:
            message = f"{type(error).__name__}: {error}"
            self.errors.append(message)
            print(f"V2_WATCHDOG_ERROR {self.stage}: {message}", flush=True)

    def monitor(self):
        last_status = 0.0
        killed_pids = set()
        with self.log_path.open("w", encoding="utf-8") as log:
            while not self.done.is_set():
                try:
                    processes = lean_processes(self.root_pid)
                    for process in processes:
                        name = process["source"]
                        elapsed = process["elapsed_seconds"]
                        self.max_elapsed[name] = max(self.max_elapsed.get(name, 0), elapsed)
                        self.max_rss[name] = max(self.max_rss.get(name, 0), process["rss_kib"])
                        if elapsed <= MODULE_TIMEOUT_SECONDS or process["pid"] in killed_pids:
                            continue
                        # Recheck ownership and the source immediately before signalling.
                        current = next((item for item in lean_processes(self.root_pid)
                                        if item["pid"] == process["pid"] and
                                        item["source"] == name and
                                        item["elapsed_seconds"] >= elapsed), None)
                        if current is None:
                            continue
                        try:
                            os.kill(current["pid"], signal.SIGKILL)
                        except ProcessLookupError:
                            continue
                        killed_pids.add(current["pid"])
                        self.killed.append(current)
                        message = (f"V2_MODULE_TIMEOUT {current['module']} "
                                   f"pid={current['pid']} elapsed={current['elapsed_seconds']}s "
                                   f"limit={MODULE_TIMEOUT_SECONDS}s stage={self.stage}")
                        print(message, flush=True)
                        log.write(message + "\n")
                    if time.monotonic() - last_status >= 60:
                        last_status = time.monotonic()
                        active = "; ".join(
                            f"{item['module']} {item['elapsed_seconds']}s "
                            f"{item['rss_kib'] // 1024}MiB"
                            for item in sorted(processes,
                                               key=lambda item: -item["elapsed_seconds"]))
                        message = f"V2_WATCHDOG_ACTIVE {self.stage}: {active or 'no Lean process'}"
                        print(message, flush=True)
                        log.write(message + "\n")
                    self.snapshot_path.write_text(json.dumps(self.report(), indent=2) + "\n")
                    log.flush()
                except (OSError, subprocess.SubprocessError, ValueError) as error:
                    message = f"{type(error).__name__}: {error}"
                    self.errors.append(message)
                    print(f"V2_WATCHDOG_ERROR {self.stage}: {message}", flush=True)
                    log.write(message + "\n")
                    log.flush()
                self.done.wait(WATCH_INTERVAL_SECONDS)


def logged(command: list[str], name: str) -> int:
    print("$ " + " ".join(command), flush=True)
    with (EVIDENCE / name).open("w", encoding="utf-8") as log:
        with subprocess.Popen(command, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True,
                              encoding="utf-8", errors="replace") as process:
            watcher = Watcher(process.pid, name)
            watcher.start()
            try:
                assert process.stdout is not None
                show_block = False
                for line in process.stdout:
                    log.write(line)
                    log.flush()
                    if line.startswith(("⚠", "✔", "✖", "ℹ")):
                        show_block = "MOM_ENGINE_STEP_V2" in line or line.startswith("✖")
                    if (name != "build.log" or show_block or "MOM_ENGINE_STEP_V2" in line or
                            line.startswith(("error:", "✖", "Build completed", "Some required"))):
                        print(line, end="", flush=True)
                code = process.wait()
            finally:
                watcher.done.set()
                watcher.join()
                WATCHDOG_RESULTS[name] = watcher.report()
                watcher.snapshot_path.write_text(json.dumps(watcher.report(), indent=2) + "\n")
            # A killed module or failed monitor must never produce a green gate.
            return 124 if watcher.killed or watcher.errors else code


def task_targets(names: list[str]) -> list[str] | None:
    """The V2 modules a task branch changed relative to the v2 base, or None."""
    head = os.environ.get("GITHUB_HEAD_REF") or os.environ.get("GITHUB_REF_NAME", "")
    if not head.startswith(TASK_BRANCH_PREFIX):
        return None
    try:
        for ref, local in ((BASE_BRANCH, "v2-base"), (head, "task-head")):
            subprocess.run(["git", "fetch", "--no-tags", "--quiet", "--depth=400", "origin",
                            f"+refs/heads/{ref}:refs/remotes/origin/{local}"], check=True)
        base = subprocess.check_output(["git", "merge-base", "HEAD", "origin/v2-base"],
                                       text=True).strip()
        changed = subprocess.check_output(
            ["git", "diff", "--name-only", base, "HEAD", "--", str(TASK.relative_to(ROOT))],
            text=True).split()
    except (OSError, subprocess.SubprocessError) as error:
        print(f"V2_SCOPE_FALLBACK full build ({type(error).__name__}: {error})", flush=True)
        return None
    targets = sorted(({Path(f).stem for f in changed if f.endswith(".lean")} & set(names))
                     - {"Interface"})
    print(f"V2_SCOPE task branch {head}: base {base[:12]}, targets {targets}", flush=True)
    return targets or None


TASK_AUDIT = """
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[MODULES]
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    match env.getModuleIdxFor? name with
    | some idx =>
      if targets.contains (env.header.moduleNames[idx.toNat]!) then names := names.push name
    | none => pure ()
  unless !names.isEmpty do
    throwError "No declarations found in the task modules"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut bad : Nat := 0
  for name in names.qsort Name.lt do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      bad := bad + 1
      logInfo m!"V2_TASK_EXTRA_AXIOMS {name}: {extra}"
  if bad == 0 then
    logInfo m!"V2_TASK_AXIOMS_PASSED: {names.size} declarations"
  else
    throwError "{bad} task declarations use axioms beyond the standard three (sorryAx means an unfinished proof)"
"""


def scoped_audit(targets: list[str]) -> dict:
    """Audit the axioms of exactly the declarations defined in the target modules."""
    imports = "".join(f"import {PREFIX}.{name}\n" for name in targets)
    modules = ", ".join(f"`{PREFIX}.{name}" for name in targets)
    audit_path = EVIDENCE / "task_AxiomAudit.lean"
    audit_path.write_text(imports + TASK_AUDIT.replace("MODULES", modules), encoding="utf-8")
    code = logged(["lake", "env", "lean", str(audit_path)], "task_axioms.log")
    output = (EVIDENCE / "task_axioms.log").read_text()
    return {"exit_code": code, "success_marker": "V2_TASK_AXIOMS_PASSED:" in output}


def main() -> int:
    EVIDENCE.mkdir(exist_ok=True)
    manifest_path = ROOT / ".github/v2/manifest.json"
    files = sorted(TASK.glob("*.lean"))
    names = [path.stem for path in files]
    manifest = (json.loads(manifest_path.read_text()) if manifest_path.exists()
                else {"groups": [{"id": "skeleton", "proved": False, "modules": names}]})
    groups = manifest["groups"]
    listed = [name for group in groups for name in group["modules"]]
    if sorted(listed) != names or len(listed) != len(set(listed)):
        raise SystemExit("The group manifest must cover every V2 module exactly once")
    if any(len(group["modules"]) > 100 for group in groups):
        raise SystemExit("Each group must have at most 100 modules")
    snapshots = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                 for path in files}
    bad = []
    for group in groups:
        pattern = r"\b(?:axiom|native_decide|admit|sorryAx)\b"
        if group["proved"]:
            pattern = r"\b(?:axiom|native_decide|admit|sorryAx|sorry)\b"
        for module in group["modules"]:
            path = TASK / (module + ".lean")
            if re.search(pattern, code_only(path.read_text())):
                bad.append(str(path.relative_to(ROOT)))
    if bad:
        raise SystemExit("Forbidden proof tokens: " + ", ".join(bad))
    environment = {
        "head": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "manifest": manifest,
        "source_sha256": snapshots,
        "allowed_axioms": ALLOWED,
        "module_timeout_seconds": MODULE_TIMEOUT_SECONDS,
        "watch_interval_seconds": WATCH_INTERVAL_SECONDS,
    }
    (EVIDENCE / "environment.json").write_text(json.dumps(environment, indent=2) + "\n")
    targets = task_targets(names)
    environment["task_targets"] = targets
    (EVIDENCE / "environment.json").write_text(json.dumps(environment, indent=2) + "\n")
    start = time.monotonic()
    build_exit = logged(["lake", "build", *("+" + PREFIX + "." + name + ":olean"
                                          for name in (targets or names))], "build.log")
    results = {"build_exit": build_exit, "module_count": len(targets or names),
               "task_targets": targets,
               "elapsed_seconds": time.monotonic() - start, "group_audits": {},
               "watchdogs": WATCHDOG_RESULTS}
    if build_exit == 0 and targets:
        results["group_audits"]["task"] = scoped_audit(targets)
    elif build_exit == 0:
        for group in groups:
            if not group["proved"]:
                continue
            group_id = group["id"]
            if not re.fullmatch(r"[a-z0-9_]+", group_id):
                raise SystemExit("Invalid group identifier")
            audit = "\n".join("import " + PREFIX + "." + name for name in group["modules"])
            audit += """
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let nsPrefix : Name := `HeckeSkeleton.Moments.EngineStepV2
  let names := (env.constants.toList.filterMap fun (name, _) =>
    if nsPrefix.isPrefixOf (privateToUserName name) then some name else none).toArray.qsort Name.lt
  unless !names.isEmpty do
    throwError "No V2 declarations found"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"AXIOMS {name}: {dependencies}"
  logInfo m!"V2_GROUP_AXIOMS_PASSED: {names.size} declarations"
"""
            audit_path = EVIDENCE / (group_id + "_AxiomAudit.lean")
            audit_path.write_text(audit)
            code = logged(["lake", "env", "lean", str(audit_path)], group_id + "_axioms.log")
            output = (EVIDENCE / (group_id + "_axioms.log")).read_text()
            results["group_audits"][group_id] = {
                "exit_code": code,
                "success_marker": "V2_GROUP_AXIOMS_PASSED:" in output,
            }
    for path, digest in snapshots.items():
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != digest:
            raise SystemExit("Source changed during verification: " + path)
    results["elapsed_seconds"] = time.monotonic() - start
    (EVIDENCE / "result.json").write_text(json.dumps(results, indent=2) + "\n")
    success = build_exit == 0 and all(
        result["exit_code"] == 0 and result["success_marker"]
        for result in results["group_audits"].values())
    summary = ("# MOM_ENGINE_STEP_V2\n\n"
               + f"- Exact head: `{environment['head']}`\n"
               + (f"- Task branch scope: {', '.join(targets)}\n" if targets else "")
               + f"- V2 modules built: {len(targets or names)}\n"
               + f"- Lake exit: {build_exit}\n"
               + f"- Per-module Lean timeout: {MODULE_TIMEOUT_SECONDS}s\n"
               + f"- Modules terminated: {sum(len(item['killed']) for item in WATCHDOG_RESULTS.values())}\n"
               + f"- Proved groups audited: {', '.join(results['group_audits']) or 'none (skeleton)'}\n"
               + f"- Result: {'PASS' if success else 'FAIL'}\n")
    (EVIDENCE / "summary.md").write_text(summary)
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as stream:
            stream.write(summary)
    print(summary, flush=True)
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())

