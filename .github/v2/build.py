#!/usr/bin/env python3
"""Compile V2 modules and audit each selected group whose proofs are complete.

The skeleton permits proof placeholders only in groups marked unproved.
Lake is the build authority; the fresh Lean audit checks every loaded V2
declaration, including private and generated declarations, recursively.
Mapped task branches default to their proved groups; other branches build all
modules. Explicit --group uses separate evidence. Task-scoped results do not
replace the shared-main or whole-project checks.
"""
from __future__ import annotations

import argparse
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
DEFAULT_EVIDENCE = ROOT / "v2-build"
EVIDENCE = DEFAULT_EVIDENCE
PREFIX = "HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2"
NAMESPACE = "HeckeSkeleton.Moments.EngineStepV2"
ALLOWED = ["propext", "Classical.choice", "Quot.sound"]
MODULE_TIMEOUT_SECONDS = 600
WATCH_INTERVAL_SECONDS = 15
WATCHDOG_RESULTS: dict[str, dict] = {}


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
    def __init__(self, root_pid: int, stage: str, evidence: Path):
        super().__init__(daemon=True)
        self.root_pid = root_pid
        self.stage = stage
        self.done = threading.Event()
        self.max_elapsed: dict[str, int] = {}
        self.max_rss: dict[str, int] = {}
        self.killed: list[dict] = []
        self.errors: list[str] = []
        self.snapshot_path = evidence / (Path(stage).stem + "_watchdog.json")
        self.log_path = evidence / (Path(stage).stem + "_watchdog.log")

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


def logged(command: list[str], name: str, evidence: Path | None = None) -> int:
    evidence = EVIDENCE if evidence is None else evidence
    print("$ " + " ".join(command), flush=True)
    with (evidence / name).open("w", encoding="utf-8") as log:
        with subprocess.Popen(command, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True,
                              encoding="utf-8", errors="replace") as process:
            watcher = Watcher(process.pid, name, evidence)
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


def current_branch() -> str:
    return (os.environ.get("GITHUB_HEAD_REF") or os.environ.get("GITHUB_REF_NAME") or
            subprocess.check_output(["git", "branch", "--show-current"], text=True).strip())


def select_scope(requested_ids: list[str], branch: str, task_branches: dict,
                 by_id: dict) -> tuple[str, list[str]]:
    if not isinstance(task_branches, dict):
        raise SystemExit("task_branches must map branch names to proved group lists")
    for task_branch, group_ids in task_branches.items():
        if (not isinstance(task_branch, str) or not task_branch.strip() or
                not isinstance(group_ids, list) or not group_ids or
                any(not isinstance(group_id, str) for group_id in group_ids) or
                len(group_ids) != len(set(group_ids)) or
                any(group_id not in by_id or not by_id[group_id]["proved"]
                    for group_id in group_ids)):
            raise SystemExit("Invalid task branch mapping: " + str(task_branch))
    if requested_ids:
        scope, selected_ids = "selected_groups", list(dict.fromkeys(requested_ids))
    elif branch != "cloud/mom-engine-step-v2" and branch in task_branches:
        scope, selected_ids = "task_branch", list(task_branches[branch])
    else:
        scope, selected_ids = "full", []
    invalid = [group_id for group_id in selected_ids
               if group_id not in by_id or not by_id[group_id]["proved"]]
    if invalid:
        raise SystemExit("Selected groups must exist and be proved: " + ", ".join(invalid))
    return scope, selected_ids


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--group", action="append", default=[], metavar="ID",
                        help="Build and audit a proved manifest group; may be repeated")
    parser.add_argument("--evidence-dir", type=Path,
                        help="Evidence directory (default: v2-build, or v2-selected-build)")
    args = parser.parse_args()
    branch = current_branch()
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
    group_ids = [group["id"] for group in groups]
    if (len(group_ids) != len(set(group_ids)) or
            any(not re.fullmatch(r"[a-z0-9_]+", group_id) for group_id in group_ids)):
        raise SystemExit("Group identifiers must be unique lowercase names")
    for group in groups:
        if not isinstance(group.get("proved"), bool):
            raise SystemExit("The proved flag must be boolean for group " + group["id"])
        required = group.get("required_declarations", [])
        if (not isinstance(required, list) or
                any(not isinstance(name, str) or
                    not re.fullmatch(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*", name)
                    for name in required)):
            raise SystemExit("Invalid required_declarations for group " + group["id"])
    by_id = {group["id"]: group for group in groups}
    scope, selected_ids = select_scope(args.group, branch, manifest.get("task_branches", {}), by_id)
    evidence = args.evidence_dir or (ROOT / "v2-selected-build" if scope == "selected_groups"
                                     else DEFAULT_EVIDENCE)
    if scope == "selected_groups" and evidence.resolve() == DEFAULT_EVIDENCE.resolve():
        raise SystemExit("Selected-group evidence must not overwrite v2-build")
    evidence.mkdir(parents=True, exist_ok=True)
    if selected_ids:
        build_groups = [by_id[group_id] for group_id in selected_ids]
    else:
        build_groups = groups
    build_names = sorted(name for group in build_groups for name in group["modules"])
    if not build_names or any(not group["modules"] for group in build_groups):
        raise SystemExit("Every selected group must contain at least one module")
    audit_groups = [group for group in build_groups if group["proved"]]
    expected_audits = [group["id"] for group in audit_groups]
    targets = ["+" + PREFIX + "." + name + ":olean" for name in build_names]
    snapshots = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                 for path in files}
    config_paths = ["lean-toolchain", "lakefile.toml", "lake-manifest.json",
                    ".github/v2/build.py", ".github/v2/manifest.json",
                    ".github/workflows/mom-engine-step-v2.yml",
                    ".github/workflows/integration-build.yml"]
    config_snapshots = {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
                        for path in config_paths}
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
        "config_sha256": config_snapshots,
        "allowed_axioms": ALLOWED,
        "branch": branch,
        "scope": scope,
        "selected_groups": selected_ids,
        "targets": targets,
        "expected_audits": expected_audits,
        "audit_selection": "all loaded V2 module declarations or V2 namespace declarations",
        "module_timeout_seconds": MODULE_TIMEOUT_SECONDS,
        "watch_interval_seconds": WATCH_INTERVAL_SECONDS,
    }
    (evidence / "environment.json").write_text(json.dumps(environment, indent=2) + "\n")
    start = time.monotonic()
    build_exit = logged(["lake", "build", *targets], "build.log", evidence)
    results = {"branch": branch, "scope": scope, "selected_groups": selected_ids, "targets": targets,
               "build_exit": build_exit, "module_count": len(build_names),
               "total_module_count": len(names), "expected_audits": expected_audits,
               "elapsed_seconds": time.monotonic() - start, "group_audits": {},
               "watchdogs": WATCHDOG_RESULTS}
    if build_exit == 0:
        for group in audit_groups:
            group_id = group["id"]
            required = group.get("required_declarations", [])
            audit = "\n".join("import " + PREFIX + "." + name for name in group["modules"])
            audit += """
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modulePrefix : Name := `HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2
  let declarationPrefix : Name := `HeckeSkeleton.Moments.EngineStepV2
  let moduleNames := env.header.moduleNames
  let names := (env.constants.toList.filterMap fun (name, _) =>
    let fromV2Module := match env.getModuleIdxFor? name with
      | some idx => modulePrefix.isPrefixOf (moduleNames[idx.toNat]!)
      | none => false
    if fromV2Module || declarationPrefix.isPrefixOf (privateToUserName name)
      then some name else none).toArray.qsort Name.lt
  unless !names.isEmpty do
    throwError "No V2 declarations found"
"""
            audit += "  let required : Array Name := #[" + ", ".join(
                "`" + name for name in required) + "]\n"
            audit += """
  for requiredName in required do
    unless names.contains requiredName do
      throwError "Required V2 declaration missing: {requiredName}"
    logInfo m!"REQUIRED_V2_DECLARATION_PRESENT: {requiredName}"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"AXIOMS {name}: {dependencies}"
  logInfo m!"V2_GROUP_AXIOMS_PASSED: {names.size} declarations"
"""
            audit_path = evidence / (group_id + "_AxiomAudit.lean")
            audit_path.write_text(audit)
            code = logged(["lake", "env", "lean", str(audit_path)],
                          group_id + "_axioms.log", evidence)
            output = (evidence / (group_id + "_axioms.log")).read_text()
            results["group_audits"][group_id] = {
                "exit_code": code,
                "success_marker": "V2_GROUP_AXIOMS_PASSED:" in output,
                "required_declarations": required,
            }
    for path, digest in snapshots.items():
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != digest:
            raise SystemExit("Source changed during verification: " + path)
    for path, digest in config_snapshots.items():
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != digest:
            raise SystemExit("Configuration changed during verification: " + path)
    results["elapsed_seconds"] = time.monotonic() - start
    success = build_exit == 0 and set(results["group_audits"]) == set(expected_audits) and all(
        result["exit_code"] == 0 and result["success_marker"]
        for result in results["group_audits"].values())
    results["success"] = success
    (evidence / "result.json").write_text(json.dumps(results, indent=2) + "\n")
    audited = (", ".join(results["group_audits"]) or
               ("not run (build failed)" if expected_audits else "none (no proved groups)"))
    summary = ("# MOM_ENGINE_STEP_V2\n\n"
               + f"- Exact head: `{environment['head']}`\n"
               + f"- Branch: `{branch or '(detached)'}`\n"
               + f"- Scope: `{scope}`\n"
               + f"- Selected groups: {', '.join(selected_ids) or 'all'}\n"
               + f"- Target modules: {len(build_names)} of {len(names)} V2 modules\n"
               + f"- Lake exit: {build_exit}\n"
               + f"- Per-module Lean timeout: {MODULE_TIMEOUT_SECONDS}s\n"
               + f"- Modules terminated: {sum(len(item['killed']) for item in WATCHDOG_RESULTS.values())}\n"
               + f"- Proved groups audited: {audited}\n"
               + f"- Result: {'PASS' if success else 'FAIL'}\n")
    if scope == "selected_groups":
        summary += "- This selected-group result does not replace the full-build gate.\n"
    elif scope == "task_branch":
        summary += "- This task-branch result does not replace the shared-main or whole-project checks.\n"
    (evidence / "summary.md").write_text(summary)
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as stream:
            stream.write(summary)
    print(summary, flush=True)
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
