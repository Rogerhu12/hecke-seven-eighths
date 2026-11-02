#!/usr/bin/env python3
"""Build all V2 modules on B, or the explicitly registered task scope.

The full skeleton permits placeholders only in groups marked unproved.
Every task-owned module is strict. Lake is the build authority; fresh Lean
audits check every loaded V2 declaration, including private and generated
declarations, and recursively allow only the three standard axioms.
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
TASK_ROUTING: dict = {}


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
    """Preserve incoming merge-base discovery for unregistered task branches."""
    head = os.environ.get("GITHUB_HEAD_REF") or os.environ.get("GITHUB_REF_NAME", "")
    TASK_ROUTING.clear()
    TASK_ROUTING.update({"method": "merge_base_diff", "branch": head,
                         "base_branch": BASE_BRANCH})
    if not head.startswith(TASK_BRANCH_PREFIX):
        TASK_ROUTING["fallback_reason"] = "No task branch in the GitHub environment"
        return None
    try:
        for ref, local in ((BASE_BRANCH, "v2-base"), (head, "task-head")):
            subprocess.run(["git", "fetch", "--no-tags", "--quiet", "--depth=400", "origin",
                            f"+refs/heads/{ref}:refs/remotes/origin/{local}"], check=True)
        base = subprocess.check_output(["git", "merge-base", "HEAD", "origin/v2-base"],
                                       text=True).strip()
        TASK_ROUTING["merge_base"] = base
        changed = subprocess.check_output(
            ["git", "diff", "--name-only", base, "HEAD", "--", str(TASK.relative_to(ROOT))],
            text=True).split()
    except (OSError, subprocess.SubprocessError) as error:
        reason = f"{type(error).__name__}: {error}"
        TASK_ROUTING["fallback_reason"] = reason
        print(f"V2_SCOPE_FALLBACK full build ({reason})", flush=True)
        return None
    targets = sorted(({Path(f).stem for f in changed if f.endswith(".lean")} & set(names))
                     - {"Interface"})
    TASK_ROUTING["targets"] = targets
    if not targets:
        TASK_ROUTING["fallback_reason"] = "No changed current V2 modules after excluding Interface"
    print(f"V2_SCOPE task branch {head}: base {base[:12]}, targets {targets}", flush=True)
    return targets or None


def checked_names(value, label: str, pattern: str, *, nonempty: bool = False) -> list[str]:
    if (not isinstance(value, list) or
            any(not isinstance(item, str) or not re.fullmatch(pattern, item) for item in value) or
            len(value) != len(set(value)) or (nonempty and not value)):
        raise ValueError("Invalid or duplicate " + label)
    return value


def select_scope(manifest: dict, names: list[str], branch: str) -> dict:
    """Resolve only the current task; inactive task maps need no files on B."""
    groups = manifest["groups"]
    group_ids = checked_names([group["id"] for group in groups],
                              "group identifiers", r"[a-z0-9_]+")
    for group in groups:
        checked_names(group["modules"], "group modules", r"[A-Za-z][A-Za-z0-9_]*")
        if type(group["proved"]) is not bool or len(group["modules"]) > 100:
            raise ValueError("Invalid proved flag or group exceeds 100 modules")
    listed = [name for group in groups for name in group["modules"]]
    if not names or sorted(listed) != names or len(listed) != len(set(listed)):
        raise ValueError("The group manifest must cover every V2 module exactly once")
    full = {"mode": "full", "branch": branch, "modules": names,
            "groups": [group["id"] for group in groups if group["proved"]],
            "roots": [], "required_declarations": [], "forced_unproved_modules": [], "note": ""}
    # Never let a task-map entry weaken the original B-branch gate.
    if branch == BASE_BRANCH:
        return full
    specs = manifest.get("task_scopes", {})
    if not isinstance(specs, dict):
        raise ValueError("task_scopes must be an object")
    if branch not in specs:
        if branch.startswith(TASK_BRANCH_PREFIX):
            TASK_ROUTING.clear()
            targets = task_targets(names)
            note = ("Unregistered task branch: public task entry points are not registered "
                    "or accepted by this run.")
            if targets:
                unproved = {name for group in groups if not group["proved"]
                            for name in group["modules"]}
                return {"mode": "unregistered_diff", "branch": branch, "modules": targets,
                        "groups": [], "roots": [], "required_declarations": [],
                        "forced_unproved_modules": sorted(set(targets) & unproved),
                        "note": note, "routing": dict(TASK_ROUTING)}
            return {**full, "note": note + " Empty/failed diff discovery uses the full gate.",
                    "routing": dict(TASK_ROUTING)}
        return full
    spec = specs[branch]
    owned_groups = checked_names(spec.get("groups", []), "task groups", r"[a-z0-9_]+")
    if not set(owned_groups) <= set(group_ids):
        raise ValueError("Task groups are missing from this branch's manifest")
    explicit = checked_names(spec.get("modules", []), "task modules", r"[A-Za-z][A-Za-z0-9_]*")
    owned = set(explicit)
    for group in groups:
        if group["id"] in owned_groups:
            owned.update(group["modules"])
    roots = checked_names(spec.get("roots", []), "task roots",
                          r"[A-Za-z][A-Za-z0-9_]*", nonempty=True)
    required = checked_names(spec.get("required_declarations", []), "required task declarations",
                             r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+",
                             nonempty=True)
    if not owned or not owned <= set(names) or not set(roots) <= owned:
        raise ValueError("Task modules must exist and must include every task root")
    if not isinstance(spec.get("note", ""), str):
        raise ValueError("Task scope note must be text")
    unproved = {name for group in groups if not group["proved"] for name in group["modules"]}
    return {"mode": "task", "branch": branch, "modules": sorted(owned),
            "groups": owned_groups, "roots": roots, "required_declarations": required,
            # These are still scanned and audited strictly, never skipped.
            "forced_unproved_modules": sorted(owned & unproved), "note": spec.get("note", "")}


def current_branch() -> str:
    return (os.environ.get("GITHUB_HEAD_REF") or os.environ.get("GITHUB_REF_NAME") or
            subprocess.check_output(["git", "branch", "--show-current"], text=True).strip())


def exact_head() -> str:
    return subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()


def input_snapshots() -> tuple[dict[str, str], dict[str, str]]:
    sources = sorted(TASK.glob("*.lean"))
    config_names = (
        ".github/v2/build.py", ".github/v2/manifest.json",
        "lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json",
    )
    configs = {ROOT / name for name in config_names if (ROOT / name).is_file()}
    for pattern in ("*.yml", "*.yaml"):
        configs.update((ROOT / ".github/workflows").glob(pattern))

    def digest(paths):
        return {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                for path in sorted(paths)}
    return digest(sources), digest(configs)


def audit_source(modules: list[str], roots: list[str], required: list[str]) -> str:
    """Fresh audit of all loaded V2 declarations and their recursive axioms."""
    tick = chr(96)

    def lean_names(names):
        return "#[" + ", ".join(tick + name for name in names) + "]"

    imports = "\n".join("import " + PREFIX + "." + name for name in modules)
    return imports + """
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames : Array Name := env.header.moduleNames
  let nsPrefix : Name := @@HeckeSkeleton.Moments.EngineStepV2
  let modulePrefix : Name := @@HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2
  let moduleOf (name : Name) : Option Name := do
    let idx ← env.getModuleIdxFor? name
    moduleNames[idx.toNat]?
  let names := (env.constants.toList.filterMap fun (name, _) =>
    if nsPrefix.isPrefixOf (privateToUserName name) ||
        (moduleOf name).any (modulePrefix.isPrefixOf ·)
    then some name else none).toArray.qsort Name.lt
  unless !names.isEmpty do
    throwError "No loaded V2 declarations found"
""".replace("@@", tick) + (
        "  let roots : Array Name := " + lean_names([PREFIX + "." + name for name in roots]) + "\n"
        "  let required : Array Name := " + lean_names(required) + "\n"
    ) + """
  for name in required do
    let some (.thmInfo _) := env.find? name
      | throwError "Required task theorem is missing or not a theorem: {name}"
    let some owner := moduleOf name
      | throwError "Required task theorem has no source module: {name}"
    unless roots.contains owner && names.contains name do
      throwError "Required task theorem is not declared in an owned task root: {name}"
    logInfo m!"V2_REQUIRED_THEOREM {name}"
  for root in roots do
    unless required.any (fun name => moduleOf name == some root) do
      throwError "Task root has no required theorem: {root}"
  let permitted : Array Name := #[@@propext, @@Classical.choice, @@Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"AXIOMS {name}: {dependencies}"
  logInfo m!"V2_GROUP_AXIOMS_PASSED: {names.size} declarations"
""".replace("@@", tick)


def main() -> int:
    EVIDENCE.mkdir(exist_ok=True)
    start = time.monotonic()
    errors = []
    snapshots, config_snapshots = input_snapshots()
    names = sorted(Path(path).stem for path in snapshots)
    scope = {"mode": "invalid", "branch": "", "modules": []}
    environment = {"source_sha256": snapshots, "verification_sha256": config_snapshots,
                   "allowed_axioms": ALLOWED, "module_timeout_seconds": MODULE_TIMEOUT_SECONDS,
                   "watch_interval_seconds": WATCH_INTERVAL_SECONDS}
    groups = []
    try:
        environment["head"] = exact_head()
        scope["branch"] = current_branch()
        manifest = json.loads((ROOT / ".github/v2/manifest.json").read_text())
        environment["manifest"] = manifest
        environment["toolchain"] = (ROOT / "lean-toolchain").read_text().strip()
        scope = select_scope(manifest, names, scope["branch"])
        groups = manifest["groups"]
        if scope["mode"] != "full":
            scans = [(module, True) for module in scope["modules"]]
        else:
            scans = [(module, group["proved"]) for group in groups for module in group["modules"]]
        for module, proved in scans:
            pattern = (r"\b(?:axiom|native_decide|admit|sorryAx|sorry)\b" if proved else
                       r"\b(?:axiom|native_decide|admit|sorryAx)\b")
            path = TASK / (module + ".lean")
            source = code_only(path.read_text())
            for match in re.finditer(pattern, source):
                line = source.count("\n", 0, match.start()) + 1
                errors.append(f"{path.relative_to(ROOT)}:{line}: forbidden {match.group()}")
    except (OSError, subprocess.SubprocessError, ValueError, KeyError, TypeError) as error:
        errors.append(f"{type(error).__name__}: {error}")
    environment["scope"] = scope
    environment["audit_scope"] = (
        "Every loaded V2 declaration by source module OR namespace, "
        "including private and generated declarations; collectAxioms is recursive.")
    (EVIDENCE / "environment.json").write_text(json.dumps(environment, indent=2) + "\n")
    preflight = ("\n".join(errors) if errors else
                 f"PASS: {scope['mode']} scope; {len(scope['modules'])} of {len(names)} V2 targets; "
                 f"task roots={scope['roots']}; forced strict={scope['forced_unproved_modules']}")
    (EVIDENCE / "preflight.log").write_text(preflight + "\n")
    print(preflight, flush=True)
    results = {"preflight_passed": not errors, "scope": scope, "build_exit": None,
               "module_count": len(scope["modules"]), "available_module_count": len(names),
               "group_audits": {}, "watchdogs": WATCHDOG_RESULTS, "errors": errors}
    if not errors:
        try:
            results["build_exit"] = logged(
                ["lake", "build", *("+" + PREFIX + "." + name + ":olean"
                                   for name in scope["modules"])], "build.log")
            if results["build_exit"] == 0:
                scope_id = "task_scope" if scope["mode"] == "task" else "unregistered_diff"
                audits = ([{"id": scope_id, "modules": scope["modules"],
                            "roots": scope["roots"],
                            "required_declarations": scope["required_declarations"]}]
                          if scope["mode"] != "full" else
                          [group for group in groups if group["proved"]])
                for group in audits:
                    group_id = group["id"]
                    audit_path = EVIDENCE / (group_id + "_AxiomAudit.lean")
                    audit_path.write_text(audit_source(group["modules"], group.get("roots", []),
                                                       group.get("required_declarations", [])))
                    code = logged(["lake", "env", "lean", str(audit_path)], group_id + "_axioms.log")
                    output = (EVIDENCE / (group_id + "_axioms.log")).read_text()
                    marker = re.search(r"V2_GROUP_AXIOMS_PASSED: (\d+) declarations", output)
                    results["group_audits"][group_id] = {
                        "exit_code": code, "success_marker": marker is not None,
                        "audited_declaration_count": int(marker.group(1)) if marker else 0,
                    }
        except Exception as error:
            errors.append(f"{type(error).__name__}: {error}")
    try:
        after_sources, after_configs = input_snapshots()
        for label, before, after in (("source", snapshots, after_sources),
                                     ("verification input", config_snapshots, after_configs)):
            for path in sorted(before.keys() | after.keys()):
                if before.get(path) != after.get(path):
                    errors.append(f"Changed {label} during verification: {path}")
        results["head_after"] = exact_head()
        if results["head_after"] != environment.get("head"):
            errors.append("Git HEAD changed during verification")
    except Exception as error:
        errors.append(f"Final integrity check failed: {type(error).__name__}: {error}")
    results["elapsed_seconds"] = time.monotonic() - start
    success = not errors and results["build_exit"] == 0 and all(
        result["exit_code"] == 0 and result["success_marker"]
        for result in results["group_audits"].values())
    if scope["mode"] in ("task", "unregistered_diff"):
        scope_id = "task_scope" if scope["mode"] == "task" else "unregistered_diff"
        success = success and scope_id in results["group_audits"]
    results["success"] = success
    results["public_task_certified"] = success and scope["mode"] == "task"
    (EVIDENCE / "result.json").write_text(json.dumps(results, indent=2) + "\n")
    tick = chr(96)
    summary = ("# MOM_ENGINE_STEP_V2\n\n"
               + f"- Exact head: {tick}{environment.get('head', 'unavailable')}{tick}\n"
               + f"- Scope: {scope['mode']} ({scope['branch'] or 'detached/unknown'})\n"
               + f"- V2 targets: {len(scope['modules'])} of {len(names)}\n"
               + f"- Required theorems: {', '.join(scope.get('required_declarations', [])) or ('none registered' if scope['mode'] == 'unregistered_diff' else 'original full gate')}\n"
               + f"- Lake exit: {results['build_exit']}\n"
               + f"- Per-module Lean timeout: {MODULE_TIMEOUT_SECONDS}s\n"
               + f"- Modules terminated: {sum(len(item['killed']) for item in WATCHDOG_RESULTS.values())}\n"
               + f"- Audits: {', '.join(results['group_audits']) or 'none'}\n"
               + f"- Result: {'PASS' if success else 'FAIL'}\n")
    if scope.get("note"):
        summary += "\nScope note: " + scope["note"] + "\n"
    if errors:
        summary += "\nVerification errors:\n\n" + "\n".join("- " + error for error in errors) + "\n"
    (EVIDENCE / "summary.md").write_text(summary)
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as stream:
            stream.write(summary)
    print(summary, flush=True)
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())

