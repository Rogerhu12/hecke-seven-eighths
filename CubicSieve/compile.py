"""Build only CubicSieve modules against the project's precompiled Lean 4.35 libraries.

No Lake configuration, external sources, or shared build outputs are changed.
Usage: python -I CubicSieve/compile.py CubicSieve.Bootstrap
       python -I CubicSieve/compile.py --check CubicSieve/Audit.lean
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / "CubicSieve"
WORK = HERE / ".build"
OUT = WORK / "out"
LOGS = WORK / "logs"
spec = importlib.util.spec_from_file_location("project_compile435", ROOT / "tools/compile435.py")
base = importlib.util.module_from_spec(spec)
sys.dont_write_bytecode = True
spec.loader.exec_module(base)
PATHS = [OUT, *(Path(p) for p in base.lean_path().split(os.pathsep)
                if Path(p) != base.OUT)]


@contextmanager
def compiler_slot():
    """Allow at most two Lean invocations across this directory's agents."""
    WORK.mkdir(parents=True, exist_ok=True)
    # Keep the original slot name so an invocation already holding it also
    # participates in the two-slot limit during this transition.
    handles = [(WORK / name).open("a+b") for name in
               ("compiler-slot.lock", "compiler-slot-1.lock")]
    selected = None
    try:
        for handle in handles:
            if handle.tell() == 0:
                handle.write(b"0")
                handle.flush()
        while selected is None:
            for handle in handles:
                handle.seek(0)
                try:
                    if os.name == "nt":
                        import msvcrt
                        msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
                    else:
                        import fcntl
                        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    selected = handle
                    break
                except OSError:
                    pass
            if selected is None:
                time.sleep(0.25)
        yield
    finally:
        if selected is not None:
            selected.seek(0)
            if os.name == "nt":
                import msvcrt
                msvcrt.locking(selected.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                import fcntl
                fcntl.flock(selected, fcntl.LOCK_UN)
        for handle in handles:
            handle.close()


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source(name: str) -> Path:
    if not re.fullmatch(r"CubicSieve(?:\.[A-Za-z_][A-Za-z_0-9]*)+", name):
        raise ValueError(f"Only CubicSieve modules may be built: {name}")
    return ROOT / (name.replace(".", "/") + ".lean")


def imports(path: Path) -> list[str]:
    body = re.sub(r"/-.*?-/", "", path.read_text(encoding="utf-8-sig"), flags=re.S)
    return re.findall(r"^(?:public\s+)?(?:meta\s+)?import\s+(\S+)", body, re.M)


def prebuilt(name: str) -> Path:
    rel = name.replace(".", "/") + ".olean"
    for directory in PATHS:
        path = directory / rel
        if path.is_file():
            return path
    raise FileNotFoundError(f"Precompiled dependency not found: {name}; no external build attempted")


def run(path: Path, module: str | None) -> int:
    LOGS.mkdir(parents=True, exist_ok=True)
    label = module or f"check-{path.stem}"
    log = LOGS / f"{label}.log"
    flags = [flag for flag in base.FLAGS if not flag.startswith("-j")]
    command = [str(base.LEAN), *flags, "-j1", "-R", str(ROOT)]
    if module:
        stem = OUT / module.replace(".", "/")
        stem.parent.mkdir(parents=True, exist_ok=True)
        command += ["-o", str(stem) + ".olean", "-i", str(stem) + ".ilean"]
    command.append(str(path))
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, PATHS)),
               LEAN_SYSROOT=str(base.TOOLCHAIN), LEAN_NUM_THREADS="1")
    started = time.monotonic()
    with compiler_slot():
        with log.open("w", encoding="utf-8") as handle:
            code = subprocess.run(command, cwd=ROOT, env=env, stdout=handle,
                                  stderr=subprocess.STDOUT).returncode
    result = {"module": module, "source": str(path.relative_to(ROOT)),
              "source_sha256": digest(path), "exit_code": code,
              "seconds": round(time.monotonic() - started, 1), "log": str(log)}
    log.with_suffix(".json").write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps(result), flush=True)
    if code or module is None:
        print(log.read_text(encoding="utf-8", errors="replace"), flush=True)
    return code


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="*")
    parser.add_argument("--check", type=Path)
    parser.add_argument("--no-deps", action="store_true",
                        help="Use existing local dependency oleans; compile only the named modules")
    args = parser.parse_args()
    if not args.modules and args.check is None:
        parser.error("Provide a CubicSieve module or --check file")
    seen: set[str] = set()

    def build(name: str) -> None:
        if name in seen:
            return
        path = source(name)
        deps = imports(path)
        for dep in deps:
            if dep.startswith("CubicSieve.") and not args.no_deps:
                build(dep)
        fingerprint = hashlib.sha256((digest(path) + "".join(
            digest(prebuilt(dep)) for dep in deps)).encode()).hexdigest()
        stamp = OUT / (name.replace(".", "/") + ".stamp")
        output = stamp.with_suffix(".olean")
        if output.is_file() and stamp.is_file() and stamp.read_text() == fingerprint:
            print(f"CACHED {name}", flush=True)
        else:
            code = run(path, name)
            if code:
                raise SystemExit(code)
            stamp.write_text(fingerprint, encoding="ascii")
        seen.add(name)

    for name in args.modules:
        build(name)
    if args.check is not None:
        path = (ROOT / args.check).resolve()
        if not path.is_relative_to(HERE):
            raise ValueError("--check file must be inside CubicSieve/")
        for dep in imports(path):
            if dep.startswith("CubicSieve.") and not args.no_deps:
                build(dep)
        return run(path, None)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
