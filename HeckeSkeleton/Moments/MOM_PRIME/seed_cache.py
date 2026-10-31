#!/usr/bin/env python3
"""Restore an optional, pinned dependency cache before ordinary Lake checking.

Only build facets of the current target's repository/vendor import closure are
installed. No source files or dependency hash records are manufactured. The
workflow subsequently runs `lake --rehash build`, so Lake must validate the
original traces against the actual current sources, options, and artifacts.
Expired or unavailable Actions artifacts are simply a cache miss.
"""

import hashlib
import re
import shutil
import sys
import tarfile
import tomllib
from pathlib import Path, PurePosixPath


BUNDLES = {
    "40-0": "eeaae4ba35ea0b43578e132afdd904caef3fb7010baa8a3ad963b7e96bcb768e",
    "40-1": "4efd5cfae24809b98675993cd5544dfe6caf7d0ffb8d823f22a64f79c8102a8d",
    "100-2": "f422c5449fc4ee1732a86ce815954f5161816d11cda1c87bce2e540693a7d27b",
}
TARGET = "HeckeSkeleton.Moments.MOM_PRIME.Audit"


def without_comments(source):
    out = []
    cursor = depth = 0
    while cursor < len(source):
        if source.startswith("/-", cursor):
            depth += 1
            cursor += 2
        elif depth and source.startswith("-/", cursor):
            depth -= 1
            cursor += 2
        elif depth:
            if source[cursor] == "\n":
                out.append("\n")
            cursor += 1
        elif source.startswith("--", cursor):
            end = source.find("\n", cursor)
            cursor = len(source) if end < 0 else end
        else:
            out.append(source[cursor])
            cursor += 1
    return "".join(out)


def build_stems(repo):
    libraries = []
    for package in (repo, repo / "vendor/class-field-theory"):
        config = tomllib.loads((package / "lakefile.toml").read_text())
        for library in config["lean_lib"]:
            libraries.append((package / library.get("srcDir", "."), package))
    seen, stems = set(), set()

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        relative = Path(*module.split("."))
        for source_root, package in libraries:
            source = (source_root / relative).with_suffix(".lean")
            if not source.is_file():
                continue
            build = package.relative_to(repo) / ".lake/build"
            for facet in ("lib/lean", "ir"):
                stems.add((build / facet / relative).as_posix())
            imports = re.findall(
                r"^(?:public\s+)?(?:meta\s+)?import\s+(\S+)",
                without_comments(source.read_text()),
                re.M,
            )
            for dependency in imports:
                visit(dependency)
            return

    visit(TARGET)
    return stems


def main():
    repo = Path.cwd().resolve()
    download = Path(sys.argv[1])
    archives = []
    for name, expected in BUNDLES.items():
        path = download / f"prime-foundation-{name}" / f"foundation-{name}.tar.gz"
        if not path.is_file():
            print(f"Optional cache {name} unavailable; Lake will build missing dependencies.")
            continue
        with path.open("rb") as source:
            actual = hashlib.file_digest(source, "sha256").hexdigest()
        if actual != expected:
            raise RuntimeError(f"Cache archive digest mismatch: {name}")
        print(f"Verified archive {name}: SHA256 {actual}")
        archives.append(path)

    stems = build_stems(repo)
    count = size = 0
    for archive in archives:
        with tarfile.open(archive, "r|gz") as bundle:
            for member in bundle:
                path = PurePosixPath(member.name)
                if path.is_absolute() or ".." in path.parts or not member.isfile():
                    continue
                stem = (path.parent / path.name.split(".", 1)[0]).as_posix()
                if stem not in stems:
                    continue
                destination = repo.joinpath(*path.parts)
                destination.parent.mkdir(parents=True, exist_ok=True)
                with bundle.extractfile(member) as source, destination.open("wb") as output:
                    shutil.copyfileobj(source, output)
                count += 1
                size += member.size
        archive.unlink()
    print(f"Installed {count} cached facets ({size} bytes) for current source modules.")
    print("Verification remains: lake --rehash build " + TARGET)


if __name__ == "__main__":
    main()
