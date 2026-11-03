#!/usr/bin/env python3
"""Build a source-only LOW diagnostic unit; never evidence of module acceptance.

No Lean process or compiler output is created here.  The generated unit may
be checked with plain ``lake env lean`` without -o/-i/-c after the ordinary
Lake gate has finished.  That gate and its required axiom audit remain final.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tomllib
from functools import lru_cache
from pathlib import Path

NAMES = (
    'GeneralHeight', 'GeneralSeparatedEnergy', 'ActualBlockEnergy',
    'GeneralReflectedBlock', 'GeneralBlockPolynomial', 'GeneralMarkedEnergy',
    'GeneralConductor', 'GeneralHeightTail', 'GeneralTailNumerics',
    'GeneralKernelTail', 'GeneralReconstruction', 'GeneralColumnCutoff',
    'GeneralSourceCutoff', 'GeneralAggregation', 'GeneralRows', 'GeneralAnnuli',
    'GeneralInactiveMass', 'GeneralInactiveEnergy', 'GeneralCanonicalBlock',
    'GeneralProductReconstruction', 'GeneralUniformEnergy', 'GeneralTupleBlocks',
    'GeneralProductEnergy', 'GeneralCompletedEnergy',
)
PREFIX = 'HeckeSkeleton.LowEnergy.'
TERMINAL_MODULES = (
    'HeckeGeneral.Analysis.CompensatedRowKernelFactorization',
    'HeckeSkeleton.LowEnergy.ActualAnnularBlockEnergy',
    'HeckeSkeleton.LowEnergy.ActualFrozenAggregation',
    'HeckeSkeleton.LowEnergy.ActualMarkedTupleEnergy',
    'HeckeSkeleton.LowEnergy.ActualFrozenReconstruction',
    'HeckeSkeleton.LowEnergy.ActualTupleReconstruction',
    'HeckeSkeleton.LowEnergy.ActualResidualDyadicEnergy',
    'HeckeSkeleton.LowEnergy.ActualCompleteIdealEnergy',
    'HeckeSkeleton.LowEnergy.ActualCompletedMarkedEnergy',
    'HeckeSkeleton.Principal',
)
EXPECTED_HEADERS = (
    'HeckeSkeleton.LowEnergy.ActualCommonMellinTail',
    'HeckeGeneral.Characters.InfinityPacket',
    'HeckeSkeleton.LowEnergy.ActualSeparatedBlock',
    'HeckeSkeleton.LowEnergy.ActualRawHybrid',
    'HeckeSkeleton.LowEnergy.MellinHybrid',
    'HeckeSkeleton.LowEnergy.BlockPolynomial',
    'HeckeSkeleton.LowEnergy.PhysicalBlockPolynomial',
    'HeckeSkeleton.LowEnergy.IdealRankin',
    'HeckeSkeleton.LowEnergy.ActualFrozenCharges',
    'HeckeSkeleton.ThetaKernel',
    'Mathlib.Analysis.SpecialFunctions.Pow.Real',
    'Mathlib.Tactic.FieldSimp', 'Mathlib.Tactic.Linarith',
    'Mathlib.Tactic.Positivity', 'Mathlib.Tactic.Ring',
    'HeckeSkeleton.LowEnergy.IdealMajorant',
    'Mathlib.Analysis.Normed.Ring.InfiniteSum',
    'HeckeSkeleton.LowEnergy.ActualSourceReindex',
    'HeckeSkeleton.Moments.MOM_BASE.ThetaBridge',
    'HeckeSkeleton.LowEnergy.ActualDyadicReflection',
    'HeckeSkeleton.LowEnergy.DyadicTail',
    'HeckeSkeleton.LowEnergy.ActualFrozenStateCount',
    'HeckeSkeleton.LowEnergy.InactiveCore',
    'HeckeSkeleton.LowEnergy.ActualReflectionReindex',
    'HeckeSkeleton.LowEnergy.WindowTuples',
    'HeckeGeneral.Analysis.FrequencyRowCounting',
    'Mathlib.Analysis.SpecialFunctions.Exp',
    'HeckeSkeleton.LowEnergy.ActualRows',
)
IMPORT = re.compile(r'(?:(?:public|private|meta)\s+)*import\s+(.+)')
SCOPE = re.compile(r'(?:(noncomputable)\s+)?(section|namespace)(?:\s+([\w.\']+))?')
END = re.compile(r'end(?:\s+([\w.\']+))?')


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def visible_lines(lines):
    """Ignore nested Lean comments while preserving original line numbers."""
    depth = 0
    for number, raw in enumerate(lines, 1):
        visible, i, string = [], 0, False
        while i < len(raw):
            pair, char = raw[i:i + 2], raw[i]
            if depth:
                if pair == '/-':
                    depth += 1
                    i += 2
                elif pair == '-/':
                    depth -= 1
                    i += 2
                else:
                    i += 1
            elif string:
                visible.append(char)
                if char == '\\' and i + 1 < len(raw):
                    visible.append(raw[i + 1])
                    i += 2
                    continue
                if char == '"':
                    string = False
                i += 1
            elif pair == '/-':
                depth += 1
                i += 2
            elif pair == '--':
                break
            else:
                visible.append(char)
                string = char == '"'
                i += 1
        yield number, ''.join(visible).strip()
    if depth:
        raise RuntimeError('Unclosed Lean block comment')


def header(lines):
    imports, positions, markers = [], [], []
    for number, line in visible_lines(lines):
        if not line:
            continue
        if line in ('module', 'prelude'):
            markers.append(line)
            continue
        match = IMPORT.fullmatch(line)
        if not match:
            break
        tokens = match.group(1).split()
        if tokens[0] == 'all':
            tokens = tokens[1:]
        if not tokens or any(not re.fullmatch(r'[\w.\']+', token) for token in tokens):
            raise RuntimeError('Unsupported import at line ' + str(number))
        imports.extend(tokens)
        positions.append(number)
    return imports, positions, markers


def check_scopes(lines, source: str) -> None:
    stack = []
    for number, line in visible_lines(lines):
        match = SCOPE.fullmatch(line)
        if match:
            noncomputable, kind, name = match.groups()
            stack.append((kind, name, bool(noncomputable)))
            continue
        match = END.fullmatch(line)
        if match:
            name = match.group(1)
            if not stack or (name is not None and name != stack[-1][1]):
                raise RuntimeError(f'{source}:{number}: inspect namespace/section closure')
            stack.pop()
    if stack != [('section', None, True)]:
        raise RuntimeError(f'{source}: expected exactly one open noncomputable section, got {stack}')


def source_roots(repo: Path, lean_source: Path, package_dirs: list[Path],
                 extra_roots: list[Path]) -> list[Path]:
    """Follow literal Lake srcDir and local package paths without running Lake."""
    roots, packages, seen = [], [repo], set()
    for directory in [repo / '.lake/packages', *package_dirs]:
        if directory.is_dir():
            packages.extend(sorted(p for p in directory.iterdir() if p.is_dir()))
    while packages:
        package = packages.pop(0).resolve()
        if package in seen:
            continue
        seen.add(package)
        roots.append(package)
        toml = package / 'lakefile.toml'
        if toml.is_file():
            config = tomllib.loads(toml.read_text())
            if isinstance(config.get('srcDir'), str):
                roots.append(package / config['srcDir'])
            for lib in config.get('lean_lib', []):
                roots.append(package / lib.get('srcDir', '.'))
            for requirement in config.get('require', []):
                if isinstance(requirement.get('path'), str):
                    packages.append(package / requirement['path'])
        else:
            lake = package / 'lakefile.lean'
            if lake.is_file():
                for relative in re.findall(r'\bsrcDir\s*:=\s*"([^"\n]+)"', lake.read_text()):
                    roots.append(package / relative)
    roots.extend([lean_source, lean_source / 'lake', *extra_roots])
    return list(dict.fromkeys(path.resolve() for path in roots if path.is_dir()))


def checkout_sources(repo: Path, expected_head: str, mapping: list[dict]) -> dict:
    if not re.fullmatch('[0-9a-f]{40}', expected_head):
        raise RuntimeError('Expected head must be an exact 40-character commit SHA')
    def git(*arguments):
        return subprocess.check_output(['git', '-C', str(repo), *arguments], text=True).strip()
    actual_head = git('rev-parse', 'HEAD')
    if actual_head != expected_head:
        raise RuntimeError('Diagnostic checkout differs from expected head: ' + actual_head)
    blobs = {}
    for line in git('ls-tree', '-r', '--full-tree', 'HEAD', '--',
                    *(entry['source_path'] for entry in mapping)).splitlines():
        fields, path = line.split('\t', 1)
        _, kind, digest = fields.split()
        if kind == 'blob':
            blobs[path] = digest
    for entry in mapping:
        if blobs.get(entry['source_path']) != entry['git_blob_sha1']:
            raise RuntimeError('Diagnostic source differs from checkout blob: ' + entry['source_path'])
    return {'checked': True, 'head': actual_head, 'selected_source_blobs_match': True}


def native_imports(repo: Path, lean_source: Path, modules) -> dict:
    # Lean/Util/Path.lean: findWithExt selects the first root containing the
    # module's top namespace, even if a later root has the requested leaf.
    paths = [Path(p) if Path(p).is_absolute() else repo / p
             for p in os.environ.get('LEAN_PATH', '').split(os.pathsep) if p]
    paths.append(lean_source.parent.parent / 'lib/lean')
    unavailable, available = [], 0
    for module in sorted(modules):
        namespace = module.split('.')[0]
        root = next((p for p in paths if (p / namespace).is_dir() or
                     (p / (namespace + '.olean')).exists()), None)
        leaf = root / Path(*module.split('.')).with_suffix('.olean') if root else None
        if leaf is None or not leaf.is_file():
            unavailable.append({'module': module, 'selected_path': str(leaf) if leaf else None})
        else:
            available += 1
    return {'checked': True, 'search_path': list(map(str, paths)),
            'available_count': available, 'unavailable': unavailable,
            'meaning': 'Dependency existence only; ordinary native imports still decide loadability.'}


def generate(repo: Path, output_dir: Path, lean_source: Path,
             package_dirs: list[Path] | None = None,
             extra_roots: list[Path] | None = None,
             expected_head: str | None = None, check_native_imports: bool = False,
             include_terminal: bool = False) -> dict:
    repo, output_dir, lean_source = repo.resolve(), output_dir.resolve(), lean_source.resolve()
    if not (repo / 'lakefile.toml').is_file() or not (lean_source / 'Init.lean').is_file():
        raise RuntimeError('Require the actual checkout and pinned Lean src/lean directory')
    expected = set(NAMES) - {'ActualBlockEnergy'}
    actual = {p.stem for p in (repo / 'HeckeSkeleton/LowEnergy').glob('General*.lean')}
    if actual != expected:
        raise RuntimeError('Review the inline module list; unexpected/missing General sources: ' +
                           repr(sorted(actual ^ expected)))
    ordered_modules = [PREFIX + name for name in NAMES]
    if include_terminal:
        ordered_modules.extend(TERMINAL_MODULES)
    inline = set(ordered_modules)
    roots = source_roots(repo, lean_source, package_dirs or [], extra_roots or [])

    @lru_cache(None)
    def resolve(module: str) -> Path:
        relative = Path(*module.split('.')).with_suffix('.lean')
        candidates = list(dict.fromkeys((root / relative).resolve() for root in roots
                                       if (root / relative).is_file()))
        if not candidates:
            raise RuntimeError('Cannot resolve import source: ' + module)
        if len(candidates) > 1:
            digests = {sha256(path.read_bytes()) for path in candidates}
            if len(digests) != 1:
                raise RuntimeError('Ambiguous source module: ' + module + ': ' + repr(candidates))
        return candidates[0]

    parts, external, completed = [], [], set()
    for module in ordered_modules:
        path = repo / Path(*module.split('.')).with_suffix('.lean')
        raw = path.read_bytes()
        lines = raw.decode('utf-8').replace('\r\n', '\n').splitlines()
        dependencies, removed, markers = header(lines)
        if markers or removed != list(range(1, len(removed) + 1)):
            raise RuntimeError(f'{path}: only contiguous original top import lines may be removed')
        check_scopes(lines, str(path.relative_to(repo)))
        for dependency in dependencies:
            if dependency in inline:
                if dependency not in completed:
                    raise RuntimeError(module + ' precedes inlined dependency ' + dependency)
            elif dependency not in external:
                external.append(dependency)
        completed.add(module)
        body = lines[len(removed):]
        parts.append((module, path, raw, body, len(removed)))
    if tuple(external[:len(EXPECTED_HEADERS)]) != EXPECTED_HEADERS or (
            not include_terminal and len(external) != len(EXPECTED_HEADERS)):
        raise RuntimeError('The reviewed 28-module external header changed; inspect before running')

    # Follow every source edge, including relocated srcDir modules and package
    # sources.  Never treat a missing file as an opaque dependency leaf.
    graph, pending = {}, [(module, [module]) for module in [*external, 'Init']]
    while pending:
        module, chain = pending.pop()
        if module in inline:
            raise RuntimeError('External imports already declare an inline module: ' + ' -> '.join(chain))
        if module in graph:
            continue
        path = resolve(module)
        with path.open(encoding='utf-8') as source:
            dependencies, _, _ = header(source)
        graph[module] = {'source_path': str(path), 'imports': dependencies}
        pending.extend((child, [*chain, child]) for child in dependencies)

    chunks = ['import ' + module for module in external] + [
        '', '/- Native diagnostics only.  Actual independent module compilation remains required. -/', '',
    ]
    mapping = []
    for index, (module, path, raw, body, offset) in enumerate(parts):
        section = 'GeneralDiagnosticPart' + str(index)
        chunks.extend(['section ' + section, ''])
        first = len(chunks) + 1
        chunks.extend(body)
        mapping.append({
            'module': module, 'source': path.name,
            'source_path': path.relative_to(repo).as_posix(),
            'sha256': sha256(raw),
            'git_blob_sha1': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
            'body_sha256': sha256(('\n'.join(body) + '\n').encode()),
            'first_diagnostic_line': first, 'last_diagnostic_line': len(chunks),
            'source_line_offset': offset,
        })
        chunks.extend(['', 'end', 'end ' + section, ''])
    text = '\n'.join(chunks) + '\n'
    regenerated = text.splitlines()
    for entry, (_, path, raw, body, _) in zip(mapping, parts, strict=True):
        if path.read_bytes() != raw:
            raise RuntimeError('Source changed during generation: ' + str(path))
        if regenerated[entry['first_diagnostic_line'] - 1:entry['last_diagnostic_line']] != body:
            raise RuntimeError('Source-map round trip failed: ' + str(path))
    header_text = '\n'.join(chunks[:len(external)]) + '\n'
    checkout = checkout_sources(repo, expected_head, mapping) if expected_head else {'checked': False}
    native = native_imports(repo, lean_source, graph) if check_native_imports else {'checked': False}
    manifest = {
        'schema': 'low-energy-source-diagnostic-bundle-v1',
        'scope': 'diagnostics only; not a module build, acceptance gate, or per-module receipt',
        'status': 'unavailable' if native.get('unavailable') else 'generated',
        'checkout': checkout, 'native_imports': native,
        'include_terminal': include_terminal,
        'repo_root': str(repo), 'source_roots': list(map(str, roots)),
        'inline_modules': [part[0] for part in parts],
        'external_imports': external, 'external_closure_count': len(graph),
        'external_closure_inline_conflicts': [],
        'external_graph_sha256': sha256(json.dumps(graph, sort_keys=True).encode()),
        'header_sha256': sha256(header_text.encode()),
        'bundle_sha256': sha256(text.encode()), 'bundle_lines': len(regenerated),
        'source_map_round_trip': True,
        'transformations': ['remove contiguous top import lines',
                            'isolate each source body in a named section',
                            'close its one original open noncomputable section'],
        'modules': mapping,
    }
    output_dir.mkdir(parents=True, exist_ok=True)
    outputs = {
        'GeneralNativeDiagnostic.lean': text,
        'GeneralNativeDiagnostic.map.json': json.dumps(mapping, indent=2) + '\n',
        'GeneralNativeDiagnostic.manifest.json': json.dumps(manifest, indent=2) + '\n',
    }
    for name, contents in outputs.items():
        destination = output_dir / name
        if destination in [part[1] for part in parts]:
            raise RuntimeError('Refusing to overwrite a source module')
        temporary = destination.with_name(destination.name + '.tmp')
        temporary.write_text(contents, encoding='utf-8')
        temporary.replace(destination)
    return manifest


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--lean-source-root', type=Path, required=True)
    parser.add_argument('--package-dir', type=Path, action='append', default=[],
                        help='Additional .lake/packages source directory for an isolated checkout')
    parser.add_argument('--source-root', type=Path, action='append', default=[])
    parser.add_argument('--expected-head', help='Check exact Git HEAD and each selected source blob')
    parser.add_argument('--check-native-imports', action='store_true',
                        help='Run under lake env; reject unavailable closure .olean files')
    parser.add_argument('--include-terminal', action='store_true',
                        help='Also inline the reviewed ten physical, calibration and Principal modules')
    args = parser.parse_args()
    manifest = generate(args.repo_root, args.output_dir, args.lean_source_root,
                        args.package_dir, args.source_root, args.expected_head,
                        args.check_native_imports, args.include_terminal)
    print(json.dumps({key: manifest[key] for key in (
        'schema', 'status', 'include_terminal', 'bundle_sha256', 'bundle_lines', 'header_sha256',
        'external_closure_count', 'source_map_round_trip')}, indent=2))
    if manifest['status'] == 'unavailable':
        print('Diagnostic unavailable: ' + str(len(manifest['native_imports']['unavailable'])) +
              ' required native dependencies are absent; see the manifest.', file=sys.stderr)
        raise SystemExit(2)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print('Diagnostic bundle generation failed: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
