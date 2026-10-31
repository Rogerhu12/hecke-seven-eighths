#!/usr/bin/env python3
"""Build the requested MOM_ENGINE_STEP modules and preserve CI proof evidence.

Run from a normal pinned checkout after the mathlib cache has been restored.
All outputs belong to a caller-selected evidence directory, intended for an
Actions artifact. Builds use Lake or the existing strict source/object cache
verifier; every cache miss is compiled from its real source with the pinned
compiler and package options. The final namespace audit is always compiled
afresh. No proof source, package option, or trusted declaration is altered.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

LEAN_VERSION = '4.35.0-rc3'
LEAN_COMMIT = '470d5ce1400764999581fd26d5d72b00d990b0f4'
MATHLIB_COMMIT = '0493595ecd5da8ef14742febab99728f98e948e8'
PREFIX = 'HeckeSkeleton.Moments.EngineStep'
MODULE_ROOT = 'HeckeSkeleton.Moments.MOM_ENGINE_STEP'
CORE_MODULES = [MODULE_ROOT + '.' + name for name in (
    'Ledger', 'Pool', 'IdealPool', 'ActualLengths', 'Coefficient', 'Capacity', 'WholeTransform',
    'CommonSupportPartition', 'PrimeSupportMass', 'CommonHarmonicMass',
)]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('modules', nargs='*', default=[MODULE_ROOT + '.Interface'], help='Fully qualified target module names')
    parser.add_argument('--namespace', default=PREFIX, help='Namespace whose declarations must all satisfy the axiom whitelist')
    parser.add_argument('--repo', type=Path, default=Path.cwd())
    parser.add_argument('--evidence', type=Path, default=Path('mom-engine-step-verification'))
    parser.add_argument('--declaration', action='append', default=[], help='Also emit #print axioms for this declaration')
    parser.add_argument('--serial-build', action='store_true', help='Build the requested modules in order before the combined axiom audit')
    parser.add_argument('--checked-project-cache', action='store_true',
                        help='Use the existing strict source/import/options/object verifier and compile every cache miss from its real source')
    args = parser.parse_args()
    repo = args.repo.resolve()
    evidence = args.evidence.resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    for module in args.modules:
        if not re.fullmatch(re.escape(MODULE_ROOT) + r'(?:\.[A-Za-z_][A-Za-z_0-9]*)+', module):
            raise SystemExit(f'Unexpected task module: {module}')
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', args.namespace):
        raise SystemExit('Invalid audit namespace: ' + args.namespace)
    for declaration in args.declaration:
        if not re.fullmatch(re.escape(args.namespace) + r'(?:\.[A-Za-z_][A-Za-z_0-9]*)+', declaration):
            raise SystemExit(f'Unexpected task declaration: {declaration}')
    results = []

    def run(name: str, command: list[str], env: dict | None = None) -> str:
        start = time.monotonic()
        with (evidence / (name + '.log')).open('w') as log:
            log.write(json.dumps({'command': command, 'cwd': str(repo)}) + '\n')
            log.flush()
            process = subprocess.Popen(command, cwd=repo, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, text=True, env=env)
            assert process.stdout is not None
            output = []
            for line in process.stdout:
                output.append(line)
                print(line, end='', flush=True)
                log.write(line)
                log.flush()
            code = process.wait()
        results.append({'step': name, 'command': command, 'exit_code': code,
                        'elapsed_seconds': time.monotonic() - start})
        (evidence / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        if code:
            raise SystemExit(code)
        return ''.join(output)

    version = run('toolchain', ['lake', 'env', 'lean', '--version'])
    if LEAN_VERSION not in version or LEAN_COMMIT not in version:
        raise SystemExit(f'Unexpected Lean compiler: {version}')
    mathlib = run('mathlib', ['git', '-C', str(repo / '.lake/packages/mathlib'), 'rev-parse', 'HEAD']).strip()
    if mathlib != MATHLIB_COMMIT:
        raise SystemExit(f'Unexpected mathlib revision: {mathlib}')
    head = run('commit', ['git', 'rev-parse', 'HEAD']).strip()
    sources = {}
    for source in sorted((repo / 'HeckeSkeleton/Moments/MOM_ENGINE_STEP').glob('*.lean')):
        sources[str(source.relative_to(repo))] = hashlib.sha256(source.read_bytes()).hexdigest()
    (evidence / 'environment.json').write_text(json.dumps({
        'commit': head, 'lean': version.strip(), 'mathlib': mathlib,
        'targets': args.modules, 'source_sha256': sources,
        'build_backend': 'checked-source-object-cache' if args.checked_project_cache else 'lake',
    }, indent=2) + '\n')

    prepared_externals: set[str] = set()

    def build(name: str, modules: list[str], fail_fast: bool = True) -> None:
        if args.checked_project_cache:
            verifier = repo / 'scripts/verify_low_hybrid_exterior.py'
            environment = dict(os.environ)
            environment['WIRE_BUILD_WORKERS'] = '1'
            attempt = 0
            while True:
                attempt += 1
                stage = name if attempt == 1 else f'{name}-attempt-{attempt}'
                missing = None
                # Discovery can fail before the verifier writes its summaries.
                # Do not label a previous stage's summaries as this attempt's.
                for item in ('environment.json', 'results.json'):
                    (repo / 'wire-low-hybrid-verification' / item).unlink(missing_ok=True)
                try:
                    run(stage, [sys.executable, '-u', str(verifier), *modules], environment)
                except SystemExit:
                    # The pinned checkpoint contains project objects. A package
                    # such as TauCeti can still need its genuine Lake build.
                    # Discover every such cache miss in this invocation, build
                    # it normally, then rerun the unchanged strict verifier.
                    match = re.search(
                        r'^RuntimeError: Missing cached external module: '
                        r'([A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*)'
                        r'; run lake exe cache get$',
                        (evidence / (stage + '.log')).read_text(), re.MULTILINE)
                    if match is None or match.group(1) in prepared_externals:
                        raise
                    missing = match.group(1)
                finally:
                    # The existing verifier updates these summaries on each
                    # call. Keep all attempts, including failed discovery.
                    for item in ('environment.json', 'results.json'):
                        source = repo / 'wire-low-hybrid-verification' / item
                        if source.is_file():
                            shutil.copyfile(source, evidence / (stage + '-project-' + item))
                if missing is None:
                    return
                package_name = missing.split('.', 1)[0]
                manifest = json.loads((repo / 'lake-manifest.json').read_text())
                package = next((p for p in manifest['packages'] if p['name'] == package_name), None)
                if package is not None and package.get('type') == 'git':
                    package_dir = repo / manifest['packagesDir'] / package_name
                    revision = run('external-revision-' + package_name,
                                   ['git', '-C', str(package_dir), 'rev-parse', 'HEAD']).strip()
                    if revision != package['rev']:
                        raise SystemExit(f'Unexpected {package_name} revision: {revision}')
                run('external-build-' + missing,
                    ['lake', '--fail-fast', 'build', '+' + missing + ':olean'])
                prepared_externals.add(missing)
        else:
            command = ['lake', *(['--fail-fast'] if fail_fast else []), 'build']
            run(name, [*command, *('+' + module + ':olean' for module in modules)])

    # Collect independent, smaller proof failures in one pass before starting
    # the full arithmetic closure. Lake reuses these exact compiled artifacts
    # for the interface build; this does not alter the final audit's scope.
    if MODULE_ROOT + '.Interface' in args.modules:
        build('core-build', CORE_MODULES, fail_fast=False)
    # '+' disambiguates genuine module targets; :olean avoids unrelated binaries.
    if args.serial_build:
        for index, module in enumerate(args.modules, 1):
            build(f'build-{index}-{module.rsplit(".", 1)[-1]}', [module])
    else:
        build('build', args.modules)
    audit = '\n'.join('import ' + module for module in args.modules) + '''
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let nsPrefix : Name := `HeckeSkeleton.Moments.EngineStep
  let names := (env.constants.toList.filterMap fun (name, _) =>
    if nsPrefix.isPrefixOf (privateToUserName name) then some name else none).toArray.qsort Name.lt
  unless !names.isEmpty do
    throwError "No MOM_ENGINE_STEP declarations found"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"AXIOMS {name}: {dependencies}"
  logInfo m!"MOM_ENGINE_STEP AXIOM AUDIT PASSED: {names.size} declarations"
'''
    audit = audit.replace('`HeckeSkeleton.Moments.EngineStep', '`' + args.namespace)
    audit += '\n'.join('#print axioms ' + name for name in args.declaration) + '\n'
    audit_file = evidence / 'AxiomAudit.lean'
    audit_file.write_text(audit)
    if args.checked_project_cache:
        # Match the verifier's precedence exactly: verified project objects,
        # including vendored modules, precede ordinary package build paths.
        compiler = run('audit-compiler', ['lake', 'env', 'which', 'lean']).strip()
        raw_path = run('audit-import-path', ['lake', 'env', 'printenv', 'LEAN_PATH']).strip()
        project_out = (repo / '.lake/build/lib/lean').resolve()
        other_paths = [(repo / path).resolve() for path in raw_path.split(os.pathsep)]
        audit_env = dict(os.environ)
        audit_env['LEAN_PATH'] = os.pathsep.join(map(str, [project_out] + [p for p in other_paths if p != project_out]))
        output = run('axioms', [compiler, '-j1', str(audit_file)], audit_env)
    else:
        output = run('axioms', ['lake', 'env', 'lean', str(audit_file)])
    if 'MOM_ENGINE_STEP AXIOM AUDIT PASSED:' not in output:
        raise SystemExit('The axiom audit success marker is missing')
    for relative, digest in sources.items():
        if hashlib.sha256((repo / relative).read_bytes()).hexdigest() != digest:
            raise SystemExit('A source changed during verification: ' + relative)
    print('PASS: target modules compiled and every task declaration has permitted axioms.', flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
