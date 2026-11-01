#!/usr/bin/env python3
"""Observe a complete, byte-reversible EOI copy; never replace native verification.

Run this only in the independent D diagnostic job, after the normal pinned
toolchain and project cache setup. The original roots job remains independent.
--prepare-only performs source/instrumentation checks without invoking Lean.
"""
from __future__ import annotations

import argparse
from collections import deque
import difflib
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time
import tomllib


SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalOriginalIntegral.lean')
SOURCE_SHA = 'ea8dcb5d7e168c1c3aab5bb16b9b8e739ad2a9769c31f3530210a97363be9c8d'
MODULE_ROOT = 'HeckeSkeleton.Moments.MOM_ENGINE_STEP'
STEP_DIRECTORY = SOURCE.parent
LEAN_VERSION = '4.35.0-rc3'
LEAN_COMMIT = '470d5ce1400764999581fd26d5d72b00d990b0f4'
MATHLIB_COMMIT = '0493595ecd5da8ef14742febab99728f98e948e8'
EXPECTED_IMPORTS = [
    MODULE_ROOT + '.ExceptionalOriginalLabel',
    MODULE_ROOT + '.WeightedNestedFourierMeasure',
    MODULE_ROOT + '.NestedHybridKernel',
]
EXPECTED_LEAN_OPTIONS = {'autoImplicit': False, 'relaxedAutoImplicit': False}
EXPECTED_STEP_MODULES = 1009
EXPECTED_INTERFACE_IMPORTS = 1008
NATIVE_TIMEOUT_SECONDS = 150
TERMINATION_GRACE_SECONDS = 10
MARKER_PREFIX = 'MOM_TRACE EOI ea8dcb5d'
INPUT_NAME = 'MomEngineDExceptionalOriginalIntegralDiagnostic.lean'


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def write_json(path: Path, value: object) -> None:
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')
    temporary.replace(path)


def instrument(source: bytes) -> tuple[bytes, list[dict]]:
    """Insert run_cmd/run_tac marker blocks only; retain every original byte."""
    require(sha(source) == SOURCE_SHA, 'EOI source differs from the reviewed frozen source')
    text = source.decode('utf-8')
    entries: list[dict] = []

    def position(anchor: str) -> int:
        require(text.count(anchor) == 1, 'Anchor is not unique: ' + repr(anchor))
        return text.index(anchor)

    def add(offset: int, label: str, *, kind: str = 'TAC', indent: int = 2,
            inline: str | None = None) -> None:
        require(0 <= offset <= len(text), 'Marker offset outside original source')
        require(not any(entry['label'] == label for entry in entries), 'Duplicate marker label')
        message = f'{MARKER_PREFIX} {kind} {label}'
        keyword = 'run_cmd' if kind == 'CMD' else 'run_tac'
        if inline is None:
            padding = '' if kind == 'CMD' else ' ' * indent
            block = (f'{padding}{keyword}\n'
                     f'{padding}  IO.eprintln "{message}"\n'
                     f'{padding}  (← IO.getStderr).flush\n')
        else:
            require(kind == 'TAC', 'Only tactic markers may be inline')
            # Braces delimit doSeq, so the following original tactic cannot be
            # consumed as another IO statement in the marker's do block.
            action = f'run_tac {{ IO.eprintln "{message}"; (← IO.getStderr).flush }}'
            block = action + '; ' if inline == 'before' else '; ' + action
        entries.append({
            'label': label, 'kind': kind, 'inline': inline,
            'original_offset_characters': offset,
            'original_offset_bytes': len(text[:offset].encode('utf-8')),
            'original_line': text.count('\n', 0, offset) + 1,
            'text': block,
        })

    structure_doc = position('/-- Proved Fourier control; this is constructed from weighted L1,')
    control_decl = position('def exceptionalFourierControl (J₁ J₂ : ℕ) :')
    after_control = position('variable {F : Type} [Field F] [NumberField F]')
    integrable_decl = position('theorem exceptionalMagnitude_nested_integrable\n')
    after_integrable = position('variable {ΨL ΨR : Ideal (𝓞 F) →* ℂ}')
    main_doc = position('/-- The complete actual source bound is integrated with both original')
    after_main = position('end SecondSideFrame\n')

    # Put markers before each doc comment, not between the comment and its declaration.
    add(structure_doc, 'DECL_1_STRUCTURE_BEFORE', kind='CMD')
    add(control_decl, 'DECL_1_STRUCTURE_AFTER', kind='CMD')
    add(control_decl, 'DECL_2_CONTROL_BEFORE', kind='CMD')
    add(position('  have h : Nonempty (ExceptionalFourierControl'), 'CONTROL_BODY_ENTER')
    add(position('    obtain ⟨s₁, s₂, C, hC, hmass⟩ :='), 'CONTROL_OBTAIN_BEFORE', indent=4)
    add(position('    exact ⟨⟨s₁, s₂, C, hC, hmass⟩⟩'), 'CONTROL_OBTAIN_RETURNED', indent=4)
    add(after_control, 'CONTROL_PROOF_RETURNED')
    add(after_control, 'DECL_2_CONTROL_AFTER', kind='CMD')
    add(integrable_decl, 'DECL_3_INTEGRABLE_BEFORE', kind='CMD')
    add(position('  letI := nestedFourierMeasure_finite F₁ F₂'), 'INTEGRABLE_BODY_ENTER')
    add(position('  exact nested_joint_magnitude_integrable _ _ _ _ _ _ _ _ _'),
        'INTEGRABLE_EXACT_BEFORE')
    add(after_integrable, 'INTEGRABLE_PROOF_RETURNED')
    add(after_integrable, 'DECL_3_INTEGRABLE_AFTER', kind='CMD')
    add(main_doc, 'DECL_4_SOURCE_BEFORE', kind='CMD')

    add(position('  let major := firstCost *\n'), 'MAIN_BODY_ENTER')
    add(position('  have hmajor : 0 ≤ major := by\n'), 'HMAJOR_BEFORE')
    add(position('    have hvolume := (exceptionalTerminalConstant_pos'), 'HMAJOR_ENTER', indent=4)
    add(position('    positivity\n'), 'HMAJOR_POSITIVITY_BEFORE', indent=4)
    hpoint = position('  have hpoint (z : U × E) :\n')
    add(hpoint, 'HMAJOR_PROOF_RETURNED', indent=4)
    add(hpoint, 'HMAJOR_RETURNED')
    add(hpoint, 'HPOINT_BEFORE')
    hs = position('    have hs := exceptional_original_label_from_atoms\n')
    add(hs, 'HPOINT_ENTER', indent=4)
    add(hs, 'HPOINT_HS_BEFORE', indent=4)
    convert = position('    convert hs using 1 <;> dsimp only [major] <;> ring\n')
    add(convert, 'HPOINT_HS_RETURNED', indent=4)
    add(convert, 'HPOINT_CONVERT_BEFORE', indent=4)
    hi = position('  have hi := (left.exceptionalMagnitude_nested_integrable')
    add(hi, 'HPOINT_CONVERT_RETURNED', indent=4)
    add(hi, 'HPOINT_RETURNED')
    add(hi, 'HI_BEFORE')
    hsource = position('  have hsource := hi.const_mul\n')
    add(hsource, 'HI_RETURNED')
    add(hsource, 'HSOURCE_BEFORE')
    calc = position('  calc\n')
    add(calc, 'HSOURCE_RETURNED')
    add(calc, 'CALC_BEFORE')

    add(position('      apply integral_mono hsource\n'), 'CALC_1_INTEGRAL_MONO_BEFORE', indent=6)
    add(position('      intro z\n'), 'CALC_1_INTEGRAL_MONO_RETURNED', indent=6)
    add(position('      exact (hpoint z).trans'), 'CALC_1_POINTWISE_BEFORE', indent=6)
    add(position('    _ = major * (heightConstant *\n'), 'CALC_1_PROOF_RETURNED', indent=6)
    add(position('      rw [integral_const_mul, integral_const_mul]\n'),
        'CALC_2_CONST_MUL_BEFORE', indent=6)
    calc_third = position('    _ ≤ major * (heightConstant *\n')
    add(calc_third, 'CALC_2_PROOF_RETURNED', indent=6)
    add(calc_third, 'CALC_3_LEFT_BOUNDARY', indent=6)

    # The third calc RHS is a pure term. Leave it entirely intact. Its boundary
    # markers live at the end of calc-2's by block and inside calc-4's by block;
    # they are not an added by/exact wrapper around the third original term.
    final_line = '    _ = _ := by dsimp only [major]; ring\n'
    final_start = position(final_line)
    dsimp = final_start + len('    _ = _ := by ')
    ring = final_start + len('    _ = _ := by dsimp only [major]; ')
    ring_end = final_start + len(final_line) - 1
    add(dsimp, 'CALC_3_RIGHT_BOUNDARY', inline='before')
    add(dsimp, 'CALC_4_DSIMP_BEFORE', inline='before')
    add(ring, 'CALC_4_RING_BEFORE', inline='before')
    add(ring_end, 'CALC_4_RING_RETURNED', inline='after')
    add(after_main, 'MAIN_CALC_RETURNED')
    add(after_main, 'DECL_4_SOURCE_AFTER', kind='CMD')

    first_print = position('#print axioms HeckeSkeleton.Moments.EngineStep.exceptionalFourierControl\n')
    second_print = position('#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.exceptional_original_label_integral_from_atoms\n')
    add(first_print, 'PRINT_1_BEFORE', kind='CMD')
    add(second_print, 'PRINT_1_AFTER', kind='CMD')
    add(second_print, 'PRINT_2_BEFORE', kind='CMD')
    add(len(text), 'PRINT_2_AFTER', kind='CMD')

    entries.sort(key=lambda entry: entry['original_offset_characters'])
    chunks: list[str] = []
    cursor = character_position = byte_position = 0
    for entry in entries:
        offset = entry['original_offset_characters']
        prefix = text[cursor:offset]
        chunks.append(prefix)
        character_position += len(prefix)
        byte_position += len(prefix.encode('utf-8'))
        entry['diagnostic_offset_characters'] = character_position
        entry['diagnostic_offset_bytes'] = byte_position
        chunks.append(entry['text'])
        character_position += len(entry['text'])
        byte_position += len(entry['text'].encode('utf-8'))
        cursor = offset
    chunks.append(text[cursor:])
    diagnostic = ''.join(chunks).encode('utf-8')
    require(restore(diagnostic, entries) == source, 'Marker reversal did not reproduce original bytes')
    original_prints = re.findall(rb'^#print axioms .*$', source, flags=re.MULTILINE)
    diagnostic_prints = re.findall(rb'^#print axioms .*$', diagnostic, flags=re.MULTILINE)
    require(original_prints == diagnostic_prints and len(original_prints) == 2,
            'Original two axiom prints were not preserved exactly')
    require(re.findall(rb'^import .*$', diagnostic, re.MULTILINE)
            == re.findall(rb'^import .*$', source, re.MULTILINE), 'Imports changed in diagnostic copy')
    return diagnostic, entries


def restore(diagnostic: bytes, entries: list[dict]) -> bytes:
    restored = diagnostic
    for entry in reversed(entries):
        start = entry['diagnostic_offset_bytes']
        block = entry['text'].encode('utf-8')
        require(restored[start:start + len(block)] == block, 'Inserted marker bytes changed')
        restored = restored[:start] + restored[start + len(block):]
    return restored


def git_text(repo: Path, *arguments: str) -> str:
    return subprocess.check_output(['git', *arguments], cwd=repo, text=True).strip()


def tracked_snapshot(repo: Path) -> dict:
    paths = subprocess.check_output(['git', 'ls-files', '-z'], cwd=repo).decode('utf-8').split('\0')
    hashes = {path: sha((repo / path).read_bytes()) if (repo / path).is_file() else None
              for path in paths if path}
    return {'head': git_text(repo, 'rev-parse', 'HEAD'),
            'tree': git_text(repo, 'rev-parse', 'HEAD^{tree}'),
            'tracked_sha256': hashes, 'tracked_file_count': len(hashes)}


def check_original_configuration(repo: Path, before: dict) -> dict:
    tracked = before['tracked_sha256']
    step_paths = {path for path in tracked
                  if path.startswith(str(STEP_DIRECTORY) + '/') and path.endswith('.lean')}
    require(len(step_paths) == EXPECTED_STEP_MODULES, 'Original STEP module count differs from 1009')
    interface = (repo / STEP_DIRECTORY / 'Interface.lean').read_text()
    imports = re.findall(r'^import ([A-Za-z_][A-Za-z_0-9.]*)$', interface, re.MULTILINE)
    expected_modules = {path[:-5].replace('/', '.') for path in step_paths
                        if path != str(STEP_DIRECTORY / 'Interface.lean')}
    require(len(imports) == EXPECTED_INTERFACE_IMPORTS and set(imports) == expected_modules,
            'Original Interface does not import exactly the other 1008 STEP modules')
    configuration = tomllib.loads((repo / 'lakefile.toml').read_text())
    options = configuration.get('leanOptions', {})
    require(options == EXPECTED_LEAN_OPTIONS, 'Project leanOptions differ from the original options')
    toolchain = (repo / 'lean-toolchain').read_text().strip()
    require(toolchain == 'leanprover/lean4:v' + LEAN_VERSION, 'Unexpected lean-toolchain file')
    return {'STEP_module_count': len(step_paths), 'Interface_import_count': len(imports),
            'Interface_import_set_matches_all_original_STEP_modules': True,
            'leanOptions': options, 'lean_toolchain_file': toolchain,
            'heartbeat_override': None, 'lean_async_override': None,
            'native_threads': 2, 'LEAN_NUM_THREADS': '2',
            'diagnostic_only_options': {'profiler': True, 'stderrAsMessages': False}}


def normalized_return_code(raw_code: int) -> int:
    return raw_code if raw_code >= 0 else 128 - raw_code


class Interrupted(Exception):
    def __init__(self, signum: int):
        super().__init__(f'Diagnostic driver received signal {signum}')
        self.signum = signum


def stop_process_group(process: subprocess.Popen) -> None:
    if process.poll() is not None:
        return
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        # The process can exit between poll() and killpg(). Still reap it so
        # returncode is populated before the stage's exit evidence is written.
        process.wait()
        return
    try:
        process.wait(timeout=TERMINATION_GRACE_SECONDS)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()


def run_stage(repo: Path, evidence: Path, result: dict, name: str,
              command: list[str], timeout: int) -> dict:
    started = time.monotonic()
    record = {'step': name, 'command': command, 'cwd': str(repo),
              'timeout_seconds': timeout, 'status': 'running'}
    result['commands'].append(record)
    write_json(evidence / 'diagnostic-result.json', result)
    print(json.dumps({'EOI_DIAGNOSTIC_STAGE_START': record}), flush=True)
    child_environment = os.environ.copy()
    child_environment['LEAN_NUM_THREADS'] = '2'
    process = None
    timed_out = False
    try:
        with (evidence / f'{name}.log').open('wb', buffering=0) as log:
            process = subprocess.Popen(command, cwd=repo, stdout=log, stderr=subprocess.STDOUT,
                                       start_new_session=True, env=child_environment)
            record['pid'] = process.pid
            deadline = started + timeout
            next_progress = started + 30
            while process.poll() is None:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    timed_out = True
                    stop_process_group(process)
                    break
                try:
                    process.wait(timeout=min(10, remaining))
                except subprocess.TimeoutExpired:
                    if time.monotonic() >= next_progress:
                        print(json.dumps({'EOI_DIAGNOSTIC_RUNNING': name,
                                          'elapsed_seconds': round(time.monotonic() - started, 1)}),
                              flush=True)
                        next_progress = time.monotonic() + 30
    finally:
        if process is not None:
            stop_process_group(process)
            record.update(exit_code_raw=process.returncode,
                          exit_code_normalized=normalized_return_code(process.returncode),
                          terminating_signal=(-process.returncode if process.returncode < 0 else None))
        record.update(status='finished' if process is not None else 'spawn_failed',
                      timed_out=timed_out, elapsed_seconds=time.monotonic() - started)
        write_json(evidence / f'{name}-status.json', record)
        write_json(evidence / 'diagnostic-result.json', result)
        print(json.dumps({'EOI_DIAGNOSTIC_STAGE_END': record}), flush=True)
    return record


def emit_native_evidence(evidence: Path) -> dict:
    native_log = evidence / 'native.log'
    status_path = evidence / 'native-status.json'
    status = json.loads(status_path.read_text()) if status_path.exists() else {}
    if not native_log.exists():
        print('EOI DIAGNOSTIC: the instrumented native compiler was not started.', flush=True)
        summary = {'native_started': False, 'last_tactic_markers': [], 'error_lines': []}
        write_json(evidence / 'marker-and-error-summary.json', summary)
        return summary
    markers, tactic_markers, errors = deque(maxlen=20), deque(maxlen=16), deque(maxlen=24)
    marker_count = error_count = 0
    log_hash = hashlib.sha256()
    error_pattern = re.compile(r'\berror(?:\[[^\]]*\])?:|maximum recursion depth|'
                               r'maximum number of heartbeats|\bPANIC\b|\bpanicked\b|'
                               r'\bfatal\b|\bfailed\b', re.IGNORECASE)
    with native_log.open('rb') as stream:
        for raw_line in stream:
            log_hash.update(raw_line)
            line = raw_line.decode('utf-8', errors='replace').rstrip('\r\n')
            if MARKER_PREFIX in line:
                marker_count += 1
                markers.append(line)
                if f'{MARKER_PREFIX} TAC ' in line:
                    tactic_markers.append(line)
            if error_pattern.search(line):
                error_count += 1
                errors.append(line)
    summary = {'native_started': 'pid' in status, 'marker_count': marker_count,
               'last_tactic_markers': list(tactic_markers), 'last_any_markers': list(markers),
               'error_line_count': error_count, 'error_lines': list(errors),
               'native_log_sha256': log_hash.hexdigest(),
               'native_log_bytes': native_log.stat().st_size,
               'interpretation': 'Diagnostic emission order only; default async may interleave command/proof work. '
                                 'Calc-3 markers are adjacent proof boundaries, not wrappers around its pure term.'}
    write_json(evidence / 'marker-and-error-summary.json', summary)
    print('EOI DIAGNOSTIC last proof markers and error lines (not acceptance):', flush=True)
    print(json.dumps(summary, indent=2, ensure_ascii=False), flush=True)
    print('EOI DIAGNOSTIC complete native.log begins:', flush=True)
    with native_log.open('r', errors='replace') as stream:
        for line in stream:
            print(line, end='', flush=True)
    print('\nEOI DIAGNOSTIC complete native.log ends.', flush=True)
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path.cwd())
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--expected-head', default=os.environ.get('EOI_DIAG_EXPECTED_HEAD'))
    parser.add_argument('--dependency-timeout', type=int, default=900)
    parser.add_argument('--prepare-only', action='store_true')
    args = parser.parse_args()
    require(args.dependency_timeout > 0, 'Dependency timeout must be positive')
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    require(not (evidence / 'diagnostic-result.json').exists(), 'Evidence directory already contains a run')
    started = time.monotonic()
    result = {'scope': 'complete instrumented EOI source; diagnostic only',
              'original_module_acceptance': False, 'mode': 'prepare-only' if args.prepare_only else 'native-diagnostic',
              'driver_sha256': sha(Path(__file__).read_bytes()), 'source_path': str(SOURCE),
              'expected_source_sha256': SOURCE_SHA, 'commands': [],
              'native_timeout_seconds': NATIVE_TIMEOUT_SECONDS,
              'heartbeat_override': None, 'lean_async_override': None,
              'profiler_is_diagnostic_only': True, 'original_roots_job_is_independent': True}
    before = diagnostic = None
    input_path = repo / INPUT_NAME
    owned_input = False
    output_directory = None
    driver_exit = 2

    def interrupted(signum, _frame):
        raise Interrupted(signum)

    previous_handlers = {signum: signal.signal(signum, interrupted)
                         for signum in (signal.SIGTERM, signal.SIGINT)}
    try:
        before = tracked_snapshot(repo)
        write_json(evidence / 'tracked-source-before.json', before)
        expected_head = args.expected_head or before['head']
        require(before['head'] == expected_head, 'Checkout differs from expected exact head')
        result.update(head=before['head'], tree=before['tree'], expected_head=expected_head)
        result['original_configuration'] = check_original_configuration(repo, before)
        source = (repo / SOURCE).read_bytes()
        require(sha(source) == SOURCE_SHA, 'Original EOI SHA256 does not match reviewed source')
        original_imports = re.findall(r'^import ([A-Za-z_][A-Za-z_0-9.]*)$', source.decode(), re.MULTILINE)
        require(original_imports == EXPECTED_IMPORTS, 'Original three import lines differ')
        result.update(source_sha256=sha(source), original_imports=original_imports,
                      import_source_sha256={module: sha((repo / (module.replace('.', '/') + '.lean')).read_bytes())
                                            for module in original_imports})
        (evidence / 'ExceptionalOriginalIntegral.original.lean').write_bytes(source)
        diagnostic, insertions = instrument(source)
        (evidence / INPUT_NAME).write_bytes(diagnostic)
        result['diagnostic_source_sha256'] = sha(diagnostic)
        write_json(evidence / 'instrumentation.json', {
            'source_sha256': sha(source), 'diagnostic_sha256': sha(diagnostic),
            'removed_markers_restore_exact_source': restore(diagnostic, insertions) == source,
            'original_two_prints_preserved': True, 'original_three_imports_preserved': True,
            'insertion_count': len(insertions), 'insertions': insertions,
            'calc_3_note': 'Pure original term untouched; markers use adjacent by-block boundaries.',
        })
        (evidence / 'markers.diff').write_text(''.join(difflib.unified_diff(
            source.decode().splitlines(True), diagnostic.decode().splitlines(True),
            fromfile=str(SOURCE), tofile=INPUT_NAME)))
        for filename in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
            (evidence / filename).write_bytes((repo / filename).read_bytes())
        write_json(evidence / 'diagnostic-result.json', result)

        if args.prepare_only:
            result['outcome'] = 'static_preparation_complete_no_Lean_execution'
            driver_exit = 0
        else:
            version = run_stage(repo, evidence, result, 'toolchain', ['lake', 'env', 'lean', '--version'], 30)
            version_text = (evidence / 'toolchain.log').read_text(errors='replace')
            require(version['exit_code_raw'] == 0 and LEAN_VERSION in version_text and LEAN_COMMIT in version_text,
                    'Pinned Lean executable identity check failed')
            mathlib = git_text(repo / '.lake/packages/mathlib', 'rev-parse', 'HEAD')
            require(mathlib == MATHLIB_COMMIT, 'Pinned mathlib revision differs')
            result.update(lean_version_output=version_text.strip(), mathlib_commit=mathlib)
            dependencies = run_stage(repo, evidence, result, 'dependencies',
                                     ['lake', 'build', *('+' + module + ':olean' for module in original_imports)],
                                     args.dependency_timeout)
            if dependencies['exit_code_raw'] != 0 or dependencies['timed_out']:
                result['outcome'] = 'original_imports_failed_diagnostic_not_started'
                print('EOI DIAGNOSTIC complete failed dependency log begins:', flush=True)
                with (evidence / 'dependencies.log').open(errors='replace') as log:
                    for line in log:
                        print(line, end='', flush=True)
                print('\nEOI DIAGNOSTIC complete failed dependency log ends.', flush=True)
                driver_exit = 124 if dependencies['timed_out'] else dependencies['exit_code_normalized']
            else:
                require((repo / SOURCE).read_bytes() == source, 'Original EOI changed during dependency build')
                require(not input_path.exists(), 'Diagnostic input path already exists; refusing to overwrite')
                with input_path.open('xb') as destination:
                    destination.write(diagnostic)
                owned_input = True
                output_directory = tempfile.TemporaryDirectory(prefix='mom-engine-d-eoi-')
                output = Path(output_directory.name)
                result.update(input_path=str(input_path), compiler_output_directory=str(output))
                native = run_stage(repo, evidence, result, 'native',
                                   ['lake', 'env', 'lean', '-j2', '-DautoImplicit=false',
                                    '-DrelaxedAutoImplicit=false', '-Dprofiler=true', '-DstderrAsMessages=false',
                                    '-o', str(output / 'EOIDiagnostic.olean'),
                                    '-i', str(output / 'EOIDiagnostic.ilean'), str(input_path)],
                                   NATIVE_TIMEOUT_SECONDS)
                result['native'] = native
                result['diagnostic_input_unchanged'] = input_path.read_bytes() == diagnostic
                result['compiler_outputs'] = [{'name': path.name, 'bytes': path.stat().st_size,
                                                'sha256': sha(path.read_bytes())}
                                               for path in sorted(output.iterdir()) if path.is_file()]
                result['outcome'] = ('diagnostic_timeout' if native['timed_out'] else
                                     'diagnostic_exited_zero_not_acceptance' if native['exit_code_raw'] == 0 else
                                     'diagnostic_compiler_error')
                driver_exit = 124 if native['timed_out'] else native['exit_code_normalized']
    except Interrupted as error:
        result['driver_error'] = str(error)
        result['outcome'] = 'driver_interrupted'
        driver_exit = 128 + error.signum
    except Exception as error:
        result['driver_error'] = f'{type(error).__name__}: {error}'
        result['outcome'] = 'diagnostic_incomplete'
        driver_exit = 2
    finally:
        # Remove only the owned, unchanged temporary input; never touch source/cache files.
        if owned_input and input_path.exists():
            if input_path.read_bytes() == diagnostic:
                input_path.unlink()
                result['temporary_input_removed'] = True
            else:
                result['temporary_input_removed'] = False
                result['temporary_input_changed'] = True
                driver_exit = 3
        if output_directory is not None:
            output_directory.cleanup()
            result['temporary_compiler_outputs_removed'] = True
        try:
            after = tracked_snapshot(repo)
            write_json(evidence / 'tracked-source-after.json', after)
            if before is not None:
                changed = sorted(path for path in before['tracked_sha256'].keys() | after['tracked_sha256'].keys()
                                 if before['tracked_sha256'].get(path) != after['tracked_sha256'].get(path))
                identity = {'head_before': before['head'], 'head_after': after['head'],
                            'unchanged': not changed and before['head'] == after['head'],
                            'changed_tracked_files': changed,
                            'source_sha256_after': sha((repo / SOURCE).read_bytes())}
                identity['original_EOI_matches_frozen_source'] = identity['source_sha256_after'] == SOURCE_SHA
                result['source_identity'] = identity
                write_json(evidence / 'source-identity.json', identity)
                if not identity['unchanged'] or not identity['original_EOI_matches_frozen_source']:
                    driver_exit = 3
        except Exception as error:
            result['identity_error'] = f'{type(error).__name__}: {error}'
            driver_exit = 3
        result['elapsed_seconds'] = time.monotonic() - started
        result['driver_exit_code'] = driver_exit
        write_json(evidence / 'diagnostic-result.json', result)
        if not args.prepare_only:
            emit_native_evidence(evidence)
        print('EOI DIAGNOSTIC final result (never a verification pass):', flush=True)
        print(json.dumps(result, indent=2, ensure_ascii=False), flush=True)
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)
    return driver_exit


if __name__ == '__main__':
    raise SystemExit(main())
