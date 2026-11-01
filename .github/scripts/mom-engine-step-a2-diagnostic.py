#!/usr/bin/env python3
"""Prepare, or explicitly run, a reversible diagnostic of one frozen full file.

First run normal Lake dependencies in the checkout:
  lake build +HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussFiniteLeaves:deps
Then:
  python3 actual_finite_leaves_diagnostic.py --repo CHECKOUT --evidence EVIDENCE [--run]

Without --run this only validates/instruments the full original source.  This
script never runs a dependency build, edits a tracked file, changes proof
options, or writes compiler products into .lake.  All acceptance flags remain
false, including if the instrumented copy exits successfully.  Marker arrival
times under default async are observational, not declaration-completion times.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import tempfile
import threading
import time

EXPECTED_SOURCE = 'cc98c8a2c5c3c3f6c59695935245f463c84e6e7f7c8292b5062e2d1813d94c87'
EXPECTED_BYTES = 40282
EXPECTED_LEAN = '4.35.0-rc3'
EXPECTED_LEAN_COMMIT = '470d5ce1400764999581fd26d5d72b00d990b0f4'
EXPECTED_MATHLIB = '0493595ecd5da8ef14742febab99728f98e948e8'
SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualGaussFiniteLeaves.lean')
PREFIX = 'A2_ACTUAL_CC98_DIAGNOSTIC'
MODULE = 'MomEngineActualDiagCc98c8a2'
TIMEOUT_SECONDS = 150
KILL_AFTER_SECONDS = 10
ACCEPTANCE = {
    'acceptance_evidence': False,
    'original_module_native_was_run': False,
    'original_module_acceptance': False,
    'complete_target_module_compiled': False,
    'complete_module_within_five_minutes': False,
    'full_task_acceptance': False,
    'compiler_outputs_can_be_restored_as_project_cache': False,
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def instrument(original: bytes) -> tuple[bytes, list[dict], dict]:
    assert len(original) == EXPECTED_BYTES and sha(original) == EXPECTED_SOURCE, \
        'Refusing to instrument a different original source'
    text = original.decode('utf-8')
    assert PREFIX not in text, 'Original already contains diagnostic markers'
    lines = text.splitlines(keepends=True)
    declaration = re.compile(
        r'^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*'
        r'(?:theorem|def|abbrev|instance)\s+([^\s:{(]+)')
    declarations = [(i, m.group(1)) for i, line in enumerate(lines)
                    if (m := declaration.match(line))]
    assert declarations, 'No declarations found'
    doc_blocks = []
    for match in re.finditer(r'^/--.*?-/', text, re.M | re.S):
        start = text.count('\n', 0, match.start())
        end = text.count('\n', 0, match.end())
        doc_blocks.append((start, end))

    def header_start(index: int) -> int:
        # Place run_cmd before the entire docstring, never between a docstring
        # and its declaration.  The frozen file has attributes on header lines.
        for start, end in reversed(doc_blocks):
            if end < index and not ''.join(lines[end + 1:index]).strip():
                return start
        return index

    insertions: dict[int, list[tuple[str, str]]] = defaultdict(list)

    def add(index: int, label: str, kind: str = 'command') -> None:
        statement = ('run_cmd' if kind == 'command' else '  run_tac') + \
            ' IO.eprintln ' + json.dumps(PREFIX + ' ' + label) + '\n'
        insertions[index].append((label, statement))

    # Full original imports are retained.  This is the first added command.
    imports = [i for i, line in enumerate(lines) if line.startswith('import ')]
    assert len(imports) == 2 and imports == [0, 1], 'Import shape changed'
    add(imports[-1] + 1, 'AFTER_ORIGINAL_IMPORTS')
    command_start = re.compile(
        r'^(?:namespace\b|end\b|variable\b|open\b|local notation\b|'
        r'noncomputable section\b|#print\b|/--)')
    checkpoints = {
        'actualRows_withMultiplier_rows',
        'phase_class_eq_fixed_fullCorrelation', 'fixed_fullCorrelation_eq_leaf_sum',
        'phase_class_eq_leaf_sum', 'coveredClassNestedSum_eq_sum',
        'phase_subsetHybridCost_eq_row_sum', 'phase_coverHybridCost_eq_cover_sum',
        'phase_coverHybridNonzeroCost_eq_nested_sum',
        'coverHybridPhaseNonzeroCost_eq_class_sum', 'coveredLeaf_sum_eq_class_sum',
        'coverHybridPhaseNonzeroCost_eq_leaf_sum', 'integral_eq_leafFamily_cost',
        'integral_coverHybridPhaseNonzeroCost_eq_leaf_sum',
        'phase_cost_eq_budgets_leaves', 'integral_phase_cost_eq_budgets_leaves',
    }
    assert checkpoints <= {name for _, name in declarations}, 'A checkpoint declaration is missing'
    for index, name in declarations:
        if name not in checkpoints:
            continue
        add(header_start(index), 'BEFORE_HEADER_' + name)
        end = len(lines)
        for following in range(index + 1, len(lines)):
            if declaration.match(lines[following]) or command_start.match(lines[following]):
                end = header_start(following) if declaration.match(lines[following]) else following
                break
        add(end, 'COMMAND_CONTINUED_AFTER_' + name)

    def body_range(name: str) -> tuple[int, int]:
        matches = [(k, i) for k, (i, n) in enumerate(declarations) if n == name]
        assert len(matches) == 1, ('Declaration not unique', name)
        k, begin = matches[0]
        end = declarations[k + 1][0] if k + 1 < len(declarations) else len(lines)
        return begin, end

    def before_step(name: str, pattern: str, label: str) -> None:
        begin, end = body_range(name)
        matches = [i for i in range(begin, end) if re.match(pattern, lines[i])]
        assert len(matches) == 1, (name, pattern, matches)
        add(matches[0], label, 'tactic')

    phase = 'phase_class_eq_fixed_fullCorrelation'
    for local in ['hkernel', 'hrows', 'hfrequency', 'hweight',
                  'hrowCoefficient', 'hleftCoefficient', 'hrightCoefficient',
                  'hleftPoint', 'hrightPoint']:
        before_step(phase, rf'^  have {local} :=', 'PHASE_BEFORE_' + local)
    before_step(phase, r'^  unfold SecondBlockProfileChart\.hybridClassCost ',
                'PHASE_BEFORE_UNFOLD')
    before_step(phase, r'^  exact phase_seven_argument_congr',
                'PHASE_BEFORE_EXACT_SEVEN_ARGUMENT_CONGR')
    before_step('fixed_fullCorrelation_eq_leaf_sum', r'^  exact\s*$',
                'FIXED_FULL_CORRELATION_BEFORE_PROVIDER_EXACT')
    before_step('phase_class_eq_leaf_sum', r'^  exact ', 'PHASE_PUBLIC_BEFORE_EXACT')
    for local in ['hclasses', 'hleaves']:
        before_step('coverHybridPhaseNonzeroCost_eq_leaf_sum', rf'^  have {local} :',
                    'SUM_PUBLIC_BEFORE_' + local)
    before_step('coverHybridPhaseNonzeroCost_eq_leaf_sum', r'^  exact hclasses\.trans',
                'SUM_PUBLIC_BEFORE_FINAL_EXACT')
    before_step('integral_coverHybridPhaseNonzeroCost_eq_leaf_sum', r'^  exact ',
                'INTEGRAL_PUBLIC_BEFORE_EXACT')
    before_step('phase_cost_eq_budgets_leaves', r'^  change ',
                'TERMINAL_SUM_BEFORE_CHANGE')
    before_step('phase_cost_eq_budgets_leaves', r'^  rw ', 'TERMINAL_SUM_BEFORE_RW')
    before_step('phase_cost_eq_budgets_leaves', r'^  simp only ',
                'TERMINAL_SUM_BEFORE_SIMP')
    before_step('phase_cost_eq_budgets_leaves', r'^  ring\s*$',
                'TERMINAL_SUM_BEFORE_RING')
    before_step('integral_phase_cost_eq_budgets_leaves', r'^  letI := ',
                'TERMINAL_INTEGRAL_BEFORE_FINITE_MEASURE')
    before_step('integral_phase_cost_eq_budgets_leaves', r'^  simp_rw ',
                'TERMINAL_INTEGRAL_BEFORE_SIMP_RW')
    before_step('integral_phase_cost_eq_budgets_leaves', r'^  rw \[integral_add ',
                'TERMINAL_INTEGRAL_BEFORE_INTEGRAL_ADD')
    before_step('integral_phase_cost_eq_budgets_leaves', r'^  rw \[integral_const, ',
                'TERMINAL_INTEGRAL_BEFORE_INTEGRAL_SUM')
    for i, line in enumerate(lines):
        if line.startswith('#print axioms '):
            add(i, 'BEFORE_ORIGINAL_PRINT_' + str(i + 1))
    add(len(lines), 'AFTER_ALL_ORIGINAL_COMMANDS')

    output = []
    manifest = []
    for i in range(len(lines) + 1):
        for label, statement in insertions.get(i, []):
            manifest.append({'label': label, 'original_insert_before_line': i + 1,
                             'instrumented_line': len(output) + 1,
                             'inserted_line': statement,
                             'kind': 'tactic' if statement.startswith('  ') else 'command'})
            output.append(statement)
        if i < len(lines):
            output.append(lines[i])
    marked = ''.join(output).encode('utf-8')
    inserted_lines = {entry['inserted_line'] for entry in manifest}
    restored = ''.join(line for line in output if line not in inserted_lines).encode('utf-8')
    assert restored == original, 'Marker removal did not exactly recover original bytes'
    assert len(inserted_lines) == len(manifest), 'Marker labels not unique'
    for start, end in doc_blocks:
        # No marker may occur after the docstring begins until its associated
        # header, including intervening blank lines.
        following = next((i for i, _ in declarations if i > end), None)
        if following is not None and not ''.join(lines[end + 1:following]).strip():
            assert not any(start < position <= following for position in insertions), \
                ('Marker would change doccomment association', start + 1, following + 1)
    assert [line for line in output if line.startswith('import ')] == \
        [line for line in lines if line.startswith('import ')]
    assert [line for line in output if line.startswith('#print axioms ')] == \
        [line for line in lines if line.startswith('#print axioms ')]
    assert sum(line.startswith('#print axioms ') for line in output) == 2
    return marked, manifest, {'byte_reversal_verified': True, 'doccomment_associations_verified': True,
                              'declaration_count': len(declarations),
                              'checkpoint_declaration_count': len(checkpoints), 'marker_count': len(manifest),
                              'original_import_count': 2, 'original_print_axioms_count': 2}


def execute(repo: Path, evidence: Path, marked: bytes, result: dict) -> None:
    version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=repo, text=True)
    assert EXPECTED_LEAN in version and EXPECTED_LEAN_COMMIT in version, version
    mathlib = subprocess.check_output(['git', '-C', str(repo / '.lake/packages/mathlib'),
                                      'rev-parse', 'HEAD'], text=True).strip()
    assert mathlib == EXPECTED_MATHLIB, mathlib
    for name in ['CoverHybridPhaseIntegral', 'HybridFiniteLeaf']:
        assert (repo / '.lake/build/lib/lean/HeckeSkeleton/Moments/MOM_ENGINE_STEP' /
                (name + '.olean')).is_file(), 'Run normal Lake :deps first: ' + name
    result.update(lean_version=version.strip(), mathlib_commit=mathlib,
                  source_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip(),
                  source_tree=subprocess.check_output(['git', 'rev-parse', 'HEAD^{tree}'], cwd=repo, text=True).strip())
    # The package-root flag only determines the name of this temporary module;
    # the original two imports resolve through the normal `lake env` paths.
    with tempfile.TemporaryDirectory(prefix='a2-actual-cc98-diagnostic-') as temporary:
        directory = Path(temporary)
        source = directory / (MODULE + '.lean')
        source.write_bytes(marked)
        compiler = directory / 'compiler'
        compiler.mkdir()
        command = ['lake', 'env', 'lean', '-j2', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
                   '-R', str(directory), '-o', str(compiler / (MODULE + '.olean')),
                   '-i', str(compiler / (MODULE + '.ilean')), str(source)]
        result.update(command=command, temporary_directory=str(directory),
                      compiler_output_directory=str(compiler), started=True)
        write_json(evidence / 'result.json', result)
        start = time.monotonic()
        observations = []
        read_errors = []
        process = subprocess.Popen(command, cwd=repo, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        result.update(owned_process_pid=process.pid, owned_process_group=process.pid)

        def reader() -> None:
            pending = b''
            try:
                with (evidence / 'complete-output.log').open('wb') as output:
                    assert process.stdout is not None
                    while chunk := process.stdout.read1(65536):
                        output.write(chunk)
                        output.flush()
                        pending += chunk
                        while b'\n' in pending:
                            line, pending = pending.split(b'\n', 1)
                            decoded = line.decode('utf-8', errors='replace')
                            if PREFIX in decoded:
                                observation = {'elapsed_seconds': time.monotonic() - start, 'line': decoded}
                                observations.append(observation)
                                print(json.dumps(observation, ensure_ascii=False), flush=True)
                                write_json(evidence / 'marker-observations.json', observations)
                    if PREFIX.encode() in pending:
                        observations.append({'elapsed_seconds': time.monotonic() - start,
                                             'line': pending.decode('utf-8', errors='replace')})
            except Exception as exc:
                read_errors.append(repr(exc))

        worker = threading.Thread(target=reader, daemon=True)
        worker.start()

        def own_group(sig: signal.Signals) -> None:
            try:
                os.killpg(process.pid, sig)
                result.setdefault('cleanup_signals', []).append(sig.name)
            except ProcessLookupError:
                pass

        old_handlers = {}

        def interrupted(signum, _frame):
            raise InterruptedError('Diagnostic runner interrupted by signal ' + str(signum))

        for sig in (signal.SIGINT, signal.SIGTERM):
            old_handlers[sig] = signal.signal(sig, interrupted)
        try:
            try:
                code = process.wait(timeout=TIMEOUT_SECONDS)
                result['status'] = 'diagnostic_process_finished'
            except subprocess.TimeoutExpired:
                result.update(status='diagnostic_timeout', timed_out=True)
                own_group(signal.SIGTERM)
                try:
                    code = process.wait(timeout=KILL_AFTER_SECONDS)
                except subprocess.TimeoutExpired:
                    own_group(signal.SIGKILL)
                    code = process.wait(timeout=5)
            result['diagnostic_exit_code'] = code
        finally:
            # Only the session created above is signaled.  No process discovery,
            # attaching, pkill, system setting, or other session is involved.
            own_group(signal.SIGTERM)
            if process.poll() is None:
                try:
                    process.wait(timeout=KILL_AFTER_SECONDS)
                except subprocess.TimeoutExpired:
                    own_group(signal.SIGKILL)
                    process.wait(timeout=5)
            own_group(signal.SIGKILL)  # remove any remaining owned descendants
            worker.join(timeout=2)
            for sig, previous in old_handlers.items():
                signal.signal(sig, previous)
            result.update(elapsed_seconds=time.monotonic() - start,
                          diagnostic_exit_code=process.returncode,
                          output_reader_finished=not worker.is_alive(), output_read_errors=read_errors,
                          observed_markers=observations,
                          last_observed_marker=observations[-1] if observations else None,
                          diagnostic_input_unchanged=sha(source.read_bytes()) == sha(marked))
            write_json(evidence / 'marker-observations.json', observations)
    result['temporary_directory_removed'] = not Path(result['temporary_directory']).exists()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--run', action='store_true', help='Run the bounded diagnostic after normal dependencies')
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    assert '.lake' not in evidence.parts, 'Evidence must not be written in .lake'
    evidence.mkdir(parents=True, exist_ok=True)
    assert not (evidence / 'result.json').exists(), 'Use a fresh evidence directory for each attempt'
    original = (repo / SOURCE).read_bytes()
    marked, manifest, checks = instrument(original)
    (evidence / 'ActualGaussFiniteLeaves.original.lean').write_bytes(original)
    (evidence / (MODULE + '.lean')).write_bytes(marked)
    write_json(evidence / 'marker-manifest.json', manifest)
    result = {**ACCEPTANCE, **checks, 'scope': 'Reversible markers on a full temporary copy; diagnostic only',
              'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'source_path': str(SOURCE), 'source_sha256': sha(original), 'source_bytes': len(original),
              'diagnostic_source_sha256': sha(marked), 'diagnostic_source_bytes': len(marked),
              'heartbeat_override': None, 'lean_async_override': None, 'profiler_override': None,
              'stderr_option_override': None, 'warning_option_override': None,
              'timeout_seconds': TIMEOUT_SECONDS, 'kill_after_seconds': KILL_AFTER_SECONDS,
              'started': False, 'status': 'prepared_only', 'timed_out': False,
              'marker_times_are_observed_arrival_only': True}
    write_json(evidence / 'result.json', result)
    try:
        if args.run:
            execute(repo, evidence, marked, result)
    except BaseException as exc:
        result.update(status='diagnostic_harness_error', harness_error=repr(exc))
        raise
    finally:
        result['original_source_unchanged'] = (repo / SOURCE).read_bytes() == original
        result.update(ACCEPTANCE)
        write_json(evidence / 'result.json', result)
    print(json.dumps({key: result[key] for key in ['status', 'source_sha256', 'marker_count',
          'byte_reversal_verified', 'doccomment_associations_verified', 'original_source_unchanged',
          'acceptance_evidence']}, ensure_ascii=False), flush=True)
    # Propagate the diagnostic status; a workflow may continue on this step's
    # failure while still running the independent original native verification.
    # All acceptance flags remain false even when this diagnostic exits zero.
    if args.run and result.get('timed_out'):
        return 124
    code = result.get('diagnostic_exit_code', 0)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
