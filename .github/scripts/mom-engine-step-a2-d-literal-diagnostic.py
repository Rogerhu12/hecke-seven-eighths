#!/usr/bin/env python3
"""Owner read-only support: complete D-owned f499 source with reversible markers.

This is a separate diagnostic module. It does not import or mutate the Actual
0858 script, its guards, any production Lean source, or a normal verifier.
All original imports, declarations, proof text and five axiom prints survive
exact marker removal. All linters, heartbeat and Lean async use their defaults.
Only the owned temporary process session is bounded and cleaned (150 s / 10 s).
This diagnostic never grants native, fresh, production or full-task acceptance.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import threading
import time

EXPECTED_SOURCE = 'f49992a4d96d0e86c404cb0e0138d613d30100b8405e1964b9258349ad4daee0'
EXPECTED_BYTES = 21240
EXPECTED_LEAN = '4.35.0-rc3'
EXPECTED_LEAN_COMMIT = '470d5ce1400764999581fd26d5d72b00d990b0f4'
EXPECTED_MATHLIB = '0493595ecd5da8ef14742febab99728f98e948e8'
SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/OrdinaryLiteralExceptionalLeaf.lean')
SOURCE_FROZEN_D_HEAD = '6fccbe95906cf07f235421ec01a4da1434193514'
SOURCE_BLOB = 'e6a6fb5dbbd15d6ab239db665a27ebf8f0f10625'
PREFIX = 'A2_D_LITERAL_F499_DIAGNOSTIC'
MODULE = 'MomEngineLiteralDiagF49992a4'
TIMEOUT_SECONDS = 150
KILL_AFTER_SECONDS = 10
EXECUTOR_BASE_SCRIPT_SHA256 = '0858bc9e93b1ba60a6d45ae39e694149001689fa29bfd1928ffcaa9696e95ed3'
FALSE_FLAGS = {
    'acceptance_evidence': False, 'original_module_native_was_run': False,
    'original_module_acceptance': False, 'complete_target_module_compiled': False,
    'complete_module_within_five_minutes': False, 'full_task_acceptance': False,
    'compiler_outputs_can_be_restored_as_project_cache': False,
    'production_approval': False, 'candidate_native_validation_performed': False,
    'fresh_axiom_audit_performed': False,
}
EXPECTED_MARKED_SHA256 = '681461a728f500718a1557fe523721a1dd91d6645d95509d21946c7af76ccd4e'
EXPECTED_MARKED_BYTES = 25235
DECLARATIONS = [('OrdinaryExceptionalBinding', 'structure', 47, 49, 65),
 ('exceptional_rows_subset', 'theorem', 73, 73, 78),
 ('exceptional_rows_zero', 'theorem', 80, 80, 87),
 ('exceptionalIntegrand_eq', 'theorem', 89, 91, 149),
 ('exceptionalCost_eq', 'theorem', 154, 156, 162),
 ('ordinaryExceptionalBindingOnCorrelationSupport', 'def', 166, 169, 204),
 ('ordinaryExceptionalCost_eq_frames', 'theorem', 214, 217, 222),
 ('ordinary_exceptional_cost_from_original_atoms', 'theorem', 262, 265, 388)]
TACTIC_BOUNDARIES = [(75, 2, 'ROWS_SUBSET_BEFORE_PROOF'),
 (79, 2, 'ROWS_SUBSET_AFTER_PROOF'),
 (83, 2, 'ROWS_ZERO_BEFORE_PROOF'),
 (88, 2, 'ROWS_ZERO_AFTER_PROOF'),
 (94, 2, 'INTEGRAND_BEFORE_HFULL'),
 (103, 4, 'INTEGRAND_BEFORE_UNFOLD'),
 (113, 8, 'INTEGRAND_BEFORE_COLUMN_RW'),
 (118, 8, 'INTEGRAND_BEFORE_LEFT_COLUMN_PROOF'),
 (130, 8, 'INTEGRAND_BEFORE_RIGHT_COLUMN_PROOF'),
 (142, 8, 'INTEGRAND_BEFORE_ROW_RW'),
 (143, 2, 'INTEGRAND_BEFORE_FINAL_EXACT'),
 (150, 2, 'INTEGRAND_AFTER_FINAL_EXACT'),
 (160, 2, 'COST_BEFORE_PROOF'),
 (163, 2, 'COST_AFTER_PROOF'),
 (189, 4, 'SUPPORT_ROWS_BEFORE_PROOF'),
 (193, 4, 'SUPPORT_ROWS_AFTER_PROOF'),
 (194, 4, 'SUPPORT_ZERO_BEFORE_PROOF'),
 (197, 4, 'SUPPORT_ZERO_AFTER_PROOF'),
 (359, 2, 'ATOMS_BEFORE_HSOURCE'),
 (369, 2, 'ATOMS_HSOURCE_RETURNED'),
 (371, 2, 'ATOMS_HBINDING_RETURNED'),
 (376, 2, 'ATOMS_SCALAR_READY'),
 (380, 6, 'ATOMS_BINDING_BEFORE_RW'),
 (382, 6, 'ATOMS_BINDING_CALC_RETURNED'),
 (385, 6, 'ATOMS_INTEGRAL_BEFORE_RW'),
 (386, 6, 'ATOMS_INTEGRAL_AFTER_RW'),
 (388, 6, 'ATOMS_INTEGRAL_RING_RETURNED'),
 (389, 2, 'ATOMS_FINAL_CALC_RETURNED')]
EXECUTOR_ADAPTATIONS = [("for name in ['CoverHybridPhaseIntegral', 'HybridFiniteLeaf']:",
  "for name in ['OrdinaryExceptionalLabelIntegral', 'ConstantCommonLeaf']:"),
 ("prefix='a2-actual-cc98-diagnostic-'", "prefix='a2-d-literal-f499-diagnostic-'")]
EXECUTOR_BASE_FUNCTION_SHA256 = 'abfb57333a4a8ed0742f9a9bc6d698d937ef988b7d91136b0872dbab38e36be0'
EXECUTOR_ADAPTED_FUNCTION_SHA256 = '61b9e442c9712943c93ffbc4652e7cb08bf4b78279cc749d8394893a3f5ae4ef'


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def instrument(original: bytes) -> tuple[bytes, list[dict], dict]:
    """Pure full-source insertion; deleting the unique marker lines is the inverse."""
    assert len(original) == EXPECTED_BYTES and sha(original) == EXPECTED_SOURCE
    assert PREFIX.encode() not in original
    lines = original.splitlines(keepends=True)
    assert len(lines) == 392 and all(line.endswith(b'\n') for line in lines)
    imports = [line for line in lines if line.startswith(b'import ')]
    assert imports == [
        b'import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryExceptionalLabelIntegral\n',
        b'import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ConstantCommonLeaf\n']
    assert sum(line.startswith(b'#print axioms ') for line in lines) == 5
    assert b'set_option ' not in original and b'as_aux_lemma' not in original
    events = []

    def add(line: int, priority: int, kind: str, indent: int, label: str) -> None:
        assert 1 <= line <= len(lines) + 1
        text = (' ' * indent + ('run_cmd' if kind == 'command' else 'run_tac') +
                ' IO.eprintln "' + PREFIX + ' ' + label + '"\n')
        events.append({'original_insert_before_line': line, 'priority': priority,
                       'kind': kind, 'indent': indent, 'label': label,
                       'inserted_line': text})

    add(3, 0, 'command', 0, 'AFTER_ORIGINAL_IMPORTS')
    for name, kind, start, header, last in DECLARATIONS:
        assert lines[header - 1].startswith((kind + ' ' + name).encode())
        if start != header:
            assert lines[start - 1].startswith(b'/--')
            assert b'-/\n' in b''.join(lines[start - 1:header - 1])
        add(start, 20, 'command', 0, 'BEFORE_HEADER_' + name)
        add(last + 1, 10, 'command', 0, 'COMMAND_CONTINUED_AFTER_' + name)
    for line, indent, label in TACTIC_BOUNDARIES:
        add(line, 0, 'tactic', indent, label)
    add(len(lines) + 1, 20, 'command', 0, 'AFTER_ALL_ORIGINAL_PRINTS')
    events.sort(key=lambda entry: (entry['original_insert_before_line'], entry['priority']))
    assert len(events) == 46 and len({entry['label'] for entry in events}) == 46
    output = []
    manifest = []
    emitted_lines = 0
    for line in range(1, len(lines) + 2):
        for entry in events:
            if entry['original_insert_before_line'] == line:
                emitted_lines += 1
                entry = dict(entry)
                entry['instrumented_line'] = emitted_lines
                manifest.append(entry)
                output.append(entry['inserted_line'].encode())
        if line <= len(lines):
            emitted_lines += 1
            output.append(lines[line - 1])
    marked = b''.join(output)
    assert len(marked) == EXPECTED_MARKED_BYTES and sha(marked) == EXPECTED_MARKED_SHA256
    marker_lines = {entry['inserted_line'].encode() for entry in manifest}
    assert len(marker_lines) == 46 and all(marked.count(line) == 1 for line in marker_lines)
    restored = b''.join(line for line in marked.splitlines(keepends=True) if line not in marker_lines)
    assert restored == original
    assert [line for line in marked.splitlines(keepends=True) if line not in marker_lines] == lines
    assert all(marked.splitlines(keepends=True)[entry['instrumented_line'] - 1] ==
               entry['inserted_line'].encode() for entry in manifest)
    # No marker may split an original declaration doccomment from its header.
    for name, kind, start, header, last in DECLARATIONS:
        if start != header:
            attachment = b''.join(lines[start - 1:header])
            assert marked.count(attachment) == 1, name
    # This declaration has a direct proof term, not a tactic block; leave it intact.
    direct_term = b''.join(lines[216:222])
    assert marked.count(direct_term) == 1
    for prefix in (b'import ', b'#print axioms '):
        assert [line for line in marked.splitlines(keepends=True) if line.startswith(prefix)] == [
            line for line in lines if line.startswith(prefix)]
    assert b'set_option ' not in marked and b'as_aux_lemma' not in marked
    checks = {
        'marker_count': 46, 'declaration_count': 8,
        'command_marker_count': 18, 'tactic_marker_count': 28,
        'original_import_count': 2, 'original_print_axioms_count': 5,
        'byte_reversal_verified': True, 'all_original_lines_preserved_in_order': True,
        'doccomment_associations_verified': True, 'direct_term_frames_proof_unchanged': True,
        'all_original_data_headers_and_proofs_preserved_after_marker_removal': True,
        'new_warning_scope_count': 0, 'warning_scope_count': 0,
        'all_original_linters_default': True,
        'original_full_source_sha256': sha(original), 'original_full_source_bytes': len(original),
        'diagnostic_source_sha256': sha(marked), 'diagnostic_source_bytes': len(marked),
        'full_original_module_copy_used': True,
    }
    return marked, manifest, checks


def execute(repo: Path, evidence: Path, marked: bytes, result: dict) -> None:
    version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=repo, text=True)
    assert EXPECTED_LEAN in version and EXPECTED_LEAN_COMMIT in version, version
    mathlib = subprocess.check_output(['git', '-C', str(repo / '.lake/packages/mathlib'),
                                      'rev-parse', 'HEAD'], text=True).strip()
    assert mathlib == EXPECTED_MATHLIB, mathlib
    for name in ['OrdinaryExceptionalLabelIntegral', 'ConstantCommonLeaf']:
        assert (repo / '.lake/build/lib/lean/HeckeSkeleton/Moments/MOM_ENGINE_STEP' /
                (name + '.olean')).is_file(), 'Run normal Lake :deps first: ' + name
    result.update(lean_version=version.strip(), mathlib_commit=mathlib,
                  source_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip(),
                  source_tree=subprocess.check_output(['git', 'rev-parse', 'HEAD^{tree}'], cwd=repo, text=True).strip())
    # The package-root flag only determines the name of this temporary module;
    # the original two imports resolve through the normal `lake env` paths.
    with tempfile.TemporaryDirectory(prefix='a2-d-literal-f499-diagnostic-') as temporary:
        directory = Path(temporary)
        source = directory / (MODULE + '.lean')
        source.write_bytes(marked)
        compiler = directory / 'compiler'
        compiler.mkdir()
        command = ['lake', 'env', 'lean', '-j2', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
                   '-DstderrAsMessages=false', '-R', str(directory), '-o', str(compiler / (MODULE + '.olean')),
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
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--evidence', required=True, type=Path)
    parser.add_argument('--run', action='store_true', help='Run the bounded diagnostic; default is pure preparation')
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    assert '.lake' not in evidence.parts
    evidence.mkdir(parents=True, exist_ok=True)
    assert not (evidence / 'result.json').exists(), 'Use a fresh evidence directory'
    original = (repo / SOURCE).read_bytes()
    marked, manifest, checks = instrument(original)
    (evidence / 'OrdinaryLiteralExceptionalLeaf.original.lean').write_bytes(original)
    (evidence / (MODULE + '.lean')).write_bytes(marked)
    write_json(evidence / 'marker-manifest.json', manifest)
    result = {
        **FALSE_FLAGS, **checks,
        'scope': 'Owner read-only diagnostic support of the complete D-owned f499 source; not production acceptance',
        'production_source_and_proof_owner': 'D',
        'owner_support_registration_comment': 6564015416,
        'source_path': str(SOURCE), 'source_sha256': sha(original), 'source_bytes': len(original),
        'source_frozen_D_head': SOURCE_FROZEN_D_HEAD, 'source_git_blob': SOURCE_BLOB,
        'diagnostic_script_sha256': sha(Path(__file__).read_bytes()),
        'executor_base_script_sha256': EXECUTOR_BASE_SCRIPT_SHA256,
        'executor_base_function_sha256': EXECUTOR_BASE_FUNCTION_SHA256,
        'executor_adapted_function_sha256': EXECUTOR_ADAPTED_FUNCTION_SHA256,
        'executor_adaptations': EXECUTOR_ADAPTATIONS,
        'original_Actual_script_imported_or_rebound': False,
        'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'heartbeat_override': None, 'lean_async_override': None, 'profiler_override': None,
        'stderr_option_override': False,
        'stderr_option_reason': 'Diagnostic marker transport only; no linter or normal verifier option changes',
        'warning_option_override': None, 'other_warning_option_override': None,
        'global_warning_option_override': None,
        'timeout_seconds': TIMEOUT_SECONDS, 'kill_after_seconds': KILL_AFTER_SECONDS,
        'lean_job_count': 2, 'started': False, 'status': 'prepared_only', 'timed_out': False,
        'marker_times_are_observed_arrival_only': True,
        'marker_interpretation': 'Quoted marker text in warning output is not a second actual marker event; inspect the complete log.',
    }
    write_json(evidence / 'result.json', result)
    try:
        if args.run:
            assert os.environ.get('LEAN_NUM_THREADS') == '2', 'Expected normal workflow thread setting'
            execute(repo, evidence, marked, result)
    except BaseException as exc:
        result.update(status='diagnostic_harness_error', harness_error=repr(exc))
        raise
    finally:
        result['original_source_unchanged'] = (repo / SOURCE).read_bytes() == original
        assert result['original_source_unchanged']
        result.update(FALSE_FLAGS)
        write_json(evidence / 'result.json', result)
    print(json.dumps({key: result[key] for key in [
        'status', 'source_sha256', 'diagnostic_source_sha256', 'marker_count',
        'byte_reversal_verified', 'all_original_linters_default', 'original_source_unchanged',
        'acceptance_evidence', 'original_module_acceptance', 'production_approval',
        'fresh_axiom_audit_performed']}, ensure_ascii=False), flush=True)
    if args.run and result.get('timed_out'):
        return 124
    code = result.get('diagnostic_exit_code', 0)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
