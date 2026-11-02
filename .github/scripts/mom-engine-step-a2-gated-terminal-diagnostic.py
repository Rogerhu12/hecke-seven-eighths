#!/usr/bin/env python3
"""Complete default-setting GatedGaussStages diagnostic from owner 16927b5c.

This standalone file copies the validated D266a execute lifecycle statically.
It imports no diagnostic wrapper and rebinds no imported guard. Full original
source, including every declaration, data definition, proof, import and axiom
print, is recoverable exactly by deleting marker lines. Normal options remain
unchanged; this bounded temporary module is not native/fresh acceptance.
The owner will select whether to publish it; its existence proves no hotspot.
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

EXPECTED_SOURCE = '74103e801a3bcb1326d9c9dbf5f7b4238b66e034bba021436ad5d7059faf1d96'
EXPECTED_BYTES = 13306
EXPECTED_LINES = 282
EXPECTED_LEAN = '4.35.0-rc3'
EXPECTED_LEAN_COMMIT = '470d5ce1400764999581fd26d5d72b00d990b0f4'
EXPECTED_MATHLIB = '0493595ecd5da8ef14742febab99728f98e948e8'
SOURCE_OWNER_HEAD = '16927b5cb39e3034ac86d3af49e39aae17440af4'
SOURCE_OWNER_TREE = 'caa913a0e45a8bb31db1251a15a69e91732ac921'
SOURCE_BLOB = '7302095dddd59a7b69bc892793ad97cc5403461a'
PREFIX = 'A2_OWNER_GATED_DIAGNOSTIC'
MODULE = 'MomEngineGatedGaussStagesDiag169'
TIMEOUT_SECONDS = 150
KILL_AFTER_SECONDS = 10
EXECUTOR_BASE_SCRIPT_SHA256 = '266a512fec83c659fc03186e46980eca1a698e22c8b8bd9fc36ec0032592f48a'
EXECUTOR_BASE_FUNCTION_SHA256 = '61b9e442c9712943c93ffbc4652e7cb08bf4b78279cc749d8394893a3f5ae4ef'
EXECUTOR_ADAPTED_FUNCTION_SHA256 = '2ea74e462faf59b61f7bc89fc215dd6feaa98661bccafc2c63b740c3f8dbb7f7'
EXECUTOR_ADAPTATIONS = [("for name in ['OrdinaryExceptionalLabelIntegral', 'ConstantCommonLeaf']:",
  "for name in ['FirstSecondCoveredSource', 'ActualGaussFiniteLeaves']:"),
 ("prefix='a2-d-literal-f499-diagnostic-'", "prefix='a2-owner-gated-169-diagnostic-'")]
EXECUTOR_ORIGIN_0858_SCRIPT_SHA256 = '0858bc9e93b1ba60a6d45ae39e694149001689fa29bfd1928ffcaa9696e95ed3'
EXPECTED_MARKED_SHA256 = '494f623054e5922ebda91869589f46002c5081faa85f548c58ecf1a5c0466ae0'
EXPECTED_MARKED_BYTES = 19535
EXPECTED_MARKER_COUNT = 75
DECLARATIONS = [('gated', 59, 57, 74, 'Stage_gated'),
 ('gated_kernel', 75, 75, 80, 'gated_kernel'),
 ('gated_sources', 81, 81, 85, 'gated_sources'),
 ('gated_leftCoefficient_nonzero', 86, 86, 93, 'gated_leftCoefficient_nonzero'),
 ('gated_rightCoefficient_nonzero', 94, 94, 101, 'gated_rightCoefficient_nonzero'),
 ('gated_sourceLeftCoefficient_nonzero', 102, 102, 108, 'gated_sourceLeftCoefficient_nonzero'),
 ('gated_sourceRightCoefficient_nonzero', 109, 109, 115, 'gated_sourceRightCoefficient_nonzero'),
 ('gated', 123, 121, 126, 'StageTerminal_gated'),
 ('gated_leaf_left_nonzero', 134, 132, 142, 'gated_leaf_left_nonzero'),
 ('gated_leaf_right_nonzero', 143, 143, 151, 'gated_leaf_right_nonzero'),
 ('gated', 160, 160, 166, 'Pool_gated'),
 ('gated', 172, 172, 178, 'PoolTerminal_gated'),
 ('gated', 192, 192, 195, 'BlockSecondStages_gated'),
 ('gated', 201, 201, 205, 'BlockSecondTerminal_gated'),
 ('gated', 217, 217, 219, 'ActualSecondStages_gated'),
 ('gated', 225, 225, 227, 'ActualSecondTerminal_gated'),
 ('actual_parent_gated_two_stage_covered_terminal_bound',
  240,
  237,
  276,
  'actual_parent_gated_two_stage_covered_terminal_bound')]
EXPECTED_IMPORTS = ['import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstSecondCoveredSource\n',
 'import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussFiniteLeaves\n']
EXPECTED_PRINTS = ['#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.gated\n',
 '#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.gated_leaf_left_nonzero\n',
 '#print axioms '
 'HeckeSkeleton.Moments.EngineStep.actual_parent_gated_two_stage_covered_terminal_bound\n']
INSERTIONS = [(3, 80, 'command', 0, 'AFTER_ORIGINAL_IMPORTS'),
 (57, 90, 'command', 0, 'BEFORE_HEADER_Stage_gated'),
 (65, 50, 'tactic', 10, 'PROFILE_BEFORE_INTRO'),
 (66, 10, 'tactic', 10, 'PROFILE_AFTER_INTRO'),
 (66, 50, 'tactic', 10, 'PROFILE_BEFORE_CASES'),
 (67, 10, 'tactic', 10, 'PROFILE_AFTER_CASES'),
 (68, 50, 'tactic', 12, 'PROFILE_LEFT_AFTER_RW_BEFORE_SIMP'),
 (69, 5, 'tactic', 12, 'PROFILE_LEFT_AFTER_SIMP'),
 (71, 50, 'tactic', 14, 'PROFILE_RIGHT_AFTER_RW_BEFORE_SIMP'),
 (72, 5, 'tactic', 14, 'PROFILE_RIGHT_AFTER_SIMP'),
 (74, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_Stage_gated'),
 (75, 90, 'command', 0, 'BEFORE_HEADER_gated_kernel'),
 (80, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_gated_kernel'),
 (81, 90, 'command', 0, 'BEFORE_HEADER_gated_sources'),
 (85, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_gated_sources'),
 (86, 90, 'command', 0, 'BEFORE_HEADER_gated_leftCoefficient_nonzero'),
 (91, 50, 'tactic', 2, 'LEFT_NONZERO_BEFORE_INTRO'),
 (92, 10, 'tactic', 2, 'LEFT_NONZERO_AFTER_INTRO'),
 (92, 50, 'tactic', 2, 'LEFT_NONZERO_BEFORE_EXACT'),
 (93, 10, 'tactic', 2, 'LEFT_NONZERO_AFTER_EXACT'),
 (93, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_gated_leftCoefficient_nonzero'),
 (94, 90, 'command', 0, 'BEFORE_HEADER_gated_rightCoefficient_nonzero'),
 (99, 50, 'tactic', 2, 'RIGHT_NONZERO_BEFORE_INTRO'),
 (100, 10, 'tactic', 2, 'RIGHT_NONZERO_AFTER_INTRO'),
 (100, 50, 'tactic', 2, 'RIGHT_NONZERO_BEFORE_EXACT'),
 (101, 10, 'tactic', 2, 'RIGHT_NONZERO_AFTER_EXACT'),
 (101, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_gated_rightCoefficient_nonzero'),
 (102, 90, 'command', 0, 'BEFORE_HEADER_gated_sourceLeftCoefficient_nonzero'),
 (107, 50, 'tactic', 2, 'SOURCE_LEFT_BEFORE_EXACT'),
 (108, 10, 'tactic', 2, 'SOURCE_LEFT_AFTER_EXACT'),
 (108, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_gated_sourceLeftCoefficient_nonzero'),
 (109, 90, 'command', 0, 'BEFORE_HEADER_gated_sourceRightCoefficient_nonzero'),
 (114, 50, 'tactic', 2, 'SOURCE_RIGHT_BEFORE_EXACT'),
 (115, 10, 'tactic', 2, 'SOURCE_RIGHT_AFTER_EXACT'),
 (115, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_gated_sourceRightCoefficient_nonzero'),
 (121, 90, 'command', 0, 'BEFORE_HEADER_StageTerminal_gated'),
 (126, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_StageTerminal_gated'),
 (132, 90, 'command', 0, 'BEFORE_HEADER_gated_leaf_left_nonzero'),
 (140, 50, 'tactic', 2, 'LEAF_LEFT_BEFORE_APPLY'),
 (141, 10, 'tactic', 2, 'LEAF_LEFT_AFTER_APPLY'),
 (141, 50, 'tactic', 2, 'LEAF_LEFT_BEFORE_EXACT'),
 (142, 10, 'tactic', 2, 'LEAF_LEFT_AFTER_EXACT'),
 (142, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_gated_leaf_left_nonzero'),
 (143, 90, 'command', 0, 'BEFORE_HEADER_gated_leaf_right_nonzero'),
 (149, 50, 'tactic', 2, 'LEAF_RIGHT_BEFORE_APPLY'),
 (150, 10, 'tactic', 2, 'LEAF_RIGHT_AFTER_APPLY'),
 (150, 50, 'tactic', 2, 'LEAF_RIGHT_BEFORE_EXACT'),
 (151, 10, 'tactic', 2, 'LEAF_RIGHT_AFTER_EXACT'),
 (151, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_gated_leaf_right_nonzero'),
 (160, 90, 'command', 0, 'BEFORE_HEADER_Pool_gated'),
 (166, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_Pool_gated'),
 (172, 90, 'command', 0, 'BEFORE_HEADER_PoolTerminal_gated'),
 (178, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_PoolTerminal_gated'),
 (192, 90, 'command', 0, 'BEFORE_HEADER_BlockSecondStages_gated'),
 (195, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_BlockSecondStages_gated'),
 (201, 90, 'command', 0, 'BEFORE_HEADER_BlockSecondTerminal_gated'),
 (205, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_BlockSecondTerminal_gated'),
 (217, 90, 'command', 0, 'BEFORE_HEADER_ActualSecondStages_gated'),
 (219, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_ActualSecondStages_gated'),
 (225, 90, 'command', 0, 'BEFORE_HEADER_ActualSecondTerminal_gated'),
 (227, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_ActualSecondTerminal_gated'),
 (237, 90, 'command', 0, 'BEFORE_HEADER_actual_parent_gated_two_stage_covered_terminal_bound'),
 (268, 50, 'tactic', 2, 'PARENT_BEFORE_OBTAIN'),
 (272, 10, 'tactic', 2, 'PARENT_AFTER_OBTAIN'),
 (272, 50, 'tactic', 2, 'PARENT_BEFORE_REFINE'),
 (274, 10, 'tactic', 2, 'PARENT_AFTER_REFINE'),
 (274, 50, 'tactic', 2, 'PARENT_BEFORE_INTRO'),
 (275, 10, 'tactic', 2, 'PARENT_AFTER_INTRO'),
 (275, 50, 'tactic', 2, 'PARENT_BEFORE_EXACT'),
 (276, 10, 'tactic', 2, 'PARENT_AFTER_EXACT'),
 (276,
  80,
  'command',
  0,
  'COMMAND_CONTINUED_AFTER_actual_parent_gated_two_stage_covered_terminal_bound'),
 (279, 80, 'command', 0, 'BEFORE_ORIGINAL_PRINT_279'),
 (280, 80, 'command', 0, 'BEFORE_ORIGINAL_PRINT_280'),
 (281, 80, 'command', 0, 'BEFORE_ORIGINAL_PRINT_281'),
 (283, 99, 'command', 0, 'AFTER_ALL_ORIGINAL_COMMANDS')]
SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/GatedGaussStages.lean')
FALSE_FLAGS = {
    'acceptance_evidence': False, 'original_module_native_was_run': False,
    'original_module_acceptance': False, 'complete_target_module_compiled': False,
    'complete_module_within_five_minutes': False, 'full_task_acceptance': False,
    'compiler_outputs_can_be_restored_as_project_cache': False,
    'production_approval': False, 'candidate_native_validation_performed': False,
    'fresh_axiom_audit_performed': False,
}

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def instrument(original: bytes) -> tuple[bytes, list[dict], dict]:
    """Pure exact whole-source insertion; all original lines survive both inverses."""
    assert len(original) == EXPECTED_BYTES and sha(original) == EXPECTED_SOURCE
    assert hashlib.sha1(b'blob ' + str(len(original)).encode() + b'\0' + original).hexdigest() == SOURCE_BLOB
    assert PREFIX.encode() not in original
    lines = original.splitlines(keepends=True)
    assert len(lines) == EXPECTED_LINES and all(line.endswith(b'\n') for line in lines)
    assert [line.decode() for line in lines if line.startswith(b'import ')] == EXPECTED_IMPORTS
    assert [line.decode() for line in lines if line.startswith(b'#print axioms ')] == EXPECTED_PRINTS
    assert b'set_option ' not in original and b'as_aux_lemma' not in original
    events = []
    for before, priority, kind, indent, label in INSERTIONS:
        assert 1 <= before <= len(lines) + 1
        assert re.fullmatch('[A-Za-z0-9_]+', label)
        assert kind in ('command', 'tactic')
        text = (' ' * indent + ('run_cmd' if kind == 'command' else 'run_tac') +
                ' IO.eprintln "' + PREFIX + ' ' + label + '"\n')
        events.append({'original_insert_before_line': before, 'priority': priority,
                       'kind': kind, 'indent': indent, 'label': label, 'inserted_line': text})
    events.sort(key=lambda e: (e['original_insert_before_line'], e['priority']))
    assert len(events) == EXPECTED_MARKER_COUNT
    assert len({e['label'] for e in events}) == EXPECTED_MARKER_COUNT
    output, manifest = [], []
    for line_no in range(1, len(lines) + 2):
        for event in events:
            if event['original_insert_before_line'] == line_no:
                entry = dict(event)
                entry['instrumented_line'] = len(output) + 1
                output.append(entry['inserted_line'].encode())
                manifest.append(entry)
        if line_no <= len(lines):
            output.append(lines[line_no - 1])
    marked = b''.join(output)
    assert len(marked) == EXPECTED_MARKED_BYTES and sha(marked) == EXPECTED_MARKED_SHA256
    marker_lines = {entry['inserted_line'].encode() for entry in manifest}
    assert len(marker_lines) == EXPECTED_MARKER_COUNT
    assert all(marked.count(line) == 1 for line in marker_lines)
    restored = b''.join(line for line in marked.splitlines(keepends=True) if line not in marker_lines)
    assert restored == original
    reverse = marked
    for entry in reversed(manifest):
        marker = entry['inserted_line'].encode()
        assert reverse.count(marker) == 1
        reverse = reverse.replace(marker, b'', 1)
    assert reverse == original
    assert [line for line in marked.splitlines(keepends=True) if line not in marker_lines] == lines
    assert all(marked.splitlines(keepends=True)[entry['instrumented_line'] - 1] ==
               entry['inserted_line'].encode() for entry in manifest)
    for name, header, start, after, label in DECLARATIONS:
        assert name.encode() in lines[header - 1]
        assert 1 <= start <= header < after <= len(lines) + 1
        if start != header:
            assert lines[start - 1].startswith((b'/--', b'include '))
            assert b'-/\n' in b''.join(lines[start - 1:header - 1])
            assert marked.count(b''.join(lines[start - 1:header])) == 1
    for prefix in (b'import ', b'#print axioms '):
        assert [line for line in marked.splitlines(keepends=True) if line.startswith(prefix)] == [
            line for line in lines if line.startswith(prefix)]
    assert b'set_option ' not in marked and b'as_aux_lemma' not in marked
    checks = {
        'marker_count': EXPECTED_MARKER_COUNT, 'declaration_count': len(DECLARATIONS),
        'command_marker_count': sum(e['kind'] == 'command' for e in manifest),
        'tactic_marker_count': sum(e['kind'] == 'tactic' for e in manifest),
        'original_import_count': len(EXPECTED_IMPORTS), 'original_print_axioms_count': len(EXPECTED_PRINTS),
        'byte_reversal_verified': True, 'individual_removal_reversal_verified': True,
        'all_original_lines_preserved_in_order': True, 'doccomment_associations_verified': True,
        'include_doc_header_blocks_preserved': True,
        'all_original_data_headers_and_proofs_preserved_after_marker_removal': True,
        'new_warning_scope_count': 0, 'warning_scope_count': 0,
        'all_original_linters_default': True, 'proof_transformations_added': 0,
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
    for name in ['FirstSecondCoveredSource', 'ActualGaussFiniteLeaves']:
        assert (repo / '.lake/build/lib/lean/HeckeSkeleton/Moments/MOM_ENGINE_STEP' /
                (name + '.olean')).is_file(), 'Run normal Lake :deps first: ' + name
    result.update(lean_version=version.strip(), mathlib_commit=mathlib,
                  source_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip(),
                  source_tree=subprocess.check_output(['git', 'rev-parse', 'HEAD^{tree}'], cwd=repo, text=True).strip())
    # The package-root flag only determines the name of this temporary module;
    # the original two imports resolve through the normal `lake env` paths.
    with tempfile.TemporaryDirectory(prefix='a2-owner-gated-169-diagnostic-') as temporary:
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
    (evidence / 'GatedGaussStages.original.lean').write_bytes(original)
    (evidence / (MODULE + '.lean')).write_bytes(marked)
    write_json(evidence / 'marker-manifest.json', manifest)
    result = {
        **FALSE_FLAGS, **checks,
        'scope': 'Owner temporary full-source default diagnostic of GatedGaussStages; not production or native acceptance',
        'production_source_and_proof_owner': 'A2/owner',
        'source_path': str(SOURCE), 'source_sha256': sha(original), 'source_bytes': len(original),
        'source_owner_head': SOURCE_OWNER_HEAD, 'source_owner_tree': SOURCE_OWNER_TREE, 'source_git_blob': SOURCE_BLOB,
        'diagnostic_script_sha256': sha(Path(__file__).read_bytes()),
        'executor_base_script_sha256': EXECUTOR_BASE_SCRIPT_SHA256,
        'executor_base_function_sha256': EXECUTOR_BASE_FUNCTION_SHA256,
        'executor_adapted_function_sha256': EXECUTOR_ADAPTED_FUNCTION_SHA256,
        'executor_adaptations': EXECUTOR_ADAPTATIONS,
        'external_wrapper_imported_or_rebound': False,
        'production_approval_flag_scope': 'This diagnostic does not grant production approval.',
        'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'heartbeat_override': None, 'lean_async_override': None, 'profiler_override': None,
        'stderr_option_override': False,
        'stderr_option_reason': 'Diagnostic marker transport only; no linter or normal verifier option changes',
        'warning_option_override': None, 'other_warning_option_override': None,
        'global_warning_option_override': None,
        'timeout_seconds': TIMEOUT_SECONDS, 'kill_after_seconds': KILL_AFTER_SECONDS,
        'lean_job_count': 2, 'started': False, 'status': 'prepared_only', 'timed_out': False,
        'marker_times_are_observed_arrival_only': True,
        'marker_interpretation': 'run_cmd shows only command continuation, which can follow error recovery; it is not proof success. run_tac shows only that the tactic sequence reached a point. Quoted warning echoes are not actual events; inspect complete-output.log for errors.',
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
