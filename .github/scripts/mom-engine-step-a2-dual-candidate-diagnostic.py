#!/usr/bin/env python3
"""Complete default-setting DualGaussHybridTerminal diagnostic from candidate abbe0828, not adopted owner production.

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

EXPECTED_SOURCE = 'e3e2453aff96995252298f97c9ee85074252d4cb937a118e40411f5e760eb6ac'
EXPECTED_BYTES = 17905
EXPECTED_LINES = 325
EXPECTED_LEAN = '4.35.0-rc3'
EXPECTED_LEAN_COMMIT = '470d5ce1400764999581fd26d5d72b00d990b0f4'
EXPECTED_MATHLIB = '0493595ecd5da8ef14742febab99728f98e948e8'
SOURCE_CANDIDATE_HEAD = 'abbe08285275bed30d830476110c3739e8b5f8b5'
SOURCE_CANDIDATE_TREE = 'cc199f73b722a985646d4a373ba67671a4b37a7c'
BASE_OWNER_HEAD = '16927b5cb39e3034ac86d3af49e39aae17440af4'
BASE_OWNER_TREE = 'caa913a0e45a8bb31db1251a15a69e91732ac921'
SOURCE_BLOB = '4fe4a4171071088fa5b9b8111db8ced928254872'
PREFIX = 'A2_DUAL_E3E2453_DIAGNOSTIC'
MODULE = 'MomEngineDualGaussHybridTerminalDiagE3e2453'
TIMEOUT_SECONDS = 150
KILL_AFTER_SECONDS = 10
EXECUTOR_BASE_SCRIPT_SHA256 = '266a512fec83c659fc03186e46980eca1a698e22c8b8bd9fc36ec0032592f48a'
EXECUTOR_BASE_FUNCTION_SHA256 = '61b9e442c9712943c93ffbc4652e7cb08bf4b78279cc749d8394893a3f5ae4ef'
EXECUTOR_ADAPTED_FUNCTION_SHA256 = '70c1d1d4958b676b6c7a35d72bba45f3f7437b498b40195eb71808ddc798271f'
EXECUTOR_ADAPTATIONS = [("for name in ['OrdinaryExceptionalLabelIntegral', 'ConstantCommonLeaf']:",
  "for name in ['ActualGaussDualRawTerminal', 'ActualGaussHybridTerminal', "
  "'ActualGaussFiniteLeaves']:"),
 ("prefix='a2-d-literal-f499-diagnostic-'", "prefix='a2-owner-dual-e3e2453-candidate-diagnostic-'"),
 ('# the original two imports resolve', '# the original three imports resolve')]
EXECUTOR_ORIGIN_0858_SCRIPT_SHA256 = '0858bc9e93b1ba60a6d45ae39e694149001689fa29bfd1928ffcaa9696e95ed3'
EXPECTED_MARKED_SHA256 = 'd2b4ed2cb225ce4baa610ea4a98960cc6ca11730ce28c083bd79ff24c9ad8d4f'
EXPECTED_MARKED_BYTES = 26850
EXPECTED_MARKER_COUNT = 108
DECLARATIONS = [['dual_scalar_integral_const_nonzero_const',
  31,
  31,
  42,
  'dual_scalar_integral_const_nonzero_const'],
 ['dual_scalar_weighted_terminal_sum', 43, 43, 58, 'dual_scalar_weighted_terminal_sum'],
 ['dualGaussHybridTerminalCircleCharacterFintype',
  79,
  79,
  81,
  'dualGaussHybridTerminalCircleCharacterFintype'],
 ['hybridCost', 89, 89, 95, 'hybridCost'],
 ['rawCost_le_hybrid', 96, 96, 104, 'rawCost_le_hybrid'],
 ['coverHybridCost', 105, 105, 111, 'coverHybridCost'],
 ['rawCost_le_coverHybrid', 112, 112, 120, 'rawCost_le_coverHybrid'],
 ['rawPhaseCost_integrable', 121, 121, 133, 'rawPhaseCost_integrable'],
 ['integral_rawPhaseCost', 134, 134, 154, 'integral_rawPhaseCost'],
 ['coverHybridPhaseCost_integrable', 155, 155, 170, 'coverHybridPhaseCost_integrable'],
 ['integral_rawPhaseCost_le_cover', 171, 171, 183, 'integral_rawPhaseCost_le_cover'],
 ['zeroBudget', 184, 184, 188, 'zeroBudget'],
 ['tailBudget', 189, 189, 192, 'tailBudget'],
 ['phase_cost_eq_budgets_leaves', 195, 193, 219, 'phase_cost_eq_budgets_leaves'],
 ['integral_phase_cost_eq_budgets_leaves', 220, 220, 241, 'integral_phase_cost_eq_budgets_leaves'],
 ['actual_gauss_dual_cover_hybrid_terminal_bound',
  257,
  253,
  286,
  'actual_gauss_dual_cover_hybrid_terminal_bound'],
 ['actual_gauss_dual_hybrid_terminal_bound',
  289,
  287,
  318,
  'actual_gauss_dual_hybrid_terminal_bound']]
EXPECTED_IMPORTS = ['import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussDualRawTerminal\n',
 'import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussHybridTerminal\n',
 'import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussFiniteLeaves\n']
EXPECTED_PRINTS = ['#print axioms '
 'HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.rawCost_le_coverHybrid\n',
 '#print axioms '
 'HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.integral_rawPhaseCost_le_cover\n',
 '#print axioms '
 'HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.integral_phase_cost_eq_budgets_leaves\n',
 '#print axioms HeckeSkeleton.Moments.EngineStep.actual_gauss_dual_cover_hybrid_terminal_bound\n',
 '#print axioms HeckeSkeleton.Moments.EngineStep.actual_gauss_dual_hybrid_terminal_bound\n']
INSERTIONS = [(4, 80, 'command', 0, 'AFTER_ORIGINAL_IMPORTS'),
 (31, 90, 'command', 0, 'BEFORE_HEADER_dual_scalar_integral_const_nonzero_const'),
 (37, 50, 'tactic', 2, 'SCALAR_RAW_BEFORE_RW'),
 (40, 10, 'tactic', 2, 'SCALAR_RAW_AFTER_RW'),
 (40, 50, 'tactic', 2, 'SCALAR_RAW_BEFORE_SIMP_ONLY'),
 (41, 10, 'tactic', 2, 'SCALAR_RAW_AFTER_SIMP_ONLY'),
 (41, 50, 'tactic', 2, 'SCALAR_RAW_BEFORE_RING'),
 (42, 10, 'tactic', 2, 'SCALAR_RAW_AFTER_RING'),
 (42, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_dual_scalar_integral_const_nonzero_const'),
 (43, 90, 'command', 0, 'BEFORE_HEADER_dual_scalar_weighted_terminal_sum'),
 (55, 50, 'tactic', 2, 'SCALAR_SUM_BEFORE_RW'),
 (56, 10, 'tactic', 2, 'SCALAR_SUM_AFTER_RW'),
 (56, 50, 'tactic', 2, 'SCALAR_SUM_BEFORE_SIMP_ONLY'),
 (57, 10, 'tactic', 2, 'SCALAR_SUM_AFTER_SIMP_ONLY'),
 (57, 50, 'tactic', 2, 'SCALAR_SUM_BEFORE_RING'),
 (58, 10, 'tactic', 2, 'SCALAR_SUM_AFTER_RING'),
 (58, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_dual_scalar_weighted_terminal_sum'),
 (79, 90, 'command', 0, 'BEFORE_HEADER_dualGaussHybridTerminalCircleCharacterFintype'),
 (81, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_dualGaussHybridTerminalCircleCharacterFintype'),
 (89, 90, 'command', 0, 'BEFORE_HEADER_hybridCost'),
 (95, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_hybridCost'),
 (96, 90, 'command', 0, 'BEFORE_HEADER_rawCost_le_hybrid'),
 (101, 50, 'tactic', 2, 'RAW_LE_HYBRID_BEFORE_APPLY'),
 (104, 10, 'tactic', 2, 'RAW_LE_HYBRID_AFTER_EXACT'),
 (104, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_rawCost_le_hybrid'),
 (105, 90, 'command', 0, 'BEFORE_HEADER_coverHybridCost'),
 (111, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_coverHybridCost'),
 (112, 90, 'command', 0, 'BEFORE_HEADER_rawCost_le_coverHybrid'),
 (117, 50, 'tactic', 2, 'RAW_LE_COVER_BEFORE_APPLY'),
 (120, 10, 'tactic', 2, 'RAW_LE_COVER_AFTER_EXACT'),
 (120, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_rawCost_le_coverHybrid'),
 (121, 90, 'command', 0, 'BEFORE_HEADER_rawPhaseCost_integrable'),
 (126, 50, 'tactic', 2, 'RAW_INTEGRABLE_BEFORE_FINITE'),
 (127, 10, 'tactic', 2, 'RAW_INTEGRABLE_AFTER_FINITE'),
 (127, 50, 'tactic', 2, 'RAW_INTEGRABLE_BEFORE_CHANGE'),
 (131, 10, 'tactic', 2, 'RAW_INTEGRABLE_AFTER_CHANGE'),
 (131, 50, 'tactic', 2, 'RAW_INTEGRABLE_BEFORE_EXACT'),
 (133, 10, 'tactic', 2, 'RAW_INTEGRABLE_AFTER_EXACT'),
 (133, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_rawPhaseCost_integrable'),
 (134, 90, 'command', 0, 'BEFORE_HEADER_integral_rawPhaseCost'),
 (143, 50, 'tactic', 2, 'RAW_INTEGRAL_BEFORE_FINITE'),
 (144, 10, 'tactic', 2, 'RAW_INTEGRAL_AFTER_FINITE'),
 (144, 50, 'tactic', 2, 'RAW_INTEGRAL_BEFORE_CHANGE'),
 (149, 10, 'tactic', 2, 'RAW_INTEGRAL_AFTER_CHANGE'),
 (149, 50, 'tactic', 2, 'RAW_INTEGRAL_BEFORE_EXACT'),
 (154, 10, 'tactic', 2, 'RAW_INTEGRAL_AFTER_EXACT'),
 (154, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_integral_rawPhaseCost'),
 (155, 90, 'command', 0, 'BEFORE_HEADER_coverHybridPhaseCost_integrable'),
 (162, 50, 'tactic', 2, 'COVER_INTEGRABLE_BEFORE_FINITE'),
 (163, 10, 'tactic', 2, 'COVER_INTEGRABLE_AFTER_FINITE'),
 (163, 50, 'tactic', 2, 'COVER_INTEGRABLE_BEFORE_CHANGE'),
 (167, 10, 'tactic', 2, 'COVER_INTEGRABLE_AFTER_CHANGE'),
 (167, 50, 'tactic', 2, 'COVER_INTEGRABLE_BEFORE_EXACT'),
 (170, 10, 'tactic', 2, 'COVER_INTEGRABLE_AFTER_EXACT'),
 (170, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_coverHybridPhaseCost_integrable'),
 (171, 90, 'command', 0, 'BEFORE_HEADER_integral_rawPhaseCost_le_cover'),
 (179, 50, 'tactic', 2, 'INTEGRAL_MONO_BEFORE_APPLY'),
 (181, 10, 'tactic', 2, 'INTEGRAL_MONO_AFTER_APPLY'),
 (182, 50, 'tactic', 2, 'INTEGRAL_MONO_BEFORE_EXACT'),
 (183, 10, 'tactic', 2, 'INTEGRAL_MONO_AFTER_EXACT'),
 (183, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_integral_rawPhaseCost_le_cover'),
 (184, 90, 'command', 0, 'BEFORE_HEADER_zeroBudget'),
 (188, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_zeroBudget'),
 (189, 90, 'command', 0, 'BEFORE_HEADER_tailBudget'),
 (192, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_tailBudget'),
 (193, 90, 'command', 0, 'BEFORE_HEADER_phase_cost_eq_budgets_leaves'),
 (204, 50, 'tactic', 2, 'SUM_BEFORE_CHANGE'),
 (208, 10, 'tactic', 2, 'SUM_AFTER_CHANGE'),
 (208, 50, 'tactic', 2, 'SUM_BEFORE_EXACT'),
 (219, 10, 'tactic', 2, 'SUM_AFTER_EXACT'),
 (219, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_phase_cost_eq_budgets_leaves'),
 (220, 90, 'command', 0, 'BEFORE_HEADER_integral_phase_cost_eq_budgets_leaves'),
 (229, 50, 'tactic', 2, 'INTEGRAL_BEFORE_FINITE'),
 (230, 10, 'tactic', 2, 'INTEGRAL_AFTER_FINITE'),
 (230, 50, 'tactic', 2, 'INTEGRAL_BEFORE_SIMP_RW'),
 (231, 10, 'tactic', 2, 'INTEGRAL_AFTER_SIMP_RW'),
 (231, 50, 'tactic', 2, 'INTEGRAL_BEFORE_INTEGRAL_ADD'),
 (233, 10, 'tactic', 2, 'INTEGRAL_AFTER_INTEGRAL_ADD'),
 (233, 50, 'tactic', 2, 'INTEGRAL_BEFORE_INTEGRAL_CONST_SUM'),
 (234, 10, 'tactic', 2, 'INTEGRAL_AFTER_INTEGRAL_CONST_SUM'),
 (235, 50, 'tactic', 4, 'INTEGRAL_AFTER_SMUL_BEFORE_CONGR'),
 (236, 10, 'tactic', 4, 'INTEGRAL_AFTER_CONGR'),
 (236, 50, 'tactic', 4, 'INTEGRAL_BEFORE_SUM_CONGR'),
 (237, 10, 'tactic', 4, 'INTEGRAL_AFTER_SUM_CONGR'),
 (238, 50, 'tactic', 4, 'INTEGRAL_COST_BEFORE_EXACT'),
 (239, 5, 'tactic', 4, 'INTEGRAL_COST_AFTER_EXACT'),
 (240, 50, 'tactic', 4, 'INTEGRAL_SIDE_BEFORE_EXACT'),
 (241, 5, 'tactic', 4, 'INTEGRAL_SIDE_AFTER_EXACT'),
 (241, 10, 'tactic', 2, 'INTEGRAL_AFTER_COMPLETE_PROOF'),
 (241, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_integral_phase_cost_eq_budgets_leaves'),
 (253, 90, 'command', 0, 'BEFORE_HEADER_actual_gauss_dual_cover_hybrid_terminal_bound'),
 (279, 50, 'tactic', 2, 'COVER_BOUND_BEFORE_OBTAIN'),
 (282, 10, 'tactic', 2, 'COVER_BOUND_AFTER_OBTAIN'),
 (285, 50, 'tactic', 2, 'COVER_BOUND_BEFORE_EXACT'),
 (286, 10, 'tactic', 2, 'COVER_BOUND_AFTER_EXACT'),
 (286, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_actual_gauss_dual_cover_hybrid_terminal_bound'),
 (287, 90, 'command', 0, 'BEFORE_HEADER_actual_gauss_dual_hybrid_terminal_bound'),
 (311, 50, 'tactic', 2, 'HYBRID_BOUND_BEFORE_OBTAIN'),
 (314, 10, 'tactic', 2, 'HYBRID_BOUND_AFTER_OBTAIN'),
 (317, 50, 'tactic', 2, 'HYBRID_BOUND_BEFORE_EXACT'),
 (318, 10, 'tactic', 2, 'HYBRID_BOUND_AFTER_EXACT'),
 (318, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_actual_gauss_dual_hybrid_terminal_bound'),
 (321, 80, 'command', 0, 'BEFORE_ORIGINAL_PRINT_287'),
 (322, 80, 'command', 0, 'BEFORE_ORIGINAL_PRINT_288'),
 (323, 80, 'command', 0, 'BEFORE_ORIGINAL_PRINT_289'),
 (324, 80, 'command', 0, 'BEFORE_ORIGINAL_PRINT_290'),
 (325, 80, 'command', 0, 'BEFORE_ORIGINAL_PRINT_291'),
 (326, 99, 'command', 0, 'AFTER_ALL_ORIGINAL_COMMANDS')]
SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualGaussHybridTerminal.lean')
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
    for name in ['ActualGaussDualRawTerminal', 'ActualGaussHybridTerminal', 'ActualGaussFiniteLeaves']:
        assert (repo / '.lake/build/lib/lean/HeckeSkeleton/Moments/MOM_ENGINE_STEP' /
                (name + '.olean')).is_file(), 'Run normal Lake :deps first: ' + name
    result.update(lean_version=version.strip(), mathlib_commit=mathlib,
                  source_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip(),
                  source_tree=subprocess.check_output(['git', 'rev-parse', 'HEAD^{tree}'], cwd=repo, text=True).strip())
    # The package-root flag only determines the name of this temporary module;
    # the original three imports resolve through the normal `lake env` paths.
    with tempfile.TemporaryDirectory(prefix='a2-owner-dual-e3e2453-candidate-diagnostic-') as temporary:
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
    (evidence / 'DualGaussHybridTerminal.original.lean').write_bytes(original)
    (evidence / (MODULE + '.lean')).write_bytes(marked)
    write_json(evidence / 'marker-manifest.json', manifest)
    result = {
        **FALSE_FLAGS, **checks,
        'scope': 'Temporary full-source default diagnostic of the pending DualGaussHybridTerminal candidate; not adopted owner production or native acceptance',
        'proof_candidate_author': 'A2/owner',
        'candidate_source_not_adopted_as_owner_production': True,
        'owner_adoption_performed_by_this_diagnostic': False,
        'source_path': str(SOURCE), 'source_sha256': sha(original), 'source_bytes': len(original),
        'source_candidate_head': SOURCE_CANDIDATE_HEAD, 'source_candidate_tree': SOURCE_CANDIDATE_TREE,
        'base_owner_head': BASE_OWNER_HEAD, 'base_owner_tree': BASE_OWNER_TREE, 'source_git_blob': SOURCE_BLOB,
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
