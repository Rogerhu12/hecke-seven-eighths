#!/usr/bin/env python3
"""Prepare a reversible provider/public warning control on complete cc98 source.

The frozen bc1a preparer supplies all 61 markers. This variant changes only
three declaration prefixes: the private phase uses the verified 69-byte W3
omit; the private provider and public phase each have a 45-byte scoped
unusedSectionVars override. The public override precedes its original doc
comment. All original proofs, headers, definitions, imports and print commands
remain byte-identical after removing those three prefixes. There is no new
alias, as_aux_lemma, global warning option or compiler-option change.

Only the frozen 0858 executor may run this temporary copy, with its unchanged
150-second timeout, 10-second kill grace, -j2 and temporary compiler outputs.
Every result is diagnostic only; all acceptance and production flags are false.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys

SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualGaussFiniteLeaves.lean')
SOURCE_SHA = 'cc98c8a2c5c3c3f6c59695935245f463c84e6e7f7c8292b5062e2d1813d94c87'
SOURCE_BYTES = 40282
MARKER_SCRIPT = Path('.github/scripts/mom-engine-step-a2-diagnostic.py')
MARKER_SCRIPT_SHA = '0858bc9e93b1ba60a6d45ae39e694149001689fa29bfd1928ffcaa9696e95ed3'
PRIOR_SCRIPT = Path('.github/scripts/mom-engine-step-a2-public-phase-after.py')
PRIOR_SCRIPT_SHA = 'bc1a8cbab78e8c713e8bada7c97be38336d1c02bff92c82025a0d832b2cb31f8'
PRIOR_CANDIDATE_SHA = '5518a6523e94b3b14be8292579cdaa7459c80b7ca4b6f06868618f3e41e4915c'
PRIOR_MARKED_SHA = 'fcbe6a79c67e550de2d340846ceb4b563fe3ce857d55441b1c97050dc8d27692'
BASELINE_MARKED_SHA = '9183fe0d033a45664d888b06640f9785bb414752d323096dcea2c7842b6bcd57'
CANDIDATE_SHA = 'c4a26eec9fb3b5a4d66ecb0220d4c82e29fc784adbdda4917c27430560bb228c'
CANDIDATE_BLOB = '750c56c5e2c368e49f554b474a79e059d4fec618'
EXPECTED_MARKED_SHA = '7285c7e5c9d6da0c314f35300ebd617f53f78efd98e4b1d3e9762a37a4da044b'
EXPECTED_MARKED_BLOB = 'a88539a04ca66fecc24444efad205af1ea3068a3'
OPTION = b'set_option linter.unusedSectionVars false in\n'
OMIT = 'omit [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] in\n'.encode()
PHASE_TARGET = 'phase_class_eq_fixed_fullCorrelation'
PROVIDER_TARGET = 'fixed_fullCorrelation_eq_leaf_sum'
PUBLIC_TARGET = 'phase_class_eq_leaf_sum'
PHASE_HEADER = ('private theorem ' + PHASE_TARGET + '\n').encode()
PROVIDER_HEADER = ('private theorem ' + PROVIDER_TARGET + '\n').encode()
PUBLIC_HEADER = ('theorem ' + PUBLIC_TARGET +
                 ' (exceptional : s.CoverHybridPredicates LC RC)\n').encode()
PUBLIC_DOC = (b'/-- This is the actual phase multiplication from the first transform,\n'
              b'followed by the literal finite allocation sum from the second. -/\n')
QUALIFIED_PREFIX = 'HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.'
WARNING_TARGETS = [QUALIFIED_PREFIX + PROVIDER_TARGET, QUALIFIED_PREFIX + PUBLIC_TARGET]
FROZEN_FALSE_FLAGS = {
    'acceptance_evidence': False,
    'original_module_native_was_run': False,
    'original_module_acceptance': False,
    'complete_target_module_compiled': False,
    'complete_module_within_five_minutes': False,
    'full_task_acceptance': False,
    'compiler_outputs_can_be_restored_as_project_cache': False,
}
FALSE_FLAGS = {
    **FROZEN_FALSE_FLAGS,
    'production_approval': False,
    'candidate_native_validation_performed': False,
    'candidate_equivalence_claimed': False,
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def load_prior_script(path: Path):
    assert sha(path.read_bytes()) == PRIOR_SCRIPT_SHA, 'Frozen 61-marker preparer changed'
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('a2_frozen_bc1a_public_phase_after', path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    assert module.SOURCE == SOURCE and module.SOURCE_SHA == SOURCE_SHA
    assert module.SOURCE_BYTES == SOURCE_BYTES and module.CANDIDATE_SHA == PRIOR_CANDIDATE_SHA
    assert module.EXPECTED_PUBLIC_MARKED_SHA == PRIOR_MARKED_SHA
    assert module.MARKER_SCRIPT == MARKER_SCRIPT and module.MARKER_SCRIPT_SHA == MARKER_SCRIPT_SHA
    assert module.FALSE_FLAGS == FROZEN_FALSE_FLAGS
    return module


def prepare(original: bytes, marker_module, prior_module):
    """Pure preparation; return baseline59, candidate159B, marked61, manifest, checks.

    This function performs no writes, process creation, module-setting changes
    or compiler invocation. Its two module arguments must be the pinned scripts.
    """
    assert len(original) == SOURCE_BYTES and sha(original) == SOURCE_SHA
    assert marker_module.EXPECTED_SOURCE == SOURCE_SHA
    assert marker_module.EXPECTED_BYTES == SOURCE_BYTES
    assert marker_module.TIMEOUT_SECONDS == 150 and marker_module.KILL_AFTER_SECONDS == 10
    assert marker_module.ACCEPTANCE == FROZEN_FALSE_FLAGS
    assert marker_module.MODULE == 'MomEngineActualDiagCc98c8a2'
    assert len(OPTION) == 45 and len(OMIT) == 69
    assert OPTION not in original and OMIT not in original
    assert b'as_aux_lemma' not in original
    for anchor in [PHASE_HEADER, PROVIDER_HEADER, PUBLIC_DOC + PUBLIC_HEADER]:
        assert original.count(anchor) == 1

    baseline, prior_candidate, prior_marked, prior_manifest, prior_checks = \
        prior_module.prepare(original, marker_module)
    assert len(baseline) == 45595 and sha(baseline) == BASELINE_MARKED_SHA
    assert len(prior_candidate) == 40372 and sha(prior_candidate) == PRIOR_CANDIDATE_SHA
    assert len(prior_marked) == 45831 and sha(prior_marked) == PRIOR_MARKED_SHA
    assert len(prior_manifest) == 61 and prior_checks['marker_count'] == 61
    assert prior_candidate.count(OPTION) == 2 and prior_marked.count(OPTION) == 2
    assert OMIT not in prior_candidate and OMIT not in prior_marked

    def change_control_prefixes(data: bytes) -> bytes:
        assert data.count(OPTION + PHASE_HEADER) == 1
        assert data.count(OPTION + PROVIDER_HEADER) == 1
        assert data.count(PUBLIC_DOC + PUBLIC_HEADER) == 1
        data = data.replace(OPTION + PHASE_HEADER, OMIT + PHASE_HEADER, 1)
        return data.replace(PUBLIC_DOC + PUBLIC_HEADER,
                            OPTION + PUBLIC_DOC + PUBLIC_HEADER, 1)

    candidate = change_control_prefixes(prior_candidate)
    marked = change_control_prefixes(prior_marked)
    assert len(candidate) == 40441 and sha(candidate) == CANDIDATE_SHA
    assert git_blob(candidate) == CANDIDATE_BLOB
    assert len(marked) == 45900 and sha(marked) == EXPECTED_MARKED_SHA
    assert git_blob(marked) == EXPECTED_MARKED_BLOB
    for data in [candidate, marked]:
        assert data.count(OMIT) == 1 and data.count(OPTION) == 2
        assert data.count(OMIT + PHASE_HEADER) == 1
        assert data.count(OPTION + PROVIDER_HEADER) == 1
        assert data.count(OPTION + PUBLIC_DOC + PUBLIC_HEADER) == 1
        assert OPTION + PHASE_HEADER not in data
        assert b'as_aux_lemma' not in data

    def restore_prior(data: bytes) -> bytes:
        assert data.count(OMIT + PHASE_HEADER) == 1
        assert data.count(OPTION + PUBLIC_DOC + PUBLIC_HEADER) == 1
        data = data.replace(OMIT + PHASE_HEADER, OPTION + PHASE_HEADER, 1)
        return data.replace(OPTION + PUBLIC_DOC + PUBLIC_HEADER,
                            PUBLIC_DOC + PUBLIC_HEADER, 1)

    def remove_controls(data: bytes) -> bytes:
        for insertion, anchor in [(OMIT, PHASE_HEADER), (OPTION, PROVIDER_HEADER),
                                  (OPTION, PUBLIC_DOC + PUBLIC_HEADER)]:
            assert data.count(insertion + anchor) == 1
            data = data.replace(insertion + anchor, anchor, 1)
        assert OMIT not in data and OPTION not in data
        return data

    marker_lines = {entry['inserted_line'].encode() for entry in prior_manifest}
    assert len(marker_lines) == 61
    assert all(marked.count(line) == 1 for line in marker_lines)

    def remove_markers(data: bytes) -> bytes:
        return b''.join(line for line in data.splitlines(keepends=True)
                        if line not in marker_lines)

    assert restore_prior(candidate) == prior_candidate
    assert restore_prior(marked) == prior_marked
    assert remove_controls(candidate) == original
    assert remove_markers(marked) == candidate
    assert remove_controls(remove_markers(marked)) == original
    assert remove_markers(remove_controls(marked)) == original
    assert remove_controls(marked) == prior_marked.replace(OPTION, b'', 2)
    assert remove_markers(prior_marked) == prior_candidate

    def before_header(target: str) -> bytes:
        return ('run_cmd IO.eprintln ' + json.dumps(
            marker_module.PREFIX + ' BEFORE_HEADER_' + target) + '\n').encode()

    assert before_header(PHASE_TARGET) + OMIT + PHASE_HEADER in marked
    assert before_header(PROVIDER_TARGET) + OPTION + PROVIDER_HEADER in marked
    assert before_header(PUBLIC_TARGET) + OPTION + PUBLIC_DOC + PUBLIC_HEADER in marked
    # The public option binds the original doccomment plus its theorem. It does
    # not bind the preceding run_cmd or an intervening generated declaration.
    assert candidate.count(PUBLIC_DOC + PUBLIC_HEADER) == 1

    manifest = []
    for entry in prior_manifest:
        updated = dict(entry)
        line = entry['inserted_line'].encode()
        updated['prior_61_instrumented_line'] = entry['instrumented_line']
        updated['instrumented_line'] = marked[:marked.index(line)].count(b'\n') + 1
        manifest.append(updated)
    assert [entry['label'] for entry in manifest] == [entry['label'] for entry in prior_manifest]
    assert [entry['inserted_line'] for entry in manifest] == \
        [entry['inserted_line'] for entry in prior_manifest]
    assert len(manifest) == 61
    marked_lines = marked.splitlines(keepends=True)
    assert all(marked_lines[entry['instrumented_line'] - 1] == entry['inserted_line'].encode()
               for entry in manifest)
    original_lines = original.splitlines(keepends=True)
    for prefix in [b'import ', b'#print axioms ']:
        assert [line for line in marked_lines if line.startswith(prefix)] == \
            [line for line in original_lines if line.startswith(prefix)]
    assert [line for line in marked_lines
            if line.lstrip().startswith(b'set_option ') and line != OPTION] == \
        [line for line in original_lines if line.lstrip().startswith(b'set_option ')]
    assert [line for line in marked_lines if line.lstrip().startswith(b'omit ')] == [OMIT]

    warning_scopes = []
    for target, anchor, preceding_doc in [
            (PROVIDER_TARGET, PROVIDER_HEADER, False),
            (PUBLIC_TARGET, PUBLIC_DOC + PUBLIC_HEADER, True)]:
        position = marked.index(OPTION + anchor)
        warning_scopes.append({
            'declaration': QUALIFIED_PREFIX + target,
            'short_name': target,
            'option': 'linter.unusedSectionVars',
            'value': False,
            'inserted_bytes': 45,
            'original_insert_before_line': original[:original.index(anchor)].count(b'\n') + 1,
            'instrumented_line': marked[:position].count(b'\n') + 1,
            'follows_before_header_marker': True,
            'precedes_original_doccomment': preceding_doc,
            'single_declaration_scope_verified': True,
        })
    phase_position = marked.index(OMIT + PHASE_HEADER)
    omit_scope = {
        'declaration': QUALIFIED_PREFIX + PHASE_TARGET,
        'classes': ['FiniteDimensional ℝ W', 'MeasurableSpace W', 'BorelSpace W'],
        'inserted_bytes': 69,
        'original_insert_before_line': original[:original.index(PHASE_HEADER)].count(b'\n') + 1,
        'instrumented_line': marked[:phase_position].count(b'\n') + 1,
        'follows_before_header_marker': True,
        'single_declaration_scope_verified': True,
    }
    checks = {
        'marker_count': 61,
        'original_marker_count': 59,
        'additional_marker_count': 2,
        'additional_marker_labels': ['AFTER_PROVIDER_EXACT', 'AFTER_PUBLIC_PHASE_EXACT'],
        'all_59_original_markers_preserved': True,
        'all_prior_61_markers_preserved': True,
        'all_prior_marker_bytes_and_order_preserved': True,
        'byte_reversal_verified': True,
        'two_way_reversal_verified': True,
        'prior_candidate_and_marked_reversal_verified': True,
        'marker_removal_recovers_candidate_bytes': True,
        'all_edits_removal_recovers_original_bytes': True,
        'doccomment_associations_verified': True,
        'all_original_proof_bodies_and_headers_preserved': True,
        'all_original_definitions_imports_and_prints_preserved': True,
        'no_alias_or_as_aux_lemma_change': True,
        'phase_warning_uses_default': True,
        'warning_scope_count': 2,
        'warning_line_bytes_per_scope': 45,
        'warning_lines_total_bytes': 90,
        'warning_scopes': warning_scopes,
        'omit_scope_count': 1,
        'omit_scope': omit_scope,
        'no_global_warning_override': True,
        'prior_61_preparation_checks': prior_checks,
    }
    return baseline, candidate, marked, manifest, checks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--evidence', required=True, type=Path)
    parser.add_argument('--run', action='store_true',
                        help='Run the bounded diagnostic after normal dependencies')
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    assert '.lake' not in evidence.parts, 'Evidence must not be written in .lake'
    evidence.mkdir(parents=True, exist_ok=True)
    assert not (evidence / 'result.json').exists(), 'Use a fresh evidence directory'
    original = (repo / SOURCE).read_bytes()
    prior_module = load_prior_script(repo / PRIOR_SCRIPT)
    marker_module = prior_module.load_marker_script(repo / MARKER_SCRIPT)
    baseline, candidate, marked, manifest, checks = prepare(original, marker_module, prior_module)
    (evidence / 'ActualGaussFiniteLeaves.original.lean').write_bytes(original)
    (evidence / 'ActualGaussFiniteLeaves.provider-public-warning-candidate.lean').write_bytes(candidate)
    (evidence / 'MomEngineActualDiagCc98c8a2.baseline-marked.lean').write_bytes(baseline)
    (evidence / (marker_module.MODULE + '.lean')).write_bytes(marked)
    write_json(evidence / 'marker-manifest.json', manifest)
    result = {
        **FALSE_FLAGS, **checks,
        'scope': 'Phase W3 omit and provider/public scoped warning controls on full cc98 with frozen 61 markers; diagnostic only',
        'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_path': str(SOURCE), 'source_sha256': sha(original), 'source_bytes': len(original),
        'marker_script_path': str(MARKER_SCRIPT), 'marker_script_sha256': MARKER_SCRIPT_SHA,
        'prior_script_path': str(PRIOR_SCRIPT), 'prior_script_sha256': PRIOR_SCRIPT_SHA,
        'prior_candidate_sha256': PRIOR_CANDIDATE_SHA, 'prior_marked_source_sha256': PRIOR_MARKED_SHA,
        'baseline_marked_source_sha256': sha(baseline), 'baseline_marked_source_bytes': len(baseline),
        'scoped_candidate_sha256': sha(candidate), 'scoped_candidate_bytes': len(candidate),
        'scoped_candidate_git_blob': git_blob(candidate),
        'diagnostic_source_sha256': sha(marked), 'diagnostic_source_bytes': len(marked),
        'diagnostic_source_git_blob': git_blob(marked),
        'heartbeat_override': None, 'lean_async_override': None, 'profiler_override': None,
        'stderr_option_override': False,
        'warning_override': None, 'global_warning_option_override': None,
        'warning_option_override': {
            'option': 'linter.unusedSectionVars', 'value': False,
            'scope': 'private provider and public phase, each one declaration',
            'declarations': WARNING_TARGETS,
            'inserted_bytes_per_declaration': 45, 'total_inserted_bytes': 90,
        },
        'public_warning_option_override': {
            'option': 'linter.unusedSectionVars', 'value': False,
            'declaration': QUALIFIED_PREFIX + PUBLIC_TARGET,
            'before_original_doccomment': True, 'inserted_bytes': 45,
        },
        'other_warning_option_override': None,
        'timeout_seconds': 150, 'kill_after_seconds': 10, 'lean_job_count': 2,
        'started': False, 'status': 'prepared_only', 'timed_out': False,
        'marker_times_are_observed_arrival_only': True,
    }
    write_json(evidence / 'result.json', result)
    try:
        if args.run:
            assert os.environ.get('LEAN_NUM_THREADS') == '2', 'Expected unchanged workflow thread setting'
            # Invoke the exact frozen executor. Do not rebind any guard,
            # compiler setting, timeout, output path or cleanup function.
            marker_module.execute(repo, evidence, marked, result)
    except BaseException as exc:
        result.update(status='diagnostic_harness_error', harness_error=repr(exc))
        raise
    finally:
        result['original_source_unchanged'] = (repo / SOURCE).read_bytes() == original
        result['marker_script_unchanged'] = sha((repo / MARKER_SCRIPT).read_bytes()) == MARKER_SCRIPT_SHA
        result['prior_script_unchanged'] = sha((repo / PRIOR_SCRIPT).read_bytes()) == PRIOR_SCRIPT_SHA
        result.update(FALSE_FLAGS)
        write_json(evidence / 'result.json', result)
    print(json.dumps({key: result[key] for key in [
        'status', 'source_sha256', 'scoped_candidate_sha256', 'diagnostic_source_sha256',
        'marker_count', 'two_way_reversal_verified', 'warning_option_override',
        'original_source_unchanged', 'marker_script_unchanged', 'prior_script_unchanged',
        'acceptance_evidence', 'production_approval']}, ensure_ascii=False), flush=True)
    if args.run and result.get('timed_out'):
        return 124
    code = result.get('diagnostic_exit_code', 0)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
