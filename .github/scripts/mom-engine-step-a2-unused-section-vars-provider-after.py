#!/usr/bin/env python3
"""Prepare or run the scoped cc98 diagnostic with one provider-return marker.

The frozen marker script remains unchanged and supplies both instrumentation
and bounded execution. Only the temporary full-source copy gains one 45-byte
option line immediately before the named private declaration and one tactic
marker after the provider exact. Every result is diagnostic only, including a
successful complete compilation.
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
BASELINE_MARKED_SHA = '9183fe0d033a45664d888b06640f9785bb414752d323096dcea2c7842b6bcd57'
CANDIDATE_SHA = '931dc1704d19663dbd391e7e7cddef8cf3541df9490d126811b7c893f9a1ed34'
OPTION = b'set_option linter.unusedSectionVars false in\n'
TARGET = 'phase_class_eq_fixed_fullCorrelation'
PROVIDER_TARGET = 'fixed_fullCorrelation_eq_leaf_sum'
PROVIDER_AFTER_LABEL = 'AFTER_PROVIDER_EXACT'
PROVIDER_AFTER_ORIGINAL_LINE = 504
EXPECTED_MARKED_SHA = 'dae6ab7725794a2f2f2fdbf5fc370b78e4a5e717b502a3cf640d5fc2c5c8a7ca'
QUALIFIED_TARGET = ('HeckeSkeleton.Moments.EngineStep.ActualGaussStage.'
                    'CoveredClassKey.phase_class_eq_fixed_fullCorrelation')
FALSE_FLAGS = {
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


def load_marker_script(path: Path):
    assert sha(path.read_bytes()) == MARKER_SCRIPT_SHA, 'Frozen marker script changed'
    # Reading the existing script must not create a repository bytecode file.
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('a2_frozen_cc98_markers', path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    assert module.EXPECTED_SOURCE == SOURCE_SHA and module.EXPECTED_BYTES == SOURCE_BYTES
    assert module.TIMEOUT_SECONDS == 150 and module.KILL_AFTER_SECONDS == 10
    assert module.ACCEPTANCE == FALSE_FLAGS
    assert module.MODULE == 'MomEngineActualDiagCc98c8a2'
    return module


def prepare(original: bytes, marker_module):
    """Pure preparation: return baseline59, candidate45B, marked60, manifest, checks.

    No file writes, process creation, option rebinding, or compiler invocation.
    baseline59 is the exact output of the frozen 0858 marker script. candidate45B
    is the original source plus the one existing scoped phase warning option.
    marked60 adds that same option and one AFTER_PROVIDER_EXACT tactic marker.
    """
    assert len(original) == SOURCE_BYTES and sha(original) == SOURCE_SHA
    assert len(OPTION) == 45 and OPTION not in original
    header = ('private theorem ' + TARGET + '\n').encode()
    assert original.count(header) == 1, 'Target header is not unique'
    baseline, original_manifest, checks = marker_module.instrument(original)
    assert sha(baseline) == BASELINE_MARKED_SHA
    assert len(original_manifest) == 59 and checks['marker_count'] == 59
    assert baseline.count(header) == 1 and OPTION not in baseline
    before_header_marker = ('run_cmd IO.eprintln ' + json.dumps(
        marker_module.PREFIX + ' BEFORE_HEADER_' + TARGET) + '\n').encode()
    option_position = baseline.index(header)
    # The option scopes only over the phase theorem, never over a run_cmd.
    assert baseline[option_position - len(before_header_marker):option_position] == before_header_marker
    candidate = original.replace(header, OPTION + header, 1)
    assert len(candidate) == 40327 and sha(candidate) == CANDIDATE_SHA
    scoped_baseline = baseline[:option_position] + OPTION + baseline[option_position:]
    assert sha(scoped_baseline) == 'c1419b51363dac8be8886e50a11e642528161e2993c005073ee36fa41fc0674c'

    original_lines = original.splitlines(keepends=True)
    original_index = PROVIDER_AFTER_ORIGINAL_LINE - 1
    assert original_lines[original_index] == b'\n'
    assert original_lines[original_index - 1].endswith(') ξ)\n'.encode())
    assert original.count(('private theorem ' + PROVIDER_TARGET + '\n').encode()) == 1
    assert not any(entry['original_insert_before_line'] == PROVIDER_AFTER_ORIGINAL_LINE
                   for entry in original_manifest)
    provider_position = sum(map(len, original_lines[:original_index])) + sum(
        len(entry['inserted_line'].encode()) for entry in original_manifest
        if entry['original_insert_before_line'] < PROVIDER_AFTER_ORIGINAL_LINE)
    final_exact_line = original_lines[original_index - 1]
    assert baseline[provider_position - len(final_exact_line):provider_position] == final_exact_line
    assert baseline[provider_position:provider_position + 1] == b'\n'
    assert provider_position > option_position
    provider_marker = ('  run_tac IO.eprintln ' + json.dumps(
        marker_module.PREFIX + ' ' + PROVIDER_AFTER_LABEL) + '\n').encode()
    assert len(provider_marker) == 71 and provider_marker not in baseline
    baseline60 = baseline[:provider_position] + provider_marker + baseline[provider_position:]
    marked = baseline60[:option_position] + OPTION + baseline60[option_position:]
    assert len(marked) == 45711 and sha(marked) == EXPECTED_MARKED_SHA
    assert marked.count(OPTION) == 1 and candidate.count(OPTION) == 1
    assert marked.count(provider_marker) == 1
    assert marked[option_position - len(before_header_marker):option_position + len(OPTION) + len(header)] == \
        before_header_marker + OPTION + header

    marker_lines = {entry['inserted_line'].encode() for entry in original_manifest}
    marker_lines.add(provider_marker)
    assert len(marker_lines) == 60

    def remove_markers(data: bytes) -> bytes:
        return b''.join(line for line in data.splitlines(keepends=True) if line not in marker_lines)

    def remove_option(data: bytes) -> bytes:
        assert data.count(OPTION) == 1
        return data.replace(OPTION, b'', 1)

    # Each intermediate full file, and both complete reversal orders, is exact.
    assert marked.replace(provider_marker, b'', 1) == scoped_baseline
    assert remove_option(marked) == baseline60
    assert remove_option(marked).replace(provider_marker, b'', 1) == baseline
    assert remove_markers(marked) == candidate
    assert remove_markers(remove_option(marked)) == original
    assert remove_option(remove_markers(marked)) == original
    assert remove_markers(baseline60) == original
    assert remove_markers(baseline) == original
    assert remove_option(candidate) == original
    option_line = baseline[:option_position].count(b'\n') + 1
    provider_baseline_line = baseline[:provider_position].count(b'\n') + 1
    provider_marked_line = provider_baseline_line + 1
    manifest = []
    for entry in original_manifest:
        updated = dict(entry)
        updated['baseline_instrumented_line'] = entry['instrumented_line']
        updated['origin'] = 'frozen_59_marker_script'
        updated['is_added_provider_after_marker'] = False
        updated['instrumented_line'] = entry['instrumented_line'] + \
            int(entry['instrumented_line'] >= option_line) + \
            int(entry['instrumented_line'] >= provider_baseline_line)
        manifest.append(updated)
    manifest.append({'label': PROVIDER_AFTER_LABEL,
                     'original_insert_before_line': PROVIDER_AFTER_ORIGINAL_LINE,
                     'instrumented_line': provider_marked_line,
                     'baseline_instrumented_line': None,
                     'inserted_line': provider_marker.decode(), 'kind': 'tactic',
                     'origin': 'provider_after_extension',
                     'is_added_provider_after_marker': True})
    manifest.sort(key=lambda entry: entry['instrumented_line'])
    assert [entry['label'] for entry in manifest if not entry['is_added_provider_after_marker']] == \
        [entry['label'] for entry in original_manifest]
    assert len(manifest) == 60
    lines = marked.splitlines(keepends=True)
    assert all(lines[entry['instrumented_line'] - 1] == entry['inserted_line'].encode()
               for entry in manifest)
    assert lines[option_line - 1] == OPTION and lines[option_line] == header
    assert lines[provider_marked_line - 1] == provider_marker
    assert lines[provider_marked_line - 2] == final_exact_line
    assert [line for line in lines if line.startswith(b'import ')] == \
        [line for line in original_lines if line.startswith(b'import ')]
    assert [line for line in lines if line.startswith(b'#print axioms ')] == \
        [line for line in original_lines if line.startswith(b'#print axioms ')]
    checks = {**checks,
              'marker_count': 60, 'original_marker_count': 59, 'additional_marker_count': 1,
              'all_59_original_markers_preserved': True,
              'additional_marker_label': PROVIDER_AFTER_LABEL,
              'two_way_reversal_verified': True,
              'new_marker_removal_recovers_scoped_59_marker_bytes': True,
              'option_removal_recovers_60_marker_baseline_bytes': True,
              'option_and_new_marker_removal_recovers_59_marker_baseline_bytes': True,
              'marker_removal_recovers_scoped_candidate_bytes': True,
              'all_edits_removal_recovers_original_bytes': True,
              'option_immediately_precedes_target_header': True,
              'option_follows_before_header_marker': True,
              'option_line_bytes': len(OPTION),
              'option_original_insert_before_line': original[:original.index(header)].count(b'\n') + 1,
              'option_instrumented_line': option_line,
              'provider_after_marker_bytes': len(provider_marker),
              'provider_after_original_insert_before_line': PROVIDER_AFTER_ORIGINAL_LINE,
              'provider_after_instrumented_line': provider_marked_line,
              'provider_warning_option_unchanged': True,
              'baseline_60_marker_source_sha256': sha(baseline60),
              'baseline_60_marker_source_bytes': len(baseline60)}
    return baseline, candidate, marked, manifest, checks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--evidence', required=True, type=Path)
    parser.add_argument('--run', action='store_true', help='Run the bounded diagnostic after normal dependencies')
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    assert '.lake' not in evidence.parts, 'Evidence must not be written in .lake'
    evidence.mkdir(parents=True, exist_ok=True)
    assert not (evidence / 'result.json').exists(), 'Use a fresh evidence directory'
    original = (repo / SOURCE).read_bytes()
    module = load_marker_script(repo / MARKER_SCRIPT)
    baseline, candidate, marked, manifest, checks = prepare(original, module)
    (evidence / 'ActualGaussFiniteLeaves.original.lean').write_bytes(original)
    (evidence / 'ActualGaussFiniteLeaves.scoped-candidate.lean').write_bytes(candidate)
    (evidence / 'MomEngineActualDiagCc98c8a2.baseline-marked.lean').write_bytes(baseline)
    (evidence / (module.MODULE + '.lean')).write_bytes(marked)
    write_json(evidence / 'marker-manifest.json', manifest)
    result = {**FALSE_FLAGS, **checks,
              'scope': 'One phase warning option plus one provider-return marker in a reversible full-source copy; diagnostic only',
              'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'source_path': str(SOURCE), 'source_sha256': sha(original), 'source_bytes': len(original),
              'marker_script_path': str(MARKER_SCRIPT), 'marker_script_sha256': MARKER_SCRIPT_SHA,
              'baseline_marked_source_sha256': sha(baseline), 'baseline_marked_source_bytes': len(baseline),
              'scoped_candidate_sha256': sha(candidate), 'scoped_candidate_bytes': len(candidate),
              'diagnostic_source_sha256': sha(marked), 'diagnostic_source_bytes': len(marked),
              'heartbeat_override': None, 'lean_async_override': None, 'profiler_override': None,
              'stderr_option_override': False,
              'warning_option_override': {'option': 'linter.unusedSectionVars', 'value': False,
                                          'scope': 'one private declaration',
                                          'declaration': QUALIFIED_TARGET, 'inserted_bytes': 45},
              'other_warning_option_override': None,
              'timeout_seconds': 150, 'kill_after_seconds': 10, 'lean_job_count': 2,
              'started': False, 'status': 'prepared_only', 'timed_out': False,
              'marker_times_are_observed_arrival_only': True}
    write_json(evidence / 'result.json', result)
    try:
        if args.run:
            assert os.environ.get('LEAN_NUM_THREADS') == '2', 'Expected unchanged workflow thread setting'
            # Reuse the frozen bounded executor without altering any module
            # settings, Lean CLI options, cleanup behavior, or output paths.
            module.execute(repo, evidence, marked, result)
    except BaseException as exc:
        result.update(status='diagnostic_harness_error', harness_error=repr(exc))
        raise
    finally:
        result['original_source_unchanged'] = (repo / SOURCE).read_bytes() == original
        result['marker_script_unchanged'] = sha((repo / MARKER_SCRIPT).read_bytes()) == MARKER_SCRIPT_SHA
        result.update(FALSE_FLAGS)
        write_json(evidence / 'result.json', result)
    print(json.dumps({key: result[key] for key in [
        'status', 'source_sha256', 'scoped_candidate_sha256', 'diagnostic_source_sha256',
        'marker_count', 'two_way_reversal_verified', 'warning_option_override',
        'original_source_unchanged', 'marker_script_unchanged', 'acceptance_evidence']},
        ensure_ascii=False), flush=True)
    if args.run and result.get('timed_out'):
        return 124
    code = result.get('diagnostic_exit_code', 0)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
