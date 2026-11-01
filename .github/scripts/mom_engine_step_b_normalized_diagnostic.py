#!/usr/bin/env python3
"""Observe the complete 4b99 Normalized proof phases; never substitute for verification."""
import argparse
import difflib
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import tempfile
import time

SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedOriginalLabelMass.lean')
SOURCE_SHA = '4b99ef65579b672d2a30a46b0bc6e89dbc3759a5f1171642d2da42f6d4eccadc'
LEAN_COMMIT = '470d5ce1400764999581fd26d5d72b00d990b0f4'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--disable-index-unused-section-vars', action='store_true',
                        help='Diagnostic control only: disable unusedSectionVars for '
                             'the main index theorem in the temporary source copy.')
    return parser.parse_args(argv)


def instrument(source):
    """Insert boundary markers only; certify exact restoration of all source bytes."""
    text = source.decode('utf-8')
    theorem = text.index('theorem normalized_pair_original_index_weight')
    body = text.index(' := by\n', theorem) + len(' := by\n')
    entries = []

    def add(offset, label, tactic=True):
        indent = '  ' if tactic else ''
        block = (indent + ('run_tac' if tactic else 'run_cmd') + '\n' + indent +
                 '  IO.eprintln "MOM_TRACE NormalizedOriginalLabelMass B24_4b99ef65 ' + label + '"\n' +
                 indent + '  (← IO.getStderr).flush\n')
        entries.append({'offset_characters': offset, 'label': label, 'text': block})

    helper = text.index('private theorem normalizedOriginalLabel_reorder_bound')
    add(helper, 'BEFORE_REORDER_HELPER', False)
    index_helper = text.index('private theorem normalizedOriginalLabel_indexWeight_eq')
    add(index_helper, 'AFTER_REORDER_HELPER_DECLARATION', False)
    add(index_helper, 'BEFORE_INDEX_WEIGHT_HELPER', False)
    add(text.index('variable {F : Type}', index_helper), 'AFTER_INDEX_WEIGHT_HELPER_DECLARATION', False)
    allowance = text.index('theorem normalized_pair_original_allowance_from_atoms')
    add(text.rfind('include L in\n', 0, allowance), 'BEFORE_ALLOWANCE_HEADER', False)
    allowance_end = text.index('\nvariable {branch : TwoDivisorCommonBranch', allowance)
    add(allowance_end, 'AFTER_ALLOWANCE_FINAL_EXACT')
    add(allowance_end, 'AFTER_ALLOWANCE_DECLARATION', False)
    add(text.rfind('include L in\n', 0, theorem), 'BEFORE_INDEX_HEADER', False)
    add(body, 'BEFORE_hz')
    for anchor, label in [
        ('  have hN :', 'BEFORE_hN'),
        ('  have hsecond :=', 'BEFORE_hsecond'),
        ('  have hfirstWeight :=', 'BEFORE_hfirstWeight'),
        ('  have hpair :=', 'BEFORE_hpair'),
        ('  have hcoeff :', 'BEFORE_hcoeff'),
        ('  have hconstant :', 'BEFORE_hconstant'),
        ('  have hupper :', 'BEFORE_hupper'),
        ('  have h := mul_le_mul hpair hcoeff', 'BEFORE_h'),
        ('  have hreordered := normalizedOriginalLabel_reorder_bound', 'BEFORE_hreordered'),
        ('  exact hreordered.trans_eq (congrArg', 'AFTER_hreordered'),
        ('  exact hreordered.trans_eq (congrArg', 'BEFORE_FINAL_TRANSPORT'),
    ]:
        add(text.index(anchor, body), label)
    end = text.index('\nend HeckeSkeleton.Moments.EngineStep', body)
    add(end, 'AFTER_FINAL_TRANSPORT')
    add(end, 'AFTER_INDEX_DECLARATION', False)
    print_allowance = text.index('#print axioms HeckeSkeleton.Moments.EngineStep.normalized_pair_original_allowance_from_atoms')
    print_index = text.index('#print axioms HeckeSkeleton.Moments.EngineStep.normalized_pair_original_index_weight')
    add(print_allowance, 'BEFORE_PRINT_ALLOWANCE', False)
    add(print_index, 'AFTER_PRINT_ALLOWANCE', False)
    add(print_index, 'BEFORE_PRINT_INDEX', False)
    add(len(text), 'AFTER_PRINT_INDEX', False)
    entries.sort(key=lambda entry: entry['offset_characters'])
    parts, cursor, position = [], 0, 0
    for entry in entries:
        offset = entry['offset_characters']
        prefix = text[cursor:offset]
        parts.append(prefix)
        position += len(prefix)
        entry['diagnostic_offset_characters'] = position
        parts.append(entry['text'])
        position += len(entry['text'])
        cursor = offset
    parts.append(text[cursor:])
    diagnostic = ''.join(parts)
    restored = diagnostic
    for entry in reversed(entries):
        offset, block = entry['diagnostic_offset_characters'], entry['text']
        assert restored[offset:offset + len(block)] == block
        restored = restored[:offset] + restored[offset + len(block):]
    assert restored.encode('utf-8') == source
    assert diagnostic.count('#print axioms ') == text.count('#print axioms ') == 2
    return diagnostic.encode('utf-8'), entries


def apply_index_linter_control(source, diagnostic, insertions, enabled):
    """Add one local option after the header marker, immediately before include L."""
    source_text = source.decode('utf-8')
    marker_text = diagnostic.decode('utf-8')
    adjusted = [dict(entry) for entry in insertions]

    def remove_markers(text, entries):
        for entry in reversed(entries):
            offset, block = entry['diagnostic_offset_characters'], entry['text']
            assert text[offset:offset + len(block)] == block
            text = text[:offset] + text[offset + len(block):]
        return text

    assert remove_markers(marker_text, insertions).encode('utf-8') == source
    control = {'enabled': bool(enabled), 'applied': False,
               'option_name': 'linter.unusedSectionVars',
               'option_value': False if enabled else None,
               'scope': 'temporary copy: normalized_pair_original_index_weight only',
               'original_module_acceptance': False,
               'marker_only_diagnostic_sha256': sha(diagnostic),
               'source_with_only_option_sha256': sha(source),
               'removed_option_then_markers_restore_exact_source': True,
               'removed_markers_then_option_restore_exact_source': True}
    if not enabled:
        return diagnostic, adjusted, control

    option = 'set_option linter.unusedSectionVars false in\n'
    declaration = 'theorem normalized_pair_original_index_weight'
    theorem = source_text.index(declaration)
    source_offset = source_text.rfind('include L in\n', 0, theorem)
    assert source_offset >= 0 and option not in marker_text
    # Keep the original docstring between include and theorem byte for byte.
    header_prefix = source_text[source_offset:theorem]
    anchor = header_prefix + declaration
    assert marker_text.count(anchor) == 1
    offset = marker_text.index(anchor)
    header_marker = next(entry for entry in insertions if entry['label'] == 'BEFORE_INDEX_HEADER')
    assert header_marker['diagnostic_offset_characters'] + len(header_marker['text']) == offset
    controlled = marker_text[:offset] + option + marker_text[offset:]
    assert controlled[offset:offset + len(option) + len('include L in\n')] == option + 'include L in\n'
    for entry in adjusted:
        if entry['diagnostic_offset_characters'] >= offset:
            entry['diagnostic_offset_characters'] += len(option)

    without_option = controlled[:offset] + controlled[offset + len(option):]
    assert without_option == marker_text
    without_markers = remove_markers(controlled, adjusted)
    expected_option_source = source_text[:source_offset] + option + source_text[source_offset:]
    assert without_markers == expected_option_source
    assert (without_markers[:source_offset] +
            without_markers[source_offset + len(option):]).encode('utf-8') == source
    assert controlled.count('#print axioms ') == source_text.count('#print axioms ') == 2
    control.update(applied=True, option_text=option,
                   option_bytes=len(option.encode('utf-8')),
                   option_offset_in_original_characters=source_offset,
                   option_offset_in_original_bytes=len(source_text[:source_offset].encode('utf-8')),
                   option_offset_in_diagnostic_characters=offset,
                   option_offset_in_diagnostic_bytes=len(marker_text[:offset].encode('utf-8')),
                   source_with_only_option_sha256=sha(without_markers.encode('utf-8')))
    return controlled.encode('utf-8'), adjusted, control


def cleanup_process_group(process, pgid, grace_seconds=10):
    """Clean only this Popen(start_new_session=True) group's saved PGID."""
    before = time.monotonic()
    record = {'pgid': pgid, 'grace_seconds': grace_seconds,
              'term_sent': False, 'kill_sent': False,
              'leader_wait_timed_out': False}

    def group_present():
        # Reap the leader if ready, but never use its exit as group liveness.
        process.poll()
        try:
            os.killpg(pgid, 0)
            return True
        except ProcessLookupError:
            return False

    def send(sig):
        try:
            os.killpg(pgid, sig)
            return True
        except ProcessLookupError:
            return False

    try:
        if pgid != process.pid or pgid <= 1 or pgid == os.getpgrp():
            raise ValueError('Refusing to signal a group not created for this command')
        record['group_present_before'] = group_present()
        if record['group_present_before']:
            record['term_sent'] = send(signal.SIGTERM)
            deadline = time.monotonic() + grace_seconds
            while group_present():
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    record['kill_sent'] = send(signal.SIGKILL)
                    break
                time.sleep(min(0.1, remaining))
        try:
            process.wait(timeout=1)
        except subprocess.TimeoutExpired:
            record['leader_wait_timed_out'] = True
        # A zombie-only group may still exist; report it without waiting forever.
        record['group_present_after'] = group_present()
    except (OSError, ValueError) as error:
        record['error'] = type(error).__name__ + ': ' + str(error)
    record['leader_exit_code_after_cleanup'] = process.poll()
    record['elapsed_seconds'] = time.monotonic() - before
    return record


def main():
    args = parse_args()
    root = Path.cwd().resolve()
    evidence = root / os.environ['EVIDENCE_DIR'] / 'normalized-diagnostic'
    evidence.mkdir(parents=True, exist_ok=True)
    result = {'scope': 'complete instrumented source, diagnostic only',
              'original_module_acceptance': False, 'heartbeat_override': None,
              'lean_async_override': None, 'driver_sha256': sha(Path(__file__).read_bytes()),
              'commands': [],
              'disable_index_unused_section_vars': args.disable_index_unused_section_vars,
              'diagnostic_control_applied': False}
    started = time.monotonic()
    input_file = root / 'MomEngineBNormalizedIndexDiagnostic.lean'
    diagnostic = None
    owned_input = False

    def run(name, command, timeout=None):
        print(json.dumps({'step': name, 'command': command}), flush=True)
        before = time.monotonic()
        timed_out = False
        with (evidence / (name + '.log')).open('wb') as log:
            process = subprocess.Popen(command, cwd=root, stdout=log, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            pgid = process.pid
            try:
                process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
            finally:
                native_elapsed_seconds = time.monotonic() - before
                native_exit_code_before_cleanup = process.poll()
                cleanup = cleanup_process_group(process, pgid, grace_seconds=10)
        record = {'step': name, 'command': command, 'exit_code': process.returncode,
                  'timed_out': timed_out, 'timeout_seconds': timeout,
                  'native_exit_code_before_cleanup': native_exit_code_before_cleanup,
                  'native_elapsed_seconds': native_elapsed_seconds,
                  'cleanup': cleanup,
                  'elapsed_seconds': time.monotonic() - before}
        result['commands'].append(record)
        print(json.dumps(record), flush=True)
        return record

    try:
        source = (root / SOURCE).read_bytes()
        result.update(source_path=str(SOURCE), source_sha256=sha(source),
                      head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
        if sha(source) != SOURCE_SHA:
            raise RuntimeError('Diagnostic frozen to 4b99 source; current source differs')
        (evidence / 'NormalizedOriginalLabelMass.original.lean').write_bytes(source)
        diagnostic, insertions = instrument(source)
        diagnostic, insertions, linter_control = apply_index_linter_control(
            source, diagnostic, insertions, args.disable_index_unused_section_vars)
        result.update(linter_control=linter_control,
                      diagnostic_control_applied=linter_control['applied'])
        (evidence / input_file.name).write_bytes(diagnostic)
        (evidence / 'instrumentation.json').write_text(json.dumps({
            'source_sha256': sha(source), 'diagnostic_sha256': sha(diagnostic),
            'removed_markers_restore_exact_source': not linter_control['enabled'],
            'removed_option_then_markers_restore_exact_source': True,
            'removed_markers_then_option_restore_exact_source': True,
            'marker_offsets_reference': 'actual temporary diagnostic source',
            'linter_control': linter_control, 'insertions': insertions,
        }, indent=2, ensure_ascii=False) + '\n')
        (evidence / 'markers.diff').write_text(''.join(difflib.unified_diff(
            source.decode().splitlines(True), diagnostic.decode().splitlines(True),
            fromfile=str(SOURCE), tofile=input_file.name)))
        imports = re.findall(r'^import ([A-Za-z_][A-Za-z_0-9.]*)$', source.decode(), re.MULTILINE)
        assert imports == ['HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalHybridMass',
                           'HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityRelativeScalar']
        version = run('toolchain', ['lake', 'env', 'lean', '--version'])
        version_text = (evidence / 'toolchain.log').read_text()
        if version['exit_code'] or '4.35.0-rc3' not in version_text or LEAN_COMMIT not in version_text:
            raise RuntimeError('Pinned Lean toolchain check failed')
        deps = run('dependencies', ['lake', 'build', *('+' + name + ':olean' for name in imports)])
        if deps['exit_code']:
            raise RuntimeError('Original imports failed; target diagnostic was not started')
        if input_file.exists():
            raise RuntimeError('Temporary diagnostic input already exists')
        input_file.write_bytes(diagnostic)
        owned_input = True
        output = Path(tempfile.mkdtemp(prefix='mom-engine-b-normalized-'))
        result.update(diagnostic_source_sha256=sha(diagnostic), input_path=str(input_file),
                      compiler_output_directory=str(output), original_imports=imports)
        native = run('native', ['lake', 'env', 'lean', '-j2', '-DautoImplicit=false',
                     '-DrelaxedAutoImplicit=false', '-Dprofiler=true', '-DstderrAsMessages=false',
                     '-o', str(output / 'NormalizedDiagnostic.olean'),
                     '-i', str(output / 'NormalizedDiagnostic.ilean'), str(input_file)], timeout=150)
        result['native'] = native
        result['diagnostic_input_unchanged'] = input_file.read_bytes() == diagnostic
        result['compiler_outputs'] = [{'name': p.name, 'bytes': p.stat().st_size}
                                      for p in sorted(output.iterdir()) if p.is_file()]
    except Exception as error:
        result['diagnostic_error'] = str(error)
        print('Diagnostic incomplete: ' + str(error), flush=True)
    finally:
        result['source_sha256_after'] = sha((root / SOURCE).read_bytes())
        result['original_source_unchanged'] = result['source_sha256_after'] == SOURCE_SHA
        result['elapsed_seconds'] = time.monotonic() - started
        (evidence / 'diagnostic-result.json').write_text(json.dumps(result, indent=2) + '\n')
        if owned_input and input_file.exists() and input_file.read_bytes() == diagnostic:
            input_file.unlink()
    # The immediately following original verify.py remains the acceptance gate.
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
