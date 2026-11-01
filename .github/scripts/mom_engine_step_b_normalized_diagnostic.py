#!/usr/bin/env python3
"""Observe the complete 4efc Normalized proof phases; never substitute for verification."""
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
SOURCE_SHA = '4efc93470cfd5cd8916c71fabebd2711cdb2723c314eeb5f0f8763fec7ecf682'
LEAN_COMMIT = '470d5ce1400764999581fd26d5d72b00d990b0f4'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def instrument(source):
    """Insert boundary markers only; certify exact restoration of all source bytes."""
    text = source.decode('utf-8')
    theorem = text.index('theorem normalized_pair_original_index_weight')
    body = text.index(' := by\n', theorem) + len(' := by\n')
    entries = []

    def add(offset, label, tactic=True):
        indent = '  ' if tactic else ''
        block = (indent + ('run_tac' if tactic else 'run_cmd') + '\n' + indent +
                 '  IO.eprintln "MOM_TRACE NormalizedOriginalLabelMass B23_4efc9347 ' + label + '"\n' +
                 indent + '  (← IO.getStderr).flush\n')
        entries.append({'offset_characters': offset, 'label': label, 'text': block})

    helper = text.index('private theorem normalizedOriginalLabel_reorder_bound')
    add(helper, 'BEFORE_REORDER_HELPER', False)
    add(text.index('variable {F : Type}', helper), 'AFTER_REORDER_HELPER_DECLARATION', False)
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
        ('  refine hreordered.trans_eq ?_', 'AFTER_hreordered'),
        ('  rw [TwoDivisorCommonBranch.indexWeight, hleft, hright, hdivisor]', 'BEFORE_FINAL_RW'),
    ]:
        add(text.index(anchor, body), label)
    end = text.index('\nend HeckeSkeleton.Moments.EngineStep', body)
    add(end, 'AFTER_FINAL_RW')
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


def main():
    root = Path.cwd().resolve()
    evidence = root / os.environ['EVIDENCE_DIR'] / 'normalized-diagnostic'
    evidence.mkdir(parents=True, exist_ok=True)
    result = {'scope': 'complete instrumented source, diagnostic only',
              'original_module_acceptance': False, 'heartbeat_override': None,
              'lean_async_override': None, 'driver_sha256': sha(Path(__file__).read_bytes()),
              'commands': []}
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
            try:
                process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
            finally:
                if process.poll() is None:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
        record = {'step': name, 'command': command, 'exit_code': process.returncode,
                  'timed_out': timed_out, 'timeout_seconds': timeout,
                  'elapsed_seconds': time.monotonic() - before}
        result['commands'].append(record)
        print(json.dumps(record), flush=True)
        return record

    try:
        source = (root / SOURCE).read_bytes()
        result.update(source_path=str(SOURCE), source_sha256=sha(source),
                      head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
        if sha(source) != SOURCE_SHA:
            raise RuntimeError('Diagnostic frozen to 4efc source; current source differs')
        (evidence / 'NormalizedOriginalLabelMass.original.lean').write_bytes(source)
        diagnostic, insertions = instrument(source)
        (evidence / input_file.name).write_bytes(diagnostic)
        (evidence / 'instrumentation.json').write_text(json.dumps({
            'source_sha256': sha(source), 'diagnostic_sha256': sha(diagnostic),
            'removed_markers_restore_exact_source': True, 'insertions': insertions,
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
