#!/usr/bin/env python3
"""Record source hashes and enumerate public HIGHBIN declarations.

This is a source inventory, not a Lean verification result. Exact elaborated
types and transitive axiom sets are produced by highbin_verify.py instead.
"""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / 'docs/highbin'


def without_comments(source):
    out = []
    index = depth = 0
    string = line_comment = False
    while index < len(source):
        char, pair = source[index], source[index:index + 2]
        if line_comment:
            out.append('\n' if char == '\n' else ' ')
            line_comment = char != '\n'
            index += 1
        elif depth:
            if pair in ('/-', '-/'):
                depth += 1 if pair == '/-' else -1
                out.extend('  ')
                index += 2
            else:
                out.append('\n' if char == '\n' else ' ')
                index += 1
        elif string:
            out.append(char)
            if char == '\\' and index + 1 < len(source):
                out.append(source[index + 1])
                index += 2
            else:
                if char == '"':
                    string = False
                index += 1
        elif pair == '--':
            line_comment = True
            out.extend('  ')
            index += 2
        elif pair == '/-':
            depth = 1
            out.extend('  ')
            index += 2
        else:
            out.append(char)
            string = char == '"'
            index += 1
    if depth:
        raise ValueError('Unterminated block comment')
    return ''.join(out)


def declarations(module):
    path = Path(*module.split('.')).with_suffix('.lean')
    raw = (ROOT / path).read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    source = without_comments(raw.decode())
    forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide)\b', source)
    if forbidden:
        raise ValueError(f'{path}: forbidden proof declarations/tactics: {forbidden}')
    stack, result = [], []
    for number, line in enumerate(source.splitlines(), 1):
        namespace = re.match(r'^namespace\s+(\S+)', line)
        section = re.match(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$', line)
        end = re.match(r'^end(?:\s+(\S+))?\s*$', line)
        if namespace:
            stack.append(('namespace', namespace.group(1)))
        elif section:
            stack.append(('section', section.group(1)))
        elif end:
            if not stack:
                raise ValueError(f'{path}:{number}: unmatched end')
            stack.pop()
        match = re.match(
            r'^(?:@\[[^\]]+\]\s*)?'
            r'((?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)'
            r'(theorem|lemma|def|abbrev|structure|inductive)\s+([^\s(:{]+)', line)
        if match and 'private' not in match.group(1).split():
            name = '.'.join([n for kind, n in stack if kind == 'namespace'] + [match.group(3)])
            result.append({'name': name, 'kind': match.group(2), 'source': str(path),
                           'line': number, 'source_sha256': digest})
    return result


def main():
    core = json.loads((DOC / 'core_modules.json').read_text())
    support = ['.'.join(p.relative_to(ROOT).with_suffix('').parts)
               for p in sorted((ROOT / 'HeckeSkeleton/HighBinSupport').glob('*.lean'))]
    groups = {'core': core, 'actual': [m for m in support if m not in core]}
    seen = set()
    for group, modules in groups.items():
        items = [item for module in modules for item in declarations(module)]
        for item in items:
            if item['name'] in seen:
                raise ValueError('Duplicate declaration: ' + item['name'])
            seen.add(item['name'])
        (DOC / f'{group}_modules.json').write_text(json.dumps(modules, indent=2) + '\n')
        (DOC / f'{group}_public_declarations.json').write_text(
            json.dumps(items, ensure_ascii=False, indent=2) + '\n')
        print(f'{group}: {len(modules)} modules, {len(items)} public source declarations')
    mellin = ['HeckeSkeleton.HighBinSupport.' + name for name in (
        'ActualNormFormHigherPrimePowers', 'ActualNormFormMellinInversion',
        'ActualNormFormPrimeDetector', 'ActualNormFormUniformMellin',
        'ActualOrbitalRapidDecay', 'ActualAdditiveMellinRapidDecay')]
    items = [item for module in mellin for item in declarations(module)]
    (DOC / 'mellin_modules.json').write_text(json.dumps(mellin, indent=2) + '\n')
    (DOC / 'mellin_public_declarations.json').write_text(
        json.dumps(items, ensure_ascii=False, indent=2) + '\n')
    print(f'mellin: {len(mellin)} actual modules, {len(items)} public source declarations')
    fourier = ['HeckeSkeleton.HighBinSupport.' + name for name in (
        'ActualGeneratorPowers', 'ActualPrimePowerSymbols', 'ActualGaussData',
        'ActualPrimePowerGauss', 'ActualGaussSigns', 'ActualFinitePoisson',
        'ActualEulerCRT', 'ActualInitialAbsolute')]
    items = [item for module in fourier for item in declarations(module)]
    (DOC / 'fourier_modules.json').write_text(json.dumps(fourier, indent=2) + '\n')
    (DOC / 'fourier_public_declarations.json').write_text(
        json.dumps(items, ensure_ascii=False, indent=2) + '\n')
    print(f'fourier: {len(fourier)} actual modules, {len(items)} public source declarations')
    # Independent arithmetic/analytic frontiers retain their full public
    # HIGHBIN import closure. They can finish while the old named aggregate
    # interface is still building in the complete actual job.
    support_set = set(support)
    core_set = set(core)

    def support_closure(leaves):
        visited = set()

        def visit(module):
            if module in visited or module not in support_set:
                return
            visited.add(module)
            path = ROOT.joinpath(*module.split('.')).with_suffix('.lean')
            for dependency in re.findall(r'^import\s+(\S+)', path.read_text(), re.M):
                visit(dependency)

        for leaf in leaves:
            visit('HeckeSkeleton.HighBinSupport.' + leaf)
        return sorted(visited - core_set)

    frontiers = {
        'euler': ['ActualCanonicalEuler'],
        'normform': ['ActualNormFormComputedPacket', 'ActualCanonicalHighBin',
                     'ActualPhysicalScheduledNorm', 'ActualPhysicalConductorProduct', 'PhysicalNormScalar'],
        'boundary': ['ActualBoundaryGeometry', 'ActualDetectorBoundary',
                     'ActualFinalContourIntegrability', 'ActualDyadicRows',
                     'ActualDyadicBoundary', 'ActualPhysicalBoundary'],
        'canonical': ['ActualTargetFamily', 'ActualCanonicalEuler'],
        'presentation': ['ActualEulerPresentation', 'ActualBoundaryCalibration',
                         'ActualNormFormRegionCalibration', 'ActualNormFormLabels',
                         'ActualPresentationGauge'],
    }
    for group, leaves in frontiers.items():
        modules = support_closure(leaves)
        items = [item for module in modules for item in declarations(module)]
        (DOC / f'{group}_modules.json').write_text(json.dumps(modules, indent=2) + '\n')
        (DOC / f'{group}_public_declarations.json').write_text(
            json.dumps(items, ensure_ascii=False, indent=2) + '\n')
        print(f'{group}: {len(modules)} actual modules, {len(items)} public source declarations')


if __name__ == '__main__':
    main()
