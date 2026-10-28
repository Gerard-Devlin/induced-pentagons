#!/usr/bin/env python3
"""Build the finite Lean certificate project, audit axioms and reject corruptions."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / 'formal'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
AUDITED = [
    'InducedPentagons.Generated.coreCertificateVerified',
    'InducedPentagons.Generated.metadata_checked',
    *(f'InducedPentagons.Generated.span_{i}_checked' for i in range(4)),
    'InducedPentagons.integer_square_nonnegative',
    'InducedPentagons.weightedSquares_nonnegative',
    'InducedPentagons.positive_square_vanishes',
    *(f'InducedPentagons.{name}' for name in (
        'inducedPentagon_injective', 'blowUp_projection_injective',
        'project_liftPentagon', 'lift_projectPentagon', 'clone_liftPentagon',
        'mem_inducedPentagons', 'clebsch_degree', 'clebsch_edges',
        'clebsch_triangle_free', 'clebsch_codegrees', 'clebsch_pentagon_enumeration',
        'clebsch_pentagons', 'clebsch_pentagons_nodup', 'clebsch_sharp_normalization',
        'pentagon_avoids_isolates', 'remove_addIsolatesPentagon', 'add_removeIsolatesPentagon',
        'squareSum_zero_iff', 'squareSum_parity', 'balanced_integer_variance_gap')),
]


def source_files():
    for directory, folders, files in os.walk(FORMAL):
        folders[:] = [n for n in folders if not n.startswith('.') and n != '__pycache__']
        yield from (Path(directory) / n for n in files if not n.startswith('.'))


def fingerprints():
    paths = [p for p in source_files() if
             (p.suffix in {'.lean', '.json', '.toml', '.md'} or p.name == 'lean-toolchain')]
    paths += [ROOT / 'scripts/export_lean_certificate.py', Path(__file__)]
    return {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(set(paths))}


def run(command, *, capture=False, cwd=FORMAL):
    result = subprocess.run(command, cwd=cwd, text=True, encoding='utf-8',
                            errors='replace', capture_output=capture)
    if result.returncode:
        if capture:
            print(result.stdout, end='')
            print(result.stderr, end='', file=sys.stderr)
        raise subprocess.CalledProcessError(result.returncode, command)
    return result


def rejection_checks(lake):
    prefix = ('import InducedPentagons\nopen InducedPentagons InducedPentagons.Generated\n'
              'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n')
    cases = {
        'changed_rational_binding': '''
def badCoefficient : Coefficient :=
  { certificate.free[0]! with scaled := certificate.free[0]!.scaled + 1 }
example : checkCoefficient certificate.scale badCoefficient = true := by decide +kernel
''',
        'changed_gram_entry': '''
def badGram : GramData :=
  gramData.set! 0 (gramData[0]!.set! 0
    (gramData[0]![0]!.set! 0 (gramData[0]![0]![0]! + 1)))
example : checkGramRowFast certificate badGram 0 0 = true := by decide +kernel
''',
        'changed_host_pattern_count': '''
def badHost : HostRow :=
  let h := hostChunk000[0]!
  { h with primitive := h.primitive.set! 1 (h.primitive[1]! + 1) }
example : checkHost certificate gramData badHost = true := by decide +kernel
''',
        'changed_span_with_valid_rational_binding': '''
def badSpan : SpanWitness :=
  let t := span0.terms[0]!
  let q := t.coefficient
  let q1 : Coefficient := { q with numerator := q.numerator + (q.denominator : Int) }
  let q2 : Coefficient := { q1 with scaled := q.scaled + (span0.scale : Int) }
  { span0 with terms := span0.terms.set! 0 { t with coefficient := q2 } }
example : checkSpan certificate badSpan = true := by decide +kernel
''',
    }
    cache = (FORMAL / '.lake').resolve()
    cache.mkdir(exist_ok=True)
    temporary = tempfile.TemporaryDirectory(prefix='lean-reject-', dir=cache)
    work = Path(temporary.name).resolve()
    if not work.is_relative_to(cache):
        raise RuntimeError('Unexpected temporary-directory target')
    records = []
    try:
        for name, text in cases.items():
            path = work / f'{name}.lean'
            print('Checking Lean rejection: ' + name, flush=True)
            claim = re.search(r'\nexample : (.+) = true := by decide \+kernel\s*$', text)
            if claim is None:
                raise RuntimeError('Malformed rejection test template: ' + name)
            target = claim[1]
            control = (prefix + text[:claim.start()] +
                       f'\ntheorem corrupted_input_rejected : {target} = false := by decide +kernel\n')
            # First require an actual kernel proof of false, so a parsing or
            # reduction failure cannot masquerade as rejecting corrupted data.
            path.write_text(control, encoding='utf-8')
            run([lake, 'env', 'lean', str(path)], capture=True)
            path.write_text(control + f'\nexample : {target} = true := by\n'
                            '  rw [corrupted_input_rejected]\n  decide +kernel\n', encoding='utf-8')
            result = subprocess.run([lake, 'env', 'lean', str(path)], cwd=FORMAL,
                                    capture_output=True, text=True, encoding='utf-8', errors='replace')
            output = result.stdout + result.stderr
            if result.returncode == 0 or 'decide' not in output or 'is false' not in output:
                raise RuntimeError(f'{name}: corruption did not fail as a false Lean proposition:\n{output}')
            records.append({'case': name, 'status': 'rejected_as_false',
                            'false_control_kernel_checked': True, 'exit_code': result.returncode})
    finally:
        temporary.cleanup()
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-build', action='store_true',
                        help='Require a current existing Lake build instead of rebuilding (for CI).')
    parser.add_argument('--kernel-recheck', action='store_true',
                        help='Also run the standalone leanchecker over the compiled project.')
    args = parser.parse_args()
    started = time.time()
    lake = shutil.which('lake')
    if lake is None:
        raise SystemExit('Lake is not on PATH. Install formal/lean-toolchain, then rerun this command.')
    os.environ.setdefault('LEAN_NUM_THREADS', '2')
    run([sys.executable, str(ROOT / 'scripts/export_lean_certificate.py'), '--check'], cwd=ROOT)
    initial = fingerprints()
    for path in source_files():
        if path.suffix != '.lean':
            continue
        text = path.read_text(encoding='utf-8')
        if re.search(r'\b(sorry|admit|native_decide|sorryAx|ofReduceBool)\b|(?m:^\s*axiom\s)', text):
            raise RuntimeError('Disallowed proof escape in ' + str(path.relative_to(ROOT)))
    version = run([lake, 'env', 'lean', '--version'], capture=True).stdout.strip()
    if not re.search(r'Lean \(version 4\.35\.0,', version):
        raise RuntimeError('Unexpected Lean toolchain: ' + version)
    run([lake, '--no-build', 'build'] if args.skip_build else [lake, 'build'])
    audit = run([lake, 'env', 'lean', 'Audit.lean'], capture=True).stdout
    print(audit, end='')
    audited = {}
    for match in re.finditer(
            r"'([^']+)' (does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])", audit):
        names = [] if match[2].startswith('does not') else [
            x.strip() for x in (match[3] or '').split(',') if x.strip()]
        if set(names) - ALLOWED_AXIOMS:
            raise RuntimeError('Unexpected transitive axioms: ' + match[0])
        audited[match[1]] = names
    if set(audited) != set(AUDITED):
        raise RuntimeError('The transitive axiom audit did not cover exactly the required declarations')
    rejected = rejection_checks(lake)
    if args.kernel_recheck:
        run([lake, 'env', 'leanchecker', 'InducedPentagons'])
    final = fingerprints()
    if final != initial:
        raise RuntimeError('Lean sources changed during verification; rerun on a stable checkout')
    manifest = json.loads((FORMAL / 'InducedPentagons/Generated/manifest.json').read_text())
    report = {'schema': 'induced-pentagons.lean-verification.v1',
              'status': 'verified_lean_finite_certificates',
              'scope': manifest['scope'], 'toolchain': version, 'counts': manifest['counts'],
              'proof_method': 'Lean kernel reduction with decide +kernel',
              'axioms': audited, 'allowed_standard_axioms': sorted(ALLOWED_AXIOMS),
              'rejection_cases': rejected, 'standalone_leanchecker_run': args.kernel_recheck,
              'source_sha256': final, 'input_sha256': manifest['inputs'],
              'elapsed_seconds': time.time() - started}
    output = ROOT / 'results/lean_verification.json'
    output.write_bytes((json.dumps(report, indent=2) + '\n').encode('utf-8'))
    print(json.dumps({'status': report['status'], 'output': str(output),
                      'rejections': len(rejected), 'seconds': round(report['elapsed_seconds'], 2)}, indent=2))


if __name__ == '__main__':
    main()
