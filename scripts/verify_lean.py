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
]


def fingerprints():
    paths = [p for p in FORMAL.rglob('*') if p.is_file() and
             not any(part.startswith('.') for part in p.relative_to(FORMAL).parts) and
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
  let q' := { q with numerator := q.numerator + (q.denominator : Int),
                    scaled := q.scaled + (span0.scale : Int) }
  { span0 with terms := span0.terms.set! 0 { t with coefficient := q' } }
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
            path.write_text(prefix + text, encoding='utf-8')
            print('Checking Lean rejection: ' + name, flush=True)
            result = subprocess.run([lake, 'env', 'lean', str(path)], cwd=FORMAL,
                                    capture_output=True, text=True, encoding='utf-8', errors='replace')
            output = result.stdout + result.stderr
            if result.returncode == 0 or 'decide' not in output or 'is false' not in output:
                raise RuntimeError(f'{name}: corruption did not fail as a false Lean proposition:\n{output}')
            records.append({'case': name, 'status': 'rejected_as_false', 'exit_code': result.returncode})
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
    for path in FORMAL.rglob('*.lean'):
        if '.lake' in path.relative_to(FORMAL).parts:
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
    for line in audit.splitlines():
        match = re.match(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[(.*)\])", line)
        if match:
            names = [] if match[2].startswith('does not') else [x.strip() for x in (match[3] or '').split(',') if x.strip()]
            if set(names) - ALLOWED_AXIOMS:
                raise RuntimeError('Unexpected transitive axioms: ' + line)
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
    output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': report['status'], 'output': str(output),
                      'rejections': len(rejected), 'seconds': round(report['elapsed_seconds'], 2)}, indent=2))


if __name__ == '__main__':
    main()
