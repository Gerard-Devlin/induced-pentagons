#!/usr/bin/env python3
"""Build and audit the Mathlib-based mathematical proof layer."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / 'formal/paper'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
AUDITED = ('toSimpleGraph_adj dart_card_blowUp pentagon_card_blowUp '
           'pentagon_card_withIsolates edgeMass_nonnegative pentagonMass_nonnegative '
           'edgeMass_scale pentagonMass_scale edgeMass_unit pentagonMass_unit '
           'edgeMass_blowUp pentagonMass_blowUp pentagonMass_withIsolates '
           'squaredRatio_scale squaredRatio_blowUp clebsch_dart_card '
           'clebsch_balanced_edgeMass clebsch_blowUp_edges periodicCost_add '
           'periodicCost_sum periodicCost_le_profileCost reduced_scalar_profile '
           'scalar_profile_cost scalar_profile bernoulliWeight_nonnegative '
           'bernoulliWeight_sum bernoulliExtension_le bernoulliExtension_pattern '
           'bernoulliExtension_patterns pattern_sum_le_of_boolean_bound '
           'mem_labelledPentagons candidateWalks_nodup labelledPentagons_nodup '
           'pentagon_card_eq_labelled_length clebsch_labelled_pentagons '
           'clebsch_pentagon_card clebsch_balanced_pentagonMass clebsch_blowUp_pentagons '
           'sharpConstant_positive sharpConstant_sq clebsch_balanced_squared_equality '
           'clebsch_balanced_sharp_equality clebsch_squaredRatio_unit '
           'clebsch_balanced_squaredRatio').split()


def sources():
    for directory, folders, files in os.walk(PAPER):
        folders[:] = [n for n in folders if not n.startswith('.') and n != '__pycache__']
        yield from (Path(directory) / n for n in files if not n.startswith('.'))
    yield ROOT / 'formal/InducedPentagons/FiniteGraph.lean'
    yield ROOT / 'formal/InducedPentagons/Isolates.lean'
    yield Path(__file__)


def fingerprints():
    return {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(set(sources()))}


def run(command, *, capture=False):
    result = subprocess.run(command, cwd=PAPER, text=True, encoding='utf-8',
                            errors='replace', capture_output=capture)
    if result.returncode:
        if capture:
            print(result.stdout + result.stderr, end='')
        raise subprocess.CalledProcessError(result.returncode, command)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-build', action='store_true',
                        help='Require the existing build to be current (for CI).')
    args = parser.parse_args()
    started = time.time()
    lake = shutil.which('lake')
    if lake is None:
        raise SystemExit('Lake is not on PATH. Install formal/paper/lean-toolchain first.')
    os.environ.setdefault('LEAN_NUM_THREADS', '2')
    initial = fingerprints()
    for path in sources():
        if path.suffix == '.lean' and re.search(
                r'\b(sorry|admit|native_decide|sorryAx|ofReduceBool)\b|(?m:^\s*axiom\s)',
                path.read_text(encoding='utf-8')):
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
            names = [] if match[2].startswith('does not') else [
                x.strip() for x in (match[3] or '').split(',') if x.strip()]
            if set(names) - ALLOWED_AXIOMS:
                raise RuntimeError('Unexpected transitive axioms: ' + line)
            audited[match[1]] = names
    if set(audited) != {'InducedPentagons.Paper.' + n for n in AUDITED}:
        raise RuntimeError('The axiom audit did not cover exactly the required declarations')
    final = fingerprints()
    if initial != final:
        raise RuntimeError('Proof sources changed during verification; rerun on a stable checkout')
    report = {'schema': 'induced-pentagons.lean-paper-verification.v1',
              'status': 'verified_lean_mathematical_components',
              'scope': ['finite weighted graph and blow-up identities',
                        'complete labelled Clebsch pentagon count and sharp construction equality',
                        'Bernoulli multilinear extension and Boolean bound transfer',
                        'scalar optimization in Lemma 12.1, with explicit envelope hypotheses'],
              'full_paper_formalized': False, 'toolchain': version,
              'mathlib_revision': next(p['rev'] for p in json.loads(
                  (PAPER / 'lake-manifest.json').read_text())['packages'] if p['name'] == 'mathlib'),
              'axioms': audited, 'allowed_standard_axioms': sorted(ALLOWED_AXIOMS),
              'source_sha256': final, 'elapsed_seconds': time.time() - started}
    output = ROOT / 'results/lean_paper_verification.json'
    output.write_bytes((json.dumps(report, indent=2) + '\n').encode('utf-8'))
    print(json.dumps({'status': report['status'], 'declarations_audited': len(audited),
                      'seconds': round(report['elapsed_seconds'], 2)}, indent=2))


if __name__ == '__main__':
    main()
