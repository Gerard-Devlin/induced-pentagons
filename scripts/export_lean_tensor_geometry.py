#!/usr/bin/env python3
"""Export reusable flag-tensor sample geometry; Lean checks the entire multiset."""
from __future__ import annotations
import argparse
from itertools import combinations, permutations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'formal/paper/InducedPentagonsPaper/Generated/TensorGeometry.lean'


def tuple_literal(values):
    return '![' + ', '.join(map(str, values)) + ']'


def source():
    text = ('import InducedPentagonsPaper.FlagTensorRecount\n\n'
            'set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
            'namespace InducedPentagons.Paper\n\n')
    for roots, free, name in [(1, 3, 'one'), (3, 2, 'three')]:
        rows = []
        for root in permutations(range(7), roots):
            remaining = sorted(set(range(7)) - set(root))
            for left in combinations(remaining, free):
                right = tuple(sorted(set(remaining) - set(left)))
                rows.append(f'  (⟨{tuple_literal(root)}, by decide⟩, '
                            f'{tuple_literal(root + left)}, {tuple_literal(root + right)})')
        text += (f'def tensorVertexList_{name} : List (JointFlagVertexPair 7 {roots} {free}) :=\n'
                 '  ([' + ',\n'.join(rows) + f'] : List (JointFlagVertexPair 7 {roots} {free}))\n\n'
                 f'def tensorVertexPairs_{name} : Multiset (JointFlagVertexPair 7 {roots} {free}) := tensorVertexList_{name}\n\n'
                 f'theorem tensorVertexPairs_{name}_checked :\n'
                 f'    jointFlagVertexPairs (n := 7) (roots := {roots}) (free := {free}) '
                 f'(by decide) = tensorVertexPairs_{name} := by\n  decide +kernel\n\n')
    return text + 'end InducedPentagons.Paper\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    expected = source().encode('utf-8')
    if args.check:
        if not OUT.is_file() or OUT.read_bytes() != expected:
            raise SystemExit('Stale tensor geometry export')
    else:
        OUT.write_bytes(expected)
    print('tensor geometry: ' + ('current' if args.check else 'exported') + ' (140 + 1260 samples)')


if __name__ == '__main__':
    main()
