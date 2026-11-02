#!/usr/bin/env python3
"""Export checked rooted classifiers whose outputs are actual tensor-basis indices."""
from __future__ import annotations

import argparse
import hashlib
from itertools import combinations, permutations
import json
from pathlib import Path
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'formal/paper/InducedPentagonsPaper/Generated'
sys.path.insert(0, str(ROOT / 'src'))
from proof_specification import FLAG_SPECIFICATIONS


def generated_files() -> dict[str, bytes]:
    outputs = {}
    with np.load(ROOT / 'certificates/flag_basis.npz', allow_pickle=False) as archive:
        for block, (name, (roots, n, root_edges, dimension, _)) in enumerate(FLAG_SPECIFICATIONS.items()):
            pairs = list(combinations(range(n), 2))
            index = {p: i for i, p in enumerate(pairs)}
            bits = len(pairs)
            root_mask = sum(1 << index[e] for e in root_edges)
            root_bits = sum(1 << i for i, (_, j) in enumerate(pairs) if j < roots)
            basis = [int(v) for v in archive['flag_masks_' + name]]
            positions = {mask: i for i, mask in enumerate(basis)}
            if len(basis) != dimension or len(positions) != dimension:
                raise RuntimeError('Unexpected rooted basis dimensions: ' + name)
            perms = [tuple(range(roots)) + p for p in permutations(range(roots, n))]
            rows = []
            for source in range(1 << bits):
                if source & root_bits != root_mask:
                    rows.append((source, 0, 0, 0))
                    continue
                def relabel(p):
                    return sum(((source >> index[tuple(sorted((p[i], p[j])))]) & 1) << k
                               for k, (i, j) in enumerate(pairs))
                target, q = min((relabel(p), p) for p in perms)
                inverse = [q.index(i) for i in range(n)]
                code = sum(v * 8**i for i, v in enumerate(inverse))
                rows.append((source, target, code, positions[target]))
            source = ('import InducedPentagonsPaper.FlagIndex\n'
                      'import InducedPentagonsPaper.Generated.FlagSeparation\n\n'
                      'set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
                      'namespace InducedPentagons.Paper\n\n'
                      f'def indexedFlagBasis_{name} : Vector Nat {dimension} := #v[' + ', '.join(map(str, basis)) + ']\n\n'
                      f'def indexedFlagData_{name} : Vector (IndexedFlagWitness {dimension}) {1 << bits} := #v[\n')
            source += ',\n'.join(f'  ⟨⟨{m}, {target}, {code}⟩, {i}⟩' for m, target, code, i in rows) + '\n]\n\n'
            source += (f'def indexedFlagLookup_{name} (m : Fin {1 << bits}) : IndexedFlagWitness {dimension} :=\n'
                       f'  indexedFlagData_{name}[m]\n\n'
                       f'theorem indexedFlagBasis_{name}_toList : indexedFlagBasis_{name}.toList = flagBasis_{name} := by\n'
                       '  decide +kernel\n\n'
                       f'theorem indexedFlagBasis_{name}_injective :\n'
                       f'    Function.Injective (fun i : Fin {dimension} => indexedFlagBasis_{name}[i]) := by\n'
                       '  decide +kernel\n\n'
                       f'theorem indexedFlagBasis_{name}_certificate :\n'
                       f'    indexedFlagBasis_{name}.toList = (Generated.certificate.blocks[{block}]!).masks.toList := by\n'
                       f'  rw [indexedFlagBasis_{name}_toList]\n'
                       f'  exact flag_basis_{name}_certificate\n\n'
                       f'theorem indexedFlagBasis_{name}_certificateAt : ∀ i : Fin {dimension},\n'
                       f'    indexedFlagBasis_{name}[i] = (Generated.certificate.blocks[{block}]!).masks[i.val]! := by\n'
                       '  decide +kernel\n\n'
                       f'theorem indexedFlagBasis_{name}_separated :\n'
                       f'    RootedFlagBasisSeparated {n} {roots} indexedFlagBasis_{name}.toList := by\n'
                       f'  rw [indexedFlagBasis_{name}_toList]\n'
                       f'  exact flag_basis_{name}_separated\n\n'
                       f'theorem indexedFlagLookup_{name}_checked :\n'
                       f'    flagIndexLookupCheck {n} {bits} {roots} {root_mask} indexedFlagBasis_{name} indexedFlagLookup_{name} = true := by\n'
                       '  decide +kernel\n\n'
                       f'def indexedFlag_{name} (g : Graph (Fin {n})) : Fin {dimension} :=\n'
                       f'  flagIndex {bits} indexedFlagLookup_{name} g\n\n')
            hs = f'edgeIndexSeparated_{"four" if n == 4 else "five"}'
            hb = f'edgeIndexBounded_{"four" if n == 4 else "five"}'
            common = (f'{hs} {hb}\n'
                      f'    indexedFlagLookup_{name}_checked indexedFlagBasis_{name}_separated\n'
                      f'    indexedFlagBasis_{name}_injective')
            source += (f'theorem indexedFlag_{name}_sound (g : Graph (Fin {n}))\n'
                       f'    (hg : rootTypeCheck {roots} {root_mask} g = true) :\n'
                       f'    Nonempty (RootedGraphEquiv {roots} g (maskGraph {n} indexedFlagBasis_{name}[indexedFlag_{name} g])) :=\n'
                       f'  flagIndex_sound {hs} {hb} indexedFlagLookup_{name}_checked g hg\n\n'
                       f'theorem indexedFlag_{name}_eq_iff (g : Graph (Fin {n}))\n'
                       f'    (hg : rootTypeCheck {roots} {root_mask} g = true) (j : Fin {dimension}) :\n'
                       f'    indexedFlag_{name} g = j ↔\n'
                       f'      Nonempty (RootedGraphEquiv {roots} g (maskGraph {n} indexedFlagBasis_{name}[j])) :=\n'
                       f'  flagIndex_eq_iff {common} g hg j\n\n'
                       f'theorem indexedFlag_{name}_isomorphic {{g h : Graph (Fin {n})}}\n'
                       f'    (hg : rootTypeCheck {roots} {root_mask} g = true) (hh : rootTypeCheck {roots} {root_mask} h = true)\n'
                       f'    (e : RootedGraphEquiv {roots} g h) : indexedFlag_{name} g = indexedFlag_{name} h :=\n'
                       f'  flagIndex_isomorphic {common} hg hh e\n\n'
                       'end InducedPentagons.Paper\n')
            outputs[f'IndexedFlag_{name}.lean'] = source.encode('utf-8')
    source = ''.join(f'import InducedPentagonsPaper.Generated.IndexedFlag_{n}\n' for n in FLAG_SPECIFICATIONS)
    source += ('\nnamespace InducedPentagons.Paper\n\n'
               'set_option maxHeartbeats 0 in\nset_option maxRecDepth 100000 in\n'
               'theorem indexedFlag_wrong_index_rejected :\n'
               '    flagIndexLookupCheck 4 6 1 0 indexedFlagBasis_one_root\n'
               '      (fun m => if m.val = 0 then { indexedFlagLookup_one_root m with index := 1 }\n'
               '        else indexedFlagLookup_one_root m) = false := by\n'
               '  decide +kernel\n\nend InducedPentagons.Paper\n')
    outputs['IndexedFlagTables.lean'] = source.encode('utf-8')
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    outputs = generated_files()
    inputs = ('src/proof_specification.py', 'certificates/flag_basis.npz')
    binding = {
        'schema': 'induced-pentagons.lean-indexed-flags.v1',
        'meaning': 'Candidate rooted witnesses and basis indices; every valid-root slot is checked by Lean',
        'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'input_sha256': {n: hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in inputs},
        'output_sha256': {n: hashlib.sha256(data).hexdigest() for n, data in outputs.items()},
        'lookup_slots': 4160, 'valid_root_slots': 576,
    }
    expected = {**outputs, 'indexed_flag_manifest.json': (json.dumps(binding, indent=2)+'\n').encode('utf-8')}
    if args.check:
        for name, data in expected.items():
            if not (OUT/name).is_file() or (OUT/name).read_bytes() != data:
                raise SystemExit('Stale indexed flag export: ' + name)
        if {p.name for p in OUT.glob('IndexedFlag*.lean')} != outputs.keys():
            raise SystemExit('Extra or missing indexed flag modules')
    else:
        OUT.mkdir(parents=True, exist_ok=True)
        for name, data in expected.items():
            (OUT/name).write_bytes(data)
    print(json.dumps({'status': 'current' if args.check else 'exported', 'files': len(outputs)}))


if __name__ == '__main__':
    main()
