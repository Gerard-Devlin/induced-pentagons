#!/usr/bin/env python3
"""Export root-preserving witnesses for the five actual certificate flag bases."""
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
        for block, (name, (roots, n, root_edges, dimension, denominator)) in enumerate(
                FLAG_SPECIFICATIONS.items()):
            pairs = list(combinations(range(n), 2))
            pair_index = {e: i for i, e in enumerate(pairs)}
            bits = len(pairs)
            root_mask = sum(1 << pair_index[e] for e in root_edges)
            root_bits = sum(1 << i for i, (_, j) in enumerate(pairs) if j < roots)
            basis = [int(v) for v in archive['flag_masks_' + name]]
            if len(basis) != dimension or int(archive['denominator_' + name]) != denominator:
                raise RuntimeError('Unexpected flag dimension or denominator: ' + name)
            perms = [tuple(range(roots)) + p for p in permutations(range(roots, n))]
            witnesses = []
            for source in range(1 << bits):
                if source & root_bits != root_mask:
                    continue
                def relabel(p):
                    return sum(((source >> pair_index[tuple(sorted((p[i], p[j])))]) & 1) << k
                               for k, (i, j) in enumerate(pairs))
                target, q = min((relabel(p), p) for p in perms)
                inverse = [q.index(i) for i in range(n)]
                code = sum(v * 8**i for i, v in enumerate(inverse))
                witnesses.append((source, target, code))
            if sorted({target for _, target, _ in witnesses}) != basis:
                raise RuntimeError('Candidate representatives differ from the stored flag basis: ' + name)
            source = ('import InducedPentagonsPaper.RootedFlags\n'
                      'import InducedPentagons.Generated.Inputs\n\n'
                      'set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
                      'namespace InducedPentagons.Paper\n\n'
                      f'def flagBasis_{name} : List Nat := {basis}\n\n'
                      f'def flagWitnesses_{name} : List RootedFlagWitness := [\n')
            source += ',\n'.join(f'  ⟨{a}, {b}, {c}⟩' for a, b, c in witnesses) + '\n]\n\n'
            source += (f'theorem flag_sources_{name} :\n'
                       f'    flagWitnesses_{name}.map RootedFlagWitness.source =\n'
                       f'      (List.range (2 ^ {bits})).filter (fun m => rootTypeCheck {roots} {root_mask} (maskGraph {n} m)) := by\n'
                       '  decide +kernel\n\n'
                       f'theorem flag_witnesses_{name}_checked :\n'
                       f'    flagWitnesses_{name}.all (rootedFlagRowCheck {n} {roots} flagBasis_{name}) = true := by\n'
                       '  decide +kernel\n\n'
                       f'theorem flag_basis_{name}_certificate :\n'
                       f'    flagBasis_{name} = (Generated.certificate.blocks[{block}]!).masks.toList := by\n'
                       '  decide +kernel\n\n'
                       f'theorem flag_basis_{name}_count : flagBasis_{name}.length = {dimension} := by decide +kernel\n\n'
                       f'theorem flag_basis_{name}_nodup : flagBasis_{name}.Nodup := by decide +kernel\n\n'
                       f'theorem flag_basis_{name}_types_checked :\n'
                       f'    flagBasis_{name}.all (fun m => rootTypeCheck {roots} {root_mask} (maskGraph {n} m)) = true := by\n'
                       '  decide +kernel\n\n'
                       f'theorem flag_basis_{name}_covers :\n'
                       f'    RootedFlagBasisCovers {n} {roots} {root_mask} flagBasis_{name} :=\n'
                       f'  rootedFlagBasisCovers_of_rows edgeIndexSeparated_{"four" if n == 4 else "five"}\n'
                       f'    edgeIndexBounded_{"four" if n == 4 else "five"} flagBasis_{name} flagWitnesses_{name}\n'
                       f'    flag_sources_{name} flag_witnesses_{name}_checked\n\n'
                       f'theorem certificate_flag_basis_{name}_covers :\n'
                       f'    RootedFlagBasisCovers {n} {roots} {root_mask}\n'
                       f'      (Generated.certificate.blocks[{block}]!).masks.toList := by\n'
                       f'  rw [← flag_basis_{name}_certificate]\n'
                       f'  exact flag_basis_{name}_covers\n\n'
                       'end InducedPentagons.Paper\n')
            outputs[f'FlagBasis_{name}.lean'] = source.encode('utf-8')
    source = ''.join(f'import InducedPentagonsPaper.Generated.FlagBasis_{name}\n'
                     for name in FLAG_SPECIFICATIONS)
    outputs['FlagBases.lean'] = source.encode('utf-8')
    source = ('import InducedPentagonsPaper.Generated.FlagBases\n'
              'import InducedPentagonsPaper.RootedFlagSeparation\n\n'
              'set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
              'namespace InducedPentagons.Paper\n\n')
    for roots, n in ((1, 4), (3, 5)):
        codes = [sum(v * 8**i for i, v in enumerate(tuple(range(roots)) + p))
                 for p in permutations(range(roots, n))]
        source += (f'def rootedPermutationCodes{n} : List Nat := {codes}\n\n'
                   f'theorem rootedPermutationCodes{n}_complete :\n'
                   f'    RootedPermutationCodesComplete {n} {roots} rootedPermutationCodes{n} := by\n'
                   '  unfold RootedPermutationCodesComplete\n'
                   '  decide +kernel\n\n')
    for block, (name, (roots, n, _, _, _)) in enumerate(FLAG_SPECIFICATIONS.items()):
        source += (f'theorem flag_basis_{name}_separation_checked :\n'
                   f'    rootedBasisSeparatedCheck {n} {roots} rootedPermutationCodes{n} flagBasis_{name} = true := by\n'
                   '  decide +kernel\n\n'
                   f'theorem flag_basis_{name}_separated :\n'
                   f'    RootedFlagBasisSeparated {n} {roots} flagBasis_{name} :=\n'
                   f'  rootedBasisSeparatedCheck_sound rootedPermutationCodes{n}_complete\n'
                   f'    flag_basis_{name}_separation_checked\n\n'
                   f'theorem certificate_flag_basis_{name}_separated :\n'
                   f'    RootedFlagBasisSeparated {n} {roots}\n'
                   f'      (Generated.certificate.blocks[{block}]!).masks.toList := by\n'
                   f'  rw [← flag_basis_{name}_certificate]\n'
                   f'  exact flag_basis_{name}_separated\n\n')
    source += ('theorem rootedWitnessCheck_rejects_moved_root :\n'
               '    rootedWitnessCheck 4 1 0 0 1665 = false := by decide +kernel\n\n'
               'theorem rootedWitnessCheck_rejects_wrong_adjacency :\n'
               '    rootedWitnessCheck 4 1 0 1 1672 = false := by decide +kernel\n\n'
               'end InducedPentagons.Paper\n')
    outputs['FlagSeparation.lean'] = source.encode('utf-8')
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    outputs = generated_files()
    inputs = ('src/proof_specification.py', 'certificates/flag_basis.npz')
    manifest = {
        'schema': 'induced-pentagons.lean-rooted-flags.v1',
        'meaning': 'Candidate rooted isomorphisms; Lean checks every witness and coverage source',
        'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'input_sha256': {n: hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in inputs},
        'output_sha256': {n: hashlib.sha256(d).hexdigest() for n, d in outputs.items()},
        'witnesses': 576,
    }
    expected = {**outputs, 'flag_manifest.json': (json.dumps(manifest, indent=2)+'\n').encode('utf-8')}
    if args.check:
        for name, data in expected.items():
            if not (OUT/name).is_file() or (OUT/name).read_bytes() != data:
                raise SystemExit('Stale rooted flag export: ' + name)
        if {p.name for p in OUT.glob('Flag*.lean')} != outputs.keys():
            raise SystemExit('Extra or missing rooted flag modules')
    else:
        OUT.mkdir(parents=True, exist_ok=True)
        for name, data in expected.items():
            (OUT/name).write_bytes(data)
    print(json.dumps({'status': 'current' if args.check else 'exported', 'files': len(outputs)}))


if __name__ == '__main__':
    main()
