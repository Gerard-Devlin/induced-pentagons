#!/usr/bin/env python3
"""Generate candidate graph-atlas extension witnesses, checked in Lean's kernel."""
from __future__ import annotations

import argparse
import hashlib
from itertools import combinations, permutations
import json
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'formal/paper/InducedPentagonsPaper/Generated'
INPUT = ROOT / 'certificates/graph_atlas_7.json'
GROUP_SIZE = {5: 9, 6: 10}


def extension_mask(n: int, source: int, bits: int) -> int:
    previous = {p: i for i, p in enumerate(combinations(range(n), 2))}
    return sum(
        (((bits >> i) & 1) if j == n else ((source >> previous[i, j]) & 1)) << dst
        for dst, (i, j) in enumerate(combinations(range(n + 1), 2)))


def canonicalizer(n: int):
    pairs = list(combinations(range(n), 2))
    index = {p: i for i, p in enumerate(pairs)}
    perms = list(permutations(range(n)))
    maps = np.array([[index[tuple(sorted((p[i], p[j])))] for i, j in pairs]
                     for p in perms], dtype=np.uint32).reshape(len(perms), len(pairs))

    def canonical(mask: int) -> tuple[int, int]:
        images = np.zeros(len(perms), dtype=np.uint32)
        for dst in range(len(pairs)):
            images |= ((np.uint32(mask) >> maps[:, dst]) & 1) << dst
        selected = int(images.argmin())
        perm = perms[selected]
        inverse = [perm.index(i) for i in range(n)]
        return int(images[selected]), sum(v * 8 ** i for i, v in enumerate(inverse))

    return canonical


def candidates():
    masks = [[0]]
    stages = []
    for n in range(7):
        canonical = canonicalizer(n + 1)
        rows = [[canonical(extension_mask(n, source, bits)) for bits in range(1 << n)]
                for source in masks[n]]
        masks.append(sorted({target for row in rows for target, _ in row}))
        stages.append(rows)
    expected = [h['mask'] for h in json.loads(INPUT.read_text(encoding='utf-8'))['hosts']]
    if masks[7] != expected:
        raise RuntimeError('Extension candidates do not match the committed seven-vertex atlas')
    return masks, stages


HEADER = ('import InducedPentagonsPaper.FiniteAtlas\n\n'
          'namespace InducedPentagons.Paper\n\n')
OPTIONS = 'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n'
END = 'end InducedPentagons.Paper\n'


def row_name(n: int, index: int) -> str:
    return f'atlasRow{n}_{index:03d}'


def row_source(n: int, index: int, source: int, row: list[tuple[int, int]]) -> str:
    values = ', '.join(f'⟨{target}, {perm}⟩' for target, perm in row)
    return (f'def {row_name(n, index)} : AtlasRow {n} where\n'
            f'  source := {source}\n'
            f'  witnesses := fun k => (#[{values}] : Array AtlasWitness)[k.val]\n\n')


def generated_files() -> dict[str, bytes]:
    masks, stages = candidates()
    outputs = {}
    mask_text = HEADER
    for n, family in enumerate(masks):
        mask_text += f'def atlasMasks{n} : List Nat := [\n'
        mask_text += ',\n'.join('  ' + ', '.join(map(str, family[i:i+12]))
                               for i in range(0, len(family), 12)) + '\n]\n\n'
    outputs['AtlasMasks.lean'] = (mask_text + END).encode('utf-8')
    small = 'import InducedPentagonsPaper.Generated.AtlasMasks\n\n' + HEADER.split('\n\n', 1)[1]
    large = small
    for n, rows in enumerate(stages):
        target = small if n < 6 else large
        for i, (source, row) in enumerate(zip(masks[n], rows, strict=True)):
            target += row_source(n, i, source, row)
        target += f'def atlasRows{n} : List (AtlasRow {n}) := [\n'
        target += ',\n'.join('  ' + ', '.join(row_name(n, i) for i in range(j, min(j+8, len(rows))))
                             for j in range(0, len(rows), 8)) + '\n]\n\n'
        if n < 6:
            small = target
        else:
            large = target
    outputs['AtlasRowsSmall.lean'] = (small + END).encode('utf-8')
    outputs['AtlasRows6.lean'] = (large + END).encode('utf-8')
    small_checks = ('import InducedPentagonsPaper.Generated.AtlasRowsSmall\n\n' +
                    OPTIONS + 'namespace InducedPentagons.Paper\n\n')
    for n in range(5):
        small_checks += (f'theorem atlasRows{n}_checked :\n'
                         f'    (atlasRows{n}).all (atlasRowCheck {n} atlasMasks{n+1}) = true := by\n'
                         '  decide +kernel\n\n')
    outputs['AtlasChecksSmall.lean'] = (small_checks + END).encode('utf-8')
    imports = ['import InducedPentagonsPaper.Generated.AtlasChecksSmall\n']
    for n in (5, 6):
        for group, start in enumerate(range(0, len(stages[n]), GROUP_SIZE[n])):
            name = f'AtlasChecks{n}_{group:02d}'
            imports.append(f'import InducedPentagonsPaper.Generated.{name}\n')
            data = 'AtlasRowsSmall' if n == 5 else 'AtlasRows6'
            content = (f'import InducedPentagonsPaper.Generated.{data}\n\n' + OPTIONS +
                       'namespace InducedPentagons.Paper\n\n')
            for i in range(start, min(start + GROUP_SIZE[n], len(stages[n]))):
                content += (f'theorem {row_name(n, i)}_checked :\n'
                            f'    atlasRowCheck {n} atlasMasks{n+1} {row_name(n, i)} = true := by\n'
                            '  decide +kernel\n\n')
            outputs[name + '.lean'] = (content + END).encode('utf-8')
    coverage = ''.join(imports) + '\n' + OPTIONS + 'namespace InducedPentagons.Paper\n\n'
    for n in range(7):
        coverage += (f'theorem atlasRows{n}_sources : atlasRows{n}.map AtlasRow.source = atlasMasks{n} := by\n'
                     '  decide +kernel\n\n')
        if n in (5, 6):
            coverage += (f'theorem atlasRows{n}_checked :\n'
                         f'    atlasRows{n}.all (atlasRowCheck {n} atlasMasks{n+1}) = true := by\n'
                         f'  simp only [atlasRows{n}, List.all_cons, List.all_nil,\n')
            coverage += ',\n'.join('    ' + ', '.join(row_name(n, i)+'_checked'
                                                     for i in range(j, min(j+5, len(stages[n]))))
                                   for j in range(0, len(stages[n]), 5))
            coverage += ', Bool.and_self]\n\n'
    coverage += 'theorem atlas0_covers : AtlasCovers 0 atlasMasks0 := atlasCovers_zero\n\n'
    for n in range(7):
        coverage += (f'theorem atlas{n+1}_covers : AtlasCovers {n+1} atlasMasks{n+1} :=\n'
                     f'  atlasCovers_succ atlas{n}_covers\n'
                     f'    (atlasExtends_of_rows (by decide) atlasRows{n} atlasRows{n}_sources atlasRows{n}_checked)\n\n')
    coverage += ('theorem atlas7_count : atlasMasks7.length = 1044 := by decide +kernel\n\n'
                 'theorem atlas7_masks_nodup : atlasMasks7.Nodup := by decide +kernel\n\n'
                 'theorem seven_vertex_graph_isomorphic_to_atlas (g : Graph (Fin 7)) :\n'
                 '    ∃ m ∈ atlasMasks7, Nonempty (toSimpleGraph g ≃g toSimpleGraph (maskGraph 7 m)) := by\n'
                 '  obtain ⟨m, hm, ⟨e⟩⟩ := atlas7_covers g\n'
                 '  exact ⟨m, hm, ⟨e.toSimpleGraphIso⟩⟩\n\n')
    outputs['AtlasCoverage.lean'] = (coverage + END).encode('utf-8')
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    outputs = generated_files()
    binding = {'schema': 'induced-pentagons.lean-atlas-witnesses.v1',
               'meaning': 'Candidate masks and permutations; all coverage assertions are proved in Lean',
               'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'input_sha256': {INPUT.relative_to(ROOT).as_posix(): hashlib.sha256(INPUT.read_bytes()).hexdigest()},
               'output_sha256': {name: hashlib.sha256(data).hexdigest() for name, data in sorted(outputs.items())}}
    manifest = (json.dumps(binding, indent=2) + '\n').encode('utf-8')
    expected = {**outputs, 'atlas_manifest.json': manifest}
    if args.check:
        for name, content in expected.items():
            path = OUT / name
            if not path.is_file() or path.read_bytes() != content:
                raise SystemExit('Stale Lean atlas candidates: ' + name)
        if {p.name for p in OUT.glob('Atlas*.lean')} != outputs.keys():
            raise SystemExit('Extra or missing generated atlas modules')
    else:
        OUT.mkdir(parents=True, exist_ok=True)
        for name, content in expected.items():
            (OUT / name).write_bytes(content)
    print(json.dumps({'status': 'current' if args.check else 'exported',
                      'files': len(outputs), 'bytes': sum(map(len, outputs.values()))}))


if __name__ == '__main__':
    main()
