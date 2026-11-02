#!/usr/bin/env python3
"""Export checked five-vertex classification candidates and fixed-density counts."""
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
from proof_specification import primitive_patterns


def generated_files() -> dict[str, bytes]:
    with np.load(ROOT / 'certificates/pattern_columns.npz', allow_pickle=False) as archive:
        masks = [int(m) for m in archive['fixed_density_graph_masks']]
        host_masks = [int(m) for m in archive['host_masks']]
        induced = archive['fixed_density_induced_counts'].tolist()
        complement = archive['fixed_density_complement_edge_counts'].tolist()
    if len(host_masks) != 1044 or any(len(r) != 34 for r in induced + complement):
        raise RuntimeError('Unexpected fixed-density table dimensions')
    pairs = list(combinations(range(5), 2))
    pair_index = {e: i for i, e in enumerate(pairs)}
    perms = list(permutations(range(5)))
    witnesses = []
    for source in range(1024):
        def relabel(p):
            return sum(((source >> pair_index[tuple(sorted((p[i], p[j])))]) & 1) << k
                       for k, (i, j) in enumerate(pairs))
        target, q = min((relabel(p), p) for p in perms)
        inverse = [q.index(i) for i in range(5)]
        code = sum(v * 8**i for i, v in enumerate(inverse))
        witnesses.append((source, target, code))
    if sorted({t for _, t, _ in witnesses}) != masks or len(masks) != 34:
        raise RuntimeError('Candidate five-vertex types differ from the stored basis')
    specs = [(i, p) for i, p in enumerate(primitive_patterns()) if p['vertices'] <= 5]
    signatures = []
    for mask in masks:
        def adj(u, v):
            return u != v and (mask >> pair_index[tuple(sorted((u, v)))]) & 1
        signatures.append([sum(all(adj(f[u], f[v]) for u, v in p['edges']) and
                               all(not adj(f[u], f[v]) for u, v in p['nonedges'])
                               for f in permutations(range(5), p['vertices'])) for _, p in specs])
    if len({tuple(s) for s in signatures}) != 34:
        raise RuntimeError('The proposed pattern signatures do not separate the five-vertex types')
    source = ('import InducedPentagonsPaper.PatternSeparation\n'
              'import InducedPentagonsPaper.Generated.PrimitivePatterns\n'
              'import InducedPentagons.Generated.Inputs\n\n'
              'set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
              'namespace InducedPentagons.Paper\n\n'
              f'def fixedTypeMasks : List Nat := {masks}\n\n'
              'def fixedTypeTable : Vector RootedFlagWitness 1024 := #v[\n')
    source += ',\n'.join(f'  ⟨{a}, {b}, {c}⟩' for a, b, c in witnesses) + '\n]\n\n'
    source += ('def fixedTypeLookup (m : Fin 1024) : RootedFlagWitness := fixedTypeTable[m]\n\n'
               'theorem fixed_type_lookup_checked :\n'
               '    rootedLookupCheck 5 10 0 0 fixedTypeMasks fixedTypeLookup = true := by\n'
               '  decide +kernel\n\n'
               'def fixedSignatureSpecs : List PrimitivePatternSpec := [\n')
    source += ',\n'.join(f'  ⟨{json.dumps(p["name"])}, {p["vertices"]}, primitivePattern{i:02d}⟩'
                          for i, p in specs) + '\n]\n\n'
    source += ('theorem fixedSignatureSpecs_ordered : orderedSpecsCheck fixedSignatureSpecs = true := by\n'
               '  decide +kernel\n\n'
               'def fixedSignatureData : List (Nat × List Nat) := [\n')
    source += ',\n'.join(f'  ({m}, {s})' for m, s in zip(masks, signatures, strict=True)) + '\n]\n\n'
    for i, (mask, sig) in enumerate(zip(masks, signatures, strict=True)):
        source += (f'theorem fixed_signature_values_{i:02d} :\n'
                   f'    fastPrimitiveCounts fixedSignatureSpecs (maskGraph 5 {mask}) = {sig} := by\n'
                   '  decide +kernel\n\n')
    source += ('theorem fixed_signature_data_masks : fixedSignatureData.map Prod.fst = fixedTypeMasks := by\n'
               '  decide +kernel\n\n'
               'theorem fixed_signature_data_semantics :\n'
               '    ∀ r ∈ fixedSignatureData, primitiveSemanticCounts fixedSignatureSpecs (maskGraph 5 r.1) = r.2 := by\n'
               '  intro r hr\n'
               '  rw [primitiveSemanticCounts_eq_fast fixedSignatureSpecs fixedSignatureSpecs_ordered]\n'
               '  simp only [fixedSignatureData, List.mem_cons, List.not_mem_nil, or_false] at hr\n'
               '  rcases hr with ' + ' | '.join('rfl' for _ in masks) + '\n')
    source += ''.join(f'  · exact fixed_signature_values_{i:02d}\n' for i in range(len(masks)))
    source += ('\ntheorem fixed_signature_data_separated : patternSignatureSeparationCheck fixedSignatureData = true := by\n'
               '  decide +kernel\n\n'
               'theorem fixed_types_separated : RootedFlagBasisSeparated 5 0 fixedTypeMasks :=\n'
               '  patternSignatureSeparationCheck_sound fixedSignatureSpecs fixedTypeMasks fixedSignatureData\n'
               '    fixed_signature_data_masks fixed_signature_data_semantics fixed_signature_data_separated\n\n'
               'theorem fixed_type_masks_certificate : fixedTypeMasks = Generated.certificate.fixedMasks.toList := by\n'
               '  decide +kernel\n\n'
               'theorem fixed_type_masks_count : fixedTypeMasks.length = 34 := by decide +kernel\n\n'
               'theorem fixed_type_masks_nodup : fixedTypeMasks.Nodup := by decide +kernel\n\n'
               'end InducedPentagons.Paper\n')
    outputs = {'FixedTypeData.lean': source.encode('utf-8')}
    chunks = (len(host_masks) + 11) // 12
    for chunk in range(chunks):
        source = ('import InducedPentagonsPaper.FixedDensity\n'
                  f'import InducedPentagons.Generated.HostData{chunk:03d}\n')
        if chunk >= 8:
            source += f'import InducedPentagonsPaper.Generated.FixedRows{chunk-8:03d}\n'
        source += ('\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
                   'namespace InducedPentagons.Paper\n\n')
        indices = list(range(chunk*12, min(len(host_masks), (chunk+1)*12)))
        for i in indices:
            row = f'Generated.hostChunk{chunk:03d}[{i%12}]'
            source += (f'theorem fixed_values_{i:04d} :\n'
                       f'    (fixedDensityCounts (maskGraph 7 {host_masks[i]}), fixedComplementCounts (maskGraph 7 {host_masks[i]})) =\n'
                       f'      ({induced[i]}, {complement[i]}) := by\n'
                       '  decide +kernel\n\n'
                       f'theorem fixed_host_{i:04d}_semantics :\n'
                       f'    (({row}).induced.toList, ({row}).complement.toList) =\n'
                       f'      (fixedDensityCounts (maskGraph 7 ({row}).mask), fixedComplementCounts (maskGraph 7 ({row}).mask)) := by\n'
                       f'  have hm : ({row}).mask = {host_masks[i]} := by decide +kernel\n'
                       f'  have hv : (({row}).induced.toList, ({row}).complement.toList) =\n'
                       f'      ({induced[i]}, {complement[i]}) := by decide +kernel\n'
                       f'  rw [hm, hv, fixed_values_{i:04d}]\n\n')
        rows = ', '.join(f'Generated.hostChunk{chunk:03d}[{i%12}]' for i in indices)
        source += (f'theorem fixed_chunk_{chunk:03d}_semantics :\n'
                   f'    ∀ h ∈ Generated.hostChunk{chunk:03d}.toList, (h.induced.toList, h.complement.toList) =\n'
                   '      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by\n'
                   '  intro h hh\n'
                   f'  have hr : Generated.hostChunk{chunk:03d}.toList = [{rows}] := rfl\n'
                   '  rw [hr] at hh\n'
                   '  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh\n'
                   '  rcases hh with ' + ' | '.join('rfl' for _ in indices) + '\n')
        source += ''.join(f'  · exact fixed_host_{i:04d}_semantics\n' for i in indices)
        source += '\nend InducedPentagons.Paper\n'
        outputs[f'FixedRows{chunk:03d}.lean'] = source.encode('utf-8')
    source = ''.join(f'import InducedPentagonsPaper.Generated.FixedRows{c:03d}\n'
                     for c in range(chunks-8, chunks))
    source += ('import InducedPentagonsPaper.Generated.PrimitiveComplete\n\n'
               'namespace InducedPentagons.Paper\n\n'
               'set_option maxRecDepth 100000 in\n'
               'theorem fixed_certificate_rows_semantics :\n'
               '    ∀ h ∈ primitiveCertificateRows, (h.induced.toList, h.complement.toList) =\n'
               '      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by\n'
               '  intro h hh\n'
               '  simp only [primitiveCertificateRows, List.mem_append, or_assoc] at hh\n'
               '  rcases hh with ' + ' | '.join(f'h{c}' for c in range(chunks)) + '\n')
    source += ''.join(f'  · exact fixed_chunk_{c:03d}_semantics h h{c}\n' for c in range(chunks))
    source += '\nend InducedPentagons.Paper\n'
    outputs['FixedComplete.lean'] = source.encode('utf-8')
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    outputs = generated_files()
    inputs = ('src/proof_specification.py', 'certificates/pattern_columns.npz')
    manifest = {
        'schema': 'induced-pentagons.lean-fixed-density.v1',
        'meaning': 'Candidate graph classifications and counts; Lean proves the graph semantics',
        'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'input_sha256': {n: hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in inputs},
        'output_sha256': {n: hashlib.sha256(d).hexdigest() for n, d in outputs.items()},
    }
    expected = {**outputs, 'fixed_manifest.json': (json.dumps(manifest, indent=2)+'\n').encode('utf-8')}
    if args.check:
        for name, data in expected.items():
            if not (OUT/name).is_file() or (OUT/name).read_bytes() != data:
                raise SystemExit('Stale fixed-density export: ' + name)
        if {p.name for p in OUT.glob('Fixed*.lean')} != outputs.keys():
            raise SystemExit('Extra or missing fixed-density modules')
    else:
        OUT.mkdir(parents=True, exist_ok=True)
        for name, data in expected.items():
            (OUT/name).write_bytes(data)
    print(json.dumps({'status': 'current' if args.check else 'exported', 'files': len(outputs)}))


if __name__ == '__main__':
    main()
