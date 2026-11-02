#!/usr/bin/env python3
"""Export primitive pattern specifications and kernel-check obligations."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'formal/paper/InducedPentagonsPaper/Generated'
sys.path.insert(0, str(ROOT / 'src'))
from proof_specification import primitive_patterns


def generated_files() -> dict[str, bytes]:
    specs = primitive_patterns()
    meta = json.loads((ROOT / 'certificates/pattern_columns.json').read_text(encoding='utf-8'))
    for wanted, stored in zip(specs, meta['patterns'], strict=True):
        if any(wanted[key] != stored[key] for key in wanted):
            raise RuntimeError('Primitive pattern specification differs from stored metadata')
    header = ('import InducedPentagonsPaper.PrimitiveFast\n\n'
              'namespace InducedPentagons.Paper\n\n')
    source = header
    def pairs(values):
        return '[' + ', '.join(f'({a}, {b})' for a, b in values) + ']'
    for i, p in enumerate(specs):
        source += (f'def primitivePattern{i:02d} : PartialPattern {p["vertices"]} where\n'
                   f'  edges := {pairs(p["edges"])}\n'
                   f'  nonedges := {pairs(p["nonedges"])}\n\n')
    source += 'def primitivePatternSpecs : List PrimitivePatternSpec := [\n'
    source += ',\n'.join(f'  ⟨{json.dumps(p["name"])}, {p["vertices"]}, primitivePattern{i:02d}⟩'
                          for i, p in enumerate(specs)) + '\n]\n\n'
    source += ('theorem primitivePatternSpecs_count : primitivePatternSpecs.length = 22 := by decide +kernel\n\n'
               'theorem primitivePatternSpecs_ordered : orderedSpecsCheck primitivePatternSpecs = true := by decide +kernel\n\n'
               'theorem primitivePattern_denominators :\n'
               '    primitivePatternSpecs.map (fun p => Nat.descFactorial 7 p.vertices) =\n'
               '      expectedPatternDenominators.toList := by decide +kernel\n\n'
               'end InducedPentagons.Paper\n')
    outputs = {'PrimitivePatterns.lean': source.encode('utf-8')}
    examples = ('import InducedPentagonsPaper.Generated.PrimitivePatterns\n'
                'import InducedPentagons.Generated.HostData000\n'
                'import InducedPentagons.Generated.HostData086\n\n'
                'set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
                'namespace InducedPentagons.Paper\n\n')
    for label, mask, chunk, offset, index in (('empty', 0, 0, 0, 0),
                                              ('complete', (1 << 21)-1, 86, 11, 1043)):
        values = [p['injection_counts'][index] for p in meta['patterns']]
        literal = str(values)
        row = f'Generated.hostChunk{chunk:03d}[{offset}]'
        examples += (f'theorem primitive_{label}_count_values :\n'
                     f'    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 {mask}) = {literal} := by\n'
                     '  decide +kernel\n\n'
                     f'theorem primitive_{label}_host_semantics :\n'
                     f'    ({row}).primitive.toList =\n'
                     f'      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 ({row}).mask) := by\n'
                     '  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered\n'
                     '  unfold fastPrimitiveRowCheck\n'
                     f'  have hm : ({row}).mask = {mask} := by decide +kernel\n'
                     f'  have hv : ({row}).primitive.toList = {literal} := by decide +kernel\n'
                     f'  rw [hm, hv, primitive_{label}_count_values]\n'
                     '  rfl\n\n')
    bad = '#[' + ', '.join(map(str, [1]+[0]*21)) + ']'
    examples += ('theorem primitive_changed_count_rejected :\n'
                 '    fastPrimitiveRowCheck primitivePatternSpecs\n'
                 f'      {{ Generated.hostChunk000[0] with primitive := {bad} }} = false := by\n'
                 '  unfold fastPrimitiveRowCheck\n'
                 f'  change ({str([1]+[0]*21)} == fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 0)) = false\n'
                 '  rw [primitive_empty_count_values]\n'
                 '  rfl\n\nend InducedPentagons.Paper\n')
    outputs['PrimitiveExamples.lean'] = examples.encode('utf-8')
    atlas = json.loads((ROOT / 'certificates/graph_atlas_7.json').read_text(encoding='utf-8'))
    hosts = atlas['hosts']
    if len(hosts) != 1044 or any(h['index'] != i for i, h in enumerate(hosts)):
        raise RuntimeError('Unexpected atlas host indexing')
    # Eight import chains bound the number of simultaneous expensive kernel jobs.
    # The numeric checks use literal masks; separate lemmas bind them to raw rows.
    chunks = (len(hosts) + 11) // 12
    for chunk in range(chunks):
        source = ('import InducedPentagonsPaper.Generated.PrimitivePatterns\n'
                  f'import InducedPentagons.Generated.HostData{chunk:03d}\n')
        if chunk >= 8:
            source += f'import InducedPentagonsPaper.Generated.PrimitiveRows{chunk-8:03d}\n'
        source += ('\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
                   'namespace InducedPentagons.Paper\n\n')
        indices = list(range(chunk*12, min(len(hosts), (chunk+1)*12)))
        for index in indices:
            mask = hosts[index]['mask']
            values = [p['injection_counts'][index] for p in meta['patterns']]
            row = f'Generated.hostChunk{chunk:03d}[{index%12}]'
            source += (f'theorem primitive_values_{index:04d} :\n'
                       f'    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 {mask}) = {values} := by\n'
                       '  decide +kernel\n\n'
                       f'theorem primitive_host_{index:04d}_semantics :\n'
                       f'    ({row}).primitive.toList =\n'
                       f'      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 ({row}).mask) := by\n'
                       '  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered\n'
                       '  unfold fastPrimitiveRowCheck\n'
                       f'  have hm : ({row}).mask = {mask} := by decide +kernel\n'
                       f'  have hv : ({row}).primitive.toList = {values} := by decide +kernel\n'
                       f'  rw [hm, hv, primitive_values_{index:04d}]\n'
                       '  rfl\n\n')
        rows = ', '.join(f'Generated.hostChunk{chunk:03d}[{i%12}]' for i in indices)
        source += (f'theorem primitive_chunk_{chunk:03d}_semantics :\n'
                   f'    ∀ h ∈ Generated.hostChunk{chunk:03d}.toList, h.primitive.toList =\n'
                   '      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by\n'
                   '  intro h hh\n'
                   f'  have hr : Generated.hostChunk{chunk:03d}.toList = [{rows}] := rfl\n'
                   '  rw [hr] at hh\n'
                   '  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh\n'
                   '  rcases hh with ' + ' | '.join('rfl' for _ in indices) + '\n')
        source += ''.join(f'  · exact primitive_host_{i:04d}_semantics\n' for i in indices)
        source += '\nend InducedPentagons.Paper\n'
        outputs[f'PrimitiveRows{chunk:03d}.lean'] = source.encode('utf-8')
    source = ''.join(f'import InducedPentagonsPaper.Generated.PrimitiveRows{c:03d}\n'
                     for c in range(max(0, chunks-8), chunks))
    source += ('\nnamespace InducedPentagons.Paper\n\n'
               'def primitiveCertificateRows : List HostRow :=\n  ')
    source += ' ++\n  '.join(f'Generated.hostChunk{c:03d}.toList' for c in range(chunks))
    source += ('\n\nset_option maxRecDepth 100000 in\n'
               'theorem primitive_certificate_rows_semantics :\n'
               '    ∀ h ∈ primitiveCertificateRows, h.primitive.toList =\n'
               '      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by\n'
               '  intro h hh\n'
               '  simp only [primitiveCertificateRows, List.mem_append, or_assoc] at hh\n'
               '  rcases hh with ' + ' | '.join(f'h{c}' for c in range(chunks)) + '\n')
    source += ''.join(f'  · exact primitive_chunk_{c:03d}_semantics h h{c}\n' for c in range(chunks))
    source += '\nend InducedPentagons.Paper\n'
    outputs['PrimitiveComplete.lean'] = source.encode('utf-8')
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    outputs = generated_files()
    inputs = ('src/proof_specification.py', 'certificates/pattern_columns.json',
              'certificates/graph_atlas_7.json')
    binding = {'schema': 'induced-pentagons.lean-primitive-patterns.v1',
               'meaning': 'Explicit required-edge/nonedge specifications; no count verdict is assumed',
               'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'input_sha256': {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in inputs},
               'output_sha256': {name: hashlib.sha256(data).hexdigest() for name, data in outputs.items()}}
    expected = {**outputs, 'primitive_manifest.json': (json.dumps(binding, indent=2)+'\n').encode('utf-8')}
    if args.check:
        for name, data in expected.items():
            if not (OUT/name).is_file() or (OUT/name).read_bytes() != data:
                raise SystemExit('Stale primitive pattern export: '+name)
        if {p.name for p in OUT.glob('Primitive*.lean')} != outputs.keys():
            raise SystemExit('Extra or missing primitive pattern modules')
    else:
        OUT.mkdir(parents=True, exist_ok=True)
        for name, data in expected.items():
            (OUT/name).write_bytes(data)
    print(json.dumps({'status': 'current' if args.check else 'exported', 'files':len(outputs)}))


if __name__ == '__main__':
    main()
