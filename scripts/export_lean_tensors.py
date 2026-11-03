#!/usr/bin/env python3
"""Export candidate sparse flag tensors; Lean recounts every joint sample."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'formal/paper/InducedPentagonsPaper/Generated'
sys.path.insert(0, str(ROOT / 'src'))
from proof_specification import FLAG_SPECIFICATIONS

EXAMPLES = {'empty': 0, 'middle': 522, 'complete': 1043}
PREAMBLE = '\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\nnamespace InducedPentagons.Paper\n\n'


def candidate_rows():
    rows = []
    with np.load(ROOT / 'certificates/flag_basis.npz', allow_pickle=False) as archive:
        masks = [int(v) for v in archive['host_masks']]
        matrices = {name: archive['C_' + name] for name in FLAG_SPECIFICATIONS}
        if len(masks) != 1044:
            raise RuntimeError('Expected exactly 1044 tensor hosts')
        for h, mask in enumerate(masks):
            entries = []
            for block, (name, (_, _, _, dimension, _)) in enumerate(FLAG_SPECIFICATIONS.items()):
                matrix = matrices[name][h]
                if matrix.shape != (dimension, dimension) or not np.array_equal(matrix, matrix.T):
                    raise RuntimeError('Unexpected or asymmetric tensor: ' + name)
                for i in range(dimension):
                    for j in range(i, dimension):
                        count = int(matrix[i, j]) + (int(matrix[j, i]) if i != j else 0)
                        if count < 0:
                            raise RuntimeError('Negative tensor count')
                        if count:
                            entries.append(((block * 72 + i) * 72 + j, count))
            rows.append((mask, entries))
    return rows


def literal(entries):
    return '[' + ', '.join(f'({key}, {count})' for key, count in entries) + ']'


def reference(index):
    return f'(Generated.hostChunk{index // 12:03d}[{index % 12}])'


def example_source(rows, example_name):
    imports = ['import InducedPentagonsPaper.FlagTensorTrie']
    imports += [f'import InducedPentagons.Generated.HostData{EXAMPLES[example_name] // 12:03d}']
    source = '\n'.join(imports) + '\n' + PREAMBLE
    for name, index in ((example_name, EXAMPLES[example_name]),):
        mask, entries = rows[index]
        row = reference(index)
        source += (f'def tensorExampleData_{name} : List (Nat × Nat) := {literal(entries)}\n\n'
                   f'theorem tensor_{name}_checked : fastTrieTensorCheck {mask} tensorExampleData_{name} = true := by\n'
                   '  decide +kernel\n\n'
                   f'theorem tensor_{name}_binding :\n'
                   f'    {row}.mask = {mask} ∧ rawFlagTensorEntries {row} = tensorExampleData_{name} := by\n'
                   '  decide +kernel\n\n'
                   f'theorem tensor_{name}_row_checked : fastTrieTensorRowCheck {row} = true := by\n'
                   '  unfold fastTrieTensorRowCheck\n'
                   f'  rw [tensor_{name}_binding.1, tensor_{name}_binding.2]\n'
                   f'  exact tensor_{name}_checked\n\n'
                   f'theorem tensor_{name}_all_key_counts : ∀ k, k < 32768 →\n'
                   f'    weightedCountAt (rawFlagTensorEntries {row}) k =\n'
                   f'      (flagTensorKeys (maskGraph 7 {row}.mask)).count k :=\n'
                   f'  fastTrieTensorRowCheck_sound {row} tensor_{name}_row_checked\n\n')
    return (source + 'end InducedPentagons.Paper\n').encode('utf-8')


def generated_files(rows):
    outputs = {f'TensorExample_{name}.lean': example_source(rows, name) for name in EXAMPLES}
    outputs['TensorExamples.lean'] = ''.join(
        f'import InducedPentagonsPaper.Generated.TensorExample_{name}\n' for name in EXAMPLES).encode('utf-8')
    example_names = {index: name for name, index in EXAMPLES.items()}
    chunks = 87
    for chunk in range(chunks):
        source = ('import InducedPentagonsPaper.Generated.TensorExamples\n'
                  f'import InducedPentagons.Generated.HostData{chunk:03d}\n')
        if chunk >= 8:
            source += f'import InducedPentagonsPaper.Generated.TensorRows{chunk - 8:03d}\n'
        source += PREAMBLE
        indices = range(chunk * 12, min(len(rows), (chunk + 1) * 12))
        for index in indices:
            mask, entries = rows[index]
            row = reference(index)
            if index in example_names:
                source += (f'theorem tensor_host_{index:04d}_checked : fastTrieTensorRowCheck {row} = true :=\n'
                           f'  tensor_{example_names[index]}_row_checked\n\n')
                continue
            source += (f'def tensorCandidate_{index:04d} : List (Nat × Nat) := {literal(entries)}\n\n'
                       f'theorem tensor_values_{index:04d} : fastTrieTensorCheck {mask} tensorCandidate_{index:04d} = true := by\n'
                       '  decide +kernel\n\n'
                       f'theorem tensor_host_{index:04d}_binding :\n'
                       f'    {row}.mask = {mask} ∧ rawFlagTensorEntries {row} = tensorCandidate_{index:04d} := by\n'
                       '  decide +kernel\n\n'
                       f'theorem tensor_host_{index:04d}_checked : fastTrieTensorRowCheck {row} = true := by\n'
                       '  unfold fastTrieTensorRowCheck\n'
                       f'  rw [tensor_host_{index:04d}_binding.1, tensor_host_{index:04d}_binding.2]\n'
                       f'  exact tensor_values_{index:04d}\n\n')
        refs = ', '.join(reference(index) for index in indices)
        source += (f'theorem tensor_chunk_{chunk:03d}_checked :\n'
                   f'    ∀ h ∈ Generated.hostChunk{chunk:03d}.toList, fastTrieTensorRowCheck h = true := by\n'
                   '  intro h hh\n'
                   f'  have hr : Generated.hostChunk{chunk:03d}.toList = [{refs}] := rfl\n'
                   '  rw [hr] at hh\n'
                   '  simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hh\n'
                   '  rcases hh with ' + ' | '.join('rfl' for _ in indices) + '\n')
        source += ''.join(f'  · exact tensor_host_{index:04d}_checked\n' for index in indices)
        source += '\nend InducedPentagons.Paper\n'
        outputs[f'TensorRows{chunk:03d}.lean'] = source.encode('utf-8')
    source = ''.join(f'import InducedPentagonsPaper.Generated.TensorRows{c:03d}\n' for c in range(79, 87))
    source += 'import InducedPentagonsPaper.PrimitiveCertificate\n' + PREAMBLE
    source += ('theorem tensor_certificate_rows_checked :\n'
               '    ∀ h ∈ primitiveCertificateRows, fastTrieTensorRowCheck h = true := by\n'
               '  intro h hh\n'
               '  simp only [primitiveCertificateRows, List.mem_append, or_assoc] at hh\n'
               '  rcases hh with ' + ' | '.join(f'h{c}' for c in range(chunks)) + '\n')
    source += ''.join(f'  · exact tensor_chunk_{c:03d}_checked h h{c}\n' for c in range(chunks))
    source += '\nend InducedPentagons.Paper\n'
    outputs['TensorComplete.lean'] = source.encode('utf-8')
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    rows = candidate_rows()
    outputs = generated_files(rows)
    inputs = ('src/proof_specification.py', 'certificates/flag_basis.npz')
    manifest = {
        'schema': 'induced-pentagons.lean-flag-tensors.v1',
        'meaning': 'Candidate counts and raw-row bindings; Lean recomputes all joint samples',
        'hosts': len(rows), 'sparse_nonzero_entries': sum(len(entries) for _, entries in rows),
        'implicit_zero_entries': 'Included by complete histogram equality',
        'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'input_sha256': {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in inputs},
        'output_sha256': {name: hashlib.sha256(data).hexdigest() for name, data in outputs.items()},
    }
    expected = {**outputs, 'tensor_manifest.json': (json.dumps(manifest, indent=2) + '\n').encode('utf-8')}
    if args.check:
        for name, data in expected.items():
            if not (OUT / name).is_file() or (OUT / name).read_bytes() != data:
                raise SystemExit('Stale tensor export: ' + name)
        if {p.name for p in OUT.glob('Tensor*.lean')} != outputs.keys():
            raise SystemExit('Extra or missing tensor proof modules')
    else:
        OUT.mkdir(parents=True, exist_ok=True)
        for name, data in expected.items():
            (OUT / name).write_bytes(data)
    print(json.dumps({'status': 'current' if args.check else 'exported', 'files': len(outputs),
                      'hosts': len(rows), 'sparse_entries': manifest['sparse_nonzero_entries']}))


if __name__ == '__main__':
    main()
