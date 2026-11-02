#!/usr/bin/env python3
"""Export invariant count encodings and a candidate increasing order of the host list."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'formal/paper/InducedPentagonsPaper/Generated'


def generated_files():
    with np.load(ROOT / 'certificates/pattern_columns.npz', allow_pickle=False) as archive:
        masks = [int(v) for v in archive['host_masks']]
        matrix = np.concatenate([archive['pattern_counts'], archive['fixed_density_induced_counts'],
                                 archive['fixed_density_complement_edge_counts']], axis=1)
    rows = []
    for mask, values in zip(masks, matrix, strict=True):
        code = 0
        for v in reversed(values):
            code = int(v) + 8192 * code
        rows.append((mask, code))
    ordered = sorted(rows, key=lambda r: r[1])
    if len(rows) != 1044 or len({code for _, code in ordered}) != 1044:
        raise RuntimeError('The proposed count codes do not separate all 1044 hosts')
    source = ('import InducedPentagonsPaper.HostSignatureCode\n\n'
              'set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
              'namespace InducedPentagons.Paper\n\n')
    for name, data in (('storedHostCodes', rows), ('sortedHostCodes', ordered)):
        source += f'def {name} : List (Nat × Nat) := [\n'
        source += ',\n'.join(f'  ({m}, {c})' for m, c in data) + '\n]\n\n'
    source += ('theorem storedHostCodes_binding : rowCountPairs = storedHostCodes := by\n'
               '  decide +kernel\n\n'
               'theorem storedHostCodes_permutation : storedHostCodes.Perm sortedHostCodes := by\n'
               '  decide +kernel\n\n'
               'theorem sortedHostCodes_checked : increasingHostCodes sortedHostCodes = true := by\n'
               '  decide +kernel\n\nend InducedPentagons.Paper\n')
    return {'HostCodeData.lean': source.encode('utf-8')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    outputs = generated_files()
    manifest = {
        'schema': 'induced-pentagons.lean-host-codes.v1',
        'meaning': 'Candidate invariant codes and ordering; Lean checks data binding, permutation and strict order',
        'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'input_sha256': {'certificates/pattern_columns.npz': hashlib.sha256(
            (ROOT / 'certificates/pattern_columns.npz').read_bytes()).hexdigest()},
        'output_sha256': {n: hashlib.sha256(d).hexdigest() for n, d in outputs.items()},
    }
    expected = {**outputs, 'host_code_manifest.json': (json.dumps(manifest, indent=2)+'\n').encode('utf-8')}
    if args.check:
        for name, data in expected.items():
            if not (OUT/name).is_file() or (OUT/name).read_bytes() != data:
                raise SystemExit('Stale host-code export: ' + name)
        if {p.name for p in OUT.glob('HostCode*.lean')} != outputs.keys():
            raise SystemExit('Extra or missing host-code modules')
    else:
        OUT.mkdir(parents=True, exist_ok=True)
        for name, data in expected.items():
            (OUT/name).write_bytes(data)
    print(json.dumps({'status': 'current' if args.check else 'exported', 'files': len(outputs)}))


if __name__ == '__main__':
    main()
