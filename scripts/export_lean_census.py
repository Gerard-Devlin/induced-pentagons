#!/usr/bin/env python3
"""Export atlas automorphism/orbit constants for independent Lean kernel recounts."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / 'certificates/graph_atlas_7.json'
OUT = ROOT / 'formal/paper/InducedPentagonsPaper/Generated'
GROUP_SIZE = 24
OPTIONS = 'set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
END = '\nend InducedPentagons.Paper\n'


def generated_files() -> dict[str, bytes]:
    hosts = json.loads(INPUT.read_text(encoding='utf-8'))['hosts']
    outputs = {}
    imports = []
    groups = []
    for group, start in enumerate(range(0, len(hosts), GROUP_SIZE)):
        name = f'CensusRows{group:02d}'
        imports.append(f'import InducedPentagonsPaper.Generated.{name}\n')
        groups.append(f'atlasCensusRows{group:02d}')
        text = ('import InducedPentagonsPaper.AtlasCensusRow\n\n' + OPTIONS +
                'namespace InducedPentagons.Paper\n\n')
        rows = hosts[start:start + GROUP_SIZE]
        names = []
        for row in rows:
            row_name = f'atlasCensusRow{row["index"]:04d}'
            names.append(row_name)
            text += (f'def {row_name} : AtlasCensusRow := '
                     f'⟨{row["mask"]}, {row["automorphism_order"]}, {row["orbit_size"]}⟩\n\n'
                     f'theorem {row_name}_checked : atlasCensusRowCheck {row_name} = true := by\n'
                     '  decide +kernel\n\n')
        text += f'def atlasCensusRows{group:02d} : List AtlasCensusRow := [{", ".join(names)}]\n\n'
        text += (f'theorem atlasCensusRows{group:02d}_checked :\n'
                 f'    atlasCensusRows{group:02d}.all atlasCensusRowCheck = true := by\n'
                 f'  simp only [atlasCensusRows{group:02d}, List.all_cons, List.all_nil,\n'
                 '    '+', '.join(n+'_checked' for n in names)+', Bool.and_self]\n')
        outputs[name+'.lean'] = (text + END).encode('utf-8')
    text = ''.join(imports) + 'import InducedPentagonsPaper.AtlasCertificate\n\n' + OPTIONS
    text += 'namespace InducedPentagons.Paper\n\n'
    text += 'def atlasCensusRows : List AtlasCensusRow :=\n  ' + ' ++\n  '.join(groups) + '\n\n'
    text += ('theorem atlas_census_rows_checked : atlasCensusRows.all atlasCensusRowCheck = true := by\n'
             '  simp only [atlasCensusRows, List.all_append,\n    '+
             ', '.join(g+'_checked' for g in groups)+', Bool.and_self]\n\n')
    text += ('theorem atlas_census_hosts : atlasCensusRows.map AtlasCensusRow.mask =\n'
             '    Generated.certificate.hosts.toList := by decide +kernel\n\n'
             'theorem atlas_census_count : atlasCensusRows.length = 1044 := by decide +kernel\n\n'
             'theorem atlas_census_semantics (r : AtlasCensusRow) (hr : r ∈ atlasCensusRows) :\n'
             '    Nat.card (toSimpleGraph (maskGraph 7 r.mask) ≃g\n'
             '      toSimpleGraph (maskGraph 7 r.mask)) = r.automorphisms ∧\n'
             '    Nat.card (CensusIsoClass (toSimpleGraph (maskGraph 7 r.mask))) = r.orbit :=\n'
             '  atlasCensusRowCheck_sound r ((List.all_eq_true.mp atlas_census_rows_checked) r hr)\n\n'
             'theorem atlas_census_labelled_total :\n'
             '    (atlasCensusRows.map AtlasCensusRow.orbit).sum = 2097152 := by decide +kernel\n')
    outputs['CensusComplete.lean'] = (text + END).encode('utf-8')
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    outputs = generated_files()
    manifest = {
        'schema': 'induced-pentagons.lean-atlas-census.v1',
        'meaning': 'Candidate census rows; every count is independently checked in Lean',
        'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'input_sha256': {INPUT.relative_to(ROOT).as_posix(): hashlib.sha256(INPUT.read_bytes()).hexdigest()},
        'output_sha256': {name: hashlib.sha256(data).hexdigest() for name, data in sorted(outputs.items())}}
    expected = {**outputs, 'census_manifest.json': (json.dumps(manifest, indent=2)+'\n').encode('utf-8')}
    if args.check:
        for name, content in expected.items():
            if not (OUT/name).is_file() or (OUT/name).read_bytes() != content:
                raise SystemExit('Stale Lean atlas census: '+name)
        if {p.name for p in OUT.glob('Census*.lean')} != outputs.keys():
            raise SystemExit('Extra or missing generated atlas census modules')
    else:
        for name, content in expected.items():
            (OUT/name).write_bytes(content)
    print(json.dumps({'status': 'current' if args.check else 'exported', 'files': len(outputs),
                      'bytes': sum(map(len, outputs.values()))}))


if __name__ == '__main__':
    main()
