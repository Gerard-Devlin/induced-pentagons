#!/usr/bin/env python3
"""Export candidate closed Boolean masks; Lean proves their graph-defined meaning."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'formal/paper/InducedPentagonsPaper/Generated'
PREFIX_DEPTH = 8
PREFIX_GROUP = 16


def candidate_masks() -> list[tuple[int, int]]:
    def edge(u, v):
        return (u ^ v) in (1, 2, 4, 8, 15)
    neighbors = [[v for v in range(16) if edge(u, v)] for u in range(16)]
    masks = []
    for a in range(16):
        for b in neighbors[a]:
            for c in neighbors[b]:
                for d in neighbors[c]:
                    if a < d and len({a, b, c, d}) == 4 and not any(
                            (edge(a, c), edge(a, d), edge(b, d))):
                        masks.append(((1 << a) + (1 << d), (1 << b) + (1 << c)))
    return masks


def render(masks) -> bytes:
    rows = ',\n'.join(f'  ⟨{r}, {e}⟩' for r, e in masks)
    return ('module\npublic import InducedPentagonsPaper.MaskPattern\n\n'
            '/-! Generated candidates. Graph equality and literal semantics are proved in ProfileMaskData. -/\n\n'
            '@[expose] public section\nnamespace InducedPentagons.Paper\n\n'
            'def clebschProfileMasks : List ProfileMask := [\n' + rows + '\n]\n\n'
            'end InducedPentagons.Paper\n').encode('utf-8')


def generated_files() -> dict[str, bytes]:
    masks = candidate_masks()
    result = {'ProfileMasks.lean': render(masks)}
    families = []
    for prefix in range(1 << PREFIX_DEPTH):
        families.append([p for p in masks if all(
            bool(prefix >> i & 1) if p[0] >> i & 1 else not bool(prefix >> i & 1)
            if p[1] >> i & 1 else True for i in range(PREFIX_DEPTH))])
    header = ('module\npublic import InducedPentagonsPaper.PatternPrefix\n\n'
              '@[expose] public section\nnamespace InducedPentagons.Paper\n\n')
    data = header
    for prefix, family in enumerate(families):
        rows = ',\n'.join(f'  ⟨{r}, {e}⟩' for r, e in family)
        data += f'def profilePrefixMasks{prefix:03d} : List ProfileMask := [\n{rows}\n]\n\n'
    result['ProfilePrefixData.lean'] = (data + 'end InducedPentagons.Paper\n').encode('utf-8')
    imports = []
    for group in range((1 << PREFIX_DEPTH) // PREFIX_GROUP):
        name = f'ProfilePrefixChecks{group:02d}'
        imports.append(f'public import InducedPentagonsPaper.Generated.{name}\n')
        source = ('module\npublic import InducedPentagonsPaper.Generated.ProfilePrefixData\n\n'
                  'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n'
                  '@[expose] public section\nnamespace InducedPentagons.Paper\n\n')
        for prefix in range(group * PREFIX_GROUP, (group + 1) * PREFIX_GROUP):
            source += (f'theorem profilePrefixData{prefix:03d} :\n'
                       f'    profilePrefixFamily {prefix} = profilePrefixMasks{prefix:03d} := by decide +kernel\n\n'
                       f'theorem profilePrefixChecked{prefix:03d} :\n'
                       f'    patternBound maskLiteral 60 profileRemainingVars profilePrefixMasks{prefix:03d} = true := by\n'
                       '  decide +kernel\n\n')
        result[name + '.lean'] = (source + 'end InducedPentagons.Paper\n').encode('utf-8')
    complete = ('module\n' + ''.join(imports) + '\nset_option maxRecDepth 100000\n'
                'set_option maxHeartbeats 0\n\n@[expose] public section\n'
                'namespace InducedPentagons.Paper\n\n'
                'theorem clebsch_profile_boolean_bound (b : Fin 16 → Bool) :\n'
                '    patternTotal maskLiteral clebschProfileMasks b ≤ 60 := by\n'
                '  rw [← patternTotal_filter_all maskLiteral clebschProfileMasks b profilePrefixVars]\n')
    predicate = 'true'
    for i in reversed(range(PREFIX_DEPTH)):
        predicate = f'acceptLiteral (maskLiteral p {i}) (b {i}) && ({predicate})'
    complete += ('  change patternTotal maskLiteral (clebschProfileMasks.filter\n'
                 f'    (fun p => {predicate})) b ≤ 60\n')

    def cases(level: int, prefix: int, indent: int) -> str:
        pad = ' ' * indent
        if level == PREFIX_DEPTH:
            return (f'{pad}change patternTotal maskLiteral (profilePrefixFamily {prefix}) b ≤ 60\n'
                    f'{pad}rw [profilePrefixData{prefix:03d}]\n'
                    f'{pad}exact patternBound_sound maskLiteral 60 profileRemainingVars '
                    f'profilePrefixMasks{prefix:03d} profilePrefixChecked{prefix:03d} b\n')
        return (f'{pad}cases h{level} : b {level} with\n'
                f'{pad}| false =>\n' + cases(level + 1, prefix, indent + 2) +
                f'{pad}| true =>\n' + cases(level + 1, prefix | (1 << level), indent + 2))

    complete += cases(0, 0, 2) + '\nend InducedPentagons.Paper\n'
    result['ProfilePrefixComplete.lean'] = complete.encode('utf-8')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    outputs = generated_files()
    manifest = OUT / 'profile_manifest.json'
    binding = {'schema': 'induced-pentagons.lean-profile-candidates.v1',
               'meaning': 'Candidate masks; not a computational PASS or an assumed mathematical fact',
               'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'output_sha256': {name: hashlib.sha256(content).hexdigest()
                                 for name, content in sorted(outputs.items())}}
    binding_bytes = (json.dumps(binding, indent=2) + '\n').encode('utf-8')
    if args.check:
        for name, content in outputs.items():
            output = OUT / name
            if not output.is_file() or output.read_bytes() != content:
                raise SystemExit('Stale Lean profile candidates: ' + name)
        actual = {p.name for p in OUT.glob('*.lean') if p.name == 'ProfileMasks.lean' or p.name.startswith('ProfilePrefix')}
        if actual != outputs.keys():
            raise SystemExit('Extra or missing generated profile modules')
        if not manifest.is_file() or manifest.read_bytes() != binding_bytes:
            raise SystemExit('Stale Lean profile mask candidate manifest')
    else:
        OUT.mkdir(parents=True, exist_ok=True)
        for name, content in outputs.items():
            (OUT / name).write_bytes(content)
        manifest.write_bytes(binding_bytes)
    print(json.dumps({'status': 'current' if args.check else 'exported',
                      'files': len(outputs), 'bytes': sum(map(len, outputs.values()))}))


if __name__ == '__main__':
    main()
