#!/usr/bin/env python3
"""Reproduce a structural manuscript inventory; this does not verify proofs.

Default: verify that the saved JSON index and readable guide match the source.
Use --write to regenerate both.  The parser targets the explicit LaTeX syntax
and shared theorem counter used by this manuscript; it is not a TeX interpreter.
"""

import _bootstrap  # local CLI module paths only

import argparse
from bisect import bisect_right
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
BODY = ['paper/sections01-05.tex', 'paper/sections06-10.tex',
        'paper/sections11-14.tex', 'paper/appendixA.tex']
FORMAL = {'theorem', 'lemma', 'proposition', 'corollary'}
NUMBERED = FORMAL | {'remark', 'definition'}
MATH = {'equation', 'equation*', 'align', 'align*', 'gather', 'gather*',
        'multline', 'multline*', 'flalign', 'flalign*', 'alignat', 'alignat*'}
SCOPE_TITLES = {
    'prop:triangle-elimination': 'Triangle elimination at reference-density equality',
    'prop:reference-equality': 'Balanced Clebsch classification at reference density',
    'lem:positive-degree-compactness': 'Positive-minimum-degree near-maxima approach full Clebsch in L1',
    'prop:sqrt-optimality': 'Optimality of the square-root edit-stability exponent',
    'rem:arithmetic-scale': 'Scope of the arithmetic deficit comparison and the phase law',
}
EXPLICIT_PROOFS = {
    'Proof of the inequalities in Theorems 1.1 and 1.3':
        [('thm:weighted', 'inequality'), ('thm:graphon', 'bound')],
    'Equality in Theorem 1.3': [('thm:graphon', 'equality')],
    'Equality in Theorem 1.1': [('thm:weighted', 'equality')],
    'Proof of Theorem 8.1': [('thm:edge-stability', 'full statement')],
    'Proof of Theorem A.1': [('thm:local-stability', 'full statement')],
}
REVIEWS = {}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def without_comments(text):
    """Remove TeX comments while preserving offsets and line numbers."""
    out = list(text)
    i = 0
    while i < len(text):
        if text[i] == '%':
            j = i - 1
            while j >= 0 and text[j] == '\\':
                j -= 1
            if (i - 1 - j) % 2 == 0:
                end = text.find('\n', i)
                if end < 0:
                    end = len(text)
                out[i:end] = ' ' * (end - i)
                i = end
                continue
        i += 1
    return ''.join(out)


def blank(text):
    return ''.join('\n' if c == '\n' else ' ' for c in text)


def display_title(title):
    return ' '.join(title.replace('$', '').replace('~', ' ').split())


def dependency_stages():
    """Curated reviewed implications, deliberately not a parsed citation graph."""
    return [
        {'id': 'direct_construction', 'items': ['Introduction: Clebsch counts'], 'requires': [],
         'basis': 'Direct construction gives ratio R* as a lower example; no upper bound is assumed.'},
        {'id': 'unconditional_links', 'items': ['3.1'], 'requires': [],
         'basis': 'Universal kernel inequalities; this proof is independent of global attainment.'},
        {'id': 'finite_attainment', 'items': ['2.1'], 'requires': [],
         'basis': 'Fixed-template compactification at E=1 uses finitely many monomials.'},
        {'id': 'global_attainment', 'items': ['2.2'],
         'requires': ['direct_construction', 'unconditional_links', 'finite_attainment'],
         'basis': 'Template stationarity, sampling, padding to 1/80, and standard cut compactness.'},
        {'id': 'global_variations', 'items': ['2.3', '2.4', '2.5'], 'requires': ['global_attainment'],
         'basis': 'Globality justifies edge/profile variations; padding preserves the global ratio.'},
        {'id': 'active_density', 'items': ['3.2', '3.3'],
         'requires': ['global_variations', 'unconditional_links', 'direct_construction'],
         'basis': 'Moment/compression argument and the construction lower bound yield active density > p*.'},
        {'id': 'finite_certificate', 'items': ['4.1', '4.3', '4.4', '4.5'], 'requires': [],
         'basis': 'Separate exact finite identities and spans; theorem truth is not assumed by their verification.'},
        {'id': 'sharp_bound', 'items': ['4.2', '1.1:inequality', '1.3:bound'],
         'requires': ['active_density', 'global_variations', 'finite_certificate'],
         'basis': 'Pad the global maximum, apply the certificate and positive slope, compare with construction.'},
        {'id': 'equality', 'items': ['6.1', '7.1', '1.3:equality', '1.1:equality'],
         'requires': ['sharp_bound', 'finite_certificate', 'global_variations', 'active_density'],
         'basis': 'After the bound, equality kernels are global; zero squares imply triangle removal and the twin quotient.'},
        {'id': 'local_stability', 'items': ['A.1', 'A.2', 'A.3', 'A.4'], 'requires': [],
         'basis': 'Self-contained local Clebsch analysis, including the unnumbered fractional and variation arguments.'},
        {'id': 'global_stability', 'items': ['8.1', '8.2', '8.3', '8.4', '9.1', '9.2', '9.3'],
         'requires': ['sharp_bound', 'equality', 'local_stability'],
         'basis': 'Peeling, positive-degree compactness, local defects and whole-vertex rounding.'},
        {'id': 'arithmetic_scale', 'items': ['9.5', '10.1', '10.2'], 'requires': ['global_stability'],
         'basis': 'Structural energy and integer class variance give the order of the edge deficit.'},
        {'id': 'arithmetic_profiles', 'items': ['11.1', '11.2', '12.1'], 'requires': [],
         'basis': 'Clebsch profile geometry, its finite envelope, explicit constructions and the scalar profile optimization.'},
        {'id': 'arithmetic_phase', 'items': ['12.2', '12.3'],
         'requires': ['global_stability', 'arithmetic_profiles', 'local_stability'],
         'basis': 'Structural reduction, profile optimization and the finite pair/template coefficients.'},
        {'id': 'fixed_offset', 'items': ['13.1', '13.2'],
         'requires': ['global_stability', 'local_stability'],
         'basis': 'Finite integral mass deviations and pair errors yield the lattice correction and exact +/-1 cases.'},
        {'id': 'eventual_polynomial', 'items': ['14.1'],
         'requires': ['fixed_offset', 'global_stability', 'local_stability'],
         'basis': 'Bounded defect data produce a finite polynomial list; this does not compute a global k_0(j).'},
    ]


def build_inventory(root):
    main = without_comments((root / 'paper/main.tex').read_text())
    require(re.search(r'\\newtheorem\{theorem\}\{Theorem\}\[section\]', main),
            'Unsupported theorem counter declaration')
    for env in ('lemma', 'proposition', 'corollary', 'remark', 'definition'):
        require(re.search(r'\\newtheorem\{' + env + r'\}\[theorem\]', main),
                'Unsupported shared theorem counter: ' + env)
    inputs = re.findall(r'\\input\{([^}]+)\}', main)
    input_paths = ['paper/' + (s if s.endswith('.tex') else s + '.tex') for s in inputs]
    require([s for s in input_paths if s in BODY] == BODY, 'Canonical body input order changed')
    scanned = ['paper/main.tex', 'paper/submission.tex'] + list(dict.fromkeys(input_paths))
    missing = [s for s in scanned if not (root / s).is_file()]
    require(set(missing) <= {'paper/author_metadata.tex'}, 'An expected main input is missing')
    scanned = [s for s in scanned if (root / s).is_file()]
    texts = {s: (root / s).read_text() for s in scanned}
    clean = {s: without_comments(t) for s, t in texts.items()}
    starts, joined, cursor = [], [], 0
    for source in BODY:
        t = clean[source]
        starts.append((cursor, source, [m.start() for m in re.finditer('\n', t)]))
        joined.append(t)
        cursor += len(t) + 1
    text = '\n'.join(joined)
    offsets = [p[0] for p in starts]

    def locate(position):
        i = bisect_right(offsets, position) - 1
        start, source, newlines = starts[max(0, i)]
        return {'source_file': source, 'line': bisect_right(newlines, position - start - 1) + 1}

    token = re.compile(
        r'\\(?P<div>section|subsection|subsubsection)(?P<star>\*)?\s*\{(?P<heading>[^{}]*)\}'
        r'|\\(?P<appendix>appendix)\b'
        r'|\\(?P<action>begin|end)\{(?P<env>[^}]+)\}(?:\[(?P<caption>[^\]]*)\])?'
        r'|\\label\{(?P<label>[^}]+)\}'
        r'|\\tag\*?\{(?P<tag>[^}]+)\}')
    sections, subdivisions, statements, proofs, equations, labels = [], [], [], [], [], []
    stack, appendix, section_no, counter, sub, subsub, figure_no = [], False, 0, 0, 0, 0, 0
    section = None
    for match in token.finditer(text):
        loc = locate(match.start())
        if match['appendix']:
            require(not appendix, 'Multiple appendix switches')
            appendix, section_no = True, 0
        elif match['div']:
            if match['star']:
                continue
            level = match['div']
            if level == 'section':
                section_no += 1
                counter, sub, subsub = 0, 0, 0
                number = chr(64 + section_no) if appendix else str(section_no)
                section = {'number': number, 'title': match['heading'], 'appendix': appendix,
                           **loc, '_start': match.start(), 'labels': []}
                sections.append(section)
            else:
                require(section is not None, 'Subdivision before any section')
                if level == 'subsection':
                    sub, subsub = sub + 1, 0
                    number = section['number'] + '.' + str(sub)
                else:
                    subsub += 1
                    number = section['number'] + '.' + str(sub) + '.' + str(subsub)
                subdivisions.append({'number': number, 'level': level, 'title': match['heading'], **loc})
        elif match['action'] == 'begin':
            env = match['env']
            entry = {'env': env, '_start': match.start(), '_content': match.end()}
            if env in NUMBERED:
                require(section is not None, 'Numbered result before section')
                counter += 1
                record = {'ordinal': len(statements) + 1, 'number': section['number'] + '.' + str(counter),
                          'kind': env, 'section': section['number'], 'title_tex': match['caption'],
                          'labels': [], 'source_file': loc['source_file'], 'line_start': loc['line'],
                          '_start': match.start(), '_content': match.end(), 'proof_ids': []}
                statements.append(record)
                entry['record'] = record
            elif env == 'proof':
                record = {'id': 'P%03d' % (len(proofs) + 1), 'caption': match['caption'],
                          'section': section['number'], 'source_file': loc['source_file'],
                          'line_start': loc['line'], '_start': match.start(), '_content': match.end()}
                proofs.append(record)
                entry['record'] = record
            elif env in MATH:
                entry['last_equation'] = None
            elif env in {'figure', 'figure*'}:
                figure_no += 1
                entry['figure'] = str(figure_no)
            stack.append(entry)
        elif match['action'] == 'end':
            require(stack and stack[-1]['env'] == match['env'],
                    'Unbalanced environment at %s:%s' % (loc['source_file'], loc['line']))
            entry = stack.pop()
            if 'record' in entry:
                record = entry['record']
                require(record['source_file'] == loc['source_file'], 'Environment spans canonical source files')
                record['line_end'] = loc['line']
                record['_end'] = match.end()
                record['source_sha256'] = hashlib.sha256(text[record['_start']:match.end()].encode()).hexdigest()
        elif match['tag'] is not None:
            require(match['tag'].isdigit(), 'Noninteger explicit equation tag')
            record = {'number': int(match['tag']), 'section': section['number'], **loc, 'labels': []}
            equations.append(record)
            math = next((entry for entry in reversed(stack) if entry['env'] in MATH), None)
            require(math is not None, 'Equation tag outside supported display environment')
            math['last_equation'] = record
        elif match['label'] is not None:
            math = next((entry for entry in reversed(stack) if entry['env'] in MATH), None)
            theorem = next((entry for entry in reversed(stack) if entry['env'] in NUMBERED), None)
            figure = next((entry for entry in reversed(stack) if 'figure' in entry), None)
            if math and math['last_equation'] is not None:
                owner = math['last_equation']
                owner['labels'].append(match['label'])
                kind, number = 'equation', str(owner['number'])
            elif theorem:
                owner = theorem['record']
                owner['labels'].append(match['label'])
                kind, number = owner['kind'], owner['number']
            elif figure:
                kind, number = 'figure', figure['figure']
            else:
                require(section is not None, 'Unowned label')
                section['labels'].append(match['label'])
                kind, number = 'section', section['number']
            labels.append({'label': match['label'], 'target_kind': kind, 'target_number': number, **loc})
    require(not stack, 'Unclosed manuscript environment')
    for source in scanned:
        if source not in BODY:
            for m in re.finditer(r'\\label\{([^}]+)\}', clean[source]):
                labels.append({'label': m[1], 'target_kind': 'frontmatter_or_status', 'target_number': None,
                               'source_file': source, 'line': clean[source].count('\n', 0, m.start()) + 1})
    require(len({x['label'] for x in labels}) == len(labels), 'Duplicate LaTeX label')
    label_map = {x['label']: x for x in labels}
    result_map = {x['number']: x for x in statements}
    statement_labels = {}
    for s in statements:
        require(len(s['labels']) == 1, 'Each current numbered statement must have one unique label')
        s['label'] = s['labels'][0]
        statement_labels[s['label']] = s
        s['title'] = display_title(s['title_tex']) if s['title_tex'] else SCOPE_TITLES.get(s['label'])
        require(s['title'], 'Add a reviewed statement-scope title for ' + s['label'])
        s['title_source'] = 'optional LaTeX title' if s['title_tex'] else 'reviewed statement scope'
        section_key = s['section']
        reviewer = ('stability' if section_key == 'A' or 8 <= int(section_key) <= 10
                    else 'foundations' if int(section_key) <= 7 else 'arithmetic')
        s['subject_area'] = reviewer
        s['additional_subject_area'] = (
            'arithmetic: finite two-vertex coefficients/template Hessian inputs, not the full local continuum proof'
            if s['number'] in {'A.3', 'A.4'} else
            'arithmetic: upstream statement/dependency traced, not an independent reproof of stability'
            if s['number'] == '9.3' else None)
        s['proof_expectation'] = 'expository remark; no proof environment required' if s['kind'] == 'remark' else 'proof location required'
    for proof in proofs:
        if proof['caption']:
            require(proof['caption'] in EXPLICIT_PROOFS, 'Unmapped explicit proof caption: ' + proof['caption'])
            targets = EXPLICIT_PROOFS[proof['caption']]
            proof['association_basis'] = 'explicit source caption plus reviewed component mapping'
        else:
            preceding = [s for s in statements if s['_end'] <= proof['_start']]
            require(preceding, 'Proof without preceding statement')
            statement = preceding[-1]
            require(not text[statement['_end']:proof['_start']].strip(),
                    'Uncaptioned proof is not immediately adjacent to its statement')
            require(statement['kind'] in FORMAL, 'Uncaptioned proof attached to a nonformal statement')
            targets = [(statement['label'], 'full statement')]
            proof['association_basis'] = 'immediately follows the statement, with only whitespace/comments between'
        proof['targets'] = []
        for label, component in targets:
            require(label in statement_labels, 'Unknown proof target ' + label)
            target = statement_labels[label]
            target['proof_ids'].append(proof['id'])
            proof['targets'].append({'label': label, 'number': target['number'],
                                     'kind': target['kind'], 'component': component})
    require(all(s['proof_ids'] for s in statements if s['kind'] in FORMAL), 'A formal result has no located proof')
    require(len(sections) == 15 and [s['number'] for s in sections] == [str(n) for n in range(1, 15)] + ['A'],
            'Expected Sections 1-14 followed by Appendix A')
    require(len(statements) == 43 and sum(s['kind'] in FORMAL for s in statements) == 42,
            'Expected 42 formal results plus Remark 10.3, not 43 formal results')
    require([s['number'] for s in statements if s['kind'] == 'remark'] == ['10.3'], 'Unexpected numbered remark')
    require(len(proofs) == 43, 'Expected 43 proof environments')
    require([e['number'] for e in equations] == list(range(1, 92)),
            'Equation tags must occur exactly once each, in source order, from 1 through 91')

    label_refs, literal_refs, section_refs, equation_refs, external_citations = [], [], [], [], []
    named = re.compile(r'\b(Theorems?|Lemmas?|Propositions?|Corollar(?:y|ies)|Remarks?)[\s~]+((?:[0-9]+|A)\.[0-9]+)\b')
    continuation = re.compile(r'[\s~]*(?:,[\s~]*(?:and[\s~]+)?|and[\s~]+|--[\s~]*|to[\s~]+)((?:[0-9]+|A)\.[0-9]+)\b')
    kind_names = {'theorem': 'theorem', 'theorems': 'theorem', 'lemma': 'lemma', 'lemmas': 'lemma',
                  'proposition': 'proposition', 'propositions': 'proposition',
                  'corollary': 'corollary', 'corollaries': 'corollary', 'remark': 'remark', 'remarks': 'remark'}
    all_sections = {s['number'] for s in sections + subdivisions}
    for source in scanned:
        t = clean[source]
        def local(position):
            return {'source_file': source, 'line': t.count('\n', 0, position) + 1}
        for m in re.finditer(r'\\(ref|eqref|pageref|autoref|nameref|cref|Cref|vref|Vref)\*?\{([^}]+)\}', t):
            for label in m[2].split(','):
                label = label.strip()
                require(label in label_map, 'Unresolved label reference: ' + label)
                label_refs.append({'command': m[1], 'label': label, 'resolved': True, **local(m.start())})
        for m in re.finditer(r'\\hyperref\[([^\]]+)\]', t):
            require(m[1] in label_map, 'Unresolved hyperref target: ' + m[1])
            label_refs.append({'command': 'hyperref', 'label': m[1], 'resolved': True, **local(m.start())})
        citation = re.compile(r'\\cite\w*\*?(?:\[[^\]]*\]){0,2}\{[^}]+\}')
        for m in citation.finditer(t):
            if named.search(m[0]):
                external_citations.append({'source': m[0], **local(m.start())})
        safe = citation.sub(lambda m: blank(m[0]), t)
        for m in named.finditer(safe):
            numbers = [(m[2], m.start())]
            tail = m.end()
            while True:
                extra = continuation.match(safe, tail)
                if not extra:
                    break
                numbers.append((extra[1], extra.start(1)))
                tail = extra.end()
            kind = kind_names[m[1].lower()]
            for number, position in numbers:
                require(number in result_map, 'Unresolved literal result reference: ' + kind + ' ' + number)
                require(result_map[number]['kind'] == kind, 'Wrong result kind in literal reference: ' + kind + ' ' + number)
                literal_refs.append({'kind': kind, 'number': number, 'target_label': result_map[number]['label'],
                                     'resolved': True, **local(position)})
        for m in re.finditer(r'\bSections?[\s~]+([0-9]+(?:\.[0-9]+)*|A)\b', safe):
            require(m[1] in all_sections, 'Unresolved literal section reference: ' + m[1])
            section_refs.append({'number': m[1], 'resolved': True, **local(m.start())})
        for m in re.finditer(r'\b[Ee]quations?[\s~]+\(([0-9]+)\)', safe):
            number = int(m[1])
            require(1 <= number <= 91, 'Unresolved named equation reference')
            equation_refs.append({'number': number, 'resolved': True, **local(m.start())})

    deps = dependency_stages()
    previous = set()
    for dep in deps:
        require(set(dep['requires']) <= previous, 'Curated dependency stages are not in acyclic order')
        previous.add(dep['id'])
        for item in dep['items']:
            if item.startswith('Introduction:'):
                continue
            require(item.split(':')[0] in result_map, 'Unknown curated dependency result ' + item)

    for record in sections + statements + proofs:
        for key in list(record):
            if key.startswith('_'):
                del record[key]
    for sec in sections:
        sec['statement_numbers'] = [s['number'] for s in statements if s['section'] == sec['number']]
        sec['equation_tags'] = [e['number'] for e in equations if e['section'] == sec['number']]
        sec['proof_ids'] = [p['id'] for p in proofs if p['section'] == sec['number']]
    return {
        'schema': 'induced-pentagons.manuscript-inventory.v1',
        'status': 'source_coverage_and_navigation_checks_passed',
        'claim': 'Structural coverage, valid locators and mathematical dependency navigation; not automated proof verification.',
        'canonical_body_order': BODY,
        'entry_points': ['paper/main.tex', 'paper/submission.tex'],
        'excluded_duplicate_sources': ['paper/Induced_pentagons_full_source.tex', 'paper/Induced_pentagons_submission.tex'],
        'optional_missing_inputs': missing,
        'counts': {'main_numbered_sections': 14, 'appendices': 1, 'numbered_statements': len(statements),
                   'formal_theorem_lemma_proposition_corollary_results': 42, 'numbered_remarks': 1,
                   'proof_environments': len(proofs), 'explicit_equation_tags': len(equations),
                   'unique_labels': len(labels), 'label_based_reference_occurrences': len(label_refs),
                   'literal_named_result_reference_occurrences': len(literal_refs),
                   'literal_named_section_reference_occurrences': len(section_refs),
                   'explicitly_named_equation_reference_occurrences': len(equation_refs),
                   'result_kinds': dict(sorted(Counter(s['kind'] for s in statements).items()))},
        'count_explanation': '43 numbered statements = 42 formal results + Remark 10.3. The 43 proofs include one shared inequality proof for Theorems 1.1/1.3 and their two separate equality proofs.',
        'checks': {'section_sequence_1_through_14_then_A': True, 'equation_tags_1_through_91_once_each_in_order': True,
                   'numbered_statement_labels_unique': True, 'all_scanned_labels_unique': True,
                   'all_label_based_references_resolve': True, 'all_recognized_named_result_references_resolve_with_correct_kind': True,
                   'every_formal_result_has_a_located_proof': True, 'all_proof_environments_mapped': True,
                   'curated_dependency_stages_acyclic': True},
        'sections': sections, 'subdivisions': subdivisions, 'statements': statements,
        'proofs': proofs, 'equation_tags': equations, 'labels': labels,
        'references': {'label_based': label_refs, 'literal_named_results': literal_refs,
                       'literal_named_sections': section_refs, 'explicitly_named_equations': equation_refs,
                       'external_citation_arguments_excluded_from_internal_reference_validation': external_citations},
                'dependency_stages': deps,
        'dependency_scope': 'Selected mathematical implications, not an exhaustive graph; ordinary source citations are not converted into proof dependencies. Theorem 1.1/1.3 components are kept separate to avoid a spurious cycle.',
        'limitations': [
            'This is a parser for the explicit source syntax of this manuscript, not a general TeX interpreter.',
            'The inventory neither validates mathematical deductions nor turns a review status into a proof.',
            'Literal named references are checked as navigation targets; bare numerical prose and all possible natural-language reference forms are not interpreted.',
            'The absence of label-based reference commands is recorded explicitly; current named result references are literal text.',
            'External citation arguments are excluded from internal result numbering checks.',
            'A proof location records where an argument is supplied, not that the argument is correct.',
        ],
        'source_sha256': {source: digest(root / source) for source in scanned},
        'generator_sha256': digest(Path(__file__).resolve()),
    }


def render_guide(inventory):
    c=inventory['counts']
    lines=['PROOF DEPENDENCY GUIDE','',
           'This guide locates the statements, equations and arguments in the manuscript.',
           'Its parser checks numbering, source coverage and reference targets; it does not',
           'automatically verify mathematical deductions. The computational witnesses are',
           'checked separately by python src/verify_project.py.','',
           'Canonical source order: '+', '.join(inventory['canonical_body_order']),
           'Numbered statements: '+str(c['numbered_statements']),
           'Proof environments: '+str(c['proof_environments']),
           'Numbered equations: '+str(c['explicit_equation_tags']),
           'Unique labels: '+str(c['unique_labels']),'',
           'Run python src/check_manuscript_inventory.py to check this index.',
           'Run with --write after reviewing a source edit to regenerate the index.','',
           'STATEMENT AND PROOF INDEX','']
    proof_map={p['id']:p for p in inventory['proofs']}
    for sec in inventory['sections']:
        lines.append(('Appendix ' if sec['appendix'] else 'Section ')+sec['number']+': '+sec['title'])
        for item in inventory['statements']:
            if item['section']!=sec['number']:continue
            lines.append('  '+item['kind'].capitalize()+' '+item['number']+': '+item['title'])
            lines.append('    Label: '+item['label'])
            for key in ('file','line','source','start_line'):
                if key in item:lines.append('    '+key+': '+str(item[key]))
        lines.append('')
    lines += ['DEPENDENCY STAGES','']
    for stage in inventory['dependency_stages']:
        lines += [stage['id']+': '+', '.join(stage['items']),
                  '  Requires: '+(', '.join(stage['requires']) or 'no earlier stage'),
                  '  '+stage['basis'],'']
    lines += ['The JSON index contains every proof mapping and equation locator.',
              'A located proof is a supplied mathematical argument, not an automated validity verdict.','']
    return '\n'.join(lines)


def main():
    if not __debug__:
        raise RuntimeError('Manuscript inventory refuses Python -O, -OO or PYTHONOPTIMIZE.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--write', action='store_true', help='Regenerate the JSON index and readable guide')
    args = parser.parse_args()
    root = args.root.resolve()
    inventory = build_inventory(root)
    outputs = {
        root / 'blueprint/statements.json': json.dumps(inventory, indent=2) + '\n',
        root / 'blueprint/proof_dependencies.txt': render_guide(inventory),
    }
    for path, expected in outputs.items():
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(expected)
        else:
            require(path.is_file(), 'Inventory artifact missing; run with --write: ' + str(path))
            require(path.read_text() == expected, 'Inventory artifact is stale; review source changes and run with --write: ' + str(path))
    print(json.dumps({'status': inventory['status'], 'mode': 'written' if args.write else 'checked',
                      'counts': inventory['counts'], 'mathematical_proof_verification': False}))


if __name__ == '__main__':
    main()
