#!/usr/bin/env python3
"""Build and audit the Mathlib-based mathematical proof layer."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / 'formal/paper'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
AUDITED = ('toSimpleGraph_adj dart_card_blowUp pentagon_card_blowUp '
           'pentagon_card_withIsolates edgeMass_nonnegative pentagonMass_nonnegative '
           'edgeMass_scale pentagonMass_scale edgeMass_unit pentagonMass_unit '
           'edgeMass_blowUp pentagonMass_blowUp pentagonMass_withIsolates '
           'squaredRatio_scale squaredRatio_blowUp clebsch_dart_card '
           'clebsch_balanced_edgeMass clebsch_blowUp_edges periodicCost_add '
           'periodicCost_sum periodicCost_le_profileCost reduced_scalar_profile '
           'scalar_profile_cost scalar_profile bernoulliWeight_nonnegative '
           'bernoulliWeight_sum bernoulliExtension_le bernoulliExtension_pattern '
           'bernoulliExtension_patterns pattern_sum_le_of_boolean_bound '
           'mem_labelledPentagons candidateWalks_nodup labelledPentagons_nodup '
           'pentagon_card_eq_labelled_length clebsch_labelled_pentagons '
           'clebsch_pentagon_card clebsch_balanced_pentagonMass clebsch_blowUp_pentagons '
           'sharpConstant_positive sharpConstant_sq clebsch_balanced_squared_equality '
           'clebsch_balanced_sharp_equality clebsch_squaredRatio_unit '
           'clebsch_balanced_squaredRatio cliqueFree_comap natCast_dart_card_sigma '
           'integral_weighted_clique scaled_integral_weighted_clique weighted_clique '
           'independentSubsetsFrom_complete clebsch_independent_family_bound '
           'clebsch_independent_card_le clebsch_complement_cliqueFree '
           'clebsch_complement_weighted patternIndicator_le_one patternTotal_filter '
           'patternBound_sound bernoulliExtension_patternTotal patternBound_fractional '
           'mem_inducedPaths candidatePaths_nodup inducedPaths_nodup clebsch_inducedPaths_count '
           'dart_sum_eq_doubleSum edgeMass_eq_orderedEdgeSum profileMaskData_exact '
           'profileMask_literals_checked pathMask_literal_eq profileLink_mask_sum '
           'clebsch_profile_boolean_bound profileLink_le_sixty_from_masks profileLink_le_sixty '
           'pathValue_le_endpoints profileLink_le_endpointSum clebsch_path_endpoint_multiplicity '
           'nonedgePairs_weight_sum clebsch_endpoint_weight_sum profileLink_le_quadratic '
           'profileDegree_nonnegative profile_envelope scalar_profile_clebsch scalar_profile_equation58 '
           'neighborhoodProfile_range neighborhoodProfile_degree pathValue_neighborhood '
           'clebsch_neighborhood_path_count neighborhoodProfile_link profile_envelope_attained '
           'path_self_maps pathTuple_pattern pathTuple_vertex_injective pathVertices_card '
           'tupleOfPathIso_induced tupleOfPathIso_vertices inducedPathSet_iff_mem_inducedPaths '
           'normalized_path_unique inducedPaths_vertices_injective pathSubsetEquiv '
           'pathSetLiteral_eq profileLink_eq_setProfileLink profile_envelope_on_induced_subsets '
           'profile_envelope_attained_on_induced_subsets scalar_profile_on_induced_subsets '
           'cycleSymmetry_card cycleSymmetry_bijective cycleRotate_pattern '
           'cycle_rooted_self_maps canonicalTuple_iff mem_inducedPentagons_iff '
           'inducedPentagons_nodup pentagonVertices_card exists_canonical_pentagon '
           'tupleOfPentagonIso_induced tupleOfPentagonIso_vertices inducedPentagonSet_iff_mem_inducedPentagons '
           'normalized_pentagon_unique inducedPentagons_vertices_injective pentagonSubsetEquiv '
           'embeddingOfPentagonIso_vertices embeddingFibreEquiv embeddingFibre_card '
           'pentagonEmbedding_product pentagonMass_eq_setMass pentagonSet_card_eq_normalized_length '
           'pentagonMass_eq_normalized_length pentagonMass_eq_normalizedMass labelled_length_eq_ten_mul_normalized '
           'clebsch_induced_pentagonSet_card '
           'BooleanGraphEquiv.toSimpleGraphIso graphExtensionEquiv atlasCovers_zero '
           'atlasCovers_succ small_neighborhoods_complete atlasWitnessCheck_sound '
           'atlasRowCheck_sound atlasExtends_of_rows atlas7_covers '
           'atlas7_count atlas7_masks_nodup seven_vertex_graph_isomorphic_to_atlas '
           'atlas7_eq_certificate_hosts seven_vertex_graph_isomorphic_to_certificate_host certificate_host_count '
           'edge5_eq_maskGraph atlasWitnessCheck_rejects_noninjective atlasWitnessCheck_rejects_wrong_graph '
           'atlasRowCheck_rejects_missing_target patternSatisfies_comp_equiv_iff patternInjectionEquiv '
           'patternInjectionCount_isomorphic satisfies_completePattern_iff pentagonPattern_satisfies_iff '
           'pentagonPatternEquiv pentagonPattern_count patternInjectionWeight_isomorphic '
           'pentagonPattern_weight '
           'toSimpleGraph_boolGraphOfSimpleGraph seven_vertex_simpleGraph_isomorphic_to_certificate_host patternInjectionCount_reduced_to_certificate ').split()


def sources():
    for directory, folders, files in os.walk(PAPER):
        folders[:] = [n for n in folders if not n.startswith('.') and n != '__pycache__']
        yield from (Path(directory) / n for n in files if not n.startswith('.'))
    yield ROOT / 'formal/InducedPentagons/FiniteGraph.lean'
    yield ROOT / 'formal/InducedPentagons/Isolates.lean'
    yield ROOT / 'formal/InducedPentagons/Verifier.lean'
    yield ROOT / 'formal/InducedPentagons/Generated/Inputs.lean'
    yield ROOT / 'certificates/graph_atlas_7.json'
    yield ROOT / 'scripts/export_lean_profiles.py'
    yield ROOT / 'scripts/export_lean_atlas.py'
    yield Path(__file__)


def fingerprints():
    return {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(set(sources()))}


def run(command, *, capture=False):
    result = subprocess.run(command, cwd=PAPER, text=True, encoding='utf-8',
                            errors='replace', capture_output=capture)
    if result.returncode:
        if capture:
            print(result.stdout + result.stderr, end='')
        raise subprocess.CalledProcessError(result.returncode, command)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-build', action='store_true',
                        help='Require the existing build to be current (for CI).')
    args = parser.parse_args()
    started = time.time()
    lake = shutil.which('lake')
    if lake is None:
        raise SystemExit('Lake is not on PATH. Install formal/paper/lean-toolchain first.')
    os.environ.setdefault('LEAN_NUM_THREADS', '2')
    run([sys.executable, str(ROOT / 'scripts/export_lean_profiles.py'), '--check'])
    run([sys.executable, str(ROOT / 'scripts/export_lean_atlas.py'), '--check'])
    initial = fingerprints()
    for path in sources():
        if path.suffix == '.lean' and re.search(
                r'\b(sorry|admit|native_decide|sorryAx|ofReduceBool)\b|(?m:^\s*axiom\s)',
                path.read_text(encoding='utf-8')):
            raise RuntimeError('Disallowed proof escape in ' + str(path.relative_to(ROOT)))
    version = run([lake, 'env', 'lean', '--version'], capture=True).stdout.strip()
    if not re.search(r'Lean \(version 4\.35\.0,', version):
        raise RuntimeError('Unexpected Lean toolchain: ' + version)
    run([lake, '--no-build', 'build'] if args.skip_build else [lake, 'build'])
    audit = run([lake, 'env', 'lean', 'Audit.lean'], capture=True).stdout
    print(audit, end='')
    audited = {}
    for match in re.finditer(
            r"'([^']+)' (does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])", audit):
        names = [] if match[2].startswith('does not') else [
            x.strip() for x in (match[3] or '').split(',') if x.strip()]
        if set(names) - ALLOWED_AXIOMS:
            raise RuntimeError('Unexpected transitive axioms: ' + match[0])
        audited[match[1]] = names
    if set(audited) != {'InducedPentagons.Paper.' + n for n in AUDITED}:
        raise RuntimeError('The axiom audit did not cover exactly the required declarations')
    final = fingerprints()
    if initial != final:
        raise RuntimeError('Proof sources changed during verification; rerun on a stable checkout')
    report = {'schema': 'induced-pentagons.lean-paper-verification.v1',
              'status': 'verified_lean_mathematical_components',
              'scope': ['finite weighted graph and blow-up identities',
                        'complete labelled Clebsch pentagon count and sharp construction equality',
                        'general labelled, canonical and induced-subset weighted pentagon conventions',
                        'universal seven-vertex atlas coverage bound to actual certificate hosts',
                        'generic partial-pattern injection semantics and isomorphism invariance',
                        'weighted clique inequality and Clebsch complement quadratic bound',
                        'Bernoulli multilinear extension and Boolean bound transfer',
                        'graph-defined Clebsch profile envelope and neighborhood attainment',
                        'scalar profile equation (58) with its Clebsch envelope hypotheses discharged'],
              'full_paper_formalized': False, 'toolchain': version,
              'mathlib_revision': next(p['rev'] for p in json.loads(
                  (PAPER / 'lake-manifest.json').read_text())['packages'] if p['name'] == 'mathlib'),
              'axioms': audited, 'allowed_standard_axioms': sorted(ALLOWED_AXIOMS),
              'source_sha256': final, 'elapsed_seconds': time.time() - started}
    output = ROOT / 'results/lean_paper_verification.json'
    output.write_bytes((json.dumps(report, indent=2) + '\n').encode('utf-8'))
    print(json.dumps({'status': report['status'], 'declarations_audited': len(audited),
                      'seconds': round(report['elapsed_seconds'], 2)}, indent=2))


if __name__ == '__main__':
    main()
