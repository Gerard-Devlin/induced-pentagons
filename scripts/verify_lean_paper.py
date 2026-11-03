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
           'toSimpleGraph_boolGraphOfSimpleGraph seven_vertex_simpleGraph_isomorphic_to_certificate_host patternInjectionCount_reduced_to_certificate '
           'prefixMatches_iff prefixSatisfies_restrict prefixSatisfies_full_iff '
           'extendPrefix_injective_iff mem_patternPrefixes patternPrefixes_nodup '
           'mem_patternInjectionEnumeration patternEnumerationEquiv patternInjectionCount_eq_enumeration_length '
           'stepMatches_iff_prefix fastPatternPrefixes_eq fastPatternEnumeration_count '
           'primitiveSemanticCounts_eq_enumerated primitiveRowCheck_sound orderedSpecsCheck_sound '
           'primitiveSemanticCounts_eq_fast fastPrimitiveRowCheck_sound unconstrainedPattern_count '
           'patternInjectionCount_le_total patternInjectionDensity_nonnegative patternInjectionDensity_le_one '
           'primitivePatternSpecs_count primitivePatternSpecs_ordered primitivePattern_denominators '
           'primitive_empty_count_values primitive_empty_host_semantics primitive_complete_count_values '
           'primitive_complete_host_semantics primitive_changed_count_rejected ').split()
AUDITED += ('primitiveSemanticCounts_isomorphic primitiveSemanticDensities_eq_zipWith '
            'primitiveSemanticDensities_isomorphic primitiveSemanticDensities_bounds '
            'primitive_counts_reduced_to_verified_rows primitive_certificate_rows_semantics '
            'primitive_certificate_rows_masks primitive_certificate_rows_indices '
            'primitive_certificate_rows_count primitive_certificate_rows_masks_nodup '
            'primitive_certificate_row_width '
            'primitive_certificate_densities primitive_counts_on_all_seven_vertex_graphs '
            'primitive_densities_on_all_seven_vertex_graphs primitive_counts_on_all_seven_vertex_simpleGraphs '
            'foldr_or_testBit rawGraphEncoding_testBit rawGraphEncoding_at_pair '
            'graphEncoding_congr graphEncoding_adj graphEncoding_equiv '
            'edgeIndexSeparated_four edgeIndexBounded_four edgeIndexSeparated_five edgeIndexBounded_five '
            'rootedWitnessCheck_sound rootedFlagBasisCovers_of_rows rootedBasisSeparatedCheck_sound '
            'rootedPermutationCodes4_complete rootedPermutationCodes5_complete '
            'rootedWitnessCheck_rejects_moved_root rootedWitnessCheck_rejects_wrong_adjacency').split()
for _flag_name in ('one_root', 'independent3', 'edge_isolate', 'path3', 'triangle3'):
    AUDITED += [f'flag_basis_{_flag_name}_{suffix}' for suffix in
                ('certificate', 'count', 'nodup', 'types_checked', 'covers', 'separated')]
    AUDITED += [f'certificate_flag_basis_{_flag_name}_{suffix}' for suffix in ('covers', 'separated')]
AUDITED += ('rootedClassify_sound rootedClassify_eq_iff rootedClassify_isomorphic '
            'patternSignatureSeparationCheck_sound kernelSort_eq_sort subsetVertex_eq_orderEmb '
            'inducedGraphTypeSet_card inducedGraphTypeSet_iff_subsetGraphIso complementEdgeCheck_iff '
            'five_subset_complement_card fiveGraphType_sound fiveGraphType_eq_iff fiveGraphType_isomorphic '
            'fiveGraphType_certificate_mem fixed_type_certificate_separated fixedSubsetCheck_iff '
            'fixedComplementSubsetCheck_iff fixedDensityCount_semantics fixedComplementCount_semantics '
            'fixedDensityCounts_semantics fixedComplementCounts_semantics fixedDensityCount_le '
            'fixedComplementCount_le five_subsets_of_seven_count inducedGraphTypeSet_image_iff '
            'complementEdge_image_iff inducedTypeSetCount_isomorphic inducedTypeComplementCount_isomorphic '
            'fixedDensityCount_isomorphic fixedComplementCount_isomorphic fixedDensityCounts_isomorphic '
            'fixedComplementCounts_isomorphic fixedDensityCounts_sum fiveTypeDensity_nonnegative '
            'fiveTypeComplementDensity_nonnegative fiveTypeDensity_le_one fiveTypeComplementDensity_le '
            'fiveTypeDensities_sum freeColumns_fixedAt fixedColumn_scale certificate_data_denominator '
            'freeColumns_fixed_normalized fixed_certificate_induced_values fixed_certificate_complement_values '
            'fixed_certificate_induced_semantics '
            'fixed_certificate_complement_semantics fixed_certificate_row_widths '
            'fixed_certificate_counts_sum fixed_certificate_entry_values fixed_certificate_free_column '
            'fixed_certificate_density_values fixed_counts_on_all_seven_vertex_graphs '
            'fixed_semantic_counts_on_all_seven_vertex_graphs fixed_counts_on_all_seven_vertex_simpleGraphs '
            'fixed_changed_induced_count_rejected fixed_changed_complement_count_rejected '
            'fixed_type_lookup_checked fixedSignatureSpecs_ordered fixed_signature_data_masks '
            'fixed_signature_data_semantics fixed_signature_data_separated fixed_types_separated '
            'fixed_type_masks_certificate fixed_type_masks_count fixed_type_masks_nodup '
            'fixed_certificate_rows_semantics').split()


AUDITED += ('graphCountCode_isomorphic rowCountCode_semantics increasingHostCodes_pairwise '
            'pairwiseHostCodes_separate increasingHostCodes_separate storedHostCodes_binding '
            'storedHostCodes_permutation sortedHostCodes_checked certificate_hosts_pairwise_nonisomorphic '
            'seven_vertex_graph_unique_certificate_host seven_vertex_simpleGraph_unique_certificate_host '
            'flagIndex_sound flagIndex_eq_iff flagIndex_isomorphic indexedFlag_wrong_index_rejected '
            'flagRootVertices_card jointFlag_left_choice_card jointFlagSample_card '
            'jointFlagSample_one_root_card jointFlagSample_three_roots_card '
            'JointFlagSample.left_card JointFlagSample.roots_left_disjoint '
            'JointFlagSample.right_available JointFlagSample.right_card JointFlagSample.swap_right '
            'JointFlagSample.swap_swap jointFlagPairCount_symmetric jointFlagPairCount_le '
            'JointFlagSample.vertex_root JointFlagSample.vertex_free JointFlagSample.free_vertex_mem '
            'JointFlagSample.vertex_injective JointFlagSample.vertex_mem jointFlagGraph_rootType '
            'jointFlagGraph_swap_rootType jointFlagPair_classifier_iff jointFlagPairCount_semantics '
            'mem_flagRootFunctions flagRootEmbeddingList_nodup mem_flagRootEmbeddingFinset '
            'mem_jointLeftChoices mem_jointFlagSamples jointFlagSamples_eq_univ jointFlagSamples_card '
            'enumeratedJointFlagPairCount_eq flagProduct_empty_one_root_value '
            'flagProduct_empty_independent3_value flagProduct_empty_nonzero_entries').split()
for _flag_name in ('one_root', 'independent3', 'edge_isolate', 'path3', 'triangle3'):
    AUDITED += [f'indexedFlagBasis_{_flag_name}_{suffix}' for suffix in
                ('toList', 'injective', 'certificate', 'certificateAt', 'separated')]
    AUDITED += [f'indexedFlagLookup_{_flag_name}_checked']
    AUDITED += [f'indexedFlag_{_flag_name}_{suffix}' for suffix in ('sound', 'eq_iff', 'isomorphic')]
    AUDITED += [f'flagProductCount_{_flag_name}_{suffix}' for suffix in ('semantics', 'symmetric', 'le')]
    AUDITED += [f'flagProductDenominator_{_flag_name}']


AUDITED += ['jointFlagPairKeys_count_upper', 'flagTensorKeys_count_one_root', 'flagTensorKeys_count_independent3', 'flagTensorKeys_count_edge_isolate', 'flagTensorKeys_count_path3', 'flagTensorKeys_count_triangle3', 'weightedCountAt_eq_zero_of_absent', 'rawFlagTensorCount_eq_zero_of_absent', 'fastTrieTensorRowCheck_one_root', 'fastTrieTensorRowCheck_one_root_omitted', 'fastTrieTensorRowCheck_independent3', 'fastTrieTensorRowCheck_independent3_omitted', 'fastTrieTensorRowCheck_edge_isolate', 'fastTrieTensorRowCheck_edge_isolate_omitted', 'fastTrieTensorRowCheck_path3', 'fastTrieTensorRowCheck_path3_omitted', 'fastTrieTensorRowCheck_triangle3', 'fastTrieTensorRowCheck_triangle3_omitted']

AUDITED += ('continuous_edgeMass continuous_pentagonMass continuousAt_squaredRatio '
            'tendsto_edgeMass tendsto_pentagonMass tendsto_squaredRatio '
            'unitMassWeights_nonempty unitMassWeights_coordinate_le_one isClosed_unitMassWeights '
            'isCompact_unitMassWeights isCompact_unitMassWeights_edgeMass '
            'exists_max_pentagonMass exists_max_edgeMass').split()

AUDITED += ['JointFlagSample.permutationFiberEquiv', 'jointFlagFullPermutation_fiber_card', 'jointFlagFullPermutation_one_root_fiber_card', 'jointFlagFullPermutation_three_roots_fiber_card', 'jointFlagFullPermutation_predicate_card', 'jointFlagFullPermutation_pair_count', 'jointFlagSample_card_mul_factorial_sq', 'jointFlagFullPermutation_probability']

AUDITED += ('edgePhasePenalty_nonnegative edgePhasePenalty_scale '
            'edgePhasePenalty_add edgePhasePenalty_le_add_abs '
            'edgePhasePenalty_lipschitz edgePhasePenalty_le_variance '
            'edgePhasePenalty_le_edit_cost phaseCoefficient_eq_phaseCost '
            'phaseCoefficient_nonnegative phaseCoefficient_le '
            'phaseCoefficient_maximum phaseCoefficient_endpoints '
            'phase_edge_residual phase_integer_offset '
            'phase_edge_residual_error phase_deficit_reduction '
            'reduced_scalar_profile_sharp phaseCoefficient_continuous '
            'phaseCoefficient_range').split()

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
    yield ROOT / 'scripts/export_lean_patterns.py'
    yield ROOT / 'scripts/export_lean_flags.py'
    yield ROOT / 'scripts/export_lean_fixed.py'
    yield ROOT / 'scripts/export_lean_flag_indices.py'
    yield ROOT / 'scripts/export_lean_host_codes.py'
    yield ROOT / 'scripts/export_lean_certificate.py'
    yield ROOT / 'src/proof_specification.py'
    yield ROOT / 'certificates/pattern_columns.json'
    yield ROOT / 'certificates/pattern_columns.npz'
    yield ROOT / 'certificates/flag_basis.npz'
    yield ROOT / 'formal/InducedPentagons/Generated/manifest.json'
    yield from (ROOT / 'formal/InducedPentagons/Generated').glob('HostData*.lean')
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
    run([sys.executable, str(ROOT / 'scripts/export_lean_patterns.py'), '--check'])
    run([sys.executable, str(ROOT / 'scripts/export_lean_flags.py'), '--check'])
    run([sys.executable, str(ROOT / 'scripts/export_lean_fixed.py'), '--check'])
    run([sys.executable, str(ROOT / 'scripts/export_lean_flag_indices.py'), '--check'])
    run([sys.executable, str(ROOT / 'scripts/export_lean_host_codes.py'), '--check'])
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
                        'universal seven-vertex atlas coverage and pairwise nonisomorphism bound to actual certificate hosts',
                        'every seven-vertex graph has a unique certificate host up to isomorphism',
                        'generic partial-pattern injection semantics and isomorphism invariance',
                        'complete prefix enumeration and proved ordered-step optimization',
                        'injection denominators, density bounds and explicit specifications of all 22 primitives',
                        'all 22968 stored primitive counts on all 1044 certificate hosts, with universal count and density transfer',
                        'all five actual rooted flag bases: coverage, separation and checked classifiers into actual tensor basis indices',
                        'complete executable joint flag sampling, rooted-isomorphism pair semantics, symmetry, bounds and actual denominators',
                        'direct kernel recounts of the two saved nonzero tensor entries on the empty host; zero entries and remaining hosts are not yet checked',
                        'all 70992 fixed-density entries on all 1044 hosts, with induced-subset semantics and normalized probabilities',
                        'the 34 actual five-vertex types form a complete separated basis; the fixed certificate columns have exact density semantics',
                        'weighted clique inequality and Clebsch complement quadratic bound',
                        'Bernoulli multilinear extension and Boolean bound transfer',
                        'graph-defined Clebsch profile envelope and neighborhood attainment',
                        'scalar profile equation (58) with its Clebsch envelope hypotheses discharged'],
              'full_paper_formalized': False,
              'seven_vertex_atlas': {'coverage_verified': True, 'pairwise_nonisomorphism_verified': True,
                                     'unique_certificate_representative_verified': True,
                                     'canonical_minimality_verified': False, 'automorphism_orbit_census_verified': False},
              'joint_flag_sampling': {'complete_executable_enumeration_verified': True,
                                      'denominators': [140, 1260, 1260, 1260, 1260],
                                      'actual_certificate_denominators_verified': True,
                                      'rooted_isomorphism_pair_count_semantics_verified': True,
                                      'swap_symmetry_verified': True,
                                      'empty_host_nonzero_entries_recounted': 2,
                                      'empty_host_zero_entries_verified': False,
                                      'full_saved_tensor_table_verified': False,
                                      'full_permutation_fiber_bridge_verified': False},
              'primitive_count_table': {'patterns_specified': 22, 'hosts_verified': 1044,
                                        'counts_verified': 22968, 'remaining_hosts': 0,
                                        'full_table_verified': True},
              'rooted_flag_bases': {'blocks_verified': 5, 'basis_sizes': [20, 72, 72, 72, 72],
                                    'coverage_witnesses': 576, 'coverage_verified': True,
                                    'pairwise_rooted_nonisomorphism_verified': True,
                                    'actual_basis_index_classifiers_verified': True,
                                    'flag_product_tensors_verified': False},
              'fixed_density_table': {'types_verified': 34, 'classification_witnesses': 1024,
                                      'hosts_verified': 1044, 'induced_entries_verified': 35496,
                                      'complement_entries_verified': 35496, 'total_entries_verified': 70992,
                                      'subset_denominator': 21, 'full_table_verified': True,
                                      'arbitrary_graph_transfer_verified': True,
                                      'fixed_free_columns_semantics_verified': True},
              'toolchain': version,
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
