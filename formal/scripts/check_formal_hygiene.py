#!/usr/bin/env python3
"""Guard the public Lean surface and audit its admitted axioms."""

from __future__ import annotations

from pathlib import Path
import re
import subprocess
import sys


REPO_ROOT = Path(__file__).resolve().parents[2]
LEAN_FILES = [REPO_ROOT / "CubicAnomaly.lean", *sorted((REPO_ROOT / "CubicAnomaly").rglob("*.lean"))]
FORBIDDEN = re.compile(
    r"\b(?:axiom|extern|implemented_by|sorry|admit|unsafe)\b|"
    r"\bpartial\s+def\b"
)
PUBLIC_THEOREM = re.compile(
    r"\b(?P<modifiers>(?:(?:protected|private|public|noncomputable)\s+)*)"
    r"(?:theorem|lemma)\s+(?P<name>[^\s:({]+)"
)
THEOREM_KEYWORD = re.compile(r"\b(?:theorem|lemma)\b")
SUPPORTED_THEOREM_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
NATIVE_AXIOMS = {"propext", "Lean.ofReduceBool", "Lean.trustCompiler", "Quot.sound"}
KERNEL_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_AUDIT = REPO_ROOT / "formal" / "AxiomAudit.lean"
NATIVE_THEOREMS = frozenset(
    {
        'CubicAnomaly.Classification.Exceptional.cartan_cubic_selector',
        'CubicAnomaly.Classification.Exceptional.exceptional_order_two_odd_graphs_connected',
        'CubicAnomaly.Classification.Exceptional.exceptional_toral_census',
        'CubicAnomaly.Classification.Selection.finite_cubic_selection_exists',
        'CubicAnomaly.Classification.Selection.finite_cubic_selection_exists_unique',
        'CubicAnomaly.Classification.Selection.finite_cubic_selection_iff',
        'CubicAnomaly.Classification.Selection.finite_cubic_selection_unique',
        'CubicAnomaly.E6.a2_occurs_exactly_on_two_extremal_cells',
        'CubicAnomaly.E6.common_maximal_multiplicity_valid',
        'CubicAnomaly.E6.context_counts_valid',
        'CubicAnomaly.E6.e6_root_table_valid',
        'CubicAnomaly.E6.extrema_counts_and_bounds_valid',
        'CubicAnomaly.E6.finite_certificate_valid',
        'CubicAnomaly.E6.intrinsic_da_dimension_ordering',
        'CubicAnomaly.E6.intrinsic_da_root_count_ordering',
        'CubicAnomaly.E6.intrinsic_da_root_count_ordering_of_orbit_membership',
        'CubicAnomaly.E6.intrinsic_pair_data_valid',
        'CubicAnomaly.E6.intrinsic_pair_dimensions_of_orbit_membership',
        'CubicAnomaly.E6.intrinsic_pair_signatures',
        'CubicAnomaly.E6.labelled_containments_valid',
        'CubicAnomaly.E6.pairwise_common_multiplicity_valid',
        'CubicAnomaly.E6.six_cell_distribution_valid',
        'CubicAnomaly.E6.six_cell_orbits_classified_valid',
        'CubicAnomaly.E6.six_weyl_orbits_partition_triple_space',
        'CubicAnomaly.E6.subsystem_orbit_sizes_valid',
        'CubicAnomaly.E6.subsystem_orbit_types_and_sizes_valid',
        'CubicAnomaly.E6.triple_space_has_38880_distinct_elements',
        'CubicAnomaly.E6.triple_space_has_38880_elements',
        'CubicAnomaly.E6.triple_universe_orbit_membership',
    }
)
KERNEL_THEOREMS = frozenset(
    {
        'CubicAnomaly.Classification.AbsoluteIrreducibility.complexification_irreducible_of_no_complex_structure',
        'CubicAnomaly.Classification.AbsoluteSimplicity.anticomplex_intertwiner_eq_zero',
        'CubicAnomaly.Classification.AbsoluteSimplicity.compact_pair_complexification_simple',
        'CubicAnomaly.Classification.AbsoluteSimplicity.compact_real_simple_is_absolutely_simple',
        'CubicAnomaly.Classification.AllRank.all_rank_structural_reduction',
        'CubicAnomaly.Classification.AllRank.hermitian_half_cubic_radical_membership',
        'CubicAnomaly.Classification.AllRankComplex.all_rank_complex_structural_reduction',
        'CubicAnomaly.Classification.AllRankComplex.all_rank_nonzero_cartan_anomaly_kernel',
        'CubicAnomaly.Classification.AllRankComplex.all_rank_nonzero_cartan_weight_kernel',
        'CubicAnomaly.Classification.AllRankGrading.all_rank_rank_deficient_or_cyclic_grading',
        'CubicAnomaly.Classification.AllRankGrading.equal_abelianRank_canonical_cyclic_grading',
        'CubicAnomaly.Classification.AnomalyComplexification.complexify_matrix_map_tmul',
        'CubicAnomaly.Classification.AnomalyComplexification.hermitian_complex_cubic_real_inputs',
        'CubicAnomaly.Classification.AnomalyComplexification.hermitian_complex_radical_eq_baseChange',
        'CubicAnomaly.Classification.AnomalyComplexification.hermitian_complex_radical_membership',
        'CubicAnomaly.Classification.AnomalyComplexification.hermitian_complex_radical_ne_bot_iff',
        'CubicAnomaly.Classification.AnomalyComplexification.hermitian_matrix_trace_cubic_real',
        'CubicAnomaly.Classification.AnomalyComplexification.hermitian_radical_ne_bot_iff_cartan_matrix_kernel',
        'CubicAnomaly.Classification.CanonicalAnomaly.canonical_anomaly_iff_cartan_weight_kernel',
        'CubicAnomaly.Classification.CanonicalAnomaly.canonical_cartan_cubic_matrix_eq_weight_matrix',
        'CubicAnomaly.Classification.CanonicalAnomaly.canonical_cubic_cartan_weight_sum',
        'CubicAnomaly.Classification.CanonicalCoroot.all_rank_exists_null_coroot',
        'CubicAnomaly.Classification.CanonicalCoroot.canonical_anomaly_iff_null_coroot',
        'CubicAnomaly.Classification.CanonicalCoroot.canonical_complex_radical_eq_iSup_null_corootIdeals',
        'CubicAnomaly.Classification.CanonicalCoroot.canonical_complex_radical_eq_lieSpan_null_coroots',
        'CubicAnomaly.Classification.CanonicalCoroot.canonical_coroot_cubic_eq_trace',
        'CubicAnomaly.Classification.CanonicalCoroot.canonical_coroot_null_iff_of_connected',
        'CubicAnomaly.Classification.CanonicalHalf.canonicalPositiveHalfEquiv_intertwines',
        'CubicAnomaly.Classification.CanonicalHalf.positiveHermitianEquiv_intertwines',
        'CubicAnomaly.Classification.CanonicalHalf.positiveHermitianEquiv_on_real_half',
        'CubicAnomaly.Classification.CartanCoroot.actual_coroot_ne_zero',
        'CubicAnomaly.Classification.CartanCoroot.coroot_cubic_zero_iff_of_connected',
        'CubicAnomaly.Classification.CartanCoroot.coroot_mem_ideal_iff_of_connected',
        'CubicAnomaly.Classification.CartanCoroot.coroot_mem_ideal_iff_of_pairing_ne_zero',
        'CubicAnomaly.Classification.CartanCoroot.coroot_mem_ideal_of_cartan_eval_ne_zero',
        'CubicAnomaly.Classification.CartanCoroot.exists_root_eval_ne_zero',
        'CubicAnomaly.Classification.CartanCoroot.ideal_eq_lieSpan_coroots',
        'CubicAnomaly.Classification.CartanCoroot.ideal_le_iff_coroot',
        'CubicAnomaly.Classification.CartanCoroot.ideal_ne_bot_iff_exists_coroot',
        'CubicAnomaly.Classification.CartanCoroot.radical_eq_lieSpan_null_coroots',
        'CubicAnomaly.Classification.CartanCoroot.radical_ne_bot_iff_coroot',
        'CubicAnomaly.Classification.CartanCoroot.radical_ne_bot_iff_coroot_basis',
        'CubicAnomaly.Classification.CartanCubic.cartan_cubic_matrix_mulVec',
        'CubicAnomaly.Classification.CartanCubic.cartan_mem_radical_iff',
        'CubicAnomaly.Classification.CartanCubic.cartan_mem_radical_iff_basis',
        'CubicAnomaly.Classification.CartanCubic.ideal_le_of_cartan_intersection_le',
        'CubicAnomaly.Classification.CartanCubic.ideal_le_radical_iff_cartan',
        'CubicAnomaly.Classification.CartanCubic.invariant_cubic_eq_zero_of_cartan',
        'CubicAnomaly.Classification.CartanCubic.radical_ne_bot_iff_cartan',
        'CubicAnomaly.Classification.CartanCubic.radical_ne_bot_iff_cartan_basis',
        'CubicAnomaly.Classification.CartanCubic.radical_ne_bot_iff_cartan_matrix_kernel',
        'CubicAnomaly.Classification.CartanTrace.complex_trace_cubic_invariant',
        'CubicAnomaly.Classification.CartanTrace.complex_trace_cubic_symmetric',
        'CubicAnomaly.Classification.CartanTrace.complex_trace_radical_ideal_iff_cartan',
        'CubicAnomaly.Classification.CartanTrace.complex_trace_radical_ne_bot_iff_matrix_kernel',
        'CubicAnomaly.Classification.CartanTrace.matrix_trace_cubic_swap_first',
        'CubicAnomaly.Classification.CartanTrace.matrix_trace_cubic_swap_last',
        'CubicAnomaly.Classification.Classical.classical_lattice_order_three_rank_drop',
        'CubicAnomaly.Classification.Classical.classical_order_three_rank_drop',
        'CubicAnomaly.Classification.Classical.classical_order_three_span_drop',
        'CubicAnomaly.Classification.Classical.classical_root_ternary_bounds',
        'CubicAnomaly.Classification.Classical.classical_zero_grade_lift_zero',
        'CubicAnomaly.Classification.Classical.classical_zero_grade_span_le_ker',
        'CubicAnomaly.Classification.Classical.cubic_coordinate_shift',
        'CubicAnomaly.Classification.Classical.e6_dual_support_arithmetic_gaps',
        'CubicAnomaly.Classification.Classical.lattice_order_three_coordinate_extension',
        'CubicAnomaly.Classification.Classical.oddD_binomial_candidate_not_exhausted',
        'CubicAnomaly.Classification.Classical.oddD_binomial_dimension_lower_bound',
        'CubicAnomaly.Classification.Classical.oddD_dimension_gap_one',
        'CubicAnomaly.Classification.Classical.oddD_dimension_gap_two',
        'CubicAnomaly.Classification.Classical.oddD_exterior_square_not_exhausted_one',
        'CubicAnomaly.Classification.Classical.oddD_exterior_square_not_exhausted_two',
        'CubicAnomaly.Classification.Classical.oddD_ratio_one_lt_two_thirds',
        'CubicAnomaly.Classification.Classical.oddD_ratio_two_lt_one_sixth',
        'CubicAnomaly.Classification.Classical.root_lattice_order_three_coordinate_extension',
        'CubicAnomaly.Classification.Classical.sum_zero_lattice_coordinate_extension',
        'CubicAnomaly.Classification.Classical.typeA_dual_support_cubic',
        'CubicAnomaly.Classification.Classical.typeA_dual_support_cubic_ne_zero',
        'CubicAnomaly.Classification.Classical.typeA_order_three_rank_drop',
        'CubicAnomaly.Classification.Classical.typeA_root_lattice_contains_difference',
        'CubicAnomaly.Classification.Classical.typeA_root_lattice_sum_zero',
        'CubicAnomaly.Classification.Classical.typeA_support_cubic_formula',
        'CubicAnomaly.Classification.Classical.typeA_support_cubic_nonzero',
        'CubicAnomaly.Classification.Classical.typeB_order_three_rank_drop',
        'CubicAnomaly.Classification.Classical.typeB_root_lattice_contains_doubled',
        'CubicAnomaly.Classification.Classical.typeC_order_three_rank_drop',
        'CubicAnomaly.Classification.Classical.typeC_root_lattice_contains_doubled',
        'CubicAnomaly.Classification.Classical.typeD_order_three_rank_drop',
        'CubicAnomaly.Classification.Classical.typeD_root_lattice_contains_doubled',
        'CubicAnomaly.Classification.Classical.typeD_weyl_dimension_one_lower_bound',
        'CubicAnomaly.Classification.Classical.typeD_weyl_dimension_two_lower_bound',
        'CubicAnomaly.Classification.Classical.typeD_weyl_exterior_gap_one',
        'CubicAnomaly.Classification.Classical.typeD_weyl_exterior_gap_two',
        'CubicAnomaly.Classification.Classical.typeD_weyl_ratio_one',
        'CubicAnomaly.Classification.Classical.typeD_weyl_ratio_two',
        'CubicAnomaly.Classification.CommonCartan.cartan_submodule_eq_root_decomposition',
        'CubicAnomaly.Classification.CommonCartan.contained_roots_add',
        'CubicAnomaly.Classification.CommonCartan.contained_roots_neg',
        'CubicAnomaly.Classification.CommonCartan.invariant_form_root_pair_zero',
        'CubicAnomaly.Classification.CommonCartan.root_space_le_of_nonzero_mem',
        'CubicAnomaly.Classification.CommonCartan.subalgebra_eq_quotient_zero_grade',
        'CubicAnomaly.Classification.CommonCartan.subalgebra_eq_root_decomposition',
        'CubicAnomaly.Classification.CompactCartan.abelianRank_le_of_injective',
        'CubicAnomaly.Classification.CompactCartan.abelianRank_subalgebra_le',
        'CubicAnomaly.Classification.CompactCartan.compact_abelian_normalizer_bracket_zero',
        'CubicAnomaly.Classification.CompactCartan.compact_equal_abelianRank_exists_complex_cartan',
        'CubicAnomaly.Classification.CompactCartan.compact_equal_abelianRank_exists_real_cartan',
        'CubicAnomaly.Classification.CompactCartan.compact_maximum_abelian_isCartan',
        'CubicAnomaly.Classification.CompactCartan.complexified_abelian_cartan',
        'CubicAnomaly.Classification.CompactCartan.complexified_abelian_subalgebra',
        'CubicAnomaly.Classification.CompactCartan.complexified_subalgebra_mono',
        'CubicAnomaly.Classification.CompactCartan.exists_abelian_finrank_eq_abelianRank',
        'CubicAnomaly.Classification.CompactCartan.finrank_le_abelianRank',
        'CubicAnomaly.Classification.CompactGeometry.compact_complexified_subalgebra_form_nondegenerate',
        'CubicAnomaly.Classification.CompactGeometry.compact_complexified_subspace_form_nondegenerate',
        'CubicAnomaly.Classification.CompactGeometry.complexifiedLieHom_inclusion_action',
        'CubicAnomaly.Classification.CompactGeometry.complexifiedSubalgebra_toSubmodule',
        'CubicAnomaly.Classification.CompactGeometry.complexified_bilinForm_restrict_equiv',
        'CubicAnomaly.Classification.CompactGeometry.complexified_bilinForm_subspace_nondegenerate',
        'CubicAnomaly.Classification.CompactGeometry.imageActionSubmodule_irreducible',
        'CubicAnomaly.Classification.CompactGeometry.imageActionSubmodule_lie',
        'CubicAnomaly.Classification.CompactGeometry.imageActionSubmodule_toSubmodule',
        'CubicAnomaly.Classification.CompactGeometry.subalgebraComplexificationEquiv_tmul',
        'CubicAnomaly.Classification.CompactKilling.compact_centerless_isKilling',
        'CubicAnomaly.Classification.CompactKilling.compact_killing_complement_top_eq_center',
        'CubicAnomaly.Classification.CompactKilling.compact_killing_self_zero_iff_center',
        'CubicAnomaly.Classification.CompactKilling.compact_skew_trace_square_zero_iff',
        'CubicAnomaly.Classification.CompactSimple.ambient_simple_of_compact_complex_complement',
        'CubicAnomaly.Classification.CompactSimple.compact_pair_ambient_simple',
        'CubicAnomaly.Classification.ComplexDuality.compact_complement_complex_type_decomposition',
        'CubicAnomaly.Classification.ComplexDuality.complex_halves_not_equivalent',
        'CubicAnomaly.Classification.ComplexDuality.complexified_bilinForm_nondegenerate',
        'CubicAnomaly.Classification.ComplexDuality.complexified_invariantForm_invariant',
        'CubicAnomaly.Classification.ComplexDuality.invariant_complex_eigenspaces_dual',
        'CubicAnomaly.Classification.ComplexDuality.opposite_complex_half_intertwiner_eq_zero',
        'CubicAnomaly.Classification.ComplexDuality.positive_invariant_complex_halves_dual',
        'CubicAnomaly.Classification.Complexification.ambient_complex_halves_disjoint',
        'CubicAnomaly.Classification.Complexification.ambient_complex_halves_irreducible',
        'CubicAnomaly.Classification.Complexification.ambient_complex_halves_sup',
        'CubicAnomaly.Classification.Complexification.compact_complexification_isKilling',
        'CubicAnomaly.Classification.Complexification.compact_pair_complexification_isCompl',
        'CubicAnomaly.Classification.Complexification.complex_irreducible_of_real_equivariant_bijection',
        'CubicAnomaly.Classification.Complexification.complex_structure_eigenspaces_isCompl',
        'CubicAnomaly.Classification.Complexification.complexification_bracket_inclusion_reflects',
        'CubicAnomaly.Classification.Complexification.complexification_imagPart_natural',
        'CubicAnomaly.Classification.Complexification.complexification_isKilling',
        'CubicAnomaly.Classification.Complexification.complexification_killing_eq_baseChange',
        'CubicAnomaly.Classification.Complexification.complexification_killing_tmul',
        'CubicAnomaly.Classification.Complexification.complexification_linearMap_injective',
        'CubicAnomaly.Classification.Complexification.complexification_mem_baseChange_iff_parts',
        'CubicAnomaly.Classification.Complexification.complexification_negative_half_irreducible',
        'CubicAnomaly.Classification.Complexification.complexification_positive_half_irreducible',
        'CubicAnomaly.Classification.Complexification.complexification_realPart_natural',
        'CubicAnomaly.Classification.Complexification.complexification_real_imag_decomposition',
        'CubicAnomaly.Classification.Complexification.complexification_real_mem_baseChange_iff',
        'CubicAnomaly.Classification.Complexification.complexification_submodule_finrank',
        'CubicAnomaly.Classification.Complexification.complexification_submodules_isCompl',
        'CubicAnomaly.Classification.Complexification.complexification_zero_iff_parts',
        'CubicAnomaly.Classification.Complexification.complexifiedEnd_square',
        'CubicAnomaly.Classification.Complexification.complexified_complex_structure_isCompl',
        'CubicAnomaly.Classification.Complexification.complexified_inclusion_range',
        'CubicAnomaly.Classification.Complexification.lieSubmoduleComplexificationEquiv_tmul',
        'CubicAnomaly.Classification.Complexification.negativeHalfRealEquiv_apply',
        'CubicAnomaly.Classification.Complexification.negativeHalfRealEquiv_map_complexStructure',
        'CubicAnomaly.Classification.Complexification.negativeHalfRealEquiv_map_lie',
        'CubicAnomaly.Classification.Complexification.negativeHalfRealEquiv_symm_apply',
        'CubicAnomaly.Classification.Complexification.positiveHalfRealEquiv_apply',
        'CubicAnomaly.Classification.Complexification.positiveHalfRealEquiv_map_complexStructure',
        'CubicAnomaly.Classification.Complexification.positiveHalfRealEquiv_map_lie',
        'CubicAnomaly.Classification.Complexification.positiveHalfRealEquiv_symm_apply',
        'CubicAnomaly.Classification.Complexification.submoduleComplexificationEquiv_tmul',
        'CubicAnomaly.Classification.CorootComponents.corootIdeal_eq_of_connected',
        'CubicAnomaly.Classification.CorootComponents.corootIdeal_isAtom',
        'CubicAnomaly.Classification.CorootComponents.corootIdeal_isSimple',
        'CubicAnomaly.Classification.CorootComponents.coroot_mem_ideal_or_compl',
        'CubicAnomaly.Classification.CorootComponents.ideal_eq_iSup_corootIdeals',
        'CubicAnomaly.Classification.CorootComponents.radical_eq_iSup_null_corootIdeals',
        'CubicAnomaly.Classification.CubicRadical.center_eq_bot_of_irreducible_hermitian_realization',
        'CubicAnomaly.Classification.CubicRadical.center_eq_bot_of_scalar_center_and_nonzero_cubic_radical',
        'CubicAnomaly.Classification.CubicRadical.central_generator_scalar_of_irreducible',
        'CubicAnomaly.Classification.CubicRadical.equivariant_scalar_of_real_eigenvector',
        'CubicAnomaly.Classification.CubicRadical.generator_radical_eq_bot_of_scalar',
        'CubicAnomaly.Classification.CubicRadical.hermitian_scalar_of_irreducible_realization',
        'CubicAnomaly.Classification.CubicRadical.hermitian_trace_square_eq_zero_iff',
        'CubicAnomaly.Classification.CubicRadical.matrix_cubic_radical_trivial_of_scalar',
        'CubicAnomaly.Classification.CubicRadical.matrix_trace_cubic_invariant',
        'CubicAnomaly.Classification.CubicRadical.matrix_trace_cubic_scalar',
        'CubicAnomaly.Classification.CubicRadical.mem_radical_iff',
        'CubicAnomaly.Classification.CubicRadical.no_nonzero_scalar_of_nonzero_matrix_cubic_radical',
        'CubicAnomaly.Classification.CubicRadical.radical_eq_bot_iff',
        'CubicAnomaly.Classification.CubicRadical.scaled_commutator_of_action',
        'CubicAnomaly.Classification.CubicRadical.trace_cubic_form_invariant',
        'CubicAnomaly.Classification.CubicRadical.trace_cubic_form_invariant_of_scaled_commutator',
        'CubicAnomaly.Classification.CyclicBracket.centralizer_vanishes_of_complex_complement',
        'CubicAnomaly.Classification.CyclicBracket.compact_complex_complement_nonsymmetric',
        'CubicAnomaly.Classification.CyclicBracket.complex_commutant_structure_skew',
        'CubicAnomaly.Classification.CyclicBracket.killing_symmetric_complex_complement_center_ne_bot',
        'CubicAnomaly.Classification.CyclicBracket.symmetric_complex_complement_cubic_radical_eq_bot',
        'CubicAnomaly.Classification.EqualRank.common_cartan_cyclic_grading',
        'CubicAnomaly.Classification.EqualRank.common_cartan_three_class_decomposition',
        'CubicAnomaly.Classification.EqualRank.compact_common_cartan_cyclic_grading',
        'CubicAnomaly.Classification.EqualRank.degree_eq_of_nonzero_root_mem_grade',
        'CubicAnomaly.Classification.EqualRank.dual_homogeneous_degrees_opposite',
        'CubicAnomaly.Classification.EqualRank.exists_nonzero_root_vector',
        'CubicAnomaly.Classification.EqualRank.irreducible_submodule_homogeneous',
        'CubicAnomaly.Classification.EqualRank.irreducible_submodule_le_grade_of_nonzero_mem',
        'CubicAnomaly.Classification.EqualRank.off_zero_grades_eq_complement',
        'CubicAnomaly.Classification.EqualRank.three_class_support_of_homogeneous_span',
        'CubicAnomaly.Classification.HermitianRealization.all_rank_structural_reduction_of_commutant',
        'CubicAnomaly.Classification.HermitianRealization.hermitian_half_coordinates_complexStructure',
        'CubicAnomaly.Classification.HermitianRealization.hermitian_half_exists_of_commutant',
        'CubicAnomaly.Classification.InvolutionObstruction.all_rank_anomalous_involution_eq_refl',
        'CubicAnomaly.Classification.InvolutionObstruction.compact_complex_type_invariant_complement_nonsymmetric',
        'CubicAnomaly.Classification.InvolutionObstruction.compact_complex_type_involution_eq_refl',
        'CubicAnomaly.Classification.InvolutionObstruction.fixed_subalgebra_eq_of_maximal',
        'CubicAnomaly.Classification.MatrixCubic.matrix_trace_cubic_eq_actual_weight_sum',
        'CubicAnomaly.Classification.MatrixCubic.matrix_trace_cubic_of_intertwining',
        'CubicAnomaly.Classification.OrthogonalDefining.all_rank_orthogonal_defining_complex_irreducible',
        'CubicAnomaly.Classification.OrthogonalDefining.all_rank_orthogonal_defining_irreducible_self_dual',
        'CubicAnomaly.Classification.OrthogonalDefining.all_rank_orthogonal_defining_real_irreducible',
        'CubicAnomaly.Classification.OrthogonalDefining.orthogonal_defining_complex_irreducible',
        'CubicAnomaly.Classification.OrthogonalDefining.orthogonal_defining_complex_self_dual',
        'CubicAnomaly.Classification.OrthogonalDefining.orthogonal_defining_no_complex_structure',
        'CubicAnomaly.Classification.OrthogonalDefining.orthogonal_defining_real_irreducible',
        'CubicAnomaly.Classification.QuadraticRestriction.compact_pair_dimension_equation',
        'CubicAnomaly.Classification.QuadraticRestriction.compact_pair_quadratic_restriction',
        'CubicAnomaly.Classification.QuadraticRestriction.traceForm_complementary_submodules',
        'CubicAnomaly.Classification.QuadraticRestriction.traceForm_contragredient',
        'CubicAnomaly.Classification.QuadraticRestriction.traceForm_equivariant_equiv',
        'CubicAnomaly.Classification.RootBracket.exists_nonzero_root_bracket',
        'CubicAnomaly.Classification.RootBracket.exists_nonzero_root_bracket_of_functions',
        'CubicAnomaly.Classification.RootBracket.lie_ne_zero_of_mem_rootSpace',
        'CubicAnomaly.Classification.RootGrading.compact_pair_cyclic_root_grading',
        'CubicAnomaly.Classification.RootGrading.compact_pair_three_class_order_three',
        'CubicAnomaly.Classification.RootGrading.complement_bracket_mem_zero_of_order_ne_three',
        'CubicAnomaly.Classification.RootGrading.cyclic_root_grading_of_nonsymmetric',
        'CubicAnomaly.Classification.RootGrading.cyclic_root_grading_of_three_class_support',
        'CubicAnomaly.Classification.RootGrading.degree_eq_of_irreducible',
        'CubicAnomaly.Classification.RootGrading.exists_weight_of_mem_weightGrade',
        'CubicAnomaly.Classification.RootGrading.genWeightSpace_le_weightGrade',
        'CubicAnomaly.Classification.RootGrading.iSupIndep_weightGrade',
        'CubicAnomaly.Classification.RootGrading.iSup_weightGrade_eq_top',
        'CubicAnomaly.Classification.RootGrading.irreducible_weights_sub_mem_rootLattice',
        'CubicAnomaly.Classification.RootGrading.lie_mem_orderThreeGrade',
        'CubicAnomaly.Classification.RootGrading.lie_mem_weightGrade',
        'CubicAnomaly.Classification.RootGrading.nonzero_class_of_proper_zero_grade',
        'CubicAnomaly.Classification.RootGrading.orderThreeClass_injective',
        'CubicAnomaly.Classification.RootGrading.orderThreeClass_one',
        'CubicAnomaly.Classification.RootGrading.orderThreeGrade_isInternal',
        'CubicAnomaly.Classification.RootGrading.order_three_of_three_class_support_and_nonsymmetric',
        'CubicAnomaly.Classification.RootGrading.order_three_of_three_class_support_and_nonzero_bracket',
        'CubicAnomaly.Classification.RootGrading.quotient_root_grade_zero_eq',
        'CubicAnomaly.Classification.RootGrading.root_mem_rootLattice',
        'CubicAnomaly.Classification.RootGrading.weightGrade_eq_bot',
        'CubicAnomaly.Classification.RootGrading.weightGrade_isInternal',
        'CubicAnomaly.Classification.RootGrading.weightGrade_zero_eq_top',
        'CubicAnomaly.Classification.RootReduction.bilinear_closed_root_subsystem_saturated',
        'CubicAnomaly.Classification.RootReduction.closed_root_subsystem_saturated',
        'CubicAnomaly.Classification.RootReduction.crystallographic_closed_root_subsystem_saturated',
        'CubicAnomaly.Classification.RootReduction.crystallographic_proper_closed_root_subsystem_lattice_ne',
        'CubicAnomaly.Classification.RootReduction.proper_closed_root_subsystem_lattice_ne',
        'CubicAnomaly.Classification.RootReduction.three_class_noninvolutive_nsmul',
        'CubicAnomaly.Classification.RootReduction.three_class_noninvolutive_order',
        'CubicAnomaly.Classification.RootSaturation.characteristic_zero_closed_root_subsystem_saturated',
        'CubicAnomaly.Classification.RootSaturation.characteristic_zero_proper_closed_root_subsystem_lattice_ne',
        'CubicAnomaly.Classification.RootSaturation.crystallographic_closed_root_subsystem_saturated_of_injective',
        'CubicAnomaly.Classification.RootSaturation.integer_pairing_sum_eq_two',
        'CubicAnomaly.Classification.RootSaturation.lie_rootSystem_closed_subsystem_saturated',
        'CubicAnomaly.Classification.RootSaturation.lie_rootSystem_proper_closed_subsystem_lattice_ne',
        'CubicAnomaly.Classification.RootSaturation.lie_weight_closed_subsystem_saturated',
        'CubicAnomaly.Classification.RootSaturation.lie_weight_proper_closed_subsystem_lattice_ne',
        'CubicAnomaly.Classification.RootSaturation.lie_weight_root_range',
        'CubicAnomaly.Classification.RootSaturation.root_sum_has_positive_pairing',
        'CubicAnomaly.Classification.RootSimple.cartan_intersection_invariant_coreflection',
        'CubicAnomaly.Classification.RootSimple.isSimple_iff_irreducible_rootSystem',
        'CubicAnomaly.Classification.RootSimple.isSimple_of_irreducible_rootSystem',
        'CubicAnomaly.Classification.SelfDualAbsorption.compact_complement_self_dual_irreducible_hom_eq_zero',
        'CubicAnomaly.Classification.SelfDualAbsorption.compact_complement_self_dual_submodule_eq_bot_or_top',
        'CubicAnomaly.Classification.SelfDualAbsorption.compact_nondegenerate_irreducible_ambient_range_le',
        'CubicAnomaly.Classification.SelfDualAbsorption.compact_self_dual_irreducible_ambient_range_le',
        'CubicAnomaly.Classification.SelfDualAbsorption.inequivalent_dual_pair_not_self_dual',
        'CubicAnomaly.Classification.SelfDualAbsorption.inequivalent_irreducible_pair_submodules',
        'CubicAnomaly.Classification.SelfDualAbsorption.invariant_nondegenerate_form_self_dual',
        'CubicAnomaly.Classification.SelfDualAbsorption.self_dual_irreducible_hom_eq_zero',
        'CubicAnomaly.Classification.SelfDualAbsorption.self_dual_irreducible_pair_hom_eq_zero',
        'CubicAnomaly.Classification.SelfDualAbsorption.self_dual_submodule_eq_bot_or_top',
        'CubicAnomaly.Classification.Structural.ambient_center_eq_bot_of_complex_complement',
        'CubicAnomaly.Classification.Structural.commutant_complex_structure_square',
        'CubicAnomaly.Classification.Structural.compact_abelian_ideal_le_center',
        'CubicAnomaly.Classification.Structural.compact_complex_centroid_abelian',
        'CubicAnomaly.Classification.Structural.compact_complex_commutant_irreducible',
        'CubicAnomaly.Classification.Structural.compact_orthogonal_complement_isCompl',
        'CubicAnomaly.Classification.Structural.compact_pair_reduction_to_semisimple_ambient',
        'CubicAnomaly.Classification.Structural.compact_semisimple_of_center_eq_bot',
        'CubicAnomaly.Classification.Structural.effective_invariant_complement_faithful',
        'CubicAnomaly.Classification.Structural.intermediate_eq_of_irreducible_complement',
        'CubicAnomaly.Classification.Structural.invariant_complement_projection_equivariant',
        'CubicAnomaly.Classification.Structural.irreducible_of_complex_commutant',
        'CubicAnomaly.Classification.Structural.maximal_of_irreducible_complement',
        'CubicAnomaly.Classification.Structural.no_fixed_vector_of_irreducible_complex_structure',
        'CubicAnomaly.Classification.Structural.quotient_complement_equiv_apply_mk',
        'CubicAnomaly.Classification.ToralCharacter.card_root_lattice_characters',
        'CubicAnomaly.Classification.ToralCharacter.character_of_basis_values_apply',
        'CubicAnomaly.Classification.ToralCharacter.compact_common_cartan_root_character',
        'CubicAnomaly.Classification.ToralCharacter.root_character_basis_formula',
        'CubicAnomaly.Classification.ToralCharacter.root_character_eq_of_basis_values',
        'CubicAnomaly.Classification.ToralCharacter.root_character_grade_eq',
        'CubicAnomaly.Classification.ToralCharacter.root_character_ne_zero_iff_basis_value',
        'CubicAnomaly.Classification.ToralCharacter.root_lattice_character_eq_iff',
        'CubicAnomaly.Classification.ToralCharacter.root_lattice_character_evaluation',
        'CubicAnomaly.Classification.ToralCharacter.root_lattice_character_ne_zero',
        'CubicAnomaly.Classification.ToralCharacter.root_lattice_degree_mem_cyclic_range',
        'CubicAnomaly.Classification.WeightCubic.symmetrized_trace_cubic_eq_sum_weights',
        'CubicAnomaly.Classification.WeightCubic.trace_cubic_eq_sum_weights',
        'CubicAnomaly.Classification.WeightCubic.trace_power_eq_sum_weights',
        'CubicAnomaly.Classification.WeightCubic.trace_prod_eq_sum_weights',
        'CubicAnomaly.Classification.WeightCubic.trace_prod_toEnd_genWeightSpace',
    }
)

EXPORTED_THEOREMS = NATIVE_THEOREMS | KERNEL_THEOREMS
EXPORTED_THEOREM_BASENAMES = frozenset(
    qualified.rsplit(".", 1)[-1] for qualified in EXPORTED_THEOREMS
)
AXIOM_TARGET = re.compile(
    r"(?m)^\s*#print\s+axioms\s+([A-Za-z0-9_.']+)\s*$"
)
AXIOM_RECEIPT = re.compile(
    r"'(?P<target>[A-Za-z0-9_.']+)'\s+(?:"
    r"depends on axioms:\s*\[(?P<axioms>[^\]]*)\]|"
    r"does not depend on any axioms)",
    re.DOTALL,
)


def strip_comments_and_strings(source: str) -> str:
    result: list[str] = []
    index = 0
    depth = 0
    in_string = False
    while index < len(source):
        pair = source[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                result.append("\n" if source[index] == "\n" else " ")
                index += 1
            continue
        if in_string:
            if source[index] == "\\" and index + 1 < len(source):
                result.extend("  ")
                index += 2
            elif source[index] == '"':
                in_string = False
                result.append(" ")
                index += 1
            else:
                result.append("\n" if source[index] == "\n" else " ")
                index += 1
            continue
        if pair == "/-":
            depth = 1
            result.extend("  ")
            index += 2
        elif pair == "--":
            newline = source.find("\n", index)
            if newline == -1:
                result.extend(" " * (len(source) - index))
                break
            result.extend(" " * (newline - index))
            index = newline
        elif source[index] == '"':
            in_string = True
            result.append(" ")
            index += 1
        else:
            result.append(source[index])
            index += 1
    return "".join(result)


def duplicates(values: list[str]) -> list[str]:
    return sorted(name for name in set(values) if values.count(name) > 1)


def source_theorem_names(cleaned_source: str) -> list[str]:
    """Read all declarations regardless of line layout; reject unsupported names.

    Basenames must remain unique across the project. Lean's named receipts
    independently verify the fully qualified targets in the explicit manifest.
    Comments and strings must have been stripped before calling this function.
    """
    declarations = list(PUBLIC_THEOREM.finditer(cleaned_source))
    if len(declarations) != len(THEOREM_KEYWORD.findall(cleaned_source)):
        raise ValueError("Unrecognized theorem/lemma declaration syntax")
    names: list[str] = []
    for match in declarations:
        name = match.group("name")
        if not SUPPORTED_THEOREM_NAME.fullmatch(name):
            raise ValueError(f"Unsupported theorem identifier for the export audit: {name!r}")
        if "private" not in match.group("modifiers").split():
            names.append(name.rsplit(".", 1)[-1])
    return names


def source_scanner_self_tests() -> int:
    positives = {
        "theorem ordinary : True := by trivial": ["ordinary"],
        "public theorem explicit_public : True := by trivial": ["explicit_public"],
        "omit [Nontrivial M] in theorem same_line : True := by trivial": ["same_line"],
        "@[simp] protected theorem qualified.name : True := by trivial": ["name"],
        "private theorem hidden : True := by trivial": [],
        "private\nlemma hidden : True := by trivial": [],
        "/- public theorem ignored : False -/ theorem real : True := by trivial": ["real"],
        'def s := "theorem ignored : False"\ntheorem actual : True := by trivial': ["actual"],
    }
    for source, expected in positives.items():
        found = source_theorem_names(strip_comments_and_strings(source))
        if found != expected:
            raise AssertionError(f"Incorrect theorem scan: {source!r}: {found}")
    for source in ("theorem α : True := by trivial", "theorem «has space» : True := by trivial",
                   "theorem : True := by trivial"):
        try:
            source_theorem_names(strip_comments_and_strings(source))
        except ValueError:
            continue
        raise AssertionError(f"Scanner silently accepted unsupported syntax: {source!r}")
    print("PASS  export scanner handles modifiers, qualified names and inline declarations")
    return 0


def axiom_manifest_failures(
    theorem_names: list[str], audit_source: str
) -> list[str]:
    failures: list[str] = []

    duplicate_theorems = duplicates(theorem_names)
    if duplicate_theorems:
        failures.append(
            "Exported theorem basenames must be unique for an unambiguous "
            f"axiom manifest: {duplicate_theorems}"
        )

    discovered_basenames = set(theorem_names)
    if discovered_basenames != EXPORTED_THEOREM_BASENAMES:
        failures.append(
            "Discovered public theorem basenames differ from the explicit "
            "exported surface: "
            f"missing={sorted(EXPORTED_THEOREM_BASENAMES - discovered_basenames)}, "
            f"unknown={sorted(discovered_basenames - EXPORTED_THEOREM_BASENAMES)}"
        )

    cleaned_audit = strip_comments_and_strings(audit_source)
    audited_targets = AXIOM_TARGET.findall(cleaned_audit)
    duplicate_targets = duplicates(audited_targets)
    if duplicate_targets:
        failures.append(
            f"Axiom audit contains duplicate fully qualified targets: {duplicate_targets}"
        )

    audited_target_set = set(audited_targets)
    if audited_target_set != EXPORTED_THEOREMS:
        failures.append(
            "Axiom audit targets differ from the explicit fully qualified "
            "exported surface: "
            f"missing={sorted(EXPORTED_THEOREMS - audited_target_set)}, "
            f"unknown={sorted(audited_target_set - EXPORTED_THEOREMS)}"
        )

    return failures


def manifest_self_tests() -> int:
    """Exercise every export, including selector claims, without running Lean."""
    targets = sorted(EXPORTED_THEOREMS)
    names = sorted(EXPORTED_THEOREM_BASENAMES)
    audit_lines = [f"#print axioms {target}" for target in targets]
    audit = "\n".join(audit_lines)
    if axiom_manifest_failures(names, audit):
        raise AssertionError("The complete exported surface must pass")

    negative_cases = 0

    def rejected(label: str, candidate_names: list[str], candidate_audit: str) -> None:
        nonlocal negative_cases
        if not axiom_manifest_failures(candidate_names, candidate_audit):
            raise AssertionError(f"Manifest accepted {label}")
        negative_cases += 1

    for target in targets:
        basename = target.rsplit(".", 1)[-1]
        line = f"#print axioms {target}"

        def replace_target(replacement: str) -> str:
            return "\n".join(replacement if entry == line else entry for entry in audit_lines)

        rejected(f"missing theorem {target}", [name for name in names if name != basename], audit)
        rejected(f"missing receipt {target}", names, replace_target(""))
        rejected(f"wrong namespace {target}", names, replace_target(f"#print axioms Wrong.{basename}"))
        rejected(f"commented receipt {target}", names, replace_target(f"/- {line} -/"))

    rejected("unknown public theorem", names + ["unlisted_selector"], audit)
    rejected("duplicate public theorem", names + [names[0]], audit)
    rejected("unknown receipt", names, audit + "\n#print axioms Wrong.unlisted_selector")
    rejected("duplicate receipt", names, audit + f"\n#print axioms {targets[0]}")
    print(f"PASS  explicit axiom manifest: positive control and {negative_cases} negative self-tests")
    return 0


def axiom_receipt_failures(output: str) -> list[str]:
    """Match every receipt to its named theorem and its declared trust class."""
    failures: list[str] = []
    if NATIVE_THEOREMS & KERNEL_THEOREMS:
        failures.append("A theorem cannot belong to both trust classes")
    receipts = list(AXIOM_RECEIPT.finditer(output))
    targets = [match.group("target") for match in receipts]
    repeated = duplicates(targets)
    if repeated:
        failures.append(f"Duplicate axiom receipts: {repeated}")
    found_targets = set(targets)
    if found_targets != EXPORTED_THEOREMS:
        failures.append(
            "Axiom receipt targets differ from the exported surface: "
            f"missing={sorted(EXPORTED_THEOREMS - found_targets)}, "
            f"unknown={sorted(found_targets - EXPORTED_THEOREMS)}"
        )
    for match in receipts:
        target = match.group("target")
        found = {
            name.strip()
            for name in (match.group("axioms") or "").replace("\n", " ").split(",")
            if name.strip()
        }
        if target in NATIVE_THEOREMS and found != NATIVE_AXIOMS:
            failures.append(
                f"{target}: native-computation receipt differs from the exact set: "
                f"missing={sorted(NATIVE_AXIOMS - found)}, "
                f"unexpected={sorted(found - NATIVE_AXIOMS)}"
            )
        elif target in KERNEL_THEOREMS and not found <= KERNEL_AXIOMS:
            failures.append(
                f"{target}: deductive proof has nonfoundational dependencies: "
                f"{sorted(found - KERNEL_AXIOMS)}"
            )
    return failures


def receipt_self_tests() -> int:
    """Reject missing, mislabeled, duplicate, and over-trusting proof receipts."""
    native = sorted(NATIVE_THEOREMS)
    kernel = sorted(KERNEL_THEOREMS)

    def receipt(target: str, axioms: set[str]) -> str:
        if not axioms:
            return f"'{target}' does not depend on any axioms"
        return f"'{target}' depends on axioms: [{', '.join(sorted(axioms))}]"

    lines = {
        target: receipt(target, NATIVE_AXIOMS if target in NATIVE_THEOREMS else KERNEL_AXIOMS)
        for target in sorted(EXPORTED_THEOREMS)
    }

    def check(label: str, candidate: list[str], expected_failure: bool) -> None:
        failed = bool(axiom_receipt_failures("\n".join(candidate)))
        if failed != expected_failure:
            raise AssertionError(f"Unexpected receipt-audit result for {label}")

    check("complete receipts", list(lines.values()), False)
    check("reordered receipts", list(reversed(list(lines.values()))), False)
    for target in lines:
        check(f"missing {target}", [line for name, line in lines.items() if name != target], True)
    first = next(iter(lines))
    check("duplicate", [*lines.values(), lines[first]], True)
    check("unknown", [*lines.values(), receipt("Wrong.unknown", set())], True)
    changed = dict(lines)
    changed[first] = receipt("Wrong." + first, KERNEL_AXIOMS)
    check("mislabeled", list(changed.values()), True)
    if native:
        changed = dict(lines)
        changed[native[0]] = receipt(native[0], NATIVE_AXIOMS - {"Lean.trustCompiler"})
        check("missing native compiler dependency", list(changed.values()), True)
    if kernel:
        for target in kernel:
            changed = dict(lines)
            changed[target] = receipt(target, set())
            check(f"axiom-free {target}", list(changed.values()), False)
            changed[target] = receipt(target, KERNEL_AXIOMS | {"Lean.trustCompiler"})
            check(f"compiler dependency in {target}", list(changed.values()), True)
            changed[target] = receipt(target, KERNEL_AXIOMS | {"sorryAx"})
            check(f"unfinished proof in {target}", list(changed.values()), True)
    print("PASS  named axiom receipts and separate native/deductive trust classes")
    return 0


def self_tests() -> int:
    source_scanner_self_tests()
    manifest_self_tests()
    return receipt_self_tests()


def main() -> int:
    self_tests()
    failures: list[str] = []
    theorem_names: list[str] = []
    for path in LEAN_FILES:
        cleaned = strip_comments_and_strings(path.read_text())
        try:
            theorem_names.extend(source_theorem_names(cleaned))
        except ValueError as error:
            failures.append(f"{path.relative_to(REPO_ROOT)}: {error}")
        match = FORBIDDEN.search(cleaned)
        if match:
            line = cleaned.count("\n", 0, match.start()) + 1
            failures.append(f"{path.relative_to(REPO_ROOT)}:{line}: forbidden proof escape: {match.group(0).strip()}")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1

    failures = axiom_manifest_failures(theorem_names, AXIOM_AUDIT.read_text())
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1

    result = subprocess.run(
        ["lake", "env", "lean", "formal/AxiomAudit.lean"],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if result.returncode != 0:
        print(result.stdout, file=sys.stderr)
        return result.returncode
    failures = axiom_receipt_failures(result.stdout)
    if failures:
        print("\n".join(failures), file=sys.stderr)
        print(result.stdout, file=sys.stderr)
        return 1
    print(f"PASS  no proof escapes; all {len(theorem_names)} exported theorems audited")
    print(f"PASS  {len(NATIVE_THEOREMS)} exact native-computation receipts: "
          + ", ".join(sorted(NATIVE_AXIOMS)))
    print(f"PASS  {len(KERNEL_THEOREMS)} deductive receipts use only: "
          + ", ".join(sorted(KERNEL_AXIOMS)))
    return 0


if __name__ == "__main__":
    raise SystemExit(self_tests() if sys.argv[1:] == ["--self-test"] else main())
