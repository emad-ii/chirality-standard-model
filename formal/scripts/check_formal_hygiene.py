#!/usr/bin/env python3
"""Guard the public Lean surface and audit its admitted axioms."""

from __future__ import annotations

from collections import Counter
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
CERTIFICATE_DERIVED_AXIOMS = NATIVE_AXIOMS | {"Classical.choice"}
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
        'CubicAnomaly.Fixed.E8BracketData.bracket_data_root_list_nodup',
    }
)
KERNEL_THEOREMS = frozenset(
    {
        'CubicAnomaly.Classification.AbsoluteIrreducibility.complexification_irreducible_of_no_complex_structure',
        'CubicAnomaly.Classification.AbsoluteSimplicity.anticomplex_intertwiner_eq_zero',
        'CubicAnomaly.Classification.AbsoluteSimplicity.compact_pair_complexification_simple',
        'CubicAnomaly.Classification.AbsoluteSimplicity.compact_real_simple_is_absolutely_simple',
        'CubicAnomaly.Classification.AdjointTraceForms.adjoint_pair_swap_of_reflexive',
        'CubicAnomaly.Classification.AdjointTraceForms.end_trace_form_apply',
        'CubicAnomaly.Classification.AdjointTraceForms.end_trace_form_invariant',
        'CubicAnomaly.Classification.AdjointTraceForms.end_trace_form_nondegenerate',
        'CubicAnomaly.Classification.AdjointTraceForms.end_trace_form_symmetric',
        'CubicAnomaly.Classification.AdjointTraceForms.form_adjoint_involutive',
        'CubicAnomaly.Classification.AdjointTraceForms.form_adjoint_mul',
        'CubicAnomaly.Classification.AdjointTraceForms.form_adjoint_one',
        'CubicAnomaly.Classification.AdjointTraceForms.form_adjoint_pair',
        'CubicAnomaly.Classification.AdjointTraceForms.mem_selfAdjoint_iff_form_adjoint',
        'CubicAnomaly.Classification.AdjointTraceForms.mem_traceZeroSelfAdjointSubmodule',
        'CubicAnomaly.Classification.AdjointTraceForms.reflexive_form_symmetric_or_alternating',
        'CubicAnomaly.Classification.AdjointTraceForms.self_adjoint_module_trace_form_invariant',
        'CubicAnomaly.Classification.AdjointTraceForms.self_adjoint_module_trace_form_nondegenerate',
        'CubicAnomaly.Classification.AdjointTraceForms.self_adjoint_self_dual',
        'CubicAnomaly.Classification.AdjointTraceForms.self_adjoint_trace_form_nondegenerate',
        'CubicAnomaly.Classification.AdjointTraceForms.trace_form_adjoint',
        'CubicAnomaly.Classification.AdjointTraceForms.trace_form_adjoint_transfer',
        'CubicAnomaly.Classification.AdjointTraceForms.trace_zero_self_adjoint_module_trace_form_invariant',
        'CubicAnomaly.Classification.AdjointTraceForms.trace_zero_self_adjoint_module_trace_form_nondegenerate',
        'CubicAnomaly.Classification.AdjointTraceForms.trace_zero_self_adjoint_self_dual',
        'CubicAnomaly.Classification.AdjointTraceForms.trace_zero_self_adjoint_trace_form_nondegenerate',
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
        'CubicAnomaly.Classification.CanonicalRootCubic.canonical_matrix_cubic_eq_actual_root_sum',
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
        'CubicAnomaly.Classification.ClassicalIsotropyFactors.all_rank_orthogonal_isotropy_simple_or_two_atoms',
        'CubicAnomaly.Classification.ClassicalIsotropyFactors.all_rank_orthogonal_no_three_isotropy_atoms',
        'CubicAnomaly.Classification.ClassicalIsotropyFactors.all_rank_symplectic_isotropy_simple_or_two_atoms',
        'CubicAnomaly.Classification.ClassicalIsotropyFactors.all_rank_symplectic_no_three_isotropy_atoms',
        'CubicAnomaly.Classification.ClassicalModuleBridge.lift_orthogonal_equivariant_operator',
        'CubicAnomaly.Classification.ClassicalModuleBridge.lift_orthogonal_range_le_action_range',
        'CubicAnomaly.Classification.ClassicalModuleBridge.lift_symplectic_equivariant_operator',
        'CubicAnomaly.Classification.ClassicalModuleBridge.lift_symplectic_range_le_action_range',
        'CubicAnomaly.Classification.ClassicalModuleBridge.orthogonal_ambient_operator_map_apply',
        'CubicAnomaly.Classification.ClassicalModuleBridge.orthogonal_ambient_operator_map_inclusion',
        'CubicAnomaly.Classification.ClassicalModuleBridge.orthogonal_ambient_operator_map_injective',
        'CubicAnomaly.Classification.ClassicalModuleBridge.orthogonal_complexified_defining_faithful',
        'CubicAnomaly.Classification.ClassicalModuleBridge.orthogonal_complexified_defining_form_invariant',
        'CubicAnomaly.Classification.ClassicalModuleBridge.orthogonal_complexified_inclusion_natural',
        'CubicAnomaly.Classification.ClassicalModuleBridge.symplectic_ambient_operator_map_apply',
        'CubicAnomaly.Classification.ClassicalModuleBridge.symplectic_ambient_operator_map_inclusion',
        'CubicAnomaly.Classification.ClassicalModuleBridge.symplectic_ambient_operator_map_injective',
        'CubicAnomaly.Classification.ClassicalModuleBridge.symplectic_complexified_defining_faithful',
        'CubicAnomaly.Classification.ClassicalModuleBridge.symplectic_complexified_inclusion_natural',
        'CubicAnomaly.Classification.ClassicalSimplicity.all_rank_orthogonal_complexified_isotropy_simple',
        'CubicAnomaly.Classification.ClassicalSimplicity.all_rank_orthogonal_cubic_radical_eq_top',
        'CubicAnomaly.Classification.ClassicalSimplicity.all_rank_orthogonal_cubic_trace_zero',
        'CubicAnomaly.Classification.ClassicalSimplicity.all_rank_orthogonal_isotropy_simple',
        'CubicAnomaly.Classification.ClassicalSimplicity.all_rank_symplectic_complexified_isotropy_simple',
        'CubicAnomaly.Classification.ClassicalSimplicity.all_rank_symplectic_cubic_radical_eq_top',
        'CubicAnomaly.Classification.ClassicalSimplicity.all_rank_symplectic_cubic_trace_zero',
        'CubicAnomaly.Classification.ClassicalSimplicity.all_rank_symplectic_isotropy_simple',
        'CubicAnomaly.Classification.ClassicalTensorPackageExclusion.actual_two_ideal_tensor_forms_impossible',
        'CubicAnomaly.Classification.ClassicalTwoFactorReduction.all_rank_orthogonal_isotropy_simple_or_actual_tensor_forms',
        'CubicAnomaly.Classification.ClassicalTwoFactorReduction.all_rank_symplectic_isotropy_simple_or_actual_tensor_forms',
        'CubicAnomaly.Classification.CommonCartan.cartan_submodule_eq_root_decomposition',
        'CubicAnomaly.Classification.CommonCartan.contained_roots_add',
        'CubicAnomaly.Classification.CommonCartan.contained_roots_neg',
        'CubicAnomaly.Classification.CommonCartan.invariant_form_root_pair_zero',
        'CubicAnomaly.Classification.CommonCartan.root_space_le_of_nonzero_mem',
        'CubicAnomaly.Classification.CommonCartan.subalgebra_eq_quotient_zero_grade',
        'CubicAnomaly.Classification.CommonCartan.subalgebra_eq_root_decomposition',
        'CubicAnomaly.Classification.CommonCartanAnomaly.canonical_anomaly_iff_common_cartan_cubic',
        'CubicAnomaly.Classification.CommonCartanAnomaly.canonical_anomaly_iff_common_cartan_kernel',
        'CubicAnomaly.Classification.CommonCartanAnomaly.common_cartan_cubic_matrix_eq_isotropy_matrix',
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
        'CubicAnomaly.Classification.CompactOperatorModel.Model.lift_injective',
        'CubicAnomaly.Classification.CompactOperatorModel.Model.lift_operator',
        'CubicAnomaly.Classification.CompactOperatorModel.Model.mem_isotropy_iff',
        'CubicAnomaly.Classification.CompactQuotientSkew.compact_complement_exists_skew_end',
        'CubicAnomaly.Classification.CompactQuotientSkew.compact_equivalent_source_exists_skew_end',
        'CubicAnomaly.Classification.CompactSimple.ambient_simple_of_compact_complex_complement',
        'CubicAnomaly.Classification.CompactSimple.compact_pair_ambient_simple',
        'CubicAnomaly.Classification.CompactTensorExclusion.compact_tensor_right_trace_zero_eq_bot',
        'CubicAnomaly.Classification.CompactTensorExclusion.compact_two_ideal_tensor_impossible',
        'CubicAnomaly.Classification.CompactTensorParity.compact_tensor_blocks_obstruction',
        'CubicAnomaly.Classification.CompactTensorParity.compact_tensor_parity_one_factor_eq_bot',
        'CubicAnomaly.Classification.CompactTensorParity.tensor_ambient_lift_mem_isotropy_iff',
        'CubicAnomaly.Classification.CompactTensorParity.tensor_ambient_lift_operator',
        'CubicAnomaly.Classification.CompactTensorSaturation.left_parity_quotient_map_bijective',
        'CubicAnomaly.Classification.CompactTensorSaturation.left_parity_quotient_map_injective',
        'CubicAnomaly.Classification.CompactTensorSaturation.right_factor_action_full_of_left_parity_nonzero',
        'CubicAnomaly.Classification.ComplexDefining.complexified_defining_action_tmul',
        'CubicAnomaly.Classification.ComplexDefining.complexified_defining_irreducible',
        'CubicAnomaly.Classification.ComplexDefining.complexified_defining_lieModule',
        'CubicAnomaly.Classification.ComplexDefining.complexify_end_map_tmul',
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
        'CubicAnomaly.Classification.ContainedCartan.cartanComapEquiv_inclusion',
        'CubicAnomaly.Classification.ContainedCartan.commonCartanInIsotropy_finrank',
        'CubicAnomaly.Classification.ContainedCartan.commonCartanInIsotropy_isCartan',
        'CubicAnomaly.Classification.ContainedCartan.commonCartanLift_action',
        'CubicAnomaly.Classification.ContainedCartan.commonCartanLift_inclusion',
        'CubicAnomaly.Classification.ContainedCartan.complexified_inclusion_comp_commonCartanLift',
        'CubicAnomaly.Classification.ContainedCartan.isCartanSubalgebra_comap_of_le_range',
        'CubicAnomaly.Classification.CoordinateCubic.actual_root_cubic_eq_coordinate_grade_sum',
        'CubicAnomaly.Classification.CoordinateCubic.actual_root_cubic_matrix_eq_intrinsic_coordinates',
        'CubicAnomaly.Classification.CorootComponents.corootIdeal_eq_of_connected',
        'CubicAnomaly.Classification.CorootComponents.corootIdeal_isAtom',
        'CubicAnomaly.Classification.CorootComponents.corootIdeal_isSimple',
        'CubicAnomaly.Classification.CorootComponents.coroot_mem_ideal_or_compl',
        'CubicAnomaly.Classification.CorootComponents.ideal_eq_iSup_corootIdeals',
        'CubicAnomaly.Classification.CorootComponents.radical_eq_iSup_null_corootIdeals',
        'CubicAnomaly.Classification.CubicIdealDecomposition.coroot_mem_radical_iff_internal_cubic_zero',
        'CubicAnomaly.Classification.CubicIdealDecomposition.cubic_mixed_ideal_compl_eq_zero',
        'CubicAnomaly.Classification.CubicIdealDecomposition.radical_eq_iSup_internal_zero_corootIdeals',
        'CubicAnomaly.Classification.CubicIdealDecomposition.radical_ne_bot_iff_exists_internal_zero_corootIdeal',
        'CubicAnomaly.Classification.CubicIdealDecomposition.semisimple_ideal_perfect',
        'CubicAnomaly.Classification.CubicIdealDecomposition.vanishesOnIdeal_iff_le_radical',
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
        'CubicAnomaly.Classification.DualPairSkew.dual_pair_sign_ne_zero',
        'CubicAnomaly.Classification.DualPairSkew.dual_pair_sign_skew',
        'CubicAnomaly.Classification.DualPairSkew.exists_skew_end_of_equiv',
        'CubicAnomaly.Classification.DualPairSkew.inequivalent_dual_pair_exists_skew_end',
        'CubicAnomaly.Classification.DualPairSkew.invariant_form_eq_zero_of_not_self_dual',
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
        'CubicAnomaly.Classification.EquivariantOperatorTransport.operator_conjugation_action',
        'CubicAnomaly.Classification.EquivariantOperatorTransport.operator_conjugation_apply',
        'CubicAnomaly.Classification.EquivariantOperatorTransport.operator_conjugation_eq_action_iff',
        'CubicAnomaly.Classification.EquivariantOperatorTransport.operator_conjugation_mem_skew_iff',
        'CubicAnomaly.Classification.EquivariantOperatorTransport.operator_conjugation_trace_product',
        'CubicAnomaly.Classification.ExternalTensor.disjoint_ideal_bracket_eq_zero',
        'CubicAnomaly.Classification.ExternalTensor.disjoint_simple_ideal_tensor_irreducible',
        'CubicAnomaly.Classification.ExternalTensor.tensor_product_nontrivial',
        'CubicAnomaly.Classification.ExternalTensor.tensor_submodule_eq_bot_or_top_of_end_stable',
        'CubicAnomaly.Classification.FlipOddObstruction.adjoint_closed_flip_odd_not_line',
        'CubicAnomaly.Classification.FlipOddObstruction.flip_odd_not_line',
        'CubicAnomaly.Classification.FullRankRoots.cartan_centralizes_of_contained_roots_zero',
        'CubicAnomaly.Classification.FullRankRoots.cartan_eq_zero_of_contained_roots_zero',
        'CubicAnomaly.Classification.FullRankRoots.compact_common_cartan_root_forms_finrank_rat',
        'CubicAnomaly.Classification.FullRankRoots.compact_common_cartan_root_forms_span_eq_top',
        'CubicAnomaly.Classification.FullRankRoots.contained_root_forms_finrank',
        'CubicAnomaly.Classification.FullRankRoots.contained_root_forms_finrank_rat',
        'CubicAnomaly.Classification.FullRankRoots.contained_root_forms_span_eq_top',
        'CubicAnomaly.Classification.FullRankRoots.equal_abelianRank_exists_full_span_cartan',
        'CubicAnomaly.Classification.HermitianRealization.all_rank_structural_reduction_of_commutant',
        'CubicAnomaly.Classification.HermitianRealization.hermitian_half_coordinates_complexStructure',
        'CubicAnomaly.Classification.HermitianRealization.hermitian_half_exists_of_commutant',
        'CubicAnomaly.Classification.IdealActionProducts.exists_nonzero_ideal_action_product',
        'CubicAnomaly.Classification.IdealActionProducts.linearMap_eq_zero_of_annihilates_ideal_actions',
        'CubicAnomaly.Classification.IdealActionProducts.nonzero_ideal_action_eq_top',
        'CubicAnomaly.Classification.IdealProductRepresentation.disjoint_ideals_bracket_zero',
        'CubicAnomaly.Classification.IdealProductRepresentation.ideal_product_map_ne_zero',
        'CubicAnomaly.Classification.IdealProductRepresentation.ideal_product_map_tmul',
        'CubicAnomaly.Classification.IdealProductRepresentation.ideal_product_map_trace_zero',
        'CubicAnomaly.Classification.IdealProductRepresentation.ideal_product_range_not_le_action_range',
        'CubicAnomaly.Classification.IdealProductRepresentation.ideal_tensor_to_adjoint_eq_zero',
        'CubicAnomaly.Classification.IdealProductRepresentation.ideal_tensor_to_adjoint_mem_left',
        'CubicAnomaly.Classification.IdealProductRepresentation.ideal_tensor_to_adjoint_mem_right',
        'CubicAnomaly.Classification.IdealProductRepresentation.perfect_disjoint_ideal_trace_zero',
        'CubicAnomaly.Classification.IdealProductRepresentation.semisimple_ideal_product_range_not_le_action_range',
        'CubicAnomaly.Classification.IdealTensorDuality.atomic_ideal_killing_form_nondegenerate',
        'CubicAnomaly.Classification.IdealTensorDuality.atomic_ideal_self_dual',
        'CubicAnomaly.Classification.IdealTensorDuality.atomic_ideal_tensor_self_dual',
        'CubicAnomaly.Classification.IdealTensorDuality.atomic_ideal_triple_self_dual',
        'CubicAnomaly.Classification.IdealTensorDuality.ideal_killing_form_invariant',
        'CubicAnomaly.Classification.IdealTensorExtensions.disjoint_third_ideal_tensor_action_eq_zero',
        'CubicAnomaly.Classification.IdealTensorExtensions.pairwise_disjoint_simple_ideal_triple_irreducible',
        'CubicAnomaly.Classification.IdealTensorExtensions.tensor_simple_ideal_irreducible_of_trivial_action',
        'CubicAnomaly.Classification.IdealTripleProduct.commuting_skew_triple_product',
        'CubicAnomaly.Classification.IdealTripleProduct.disjoint_ideal_actions_commute',
        'CubicAnomaly.Classification.IdealTripleProduct.exists_nonzero_ideal_action_triple_product',
        'CubicAnomaly.Classification.IdealTripleProduct.ideal_triple_product_map_mem_skewAdjointLieSubalgebra',
        'CubicAnomaly.Classification.IdealTripleProduct.ideal_triple_product_map_ne_zero',
        'CubicAnomaly.Classification.IdealTripleProduct.ideal_triple_product_map_outer_tmul',
        'CubicAnomaly.Classification.IdealTripleProduct.ideal_triple_product_map_skew',
        'CubicAnomaly.Classification.IdealTripleProduct.ideal_triple_product_map_tmul',
        'CubicAnomaly.Classification.IdealTripleProduct.ideal_triple_product_range_not_le_action_range',
        'CubicAnomaly.Classification.IdealTripleProduct.ideal_triple_tensor_to_adjoint_eq_zero',
        'CubicAnomaly.Classification.IdealTripleProduct.ideal_triple_tensor_to_adjoint_mem_left',
        'CubicAnomaly.Classification.IdealTripleProduct.ideal_triple_tensor_to_adjoint_mem_middle',
        'CubicAnomaly.Classification.IdealTripleProduct.semisimple_ideal_triple_product_range_not_le_action_range',
        'CubicAnomaly.Classification.IntrinsicAnomaly.canonical_anomaly_iff_intrinsic_rational_kernel',
        'CubicAnomaly.Classification.IntrinsicCartanBasis.intrinsic_root_form_basis_apply',
        'CubicAnomaly.Classification.IntrinsicCartanBasis.intrinsic_root_form_basis_repr_lattice',
        'CubicAnomaly.Classification.IntrinsicCartanBasis.linear_form_apply_intrinsic_cartan_basis',
        'CubicAnomaly.Classification.IntrinsicCartanBasis.root_apply_intrinsic_cartan_basis',
        'CubicAnomaly.Classification.IntrinsicCartanBasis.root_lattice_to_dual_apply',
        'CubicAnomaly.Classification.IntrinsicCartanBasis.root_lattice_to_dual_root',
        'CubicAnomaly.Classification.IntrinsicToral.all_rank_rank_deficient_or_intrinsic_toral_data',
        'CubicAnomaly.Classification.IntrinsicToral.equal_abelianRank_intrinsic_toral_data',
        'CubicAnomaly.Classification.InvolutionObstruction.all_rank_anomalous_involution_eq_refl',
        'CubicAnomaly.Classification.InvolutionObstruction.compact_complex_type_invariant_complement_nonsymmetric',
        'CubicAnomaly.Classification.InvolutionObstruction.compact_complex_type_involution_eq_refl',
        'CubicAnomaly.Classification.InvolutionObstruction.fixed_subalgebra_eq_of_maximal',
        'CubicAnomaly.Classification.KillingDimension.actual_root_count_eq_card',
        'CubicAnomaly.Classification.KillingDimension.killing_dimension_eq_rank_add_twice',
        'CubicAnomaly.Classification.KillingDimension.killing_dimension_parity',
        'CubicAnomaly.Classification.KillingDimension.killing_finrank_eq_cartan_add_roots',
        'CubicAnomaly.Classification.KillingDimension.nonzero_even_killing_dimension_ge_six',
        'CubicAnomaly.Classification.KillingDimension.nonzero_killing_dimension_ge_three',
        'CubicAnomaly.Classification.KillingDimension.root_count_eq_twice_positive',
        'CubicAnomaly.Classification.KillingDimension.three_cartan_finrank_le',
        'CubicAnomaly.Classification.LieDensity.lie_action_adjoin_eq_top',
        'CubicAnomaly.Classification.LieDensity.subalgebra_eq_top_of_lie_action_mem',
        'CubicAnomaly.Classification.MatrixCubic.matrix_trace_cubic_eq_actual_weight_sum',
        'CubicAnomaly.Classification.MatrixCubic.matrix_trace_cubic_of_intertwining',
        'CubicAnomaly.Classification.OrthogonalComplexification.orthogonal_complexification_action_tmul',
        'CubicAnomaly.Classification.OrthogonalComplexification.orthogonal_complexification_equiv_action',
        'CubicAnomaly.Classification.OrthogonalComplexification.orthogonal_complexification_injective',
        'CubicAnomaly.Classification.OrthogonalComplexification.orthogonal_complexification_surjective',
        'CubicAnomaly.Classification.OrthogonalComplexification.orthogonal_matrix_equiv_action',
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
        'CubicAnomaly.Classification.RankOneObstruction.all_rank_even_rank_two_not_rank_deficient',
        'CubicAnomaly.Classification.RankOneObstruction.compact_abelianRank_one_finrank_eq_three',
        'CubicAnomaly.Classification.RankOneObstruction.compact_abelianRank_pos',
        'CubicAnomaly.Classification.RankOneObstruction.rank_one_actual_root_count',
        'CubicAnomaly.Classification.RankOneObstruction.rank_one_killing_finrank_eq_three',
        'CubicAnomaly.Classification.RationalKernel.integer_matrix_complex_kernel_iff_rational',
        'CubicAnomaly.Classification.RationalKernel.nonzero_kernel_map_iff',
        'CubicAnomaly.Classification.RootBracket.exists_nonzero_root_bracket',
        'CubicAnomaly.Classification.RootBracket.exists_nonzero_root_bracket_of_functions',
        'CubicAnomaly.Classification.RootBracket.lie_ne_zero_of_mem_rootSpace',
        'CubicAnomaly.Classification.RootCharacterCoordinates.character_grade_root_count_eq_coordinate_filter',
        'CubicAnomaly.Classification.RootCharacterCoordinates.character_grade_roots_eq_image',
        'CubicAnomaly.Classification.RootCharacterCoordinates.intrinsic_root_coordinates_injective',
        'CubicAnomaly.Classification.RootCharacterCoordinates.root_character_coordinate_formula',
        'CubicAnomaly.Classification.RootCharacterCoordinates.root_coordinates_sub_eq_iff',
        'CubicAnomaly.Classification.RootCharacterCoordinates.root_mem_character_grade_iff',
        'CubicAnomaly.Classification.RootCharacterCoordinates.root_mem_grade_iff_coordinate_dot',
        'CubicAnomaly.Classification.RootCharacterCoordinates.root_space_le_character_grade_iff',
        'CubicAnomaly.Classification.RootCharacterCoordinates.support_adjacency_iff_root_coordinates',
        'CubicAnomaly.Classification.RootCubicKernel.canonical_anomaly_iff_actual_root_cubic',
        'CubicAnomaly.Classification.RootCubicKernel.canonical_anomaly_iff_actual_root_kernel',
        'CubicAnomaly.Classification.RootCubicKernel.common_cartan_matrix_eq_actual_root_matrix',
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
        'CubicAnomaly.Classification.RootGraphCriterion.connected_support_reachable',
        'CubicAnomaly.Classification.RootGraphCriterion.nondegenerate_root_support_connected_iff_irreducible',
        'CubicAnomaly.Classification.RootGraphCriterion.reachable_preserves_root_space_containment',
        'CubicAnomaly.Classification.RootGraphCriterion.root_support_connected_iff_irreducible',
        'CubicAnomaly.Classification.RootLatticeBasis.actual_root_lattice_finrank',
        'CubicAnomaly.Classification.RootLatticeBasis.card_actual_root_lattice_characters',
        'CubicAnomaly.Classification.RootLatticeBasis.intrinsic_root_character_formula',
        'CubicAnomaly.Classification.RootLatticeBasis.intrinsic_root_character_ne_zero_iff',
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
        'CubicAnomaly.Classification.RootSupportDimension.cartan_submodule_eq_supported_root_sum',
        'CubicAnomaly.Classification.RootSupportDimension.compact_common_cartan_root_count_formulas',
        'CubicAnomaly.Classification.RootSupportDimension.containedRoots_finite',
        'CubicAnomaly.Classification.RootSupportDimension.finrank_eq_supported_root_count',
        'CubicAnomaly.Classification.RootSupportDimension.finrank_supported_root_sum',
        'CubicAnomaly.Classification.RootSupportDimension.subalgebra_finrank_eq_cartan_add_root_count',
        'CubicAnomaly.Classification.RootSupportGraph.compact_common_cartan_half_support_connected',
        'CubicAnomaly.Classification.RootSupportGraph.equal_abelianRank_exists_connected_half_support',
        'CubicAnomaly.Classification.RootSupportGraph.irreducible_root_support_connected',
        'CubicAnomaly.Classification.RootSupportGraph.reachable_of_nonzero_root_mem_component',
        'CubicAnomaly.Classification.RootSupportGraph.rootComponent_le',
        'CubicAnomaly.Classification.RootSupportGraph.rootSpace_le_rootComponent',
        'CubicAnomaly.Classification.RootSupportTrace.supported_weight_finrank_eq_one',
        'CubicAnomaly.Classification.RootSupportTrace.symmetrized_trace_cubic_eq_actual_root_sum',
        'CubicAnomaly.Classification.RootSupportTrace.trace_cubic_eq_actual_root_sum',
        'CubicAnomaly.Classification.RootSupportTrace.weight_mem_containedRoots',
        'CubicAnomaly.Classification.ScalarAdjointDensity.action_range_eq_skew_adjoint_of_trace_zero_eq_bot',
        'CubicAnomaly.Classification.ScalarAdjointDensity.action_range_eq_skew_adjoint_of_trace_zero_lie_submodule_eq_bot',
        'CubicAnomaly.Classification.ScalarAdjointDensity.scalar_sup_action_range_eq_top',
        'CubicAnomaly.Classification.ScalarAdjointDensity.self_adjoint_eq_smul_one_of_trace_zero_eq_bot',
        'CubicAnomaly.Classification.ScalarAdjointDensity.skew_anticommutator_self_adjoint',
        'CubicAnomaly.Classification.ScalarModule.scalar_module_irreducible',
        'CubicAnomaly.Classification.ScalarModule.scalar_module_not_adjoint',
        'CubicAnomaly.Classification.ScalarModule.scalar_module_self_dual',
        'CubicAnomaly.Classification.ScalarTraceZeroDensity.action_range_eq_trace_zero_of_trace_zero_lie_submodule_eq_bot',
        'CubicAnomaly.Classification.ScalarTraceZeroDensity.action_range_eq_trace_zero_of_trace_zero_self_adjoint_eq_bot',
        'CubicAnomaly.Classification.ScalarTraceZeroDensity.exists_action_eq_of_scalar_sup_eq_top',
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
        'CubicAnomaly.Classification.SelfDualInvariantForm.exists_invariant_nondegenerate_form_of_self_dual',
        'CubicAnomaly.Classification.SelfDualInvariantForm.self_dual_bilin_form_apply',
        'CubicAnomaly.Classification.SelfDualInvariantForm.self_dual_bilin_form_invariant',
        'CubicAnomaly.Classification.SelfDualInvariantForm.self_dual_bilin_form_nondegenerate',
        'CubicAnomaly.Classification.SelfDualQuotientObstruction.compact_self_dual_block_projection_surjective',
        'CubicAnomaly.Classification.SelfDualQuotientObstruction.compact_two_ambient_blocks_obstruction',
        'CubicAnomaly.Classification.SelfDualQuotientObstruction.complexified_complement_projection_eq_zero_iff',
        'CubicAnomaly.Classification.SelfDualQuotientObstruction.injective_range_self_dual',
        'CubicAnomaly.Classification.SelfDualQuotientObstruction.self_dual_embedding_surjective',
        'CubicAnomaly.Classification.SelfDualQuotientObstruction.two_blocks_obstruction',
        'CubicAnomaly.Classification.SieveBounds.all_rank_exceptional_size_half_bounds',
        'CubicAnomaly.Classification.SieveBounds.all_rank_half_dimension_inequalities',
        'CubicAnomaly.Classification.SieveBounds.all_rank_isotropy_dimension_bounds',
        'CubicAnomaly.Classification.SieveBounds.all_rank_isotropy_ne_bot',
        'CubicAnomaly.Classification.SimpleIdealStructure.semisimple_simple_or_disjoint_atoms',
        'CubicAnomaly.Classification.SimpleIdealStructure.semisimple_simple_or_disjoint_simple_ideals',
        'CubicAnomaly.Classification.SimpleIdealStructure.semisimple_simple_or_two_atoms_of_no_three',
        'CubicAnomaly.Classification.SimpleIdealStructure.simple_of_complexification_simple',
        'CubicAnomaly.Classification.SkewTraceComplement.action_mem_skew_adjoint',
        'CubicAnomaly.Classification.SkewTraceComplement.mem_skew_adjoint_iff_form_adjoint',
        'CubicAnomaly.Classification.SkewTraceComplement.skew_action_complement_eq_bot_iff',
        'CubicAnomaly.Classification.SkewTraceComplement.skew_action_complement_inclusion_injective',
        'CubicAnomaly.Classification.SkewTraceComplement.skew_action_complement_isCompl',
        'CubicAnomaly.Classification.SkewTraceComplement.skew_action_complement_self_dual',
        'CubicAnomaly.Classification.SkewTraceComplement.skew_action_complement_trace_nondegenerate',
        'CubicAnomaly.Classification.SkewTraceComplement.skew_action_module_range_eq_top_iff',
        'CubicAnomaly.Classification.SkewTraceComplement.skew_action_range_trace_nondegenerate',
        'CubicAnomaly.Classification.SkewTraceComplement.skew_adjoint_module_trace_form_invariant',
        'CubicAnomaly.Classification.SkewTraceComplement.skew_adjoint_module_trace_form_nondegenerate',
        'CubicAnomaly.Classification.SkewTraceComplement.skew_adjoint_self_dual',
        'CubicAnomaly.Classification.SkewTraceComplement.skew_adjoint_trace_form_nondegenerate',
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
        'CubicAnomaly.Classification.SymmetricPairDerivations.equivariant_skew_extension_eq_zero',
        'CubicAnomaly.Classification.SymmetricPairDerivations.symmetric_complement_not_inequivalent_dual_pair',
        'CubicAnomaly.Classification.SymmetricPairDerivations.symmetric_complement_skew_end_eq_zero',
        'CubicAnomaly.Classification.SymplecticComplexification.symplectic_complexification_equiv_tmul',
        'CubicAnomaly.Classification.SymplecticComplexification.symplectic_complexification_injective',
        'CubicAnomaly.Classification.SymplecticComplexification.symplectic_complexification_surjective',
        'CubicAnomaly.Classification.SymplecticDefining.all_rank_symplectic_complexified_defining_irreducible',
        'CubicAnomaly.Classification.SymplecticDefining.all_rank_symplectic_defining_irreducible',
        'CubicAnomaly.Classification.SymplecticDefining.self_adjoint_commutant_preserves_quaternionic',
        'CubicAnomaly.Classification.SymplecticDefining.symplectic_defining_irreducible',
        'CubicAnomaly.Classification.SymplecticForm.all_rank_symplectic_defining_irreducible_self_dual',
        'CubicAnomaly.Classification.SymplecticForm.quaternionic_form_alternating',
        'CubicAnomaly.Classification.SymplecticForm.quaternionic_form_apply',
        'CubicAnomaly.Classification.SymplecticForm.quaternionic_form_complexified_invariant',
        'CubicAnomaly.Classification.SymplecticForm.quaternionic_form_invariant',
        'CubicAnomaly.Classification.SymplecticForm.quaternionic_form_nondegenerate',
        'CubicAnomaly.Classification.SymplecticForm.symplectic_complexified_defining_self_dual',
        'CubicAnomaly.Classification.SymplecticGeometry.QuaternionicStructure.apply_add',
        'CubicAnomaly.Classification.SymplecticGeometry.QuaternionicStructure.apply_neg',
        'CubicAnomaly.Classification.SymplecticGeometry.QuaternionicStructure.apply_smul',
        'CubicAnomaly.Classification.SymplecticGeometry.QuaternionicStructure.apply_sub',
        'CubicAnomaly.Classification.SymplecticGeometry.QuaternionicStructure.apply_zero',
        'CubicAnomaly.Classification.SymplecticGeometry.QuaternionicStructure.conjugateEnd_apply',
        'CubicAnomaly.Classification.SymplecticGeometry.QuaternionicStructure.conjugateEnd_apply_image',
        'CubicAnomaly.Classification.SymplecticGeometry.QuaternionicStructure.image_conjugateEnd_apply',
        'CubicAnomaly.Classification.SymplecticGeometry.QuaternionicStructure.injective',
        'CubicAnomaly.Classification.SymplecticGeometry.QuaternionicStructure.inner_conjugateEnd_left',
        'CubicAnomaly.Classification.SymplecticGeometry.QuaternionicStructure.inner_conjugateEnd_right',
        'CubicAnomaly.Classification.SymplecticGeometry.QuaternionicStructure.inner_left',
        'CubicAnomaly.Classification.SymplecticGeometry.QuaternionicStructure.inner_right',
        'CubicAnomaly.Classification.SymplecticGeometry.QuaternionicStructure.inner_self_image',
        'CubicAnomaly.Classification.SymplecticGeometry.QuaternionicStructure.surjective',
        'CubicAnomaly.Classification.SymplecticGeometry.complexCrossSkew_skew',
        'CubicAnomaly.Classification.SymplecticGeometry.isometry_inverse_commutes',
        'CubicAnomaly.Classification.SymplecticGeometry.symplecticConjugation_apply',
        'CubicAnomaly.Classification.SymplecticGeometry.symplecticCrossSkew_apply_right',
        'CubicAnomaly.Classification.SymplecticGeometry.symplectic_commutes',
        'CubicAnomaly.Classification.SymplecticGeometry.symplectic_skew_action',
        'CubicAnomaly.Classification.TensorEndomorphismDescent.commutes_all_left_of_commutes_action',
        'CubicAnomaly.Classification.TensorEndomorphismDescent.equivariant_commutes_left_action',
        'CubicAnomaly.Classification.TensorEndomorphismDescent.exists_nonzero_skew_right_equivariant_factor',
        'CubicAnomaly.Classification.TensorEndomorphismDescent.exists_right_equivariant_factor',
        'CubicAnomaly.Classification.TensorEndomorphismDescent.exists_unique_right_factor_of_commutes',
        'CubicAnomaly.Classification.TensorEndomorphismDescent.exists_unique_right_factor_of_commutes_action',
        'CubicAnomaly.Classification.TensorEndomorphismDescent.right_factor_equivariant',
        'CubicAnomaly.Classification.TensorEndomorphismDescent.right_factor_ne_zero',
        'CubicAnomaly.Classification.TensorEndomorphismDescent.right_factor_skew_of_tensor_skew',
        'CubicAnomaly.Classification.TensorEndomorphismDescent.right_tensor_operator_injective',
        'CubicAnomaly.Classification.TensorEndomorphismDescent.tensor_comm_lie_equiv_tmul',
        'CubicAnomaly.Classification.TensorEndomorphismDescent.tensor_form_isometry_swap',
        'CubicAnomaly.Classification.TensorEndomorphismDescent.tensor_form_pullback_comm',
        'CubicAnomaly.Classification.TensorEndomorphisms.tensor_endomorphism_equiv_injective',
        'CubicAnomaly.Classification.TensorEndomorphisms.tensor_endomorphism_equiv_tmul',
        'CubicAnomaly.Classification.TensorEndomorphisms.tensor_endomorphism_trace_product',
        'CubicAnomaly.Classification.TensorEndomorphisms.tensor_operator_adjointness_signs',
        'CubicAnomaly.Classification.TensorEndomorphisms.tensor_self_adjoint_skew_operator',
        'CubicAnomaly.Classification.TensorEndomorphisms.tensor_skew_self_adjoint_operator',
        'CubicAnomaly.Classification.TensorEvaluation.atomic_lieSubmodule_irreducible',
        'CubicAnomaly.Classification.TensorEvaluation.commutingIdealEvaluationEquiv_tmul',
        'CubicAnomaly.Classification.TensorEvaluation.commutingIdealHomLieModule',
        'CubicAnomaly.Classification.TensorEvaluation.commutingIdealHomPostcompose_apply',
        'CubicAnomaly.Classification.TensorEvaluation.commutingIdealHom_faithful',
        'CubicAnomaly.Classification.TensorEvaluation.commutingIdealHom_irreducible',
        'CubicAnomaly.Classification.TensorEvaluation.commutingIdeal_lieHomEvaluation_surjective',
        'CubicAnomaly.Classification.TensorEvaluation.commutingIdeal_restrictedEvaluation_surjective',
        'CubicAnomaly.Classification.TensorEvaluation.exists_atomic_evaluation_factorization',
        'CubicAnomaly.Classification.TensorEvaluation.lieHomEvaluation_comp_left_action',
        'CubicAnomaly.Classification.TensorEvaluation.lieHomEvaluation_comp_right_action',
        'CubicAnomaly.Classification.TensorEvaluation.lieHomEvaluation_injective',
        'CubicAnomaly.Classification.TensorEvaluation.lieHomEvaluation_left_faithful',
        'CubicAnomaly.Classification.TensorEvaluation.lieHomEvaluation_tmul',
        'CubicAnomaly.Classification.TensorEvaluation.lieHom_space_finite',
        'CubicAnomaly.Classification.TensorEvaluation.restrictedLieHomEvaluation_tmul',
        'CubicAnomaly.Classification.TensorFactorActions.ambientTensorEvaluationLieEquiv_tmul',
        'CubicAnomaly.Classification.TensorFactorActions.complementaryIdealProjection_add',
        'CubicAnomaly.Classification.TensorFactorActions.complementaryIdealProjection_left',
        'CubicAnomaly.Classification.TensorFactorActions.complementaryIdealProjection_right',
        'CubicAnomaly.Classification.TensorFactorActions.exists_atomic_ambient_tensor_factorization',
        'CubicAnomaly.Classification.TensorFactorActions.idealInflationLieModule',
        'CubicAnomaly.Classification.TensorFactorActions.idealInflation_action',
        'CubicAnomaly.Classification.TensorFactorActions.idealInflation_complement_trivial',
        'CubicAnomaly.Classification.TensorFactorActions.idealInflation_irreducible',
        'CubicAnomaly.Classification.TensorFactorActions.multiplicityAmbientLieModule',
        'CubicAnomaly.Classification.TensorFactorActions.multiplicityAmbient_action_apply',
        'CubicAnomaly.Classification.TensorFactorActions.multiplicityAmbient_first_trivial',
        'CubicAnomaly.Classification.TensorFactorActions.multiplicityAmbient_irreducible',
        'CubicAnomaly.Classification.TensorFactorDuality.exists_nondegenerate_left_coefficient',
        'CubicAnomaly.Classification.TensorFactorDuality.exists_nondegenerate_right_coefficient',
        'CubicAnomaly.Classification.TensorFactorDuality.exists_nonzero_left_coefficient',
        'CubicAnomaly.Classification.TensorFactorDuality.exists_nonzero_right_coefficient',
        'CubicAnomaly.Classification.TensorFactorDuality.invariant_form_nondegenerate_of_ne_zero',
        'CubicAnomaly.Classification.TensorFactorDuality.left_coefficient_form_apply',
        'CubicAnomaly.Classification.TensorFactorDuality.left_coefficient_form_invariant',
        'CubicAnomaly.Classification.TensorFactorDuality.left_factor_self_dual_of_nondegenerate_invariant',
        'CubicAnomaly.Classification.TensorFactorDuality.left_factor_self_dual_of_nonzero_invariant',
        'CubicAnomaly.Classification.TensorFactorDuality.right_coefficient_form_apply',
        'CubicAnomaly.Classification.TensorFactorDuality.right_coefficient_form_invariant',
        'CubicAnomaly.Classification.TensorFactorDuality.right_factor_self_dual_of_nondegenerate_invariant',
        'CubicAnomaly.Classification.TensorFactorDuality.right_factor_self_dual_of_nonzero_invariant',
        'CubicAnomaly.Classification.TensorFactorFaithfulness.idealInflation_restrict_injective',
        'CubicAnomaly.Classification.TensorFactorFaithfulness.idealInflation_self_action',
        'CubicAnomaly.Classification.TensorFactorFaithfulness.multiplicityAmbient_restrict_injective',
        'CubicAnomaly.Classification.TensorFixedVectors.fixed_eq_zero_of_bijective',
        'CubicAnomaly.Classification.TensorFixedVectors.hom_eq_zero_of_trivial_to_no_fixed',
        'CubicAnomaly.Classification.TensorFixedVectors.ideal_adjoint_fixed_eq_zero',
        'CubicAnomaly.Classification.TensorFixedVectors.ideal_tensor_fixed_eq_zero',
        'CubicAnomaly.Classification.TensorFixedVectors.left_parity_source_fixed_eq_zero',
        'CubicAnomaly.Classification.TensorFixedVectors.right_parity_source_fixed_eq_zero',
        'CubicAnomaly.Classification.TensorFixedVectors.tensor_fixed_eq_zero',
        'CubicAnomaly.Classification.TensorFixedVectors.tensor_fixed_eq_zero_right',
        'CubicAnomaly.Classification.TensorFixedVectors.trace_zero_self_adjoint_ideal_action_eq_zero',
        'CubicAnomaly.Classification.TensorFormFactorization.equivariant_end_eq_smul_id',
        'CubicAnomaly.Classification.TensorFormFactorization.exists_coefficient_factorization',
        'CubicAnomaly.Classification.TensorFormFactorization.exists_nondegenerate_invariant_factorization',
        'CubicAnomaly.Classification.TensorFormFactorization.invariant_form_eq_smul',
        'CubicAnomaly.Classification.TensorFormFactorization.invariant_form_isRefl',
        'CubicAnomaly.Classification.TensorFormFactorization.normalized_right_form_apply',
        'CubicAnomaly.Classification.TensorFormFactorization.normalized_right_form_invariant',
        'CubicAnomaly.Classification.TensorFormFactorization.right_form_nondegenerate_of_tensor_factorization',
        'CubicAnomaly.Classification.TensorFormFactorization.tensor_form_eq_left_tmul_normalized_right',
        'CubicAnomaly.Classification.TensorFormFactorization.tensor_form_pure_factorization',
        'CubicAnomaly.Classification.TensorInvariantForms.pullback_bilin_form_nondegenerate',
        'CubicAnomaly.Classification.TensorInvariantForms.tensor_bilin_form_invariant',
        'CubicAnomaly.Classification.TensorInvariantForms.tensor_bilin_form_nondegenerate',
        'CubicAnomaly.Classification.TensorParityBlocks.atomic_left_parity_source_self_dual',
        'CubicAnomaly.Classification.TensorParityBlocks.atomic_right_parity_source_self_dual',
        'CubicAnomaly.Classification.TensorParityBlocks.ideal_action_module_hom_apply',
        'CubicAnomaly.Classification.TensorParityBlocks.left_parity_block_injective',
        'CubicAnomaly.Classification.TensorParityBlocks.left_parity_block_mem_skewAdjointLieSubalgebra',
        'CubicAnomaly.Classification.TensorParityBlocks.left_parity_block_ne_zero',
        'CubicAnomaly.Classification.TensorParityBlocks.left_parity_block_tmul',
        'CubicAnomaly.Classification.TensorParityBlocks.right_parity_block_injective',
        'CubicAnomaly.Classification.TensorParityBlocks.right_parity_block_mem_skewAdjointLieSubalgebra',
        'CubicAnomaly.Classification.TensorParityBlocks.right_parity_block_ne_zero',
        'CubicAnomaly.Classification.TensorParityBlocks.right_parity_block_tmul',
        'CubicAnomaly.Classification.TensorParitySeparation.form_adjoint_eq_neg_of_skew',
        'CubicAnomaly.Classification.TensorParitySeparation.invariant_action_trace_zero',
        'CubicAnomaly.Classification.TensorParitySeparation.left_parity_block_partial_adjoint',
        'CubicAnomaly.Classification.TensorParitySeparation.left_parity_block_partial_traces_zero',
        'CubicAnomaly.Classification.TensorParitySeparation.left_partial_adjoint_map',
        'CubicAnomaly.Classification.TensorParitySeparation.left_partial_trace_map',
        'CubicAnomaly.Classification.TensorParitySeparation.opposite_parity_sum_eq_tensor_sum',
        'CubicAnomaly.Classification.TensorParitySeparation.parity_blocks_eq_diagonal_action',
        'CubicAnomaly.Classification.TensorParitySeparation.parity_blocks_eq_tensor_sum',
        'CubicAnomaly.Classification.TensorParitySeparation.parity_blocks_tensor_sum_separation',
        'CubicAnomaly.Classification.TensorParitySeparation.right_parity_block_partial_adjoint',
        'CubicAnomaly.Classification.TensorParitySeparation.right_parity_block_partial_traces_zero',
        'CubicAnomaly.Classification.TensorParitySeparation.right_partial_trace_map',
        'CubicAnomaly.Classification.TensorParitySeparation.tensor_action_eq_sum',
        'CubicAnomaly.Classification.TensorParitySeparation.trace_eq_zero_of_skew',
        'CubicAnomaly.Classification.TensorScalarSkew.tensor_skew_range_le_diagonal_of_irreducible_factors',
        'CubicAnomaly.Classification.TensorScalarSkew.tensor_skew_range_le_diagonal_of_scalar_action_spans',
        'CubicAnomaly.Classification.TensorScalarSkew.tensor_skew_range_le_diagonal_of_trace_zero_parts_eq_bot',
        'CubicAnomaly.Classification.TensorUnitary.adjoint_commutes_of_skew_adjoint',
        'CubicAnomaly.Classification.TensorUnitary.complexified_defining_real_action_skew',
        'CubicAnomaly.Classification.TensorUnitary.complexified_defining_tensor_equivariant_adjoint_mem',
        'CubicAnomaly.Classification.TensorUnitary.complexified_equivariant_adjoint_mem',
        'CubicAnomaly.Classification.TensorUnitary.complexified_tensor_equivariant_adjoint_mem',
        'CubicAnomaly.Classification.TensorUnitary.equivariant_hom_mem',
        'CubicAnomaly.Classification.TensorUnitary.equivariant_operator_mem_iff_commute',
        'CubicAnomaly.Classification.TensorUnitary.tensor_action_adjoint_of_skew',
        'CubicAnomaly.Classification.TensorUnitary.tensor_flip_adjoint',
        'CubicAnomaly.Classification.TensorUnitary.tensor_flip_mem',
        'CubicAnomaly.Classification.TensorUnitary.tensor_flip_sq',
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
        'CubicAnomaly.Classification.TraceReshuffle.dual_tensor_end_lie_equiv_tmul',
        'CubicAnomaly.Classification.TraceReshuffle.equivariant_trace_reshuffle_toLinearMap',
        'CubicAnomaly.Classification.TraceReshuffle.equivariant_trace_skew_iff_flip_odd',
        'CubicAnomaly.Classification.TraceReshuffle.exists_flip_odd_line_of_trace_skew_line',
        'CubicAnomaly.Classification.TraceReshuffle.tensor_flip_conjugation',
        'CubicAnomaly.Classification.TraceReshuffle.tensor_flip_conjugation_eq_neg_iff',
        'CubicAnomaly.Classification.TraceReshuffle.tensor_flip_mul_self',
        'CubicAnomaly.Classification.TraceReshuffle.tensor_flip_tmul',
        'CubicAnomaly.Classification.TraceReshuffle.trace_dual_equiv_apply',
        'CubicAnomaly.Classification.TraceReshuffle.trace_reshuffle_adjoint',
        'CubicAnomaly.Classification.TraceReshuffle.trace_reshuffle_trace_tensor',
        'CubicAnomaly.Classification.TraceReshuffle.trace_skew_iff_flip_odd',
        'CubicAnomaly.Classification.TraceReshuffle.trace_tensor_equiv_adjoint',
        'CubicAnomaly.Classification.TraceReshuffle.trace_tensor_equiv_tmul',
        'CubicAnomaly.Classification.TraceZeroEndKilling.end_killing_form',
        'CubicAnomaly.Classification.TraceZeroEndKilling.mem_traceZeroEndIdeal',
        'CubicAnomaly.Classification.TraceZeroEndKilling.sandwich_apply',
        'CubicAnomaly.Classification.TraceZeroEndKilling.trace_sandwich',
        'CubicAnomaly.Classification.TraceZeroEndKilling.trace_zero_end_isKilling',
        'CubicAnomaly.Classification.TraceZeroEndKilling.trace_zero_end_killing_form',
        'CubicAnomaly.Classification.TraceZeroEndKilling.trace_zero_end_trace_form_nondegenerate',
        'CubicAnomaly.Classification.TraceZeroSymmetricPair.full_skew_trace_zero_self_adjoint_not_inequivalent_dual_pair',
        'CubicAnomaly.Classification.TraceZeroSymmetricPair.full_skew_trace_zero_self_adjoint_skew_end_eq_zero',
        'CubicAnomaly.Classification.TraceZeroSymmetricPair.self_adjoint_trace_zero_bracket_mem_skew',
        'CubicAnomaly.Classification.TraceZeroSymmetricPair.skew_adjoint_trace_zero',
        'CubicAnomaly.Classification.TraceZeroSymmetricPair.skew_self_adjoint_trace_zero_isCompl',
        'CubicAnomaly.Classification.TraceZeroSymmetricPair.skew_trace_zero_centralizer_eq_zero',
        'CubicAnomaly.Classification.TraceZeroSymmetricPair.trace_zero_form_invariant',
        'CubicAnomaly.Classification.TraceZeroSymmetricPair.trace_zero_form_restrict_skew_nondegenerate',
        'CubicAnomaly.Classification.TwoIdealTensorForms.exists_atomic_two_ideal_tensor_forms',
        'CubicAnomaly.Classification.UnitaryComplexification.complexify_skew_map_injective',
        'CubicAnomaly.Classification.UnitaryComplexification.special_unitary_complexification_equiv_tmul',
        'CubicAnomaly.Classification.UnitaryComplexification.special_unitary_complexification_injective',
        'CubicAnomaly.Classification.UnitaryComplexification.special_unitary_complexification_surjective',
        'CubicAnomaly.Classification.UnitaryComplexification.special_unitary_matrix_equiv_action',
        'CubicAnomaly.Classification.UnitaryComplexification.special_unitary_matrix_equiv_tmul',
        'CubicAnomaly.Classification.UnitaryComplexification.trace_adjoint_eq_conj',
        'CubicAnomaly.Classification.UnitaryDefining.all_rank_special_unitary_complexified_defining_irreducible',
        'CubicAnomaly.Classification.UnitaryDefining.all_rank_special_unitary_defining_irreducible',
        'CubicAnomaly.Classification.UnitaryDefining.special_unitary_defining_irreducible',
        'CubicAnomaly.Classification.UnitaryDefining.special_unitary_defining_irreducible_of_centralizer',
        'CubicAnomaly.Classification.UnitaryEndDecomposition.complement_projection_insertion',
        'CubicAnomaly.Classification.UnitaryEndDecomposition.isotropy_projection_insertion',
        'CubicAnomaly.Classification.UnitaryEndDecomposition.scalar_isotropy_complement_sum',
        'CubicAnomaly.Classification.UnitaryEndDecomposition.scalar_projection_insertion',
        'CubicAnomaly.Classification.UnitaryGeometry.invariant_starProjection_commutes',
        'CubicAnomaly.Classification.UnitaryGeometry.skew_invariant_orthogonal_mem',
        'CubicAnomaly.Classification.UnitaryGeometry.special_unitary_skew_action',
        'CubicAnomaly.Classification.UnitaryGeometry.unitaryConjugation_apply',
        'CubicAnomaly.Classification.UnitaryGeometry.unitary_mem_iff',
        'CubicAnomaly.Classification.UnitaryGeometry.unitary_skew_action',
        'CubicAnomaly.Classification.UnitaryModuleBridge.lift_trace_zero_equivariant_operator',
        'CubicAnomaly.Classification.UnitaryModuleBridge.lift_trace_zero_range_le_action_range',
        'CubicAnomaly.Classification.UnitaryModuleBridge.special_unitary_ambient_operator_map_apply',
        'CubicAnomaly.Classification.UnitaryModuleBridge.special_unitary_ambient_operator_map_inclusion',
        'CubicAnomaly.Classification.UnitaryModuleBridge.special_unitary_ambient_operator_map_injective',
        'CubicAnomaly.Classification.UnitaryModuleBridge.special_unitary_complexified_defining_faithful',
        'CubicAnomaly.Classification.UnitaryModuleBridge.special_unitary_complexified_inclusion_natural',
        'CubicAnomaly.Classification.UnitaryNoGo.all_rank_special_unitary_cubic_radical_eq_bot',
        'CubicAnomaly.Classification.UnitaryNoGo.all_rank_special_unitary_end_trace_skew_line',
        'CubicAnomaly.Classification.UnitaryNoGo.all_rank_special_unitary_nonzero_cubic_radical_impossible',
        'CubicAnomaly.Classification.UnitarySelfDualExclusion.all_rank_special_unitary_defining_not_self_dual',
        'CubicAnomaly.Classification.UnitarySelfDualExclusion.all_rank_special_unitary_no_invariant_nondegenerate_form',
        'CubicAnomaly.Classification.UnitarySelfDualExclusion.special_unitary_mem_isotropy_iff_action_range',
        'CubicAnomaly.Classification.UnitarySelfDualExclusion.special_unitary_no_invariant_nondegenerate_form_of_irreducible',
        'CubicAnomaly.Classification.UnitarySimplicity.all_rank_special_unitary_complexified_isotropy_simple',
        'CubicAnomaly.Classification.UnitarySimplicity.all_rank_special_unitary_cubic_radical_eq_top',
        'CubicAnomaly.Classification.UnitarySimplicity.all_rank_special_unitary_cubic_trace_zero',
        'CubicAnomaly.Classification.UnitarySimplicity.all_rank_special_unitary_isotropy_simple',
        'CubicAnomaly.Classification.UnitarySkewLine.dual_pair_hom_to_self_dual_eq_zero',
        'CubicAnomaly.Classification.UnitarySkewLine.dual_pair_skew_end_eq_smul_sign',
        'CubicAnomaly.Classification.UnitarySkewLine.irreducible_hom_eq_zero_of_not_equiv',
        'CubicAnomaly.Classification.UnitarySkewLine.three_block_trace_skew_line',
        'CubicAnomaly.Classification.UnitaryTraceSkewObstruction.complexified_defining_trace_skew_not_line',
        'CubicAnomaly.Classification.UnitaryTraceSkewObstruction.complexified_trace_skew_not_line',
        'CubicAnomaly.Classification.WeightCubic.symmetrized_trace_cubic_eq_sum_weights',
        'CubicAnomaly.Classification.WeightCubic.trace_cubic_eq_sum_weights',
        'CubicAnomaly.Classification.WeightCubic.trace_power_eq_sum_weights',
        'CubicAnomaly.Classification.WeightCubic.trace_prod_eq_sum_weights',
        'CubicAnomaly.Classification.WeightCubic.trace_prod_toEnd_genWeightSpace',
        'CubicAnomaly.Fixed.AdjointRecognition.generated_adjoint_equiv_val',
        'CubicAnomaly.Fixed.AdjointRecognition.generated_adjoint_finrank',
        'CubicAnomaly.Fixed.AdjointRecognition.generated_adjoint_recognition',
        'CubicAnomaly.Fixed.AdjointRecognition.generated_intertwiner_equivariance',
        'CubicAnomaly.Fixed.AdjointRecognition.irreducible_generated_intertwiner_injective',
        'CubicAnomaly.Fixed.AdjointRecognition.irreducible_generated_intertwiner_mem',
        'CubicAnomaly.Fixed.E8A2.e8_a2_tracelessProjection_apply',
        'CubicAnomaly.Fixed.E8A4.e8_a4_tracelessProjection_apply',
        'CubicAnomaly.Fixed.E8BracketBinding.bracket_data_diagram_sign',
        'CubicAnomaly.Fixed.E8BracketBinding.bracket_data_diagram_sign_sq',
        'CubicAnomaly.Fixed.E8BracketBinding.bracket_data_isRoot_iff_list',
        'CubicAnomaly.Fixed.E8BracketBinding.bracket_data_sparse_coefficients',
        'CubicAnomaly.Fixed.E8BracketBinding.bracket_vector_get_mem_iff',
        'CubicAnomaly.Fixed.E8BracketData.bracket_data_root_list_length',
        'CubicAnomaly.Fixed.E8ClassicalEmbedding.e8_gaugeSl5Embedding_injective',
        'CubicAnomaly.Fixed.E8GradingData.e8_e6_cartan_submatrix',
        'CubicAnomaly.Fixed.E8GradingData.e8_mem_gradeLabels',
        'CubicAnomaly.Fixed.E8GradingData.e8_sparse_bracket_graded',
        'CubicAnomaly.Fixed.E8MatterData.e8_matter_labelList_nodup',
        'CubicAnomaly.Fixed.E8MatterData.e8_matter_labelList_toFinset',
        'CubicAnomaly.Fixed.E8MatterMatching.e8_coupledAction_coordinates',
        'CubicAnomaly.Fixed.E8Metric.coordinate_factor_gram',
        'CubicAnomaly.Fixed.E8Metric.rational_factor_gram',
        'CubicAnomaly.Fixed.E8Metric.rational_factor_left_inverse',
        'CubicAnomaly.Fixed.E8RootPairing.cartan_coordinates_eq',
        'CubicAnomaly.Fixed.E8RootPairing.cartan_det_ne_zero',
        'CubicAnomaly.Fixed.E8RootPairing.cartan_mul_inverse',
        'CubicAnomaly.Fixed.E8RootPairing.coordinate_vector_get_ofFn',
        'CubicAnomaly.Fixed.E8RootPairing.form_apply',
        'CubicAnomaly.Fixed.E8RootPairing.form_nondegenerate',
        'CubicAnomaly.Fixed.E8RootPairing.form_rootVectors',
        'CubicAnomaly.Fixed.E8RootPairing.form_symmetric',
        'CubicAnomaly.Fixed.E8RootPairing.innerZ_smul_left',
        'CubicAnomaly.Fixed.E8RootPairing.innerZ_sub_left',
        'CubicAnomaly.Fixed.E8RootPairing.reflectZ_apply',
        'CubicAnomaly.Fixed.E8RootPairing.reflectZ_eq',
        'CubicAnomaly.Fixed.E8RootPairing.reflectZ_involutive',
        'CubicAnomaly.Fixed.E8RootPairing.rootVector_injective',
        'CubicAnomaly.Fixed.E8RootPairing.unsigned_cartan_det_ne_zero',
        'CubicAnomaly.Fixed.E8RootPairing.unsigned_cartan_mul_inverse',
        'CubicAnomaly.Fixed.FamilyAnomaly.family_cubic_witness',
        'CubicAnomaly.Fixed.FamilyAnomaly.family_representation_radical_eq_bot',
        'CubicAnomaly.Fixed.FamilyAnomaly.family_representation_trace',
        'CubicAnomaly.Fixed.FamilyAnomaly.family_tensor_27_cubic_witness',
        'CubicAnomaly.Fixed.FamilyAnomaly.family_tensor_full_cubic',
        'CubicAnomaly.Fixed.FamilyAnomaly.family_tensor_pure_cubic',
        'CubicAnomaly.Fixed.FamilyAnomaly.family_tensor_radical_eq_left_ideal',
        'CubicAnomaly.Fixed.FamilyAnomaly.three_by_three_cubic_detects_matrix',
        'CubicAnomaly.Fixed.MatrixCompactForm.compact_complexification_equiv_tmul',
        'CubicAnomaly.Fixed.MatrixCompactForm.compact_complexification_injective',
        'CubicAnomaly.Fixed.MatrixCompactForm.compact_complexification_surjective',
        'CubicAnomaly.Fixed.MatrixCompactForm.compact_form_trace',
        'CubicAnomaly.Fixed.MatrixCompactForm.compact_skew_parts',
        'CubicAnomaly.Fixed.MatrixCompactForm.metric_matrix_action',
        'CubicAnomaly.Fixed.MatrixCompactForm.metric_matrix_adjoint',
        'CubicAnomaly.Fixed.MatrixCompactForm.metric_space_inner',
        'CubicAnomaly.Fixed.MatrixCompactForm.negative_trace_form_apply',
        'CubicAnomaly.Fixed.MatrixUnitHom.matrix_unit_lieHom_single',
        'CubicAnomaly.Fixed.MatrixUnitHom.matrix_unit_linearMap_apply',
        'CubicAnomaly.Fixed.MatrixUnitHom.matrix_unit_linearMap_lie',
        'CubicAnomaly.Fixed.MatrixUnitHom.matrix_unit_linearMap_single',
        'CubicAnomaly.Fixed.MatterAlternating.alternating_action_val',
        'CubicAnomaly.Fixed.MatterAlternating.alternating_coordinates_diagonal',
        'CubicAnomaly.Fixed.MatterAlternating.alternating_diagonal_action',
        'CubicAnomaly.Fixed.MatterAlternating.alternating_finrank',
        'CubicAnomaly.Fixed.MatterAnomaly.family_standard_model_cube_trace',
        'CubicAnomaly.Fixed.MatterAnomaly.family_standard_model_linear_trace',
        'CubicAnomaly.Fixed.MatterAnomaly.matter27_matrix_operator',
        'CubicAnomaly.Fixed.MatterAnomaly.matter27_matrix_trace',
        'CubicAnomaly.Fixed.MatterAnomaly.matter27_standard_model_cube_trace',
        'CubicAnomaly.Fixed.MatterAnomaly.matter27_standard_model_full_cubic',
        'CubicAnomaly.Fixed.MatterAnomaly.matter27_standard_model_linear_trace',
        'CubicAnomaly.Fixed.MatterAnomaly.weak_traceless_cube_trace',
        'CubicAnomaly.Fixed.MatterBlocks.alternating_block_action',
        'CubicAnomaly.Fixed.MatterBranching.standard_model_generator_trace',
        'CubicAnomaly.Fixed.MatterBranching.ten_block_action',
        'CubicAnomaly.Fixed.MatterBranching.ten_finrank',
        'CubicAnomaly.Fixed.MatterBranching.ten_hypercharge_action',
        'CubicAnomaly.Fixed.MatterBranching.ten_standard_model_action',
        'CubicAnomaly.Fixed.MatterChirality.extra_copies_finrank',
        'CubicAnomaly.Fixed.MatterChirality.matter81_sm_three_families_self_dual_remainder',
        'CubicAnomaly.Fixed.MatterChirality.matter81_three_families_self_dual_remainder',
        'CubicAnomaly.Fixed.MatterChirality.three_families_finrank',
        'CubicAnomaly.Fixed.MatterChirality.vectorlike_self_dual_apply',
        'CubicAnomaly.Fixed.MatterCoordinates.matter27_coordinates_first_dual',
        'CubicAnomaly.Fixed.MatterCoordinates.matter27_coordinates_five',
        'CubicAnomaly.Fixed.MatterCoordinates.matter27_coordinates_second_dual',
        'CubicAnomaly.Fixed.MatterCoordinates.matter27_coordinates_singlets',
        'CubicAnomaly.Fixed.MatterCoordinates.matter27_coordinates_ten',
        'CubicAnomaly.Fixed.MatterCoordinates.matter27_unit_action',
        'CubicAnomaly.Fixed.MatterCoordinates.matter81_coordinates_apply',
        'CubicAnomaly.Fixed.MatterCoordinates.matter81_unit_action',
        'CubicAnomaly.Fixed.MatterDual.anti_five_block_action',
        'CubicAnomaly.Fixed.MatterDual.anti_five_hypercharge_action',
        'CubicAnomaly.Fixed.MatterDual.anti_five_sm_action',
        'CubicAnomaly.Fixed.MatterDual.anti_five_standard_model_action',
        'CubicAnomaly.Fixed.MatterDual.dual_coordinates_apply',
        'CubicAnomaly.Fixed.MatterDual.dual_matrix_action',
        'CubicAnomaly.Fixed.MatterDual.weak_dual_action',
        'CubicAnomaly.Fixed.MatterDual.weak_dual_traceless_action',
        'CubicAnomaly.Fixed.MatterFamilyAnomaly.coupled_matter81_dimension',
        'CubicAnomaly.Fixed.MatterFamilyAnomaly.coupled_matter81_family_cubic_witness',
        'CubicAnomaly.Fixed.MatterFamilyAnomaly.coupled_matter81_full_cubic',
        'CubicAnomaly.Fixed.MatterFamilyAnomaly.coupled_matter81_gauge_action',
        'CubicAnomaly.Fixed.MatterFamilyAnomaly.coupled_matter81_gauge_insertion_zero',
        'CubicAnomaly.Fixed.MatterFamilyAnomaly.coupled_matter81_linear_trace',
        'CubicAnomaly.Fixed.MatterFamilyAnomaly.coupled_matter81_radical_eq_gauge_ideal',
        'CubicAnomaly.Fixed.MatterFamilyAnomaly.coupled_matter81_radical_ne_bot',
        'CubicAnomaly.Fixed.MatterFamilyAnomaly.gauge_hypercharge_ne_zero',
        'CubicAnomaly.Fixed.MatterFamilyCoordinates.coupled_family_copy_action',
        'CubicAnomaly.Fixed.MatterFamilyCoordinates.family_copy_action_map_apply',
        'CubicAnomaly.Fixed.MatterFamilyCoordinates.matter81_family_unit_action',
        'CubicAnomaly.Fixed.MatterFamilyCoordinates.matter_family_copy_coordinates',
        'CubicAnomaly.Fixed.MatterGroupAction.alternating_unitary_group_action_val',
        'CubicAnomaly.Fixed.MatterGroupAction.antifive_circle_group_action',
        'CubicAnomaly.Fixed.MatterGroupAction.antifive_gauge_group_action',
        'CubicAnomaly.Fixed.MatterGroupAction.five_circle_group_action',
        'CubicAnomaly.Fixed.MatterGroupAction.five_gauge_group_action',
        'CubicAnomaly.Fixed.MatterGroupAction.matter27_gauge_group_action',
        'CubicAnomaly.Fixed.MatterGroupAction.matter81_cover_group_descent',
        'CubicAnomaly.Fixed.MatterGroupAction.matter81_cover_kernel_trivial',
        'CubicAnomaly.Fixed.MatterGroupAction.matter81_gauge_group_action',
        'CubicAnomaly.Fixed.MatterGroupAction.ten_circle_group_action',
        'CubicAnomaly.Fixed.MatterGroupAction.ten_gauge_group_action',
        'CubicAnomaly.Fixed.MatterLabels.matter_label_card',
        'CubicAnomaly.Fixed.MatterLabels.matter_local_label_card',
        'CubicAnomaly.Fixed.MatterLabels.matter_pair_label_card',
        'CubicAnomaly.Fixed.MatterLieAlgebra.standard_model_element_parameters',
        'CubicAnomaly.Fixed.MatterLieAlgebra.standard_model_generator_element_val',
        'CubicAnomaly.Fixed.MatterLieAlgebra.standard_model_matter27_action',
        'CubicAnomaly.Fixed.MatterNonSelfDual.family_hypercharge_fifth_trace',
        'CubicAnomaly.Fixed.MatterNonSelfDual.family_not_self_dual',
        'CubicAnomaly.Fixed.MatterNonSelfDual.matter27_hypercharge_fifth_trace',
        'CubicAnomaly.Fixed.MatterNonSelfDual.matter81_hypercharge_fifth_trace',
        'CubicAnomaly.Fixed.MatterNonSelfDual.matter81_not_self_dual',
        'CubicAnomaly.Fixed.MatterSmall.alternating_three_action',
        'CubicAnomaly.Fixed.MatterSmall.alternating_three_traceless_action',
        'CubicAnomaly.Fixed.MatterSmall.alternating_two_action',
        'CubicAnomaly.Fixed.MatterSmall.alternating_two_traceless_action',
        'CubicAnomaly.Fixed.MatterSpectrum.copies_lie_apply',
        'CubicAnomaly.Fixed.MatterSpectrum.family_finrank',
        'CubicAnomaly.Fixed.MatterSpectrum.family_standard_model_action',
        'CubicAnomaly.Fixed.MatterSpectrum.five_standard_model_action',
        'CubicAnomaly.Fixed.MatterSpectrum.matter27_finrank',
        'CubicAnomaly.Fixed.MatterSpectrum.matter81_family_action',
        'CubicAnomaly.Fixed.MatterSpectrum.matter81_finrank',
        'CubicAnomaly.Fixed.MatterSpectrum.matter81_full_hypercharge_action',
        'CubicAnomaly.Fixed.MatterSpectrum.product_lie',
        'CubicAnomaly.Fixed.MatterSpectrum.two_singlets_action_zero',
        'CubicAnomaly.Fixed.MatterSpectrum.two_singlets_finrank',
        'CubicAnomaly.Fixed.MatterSpectrum.vectorlike_hypercharge_action',
        'CubicAnomaly.Fixed.MatterSpectrum.vectorlike_pair_finrank',
        'CubicAnomaly.Fixed.SparseBilinear.sparse_bilinear_basis',
        'CubicAnomaly.Fixed.SparseBilinear.sparse_bilinear_derivation',
        'CubicAnomaly.Fixed.SparseBilinear.sparse_bilinear_label',
        'CubicAnomaly.Fixed.SparseBilinear.sparse_bilinear_realize_both',
        'CubicAnomaly.Fixed.SparseBilinear.sparse_bilinear_realize_left',
        'CubicAnomaly.Fixed.SparseBilinear.sparse_bilinear_realize_right',
        'CubicAnomaly.Fixed.SparseBilinear.sparse_matrixMap_equivariance',
        'CubicAnomaly.Fixed.SparseBilinear.sparse_matrixMap_image',
        'CubicAnomaly.Fixed.SparseBilinear.sparse_matrixMap_mulVec',
        'CubicAnomaly.Fixed.SparseRealization.sparse_coefficients_eq_of_support',
        'CubicAnomaly.Fixed.SparseRealization.sparse_map_realize',
        'CubicAnomaly.Fixed.SparseRealization.sparse_realize_action',
        'CubicAnomaly.Fixed.SparseRealization.sparse_realize_append',
        'CubicAnomaly.Fixed.SparseRealization.sparse_realize_cons',
        'CubicAnomaly.Fixed.SparseRealization.sparse_realize_eq_of_coefficients',
        'CubicAnomaly.Fixed.SparseRealization.sparse_realize_linearExtend',
        'CubicAnomaly.Fixed.SparseRealization.sparse_realize_nil',
        'CubicAnomaly.Fixed.SparseRealization.sparse_realize_scale',
        'CubicAnomaly.Fixed.StandardModelGroup.cover_blocks_determinant',
        'CubicAnomaly.Fixed.StandardModelGroup.phase_power_surjective',
        'CubicAnomaly.Fixed.StandardModelGroup.phase_scale_determinant',
        'CubicAnomaly.Fixed.StandardModelGroup.scalar_block_determinant',
        'CubicAnomaly.Fixed.StandardModelGroup.sixth_root_character_trivial_iff',
        'CubicAnomaly.Fixed.StandardModelGroup.standard_model_block_embedding_injective',
        'CubicAnomaly.Fixed.StandardModelGroup.standard_model_central_circle_injective',
        'CubicAnomaly.Fixed.StandardModelGroup.standard_model_charge_lattice',
        'CubicAnomaly.Fixed.StandardModelGroup.standard_model_circle_blocks',
        'CubicAnomaly.Fixed.StandardModelGroup.standard_model_cover_kernel',
        'CubicAnomaly.Fixed.StandardModelGroup.standard_model_cover_surjective',
        'CubicAnomaly.Fixed.StandardModelGroup.standard_model_hom_descends_iff',
        'CubicAnomaly.Fixed.StandardModelGroup.standard_model_kernel_card',
        'CubicAnomaly.Fixed.StandardModelGroup.standard_model_kernel_central',
        'CubicAnomaly.Fixed.StandardModelGroup.standard_model_kernel_cyclic',
        'CubicAnomaly.Fixed.StandardModelGroup.standard_model_kernel_root_injective',
        'CubicAnomaly.Fixed.StandardModelGroup.standard_model_kernel_root_surjective',
        'CubicAnomaly.Fixed.StandardModelGroup.standard_model_representation_descent_charge_iff',
        'CubicAnomaly.Fixed.TensorAnomaly.mem_tensor_representation_radical_iff',
        'CubicAnomaly.Fixed.TensorAnomaly.tensor_27_by_3_family_cubic',
        'CubicAnomaly.Fixed.TensorAnomaly.tensor_action_trace',
        'CubicAnomaly.Fixed.TensorAnomaly.tensor_action_trace_cubic',
        'CubicAnomaly.Fixed.TensorAnomaly.tensor_radical_eq_first_ideal',
        'CubicAnomaly.Fixed.TensorAnomaly.tensor_representation_cubic',
    }
)

CERTIFICATE_DERIVED_THEOREMS = frozenset(
    {
        'CubicAnomaly.Fixed.E8A2.e8_a2_gl3Hom_mem_zero',
        'CubicAnomaly.Fixed.E8A2.e8_a2_gl3Hom_unit',
        'CubicAnomaly.Fixed.E8A2.e8_a2_recovery_gl3Hom',
        'CubicAnomaly.Fixed.E8A2.e8_a2_recovery_sl3',
        'CubicAnomaly.Fixed.E8A2.e8_a2_recovery_sparse',
        'CubicAnomaly.Fixed.E8A2.e8_a2_recovery_unitVector',
        'CubicAnomaly.Fixed.E8A2.e8_a2_sl3Embedding_injective',
        'CubicAnomaly.Fixed.E8A2.e8_a2_sl3Embedding_mem_zero',
        'CubicAnomaly.Fixed.E8A2.e8_a2_sl3ZeroEmbedding_injective',
        'CubicAnomaly.Fixed.E8A2.e8_a2_unitImage_bracket',
        'CubicAnomaly.Fixed.E8A2.e8_a2_unitImage_mem_zero',
        'CubicAnomaly.Fixed.E8A2.e8_a2_unitVector_bracket',
        'CubicAnomaly.Fixed.E8A2Data.e8_a2_recovery_vanishes_on_a4_certificate',
        'CubicAnomaly.Fixed.E8A2Data.e8_a2_unit_bracket_certificate',
        'CubicAnomaly.Fixed.E8A2Data.e8_a2_unit_recovery_certificate',
        'CubicAnomaly.Fixed.E8A2Data.e8_a2_unit_support_certificate',
        'CubicAnomaly.Fixed.E8A2Data.e8_a4_a2_commuting_certificate',
        'CubicAnomaly.Fixed.E8A4.e8_a4_gl5Hom_lower_simple',
        'CubicAnomaly.Fixed.E8A4.e8_a4_gl5Hom_mem_zero',
        'CubicAnomaly.Fixed.E8A4.e8_a4_gl5Hom_unit',
        'CubicAnomaly.Fixed.E8A4.e8_a4_gl5Hom_upper_simple',
        'CubicAnomaly.Fixed.E8A4.e8_a4_recovery_gl5Hom',
        'CubicAnomaly.Fixed.E8A4.e8_a4_recovery_sl5',
        'CubicAnomaly.Fixed.E8A4.e8_a4_recovery_sparse',
        'CubicAnomaly.Fixed.E8A4.e8_a4_recovery_unitVector',
        'CubicAnomaly.Fixed.E8A4.e8_a4_sl5Embedding_injective',
        'CubicAnomaly.Fixed.E8A4.e8_a4_sl5Embedding_mem_zero',
        'CubicAnomaly.Fixed.E8A4.e8_a4_sl5ZeroEmbedding_injective',
        'CubicAnomaly.Fixed.E8A4.e8_a4_unitImage_bracket',
        'CubicAnomaly.Fixed.E8A4.e8_a4_unitImage_mem_zero',
        'CubicAnomaly.Fixed.E8A4.e8_a4_unitVector_bracket',
        'CubicAnomaly.Fixed.E8A4Data.e8_a4_simple_unit_certificate',
        'CubicAnomaly.Fixed.E8A4Data.e8_a4_unit_bracket_certificate',
        'CubicAnomaly.Fixed.E8A4Data.e8_a4_unit_recovery_certificate',
        'CubicAnomaly.Fixed.E8A4Data.e8_a4_unit_support_certificate',
        'CubicAnomaly.Fixed.E8Adjoint.e8_adjointEquiv_bracket',
        'CubicAnomaly.Fixed.E8Adjoint.e8_adjointEquiv_val',
        'CubicAnomaly.Fixed.E8Adjoint.e8_adjoint_irreducible',
        'CubicAnomaly.Fixed.E8Adjoint.e8_bracketMatrixMap_injective',
        'CubicAnomaly.Fixed.E8Adjoint.e8_bracketMatrixMap_mem',
        'CubicAnomaly.Fixed.E8Adjoint.e8_bracketMatrixMap_mulVec',
        'CubicAnomaly.Fixed.E8Adjoint.e8_bracketMatrixMap_range',
        'CubicAnomaly.Fixed.E8Adjoint.e8_candidateBracket_basis',
        'CubicAnomaly.Fixed.E8Adjoint.e8_candidateBracket_commutator',
        'CubicAnomaly.Fixed.E8Adjoint.e8_candidateBracket_labels',
        'CubicAnomaly.Fixed.E8Adjoint.e8_candidateBracket_realize',
        'CubicAnomaly.Fixed.E8Adjoint.e8_e_bracketMatrixMap_equivariance',
        'CubicAnomaly.Fixed.E8Adjoint.e8_e_bracketMatrixMap_image',
        'CubicAnomaly.Fixed.E8Adjoint.e8_f_bracketMatrixMap_equivariance',
        'CubicAnomaly.Fixed.E8Adjoint.e8_f_bracketMatrixMap_image',
        'CubicAnomaly.Fixed.E8Adjoint.e8_h_bracketMatrixMap_equivariance',
        'CubicAnomaly.Fixed.E8Adjoint.e8_h_bracketMatrixMap_image',
        'CubicAnomaly.Fixed.E8Adjoint.e8_lieAlgebra_finrank',
        'CubicAnomaly.Fixed.E8Adjoint.e8_lieAlgebra_isSimple',
        'CubicAnomaly.Fixed.E8Adjoints.e8_root_string_coefficients',
        'CubicAnomaly.Fixed.E8Adjoints.geck_cartan_weighted_adjoint',
        'CubicAnomaly.Fixed.E8Adjoints.geck_lowering_weighted_adjoint',
        'CubicAnomaly.Fixed.E8Adjoints.geck_raising_weighted_adjoint',
        'CubicAnomaly.Fixed.E8Adjoints.root_add_sub_exclusive',
        'CubicAnomaly.Fixed.E8Adjoints.simple_gram_apply',
        'CubicAnomaly.Fixed.E8BracketBinding.bracket_data_generator_derivations',
        'CubicAnomaly.Fixed.E8BracketBinding.bracket_data_generator_images',
        'CubicAnomaly.Fixed.E8BracketBinding.bracket_data_generators_supported',
        'CubicAnomaly.Fixed.E8BracketBinding.bracket_data_isRoot_iff',
        'CubicAnomaly.Fixed.E8BracketBinding.bracket_data_isRoot_iff_coordinates',
        'CubicAnomaly.Fixed.E8BracketBinding.bracket_data_negative_simple_mem_basis',
        'CubicAnomaly.Fixed.E8BracketBinding.bracket_data_root_binding',
        'CubicAnomaly.Fixed.E8BracketBinding.bracket_data_root_mem_iff',
        'CubicAnomaly.Fixed.E8BracketBinding.bracket_data_simple_mem_basis',
        'CubicAnomaly.Fixed.E8BracketBinding.bracket_data_supported',
        'CubicAnomaly.Fixed.E8BracketData.bracket_data_generator_derivation_certificate',
        'CubicAnomaly.Fixed.E8BracketData.bracket_data_generator_image_certificate',
        'CubicAnomaly.Fixed.E8BracketData.bracket_data_sign_certificate',
        'CubicAnomaly.Fixed.E8BracketData.bracket_data_support_certificate',
        'CubicAnomaly.Fixed.E8ClassicalEmbedding.e8_a4_a2_matrices_commute',
        'CubicAnomaly.Fixed.E8ClassicalEmbedding.e8_a4_a2_units_commute',
        'CubicAnomaly.Fixed.E8ClassicalEmbedding.e8_classicalEmbedding_injective',
        'CubicAnomaly.Fixed.E8ClassicalEmbedding.e8_family_recovery_a4',
        'CubicAnomaly.Fixed.E8ClassicalEmbedding.e8_family_recovery_a4_unit',
        'CubicAnomaly.Fixed.E8ClassicalEmbedding.e8_gaugeFamilyEmbedding_injective',
        'CubicAnomaly.Fixed.E8ClassicalEmbedding.e8_gaugeFamilyEmbedding_mem_zero',
        'CubicAnomaly.Fixed.E8ClassicalEmbedding.e8_gaugeFamilyZeroEmbedding_injective',
        'CubicAnomaly.Fixed.E8Compact.e8_compact_complexification_tmul',
        'CubicAnomaly.Fixed.E8Compact.e8_compact_form_trace',
        'CubicAnomaly.Fixed.E8Compact.e8_compact_real_finiteDimensional',
        'CubicAnomaly.Fixed.E8Compact.e8_operator_adjoint_closed',
        'CubicAnomaly.Fixed.E8Geck.base_card',
        'CubicAnomaly.Fixed.E8Geck.cartanSubalgebra_abelian',
        'CubicAnomaly.Fixed.E8Geck.cartan_generator_mem',
        'CubicAnomaly.Fixed.E8Geck.defining_space_finrank',
        'CubicAnomaly.Fixed.E8Geck.defining_space_irreducible',
        'CubicAnomaly.Fixed.E8Geck.lieAlgebra_finiteDimensional',
        'CubicAnomaly.Fixed.E8Geck.lieAlgebra_hasTrivialRadical',
        'CubicAnomaly.Fixed.E8Geck.lowering_generator_mem',
        'CubicAnomaly.Fixed.E8Geck.raising_generator_mem',
        'CubicAnomaly.Fixed.E8Geck.root_card',
        'CubicAnomaly.Fixed.E8GeneratorCoordinates.e8_e_coordinate_formula',
        'CubicAnomaly.Fixed.E8GeneratorCoordinates.e8_f_coordinate_formula',
        'CubicAnomaly.Fixed.E8GeneratorCoordinates.e8_h_coordinate_formula',
        'CubicAnomaly.Fixed.E8GeneratorCoordinates.e8_negative_simple_coordinates',
        'CubicAnomaly.Fixed.E8GeneratorCoordinates.e8_pairingIn_coordinates',
        'CubicAnomaly.Fixed.E8GeneratorMatching.geck_e_realize_basis',
        'CubicAnomaly.Fixed.E8GeneratorMatching.geck_f_realize_basis',
        'CubicAnomaly.Fixed.E8GeneratorMatching.geck_h_realize_basis',
        'CubicAnomaly.Fixed.E8Grading.e8_actual_bracket_graded',
        'CubicAnomaly.Fixed.E8Grading.e8_actual_grade_decomposition',
        'CubicAnomaly.Fixed.E8Grading.e8_basisVector_homogeneous',
        'CubicAnomaly.Fixed.E8Grading.e8_bilinear_map_graded',
        'CubicAnomaly.Fixed.E8Grading.e8_complementary_module_dimensions',
        'CubicAnomaly.Fixed.E8Grading.e8_gradeModule_finrank',
        'CubicAnomaly.Fixed.E8Grading.e8_gradeProjection_homogeneous',
        'CubicAnomaly.Fixed.E8Grading.e8_gradeSpace_dimensions',
        'CubicAnomaly.Fixed.E8Grading.e8_gradeSpace_disjoint',
        'CubicAnomaly.Fixed.E8Grading.e8_gradeSpace_finrank',
        'CubicAnomaly.Fixed.E8Grading.e8_grade_decomposition',
        'CubicAnomaly.Fixed.E8Grading.e8_grade_module_invariant',
        'CubicAnomaly.Fixed.E8Grading.e8_realize_homogeneous',
        'CubicAnomaly.Fixed.E8Grading.e8_transferred_bracket_graded',
        'CubicAnomaly.Fixed.E8Grading.e8_transferred_grade_finrank',
        'CubicAnomaly.Fixed.E8Grading.e8_zeroSubalgebra_finrank',
        'CubicAnomaly.Fixed.E8GradingData.e8_grading_card_certificate',
        'CubicAnomaly.Fixed.E8GradingData.e8_zero_root_decomposition_certificate',
        'CubicAnomaly.Fixed.E8Matter.e8_actual_coordinates_action',
        'CubicAnomaly.Fixed.E8Matter.e8_actual_matrix_representation_eq',
        'CubicAnomaly.Fixed.E8Matter.e8_actual_matter_action',
        'CubicAnomaly.Fixed.E8Matter.e8_actual_matter_family_cubic_witness',
        'CubicAnomaly.Fixed.E8Matter.e8_actual_matter_finrank',
        'CubicAnomaly.Fixed.E8Matter.e8_actual_matter_full_cubic',
        'CubicAnomaly.Fixed.E8Matter.e8_actual_matter_gauge_insertion_zero',
        'CubicAnomaly.Fixed.E8Matter.e8_actual_matter_linear_trace',
        'CubicAnomaly.Fixed.E8Matter.e8_actual_matter_not_self_dual',
        'CubicAnomaly.Fixed.E8Matter.e8_actual_matter_radical_eq_gauge_ideal',
        'CubicAnomaly.Fixed.E8Matter.e8_actual_matter_radical_ne_bot',
        'CubicAnomaly.Fixed.E8Matter.e8_actual_matter_sm_action',
        'CubicAnomaly.Fixed.E8Matter.e8_actual_matter_sm_three_families_self_dual_remainder',
        'CubicAnomaly.Fixed.E8MatterData.e8_matter_a4_unit_match_certificate',
        'CubicAnomaly.Fixed.E8MatterData.e8_matter_basis_sign_sq',
        'CubicAnomaly.Fixed.E8MatterData.e8_matter_family_unit_match_certificate',
        'CubicAnomaly.Fixed.E8MatterData.e8_matter_label_grade',
        'CubicAnomaly.Fixed.E8MatterData.e8_matter_label_mem_basis',
        'CubicAnomaly.Fixed.E8MatterData.e8_matter_label_mem_grade',
        'CubicAnomaly.Fixed.E8MatterData.e8_matter_labels_exact',
        'CubicAnomaly.Fixed.E8MatterData.e8_matter_labels_injective',
        'CubicAnomaly.Fixed.E8MatterData.e8_matter_rootLabel_injective',
        'CubicAnomaly.Fixed.E8MatterMatching.e8_actualMatterEquiv_action',
        'CubicAnomaly.Fixed.E8MatterMatching.e8_actualMatterEquiv_val',
        'CubicAnomaly.Fixed.E8MatterMatching.e8_actual_matter_coordinates_action',
        'CubicAnomaly.Fixed.E8MatterMatching.e8_family_vector_action',
        'CubicAnomaly.Fixed.E8MatterMatching.e8_five_vector_action',
        'CubicAnomaly.Fixed.E8MatterMatching.e8_matter_family_action',
        'CubicAnomaly.Fixed.E8MatterMatching.e8_matter_full_action',
        'CubicAnomaly.Fixed.E8MatterMatching.e8_matter_gauge_action',
        'CubicAnomaly.Fixed.E8MatterRealization.e8_matrixColumnData_realize',
        'CubicAnomaly.Fixed.E8MatterRealization.e8_matterCoordinateEquiv_val',
        'CubicAnomaly.Fixed.E8MatterRealization.e8_matterCoordinateMap_apply',
        'CubicAnomaly.Fixed.E8MatterRealization.e8_matterCoordinateMap_homogeneous',
        'CubicAnomaly.Fixed.E8MatterRealization.e8_matterCoordinateMap_injective',
        'CubicAnomaly.Fixed.E8MatterRealization.e8_matterCoordinateMap_single',
        'CubicAnomaly.Fixed.E8MatterRealization.e8_matter_a4_basis_action',
        'CubicAnomaly.Fixed.E8MatterRealization.e8_matter_a4_unit_action',
        'CubicAnomaly.Fixed.E8MatterRealization.e8_matter_family_basis_action',
        'CubicAnomaly.Fixed.E8MatterRealization.e8_matter_family_unit_action',
        'CubicAnomaly.Fixed.E8Metric.gramMatrix_hermitian',
        'CubicAnomaly.Fixed.E8Metric.gramMatrix_isUnit',
        'CubicAnomaly.Fixed.E8Metric.gramMatrix_posDef',
        'CubicAnomaly.Fixed.E8RootPairing.coordinateRoots_card',
        'CubicAnomaly.Fixed.E8RootPairing.coordinateRoots_norm_two',
        'CubicAnomaly.Fixed.E8RootPairing.coordinateRoots_reflection_closed',
        'CubicAnomaly.Fixed.E8RootPairing.coordinateRoots_sign',
        'CubicAnomaly.Fixed.E8RootPairing.coordinate_certificate',
        'CubicAnomaly.Fixed.E8RootPairing.form_simpleRoots',
        'CubicAnomaly.Fixed.E8RootPairing.invariant_subspace_eq_top',
        'CubicAnomaly.Fixed.E8RootPairing.rootPairing_coroot',
        'CubicAnomaly.Fixed.E8RootPairing.rootPairing_pairing',
        'CubicAnomaly.Fixed.E8RootPairing.rootPairing_root',
        'CubicAnomaly.Fixed.E8RootPairing.rootVector_simpleRoot',
        'CubicAnomaly.Fixed.E8RootPairing.root_mem_or_neg_mem_simpleCone',
        'CubicAnomaly.Fixed.E8RootPairing.simpleBase_cartanMatrix',
        'CubicAnomaly.Fixed.E8RootPairing.simpleBase_unsigned_cartan_det_ne_zero',
        'CubicAnomaly.Fixed.E8RootPairing.simpleIndex_bijective',
        'CubicAnomaly.Fixed.E8RootPairing.simpleRoot_injective',
        'CubicAnomaly.Fixed.E8RootPairing.simpleRoots_mem',
        'CubicAnomaly.Fixed.E8RootPairing.simpleSupport_coe',
        'CubicAnomaly.Fixed.E8RootPairing.simpleSupport_image',
        'CubicAnomaly.Fixed.E8RootPairing.simpleSupport_independent',
        'CubicAnomaly.Fixed.E8RootPairing.span_rootVector_eq_top',
        'CubicAnomaly.Fixed.E8SparseModel.e8_basisVector_dataIndex',
        'CubicAnomaly.Fixed.E8SparseModel.e8_dataIndex_injective',
        'CubicAnomaly.Fixed.E8SparseModel.e8_dataIndex_mem_basisList',
        'CubicAnomaly.Fixed.E8SparseModel.e8_mem_basisList_iff',
        'CubicAnomaly.Fixed.E8SparseModel.e8_realize_append',
        'CubicAnomaly.Fixed.E8SparseModel.e8_realize_apply',
        'CubicAnomaly.Fixed.E8SparseModel.e8_realize_eq_of_sparseEq',
        'CubicAnomaly.Fixed.E8SparseModel.e8_realize_scale',
        'CubicAnomaly.Fixed.E8SparseModel.e8_realize_singleton',
        'CubicAnomaly.Fixed.E8Structure.e8_compact_dimension_eq',
        'CubicAnomaly.Fixed.E8Structure.e8_compact_finrank',
        'CubicAnomaly.Fixed.E8Structure.e8_compact_isSimple',
    }
)

EXPORTED_THEOREMS = NATIVE_THEOREMS | KERNEL_THEOREMS | CERTIFICATE_DERIVED_THEOREMS
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
    return sorted(name for name, count in Counter(values).items() if count > 1)


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
    if (NATIVE_THEOREMS & KERNEL_THEOREMS
            or NATIVE_THEOREMS & CERTIFICATE_DERIVED_THEOREMS
            or KERNEL_THEOREMS & CERTIFICATE_DERIVED_THEOREMS):
        failures.append("A theorem cannot belong to multiple trust classes")
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
        elif target in CERTIFICATE_DERIVED_THEOREMS and found != CERTIFICATE_DERIVED_AXIOMS:
            failures.append(
                f"{target}: certificate-derived receipt differs from the exact set: "
                f"missing={sorted(CERTIFICATE_DERIVED_AXIOMS - found)}, "
                f"unexpected={sorted(found - CERTIFICATE_DERIVED_AXIOMS)}"
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
    derived = sorted(CERTIFICATE_DERIVED_THEOREMS)

    def receipt(target: str, axioms: set[str]) -> str:
        if not axioms:
            return f"'{target}' does not depend on any axioms"
        return f"'{target}' depends on axioms: [{', '.join(sorted(axioms))}]"

    lines = {
        target: receipt(target,
                        NATIVE_AXIOMS if target in NATIVE_THEOREMS else
                        CERTIFICATE_DERIVED_AXIOMS if target in CERTIFICATE_DERIVED_THEOREMS else
                        KERNEL_AXIOMS)
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
        changed[native[0]] = receipt(native[0], CERTIFICATE_DERIVED_AXIOMS)
        check("choice dependency in original native profile", list(changed.values()), True)
    for target in derived:
        for missing in CERTIFICATE_DERIVED_AXIOMS:
            changed = dict(lines)
            changed[target] = receipt(target, CERTIFICATE_DERIVED_AXIOMS - {missing})
            check(f"missing {missing} in certificate-derived {target}", list(changed.values()), True)
        for unexpected in ("sorryAx", "Project.unprovedClassification"):
            changed = dict(lines)
            changed[target] = receipt(target, CERTIFICATE_DERIVED_AXIOMS | {unexpected})
            check(f"unexpected {unexpected} in certificate-derived {target}", list(changed.values()), True)
    if kernel:
        for target in kernel:
            changed = dict(lines)
            changed[target] = receipt(target, set())
            check(f"axiom-free {target}", list(changed.values()), False)
            changed[target] = receipt(target, KERNEL_AXIOMS | {"Lean.trustCompiler"})
            check(f"compiler dependency in {target}", list(changed.values()), True)
            changed[target] = receipt(target, KERNEL_AXIOMS | {"sorryAx"})
            check(f"unfinished proof in {target}", list(changed.values()), True)
    print("PASS  named axiom receipts and separate native/deductive/certificate-derived trust classes")
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
    print(f"PASS  {len(CERTIFICATE_DERIVED_THEOREMS)} exact certificate-derived receipts: "
          + ", ".join(sorted(CERTIFICATE_DERIVED_AXIOMS)))
    return 0


if __name__ == "__main__":
    raise SystemExit(self_tests() if sys.argv[1:] == ["--self-test"] else main())
