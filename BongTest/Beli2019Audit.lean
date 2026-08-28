/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem
import Bong.Bong.Beli2019FinalStep
import Bong.Bong.Beli2019Lemma912SectionNine
import Bong.Bong.Beli2019Lemma81
import Bong.Bong.Beli2019Lemma82
import Bong.Bong.Beli2019Lemma82Unit
import Bong.Bong.Beli2019Lemma84
import Bong.Bong.Beli2019Lemma85
import Bong.Bong.Beli2019Lemma86
import Bong.Bong.Beli2019Remark87
import Bong.Bong.Beli2019Lemma88Statement
import Bong.Bong.Beli2019Lemma88Necessity
import Bong.Bong.Beli2019Lemma83
import Bong.Bong.Beli2019Lemma88Binary
import Bong.Bong.Beli2019Lemma88Tail
import Bong.Bong.Beli2019Lemma88Choice
import Bong.Bong.Beli2019Lemma88Induction
import Bong.Bong.Beli2019Lemma88Critical
import Bong.Bong.Beli2019Lemma88Quaternary
import Bong.Bong.Beli2019Lemma88ExceptionA
import Bong.Bong.Beli2019Lemma88Sufficiency
import Bong.Bong.Beli2019Corollary810
import Bong.Bong.Beli2019Corollary811
import Bong.Bong.Beli2019Lemma812
import Bong.Bong.Beli2019Lemma813
import Bong.Bong.Beli2019Lemma814Statement
import Bong.Bong.Beli2019Lemma814Invariants
import Bong.Bong.Beli2019Lemma814GeometricInvariants
import Bong.Bong.Beli2019Lemma814ComplementInvariants
import Bong.Bong.Beli2019Lemma814Necessity
import Bong.Bong.Beli2019Lemma814Complete
import Bong.Bong.Beli2019Lemma91OrderBranches
import Bong.Bong.Beli2019Lemma91SecondOrder
import Bong.Bong.Beli2019Lemma91ExceptionA
import Bong.Bong.Beli2019Lemma91ExceptionB
import Bong.Bong.Beli2019Lemma91ExceptionC
import Bong.Bong.Beli2019Lemma91
import Bong.Bong.Beli2019Lemma710SegmentDual
import Bong.Bong.Beli2019Lemma79Conditions
import Bong.Bong.Beli2019Lemma79OrderTypeIAssembled
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapOrderComplete
import Bong.Bong.Beli2019Lemma79OrderTypeIIINonterminal
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIIComplete
import Bong.Bong.Beli2019Lemma69CappedPropagationRight
import Bong.Bong.Beli2019FullRankDefect
import Bong.Bong.Beli2019Lemma69TypeIRightComplete
import Bong.Bong.Beli2019Lemma77TypeINonterminal
import Bong.Bong.Beli2019Lemma78Arithmetic
import Bong.Bong.Beli2019DefectDual
import Bong.Bong.Beli2019RepresentationAlphaDual
import Bong.Bong.Beli2019DefectConditionDual
import Bong.Bong.Beli2019OrderConditionDual
import Bong.Bong.Beli2019Lemma78Dual
import Bong.Bong.Beli2019Lemma78Defect
import Bong.Bong.Beli2019Lemma69TypeIIISecondary
import Bong.Bong.Beli2019Lemma69TypeIIIPrimary
import Bong.Bong.Beli2019Lemma78AlphaZero
import Bong.Bong.Beli2019CappedDefectSharp
import Bong.Bong.Beli2019Lemma78PrefixDefect
import Bong.Bong.Beli2019Lemma78TailBound
import Bong.Bong.Beli2019Lemma78SourcePropagation
import Bong.Bong.Beli2019Lemma78TargetAlpha
import Bong.Bong.Beli2019Remark616
import Bong.Bong.Beli2019Lemma78PreviousAlpha
import Bong.Bong.Beli2019Lemma69TypeIIILeftValue
import Bong.Bong.Beli2019Lemma69TypeIIIRightValue
import Bong.Bong.Beli2019Lemma78TargetPropagation
import Bong.Bong.Beli2019Lemma71Index
import Bong.Bong.Beli2019Lemma73
import Bong.Bong.Beli2019Lemma75Splitting
import Bong.Bong.Beli2019Lemma75EndpointClass
import Bong.Bong.Beli2019Lemma75Models
import Bong.Bong.Beli2019Lemma75StandardModels
import Bong.Bong.Beli2019Lemma75
import Bong.Bong.Beli2019Lemma76Early
import Bong.Bong.Beli2019Lemma710Extension
import Bong.Bong.Beli2019Lemma710Orders
import Bong.Bong.Beli2019Lemma710OrthogonalSum
import Bong.Bong.Beli2019Lemma710ProjectionProduct
import Bong.Bong.Beli2019Lemma710BONGProduct
import Bong.Bong.Beli2019Lemma710PrefixProduct
import Bong.Bong.Beli2019Lemma710RightEnd
import Bong.Lattice.DualIsometry
import Bong.Lattice.OrthogonalDecompositionDual
import Bong.Bong.MaximalNormSplittingDual
import Bong.Bong.Beli2019Lemma710DualProduct
import Bong.Bong.Beli2019Lemma710Swap
import Bong.Bong.Beli2019Lemma710General
import Bong.Bong.Beli2019Lemma710TargetPrefix
import Bong.Bong.Beli2019Lemma711
import Bong.Bong.Beli2019Lemma76Boundary
import Bong.Bong.Beli2019Lemma76CanonicalBoundary
import Bong.Bong.Beli2019Lemma69TypeIWeight
import Bong.Bong.Beli2019IntervalRigidity
import Bong.Bong.Beli2019Lemma69TypeIInterval
import Bong.Bong.Beli2019WeightSegmentSum
import Bong.Bong.Beli2019Lemma69TypeISum
import Bong.Bong.Beli2019BoundaryRounding
import Bong.Bong.Beli2019Lemma69TypeIBoundary
import Bong.Bong.Beli2019Lemma69TypeINeighbor
import Bong.Bong.Beli2019Lemma69TypeIRightNeighbor
import Bong.Bong.Beli2019Lemma69TypeIPivot
import Bong.Bong.Beli2019Lemma69TypeIAlphaTail
import Bong.Bong.Beli2019Lemma714Plateau
import Bong.Bong.Beli2019Lemma714Types
import Bong.Bong.Beli2019Lemma714BoundaryOrders
import Bong.Bong.Beli2019Lemma66
import Bong.Bong.Beli2019Lemma65
import Bong.Bong.Beli2019Lemma67Classification
import Bong.Bong.Beli2019Lemma72TypeI
import Bong.Bong.Beli2019Lemma72TypeII
import Bong.Bong.Beli2019Lemma72TypeIII

/-!
# Beli 2019 v2 public-theorem axiom audit

This file checks the final Section 5--9 assembly and both formulations of
Theorem 2.1.  The expected kernel dependencies are only Lean's standard
logical axioms: `propext`, `Classical.choice`, and `Quot.sound`.
-/

-- Lemmas 5.13 and 5.17
#print axioms Bong.BONG.GoodBONG.representationDefectCondition_of_lemma513
#print axioms Bong.BONG.GoodBONG.Beli2019Lemma517Data.commonBound_of_leftCap
#print axioms Bong.BONG.GoodBONG.exists_goodBONG_with_ambientPrefix_of_lemma517

-- Sections 5--6
#print axioms Bong.BONG.GoodBONG.Beli2019SectionFiveDefectData.defectCondition
#print axioms Bong.BONG.GoodBONG.Beli2019SectionFiveData.representationConditions
#print axioms Bong.BONG.GoodBONG.Beli2019SectionFiveData.representationConditionsPrime

-- Sections 4--6, necessity
#print axioms Bong.BONG.GoodBONG.representationAlpha_self_le_alpha
#print axioms Bong.BONG.GoodBONG.representationConditions_self
#print axioms Bong.BONG.GoodBONG.representationConditions_sameLattice
#print axioms Bong.BONG.GoodBONG.representationOrderCondition_changeBONG_iff
#print axioms Bong.BONG.GoodBONG.representationDefectCondition_changeBONG_iff
#print axioms Bong.BONG.GoodBONG.centralAdjustedAlpha_invariant
#print axioms Bong.BONG.GoodBONG.centralAlphaTrigger_changeBONG_iff
#print axioms Bong.BONG.GoodBONG.longRepresentationTrigger_changeBONG_iff
#print axioms Bong.BONG.diagonalRepresents_values
#print axioms Bong.BONG.GoodBONG.fullPrefix_represents
#print axioms Bong.BONG.GoodBONG.isSpaceApproximation_prefixValueUnits
#print axioms Bong.BONG.GoodBONG.spaceApproximationRepresentationBridge_prefixValueUnits
#print axioms Bong.BONG.GoodBONG.isSpaceApproximation_prefixValueUnits_of_bridge
#print axioms Bong.EvenTruthParity.second_iff_third_of_first_fourth
#print axioms Bong.EvenTruthParity.first_iff_third_of_second_fourth
#print axioms Bong.hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
#print axioms Bong.BONG.GoodBONG.leftApproximationTrigger_of_prefixCaps
#print axioms Bong.BONG.GoodBONG.rightApproximationTrigger_of_prefixCaps
#print axioms Bong.BONG.GoodBONG.alpha_eq_min_halfGap_add_cappedAdjacent
#print axioms Bong.BONG.GoodBONG.truncatedPrefixDefect_triangle_alternative
#print axioms Bong.withTop_alpha_sum_alternative
#print axioms Bong.BONG.GoodBONG.beli2019Lemma218_target
#print axioms Bong.BONG.GoodBONG.beli2019Lemma218_source
#print axioms Bong.BONG.GoodBONG.centralTarget_iff_of_lemma218
#print axioms Bong.BONG.GoodBONG.centralSource_iff_of_lemma218
#print axioms Bong.DiagonalRepresents.symm_of_sameRank
#print axioms Bong.isSquare_of_two_mul_e_lt_defectOrder
#print axioms Bong.BONG.GoodBONG.longTarget_iff_of_cancellation
#print axioms Bong.BONG.GoodBONG.longSource_iff_of_cancellation
#print axioms Bong.BONG.GoodBONG.centralPrefix_change_of_approximation
#print axioms Bong.BONG.GoodBONG.longPrefix_change_of_approximation
#print axioms Bong.BONG.GoodBONG.representationConditions_changeBONG_iff
#print axioms Bong.BONG.GoodBONG.Beli2019PrimeChainCertificate.representationConditions
#print axioms Bong.Lattice.indexPChain_of_le
#print axioms Bong.Lattice.IndexPChain.representationConditions
#print axioms Bong.BONG.GoodBONG.representationConditions_of_lattice_le
#print axioms Bong.RepresentationConditions.toPrime
#print axioms Bong.exists_goodBONGSameRankIntegralImageData
#print axioms Bong.BONG.GoodBONG.representationConditionsPrime_of_scalarAgreement
#print axioms Bong.BONG.GoodBONG.representationConditionsPrime_of_prefixAgreement

-- Sections 7--9, sufficiency
#print axioms Bong.Lattice.mem_nonNormGeneratorLattice_iff
#print axioms Bong.Lattice.exists_sub_smul_mem_nonNormGeneratorLattice
#print axioms Bong.Lattice.IndexPGeneratorCertificate.toBeli2019IndexPInclusion
#print axioms Bong.BONG.GoodBONG.Beli2019Lemma71Data.indexPInclusion
#print axioms Bong.BONG.GoodBONG.beli2019Lemma73_step
#print axioms Bong.BONG.GoodBONG.beli2019Lemma73_i
#print axioms Bong.BONG.GoodBONG.beli2019Lemma73_ii
#print axioms Bong.BONG.GoodBONG.order_sub_add_alpha_le_cappedAdjacent
#print axioms Bong.BONG.GoodBONG.truncatedPrefixDefect_alternating_ge
#print axioms Bong.BONG.GoodBONG.beli2019Lemma74_i
#print axioms Bong.BONG.GoodBONG.beli2019Lemma74_ii
#print axioms Bong.BONG.GoodBONG.beli2019Lemma74_iii
#print axioms Bong.BONG.GoodBONG.beli2019Lemma75_arithmetic
#print axioms Bong.BONG.GoodBONG.beli2019Lemma75_pairBlock_split
#print axioms Bong.BONG.GoodBONG.beli2019Lemma75_betweenPair_split
#print axioms Bong.BONG.adjacentUnitSquareClass_endpoint_cases
#print axioms Bong.BONG.GoodBONG.beli2019Lemma75_pairBlock_endpointClass
#print axioms Bong.BONG.normalizedBinaryModel_isIsometric
#print axioms Bong.BONG.rescaledBinaryModel_isIsometric_mul_valuationUnit_square
#print axioms Bong.BONG.endpointModel_cases
#print axioms Bong.BONG.GoodBONG.beli2019Lemma75_pairBlock_modelCases
#print axioms Bong.BONG.rescaledBinaryModel_isIsometric_of_shear_sub_integral
#print axioms Bong.BONG.endpointStandardModel_cases
#print axioms Bong.BONG.standardEndpointModelSpace_isIsometric_binaryDiagonal
#print axioms Bong.BONG.GoodBONG.beli2019Lemma75_pairBlock_standardModelCases
#print axioms Bong.BONG.GoodBONG.beli2019Lemma75_pairBlock_geometricCases
#print axioms Bong.BONG.GoodBONG.beli2019Lemma75
#print axioms Bong.BONG.GoodBONG.beli2019Lemma76_early_of_canonical
#print axioms Bong.BONG.GoodBONG.beli2019Lemma76_boundary_of_canonical
#print axioms Bong.BONG.GoodBONG.beli2019Lemma711
#print axioms Bong.BONG.GoodBONG.alternatingPrefixDefect_boundary_cases
#print axioms Bong.BONG.GoodBONG.lemma76_leftSwitch_skip
#print axioms Bong.BONG.GoodBONG.lemma76_leftSwitch_gap_odd
#print axioms Bong.BONG.GoodBONG.beli2019Lemma76_switch_of_alpha_le_one
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_i_typeI_leftSwitch
#print axioms Bong.BONG.GoodBONG.beli2019Lemma76_typeI
#print axioms Bong.BONG.GoodBONG.beli2019Lemma77_of_nonpositive
#print axioms Bong.BONG.GoodBONG.beli2019Lemma77_of_plateau
#print axioms Bong.BONG.GoodBONG.lemma77_typeI_source_plateau
#print axioms Bong.BONG.GoodBONG.beli2019Lemma77_typeI_of_alpha_ge_two
#print axioms Bong.BONG.GoodBONG.lemma69_v_typeI_order_gap_two
#print axioms Bong.BONG.GoodBONG.lemma69_v_typeI_alpha_ge_two_of_leftEndpoint_eq
#print axioms Bong.BONG.GoodBONG.beli2019Lemma77_typeI_of_leftEndpoint_eq
#print axioms Bong.BeliOrderLE.segmentSequence_eq_of_segmentSum_eq
#print axioms Bong.BeliOrderLE.entryOrZero_eq_of_segmentSum_eq
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_v_typeI_of_interval
#print axioms Bong.BONG.GoodBONG.beli2019Lemma77_typeI_of_weightInterval
#print axioms Bong.BONG.GoodBONG.weightSequence_entryPair
#print axioms Bong.BONG.GoodBONG.weightSegmentSum_eq_of_adjacentOrderSums
#print axioms Bong.BONG.GoodBONG.lemma69_v_typeI_adjacent_entry_sum_eq
#print axioms Bong.BONG.GoodBONG.lemma69_v_typeI_weightSegmentSum_eq
#print axioms Bong.BONG.GoodBONG.beli2019Lemma77_typeI_of_weightBoundaries
#print axioms Bong.IsRationalInteger.le_of_le_add_half
#print axioms Bong.BeliOrderLE.entryOrZero_le_of_previous_le_add_half
#print axioms Bong.BeliOrderLE.entryOrZero_le_of_next_le_add_half
#print axioms Bong.BONG.GoodBONG.lemma69_v_typeI_interval_orderGap_even
#print axioms Bong.BONG.GoodBONG.lemma69_v_typeI_even_weight_integral
#print axioms Bong.BONG.GoodBONG.lemma69_v_typeI_leftBoundary_of_previous
#print axioms Bong.BONG.GoodBONG.lemma69_v_typeI_rightBoundary_of_next
#print axioms Bong.BONG.GoodBONG.beli2019Lemma77_typeI_of_neighborBounds
#print axioms Bong.BONG.GoodBONG.oddWeightCoordinate_le_currentOrder_add_half
#print axioms Bong.BONG.GoodBONG.lemma69_v_typeI_previous_target_order
#print axioms Bong.BONG.GoodBONG.lemma69_v_typeI_previousAlpha_eq_one_of_le_one
#print axioms Bong.BONG.GoodBONG.lemma69_v_typeI_leftNeighbor_of_previousAlpha_le_one
#print axioms Bong.BONG.GoodBONG.nextOrder_le_evenWeightCoordinate_add_half
#print axioms Bong.BONG.GoodBONG.lemma69_v_typeI_rightSwitch_skip
#print axioms Bong.BONG.GoodBONG.lemma69_v_typeI_next_source_target_order
#print axioms Bong.BONG.GoodBONG.lemma69_v_typeI_nextTargetAlpha_eq_one_of_le_one
#print axioms Bong.BONG.GoodBONG.lemma69_v_typeI_rightNeighbor_of_nextAlpha_le_one
#print axioms Bong.BONG.GoodBONG.lemma69_i_typeI_leftPivotData
#print axioms Bong.BONG.GoodBONG.lemma69_i_typeI_leftTailAlpha_le_of_pivot
#print axioms Bong.BONG.GoodBONG.lemma69_i_typeI_previousAlpha_le_of_pivot
#print axioms Bong.BONG.GoodBONG.lemma69_v_typeI_leftNeighbor_of_pivotAlpha_le_one
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_i_typeI_pivotAlpha
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_i_typeI_sourceLeftTail
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_i_typeI_targetLeftTail
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_i_typeI_leftTail
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_v_typeI_leftNeighbor
#print axioms Bong.BONG.GoodBONG.lemma69_i_typeI_rightPivotData
#print axioms Bong.BONG.GoodBONG.lemma69_i_typeI_rightTailAlpha_le_of_pivot
#print axioms Bong.BONG.GoodBONG.lemma69_i_typeI_nextTargetAlpha_le_of_pivot
#print axioms Bong.BONG.GoodBONG.alpha_le_laterOrder_sub_add_cappedAdjacent
#print axioms Bong.BONG.GoodBONG.truncatedPrefixDefect_full_eq_top
#print axioms Bong.BONG.GoodBONG.lemma69_typeI_rightOdd_orders
#print axioms Bong.BONG.GoodBONG.lemma69_i_typeI_rightPivot_prefixSum
#print axioms Bong.BONG.GoodBONG.lemma69_i_typeI_rightSourceLocal_gt_cutoff
#print axioms Bong.BONG.GoodBONG.lemma69_i_typeI_rightTargetLocal_gt_cutoff
#print axioms Bong.BONG.GoodBONG.lemma69_i_typeI_rightCommon_of_boundary
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma69_i_typeI_rightPivotAlpha_of_boundary_of_secondary_case
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_i_typeI_rightPivotAlpha_of_boundary
#print axioms Bong.BONG.GoodBONG.lemma69_i_typeI_rightPivot_secondary_pos_of_interior
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_i_typeI_rightPivotAlpha_of_boundary_of_interior
#print axioms Bong.BONG.GoodBONG.beli2019Lemma63_sameRank
#print axioms Bong.BONG.GoodBONG.beli2019Lemma63_sameRank_value
#print axioms Bong.BONG.GoodBONG.beli2019Lemma63_sameRank_right
#print axioms Bong.BONG.GoodBONG.beli2019Lemma63_sameRank_right_value
#print axioms Bong.BONG.GoodBONG.lemma69_i_typeI_rightBoundary_gt_cutoff
#print axioms Bong.BONG.GoodBONG.adjacentDefect_eq_zero_of_order_sum_odd
#print axioms Bong.BONG.GoodBONG.lemma69_i_typeI_rightPivotAlpha_of_secondary_of_endpoint
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_i_typeI_rightPivotAlpha
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_i_typeI_targetRightTail
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_i_typeI_nextTargetAlpha
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_v_typeI_rightNeighbor
#print axioms Bong.BONG.GoodBONG.beli2019Lemma77_typeI_of_rightSwitch_lt_last
#print axioms Bong.BONG.GoodBONG.lemma78_typeIII_initialGap_le_centralGap
#print axioms Bong.BONG.GoodBONG.lemma78_typeIII_centralGap_even
#print axioms Bong.BONG.GoodBONG.beli2019Lemma78_sourceAlpha_and_gap
#print axioms Bong.BONG.GoodBONG.defectOrder_inv
#print axioms Bong.BONG.GoodBONG.truncatedPrefixDefect_reverseDual_swap_general
#print axioms Bong.BONG.GoodBONG.truncatedPrefixDefect_reverseDual_swap
#print axioms Bong.BONG.GoodBONG.exists_reverseDualPair_with_truncatedPrefixDefect
#print axioms Bong.BONG.GoodBONG.representationAlpha_reverseDual_swap
#print axioms Bong.BONG.GoodBONG.representationAlphaValue_reverseDual_swap
#print axioms Bong.BONG.GoodBONG.representationDefectCondition_reverseDual_swap
#print axioms Bong.BeliOrderSequence.prefixGap_reverseNegate_swap
#print axioms Bong.BONG.GoodBONG.representationOrderCondition_reverseDual_swap
#print axioms Bong.BONG.GoodBONG.totalOrderSum_reverseDual_swap
#print axioms Bong.BONG.GoodBONG.orderPrefixGap_reverseDual_swap
#print axioms Bong.BeliOrderLE.exists_noGapTwoOuterConsequences_of_transition
#print axioms Bong.BONG.GoodBONG.exists_reverseDual_typeIII
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_i_typeIII_target
#print axioms Bong.BONG.GoodBONG.beli2019Lemma78_alphas_and_gap
#print axioms Bong.BONG.GoodBONG.representationAlpha_nonneg_of_candidates
#print axioms Bong.BONG.GoodBONG.representationPrimaryDefect_eq_zero_of_alphaValue_eq_zero
#print axioms Bong.BONG.GoodBONG.truncatedPrefixDefect_eq_neg_order_of_primary_eq_zero
#print axioms Bong.BONG.GoodBONG.truncatedPrefixDefect_eq_neg_order_of_alphaValue_eq_zero
#print axioms Bong.BONG.GoodBONG.representationSecondaryDefect_pos_of_orderCoefficient_pos
#print axioms Bong.BONG.GoodBONG.lemma78_typeIII_representationHalfGap_pos
#print axioms Bong.BONG.GoodBONG.beli2019Lemma78_centralMixedDefect
#print axioms Bong.BONG.GoodBONG.beli2019Lemma78_centralMixedDefect_of_alpha_zero
#print axioms Bong.BONG.GoodBONG.lemma69_typeIII_secondaryCoefficient_pos
#print axioms Bong.BONG.GoodBONG.lemma69_typeIII_primaryDefect_nonneg
#print axioms Bong.BONG.GoodBONG.beli2019Lemma78_representationAlpha_eq_zero
#print axioms Bong.BONG.GoodBONG.beli2019Lemma78_centralMixedDefect_exact
#print axioms Bong.BONG.GoodBONG.truncatedPrefixDefect_mul_eq_left_of_lt_right
#print axioms Bong.BONG.GoodBONG.truncatedPrefixDefect_zero_left_eq_self
#print axioms Bong.BONG.GoodBONG.truncatedPrefixDefect_zero_right_eq_self
#print axioms Bong.BONG.GoodBONG.lemma78_typeIII_targetPrefix_gt_mixedShift
#print axioms Bong.BONG.GoodBONG.beli2019Lemma78_firstSourcePrefixDefect
#print axioms Bong.BONG.GoodBONG.lemma78_typeIII_sourceRightPlateau
#print axioms Bong.BONG.GoodBONG.lemma78_typeIII_sourceTail_gt_mixedShift
#print axioms Bong.BONG.GoodBONG.beli2019Lemma78_sourcePrefixDefect
#print axioms Bong.BONG.GoodBONG.lemma78_typeIII_targetAlpha_ge_mixedShift
#print axioms Bong.BONG.GoodBONG.beli2019Remark616_rightPrefix
#print axioms
  Bong.BONG.GoodBONG.lemma78_typeIII_sourcePreviousAlpha_eq_one_of_center
#print axioms Bong.BONG.GoodBONG.lemma78_typeIII_sourcePreviousAlpha_eq_one
#print axioms Bong.BONG.GoodBONG.lemma78_typeIII_left_boundary_orders
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma69_ii_typeIII_sourceLeftValue_of_center
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_ii_typeIII_sourceLeftValue
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_ii_typeIII_targetRightValue
#print axioms Bong.BONG.GoodBONG.truncatedPrefixDefect_self_full_eq
#print axioms Bong.BONG.GoodBONG.beli2019Lemma78_targetPrefixDefect_of_lt_rank
#print axioms Bong.BONG.GoodBONG.beli2019Lemma78_targetPrefixDefect
#print axioms Bong.BONG.GoodBONG.beli2019Lemma78_typeIII
#print axioms Bong.BeliOrderLE.compare_of_source_bounds
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma79_orderCondition_of_type_interiors
#print axioms Bong.BONG.GoodBONG.beli2019Lemma79_i_typeI_middleOdd
#print axioms Bong.BONG.GoodBONG.beli2019Lemma79_i_typeIII_leftOuter
#print axioms Bong.BONG.GoodBONG.beli2019Lemma79_i_typeIII_rightAlternating
#print axioms Bong.BONG.GoodBONG.beli2019Lemma79_i_typeII
#print axioms Bong.BONG.GoodBONG.lemma79_typeIII_thirdPrefix_gt_mixedShift
#print axioms
  Bong.BONG.GoodBONG.lemma79_typeIII_comparisonPrefix_eq_mixedShift
#print axioms
  Bong.BONG.GoodBONG.representationDefectCandidate_le_of_alphaValue_le_of_lt_halfGap
#print axioms
  Bong.BONG.GoodBONG.lemma79_typeIII_mixedShift_lt_representationHalfGap
#print axioms
  Bong.BONG.GoodBONG.lemma79_typeIII_pair_of_primary_le_mixedShift
#print axioms
  Bong.BONG.GoodBONG.representationSecondarySourceAlpha_le_of_current_le_comparison
#print axioms Bong.BONG.GoodBONG.one_le_alphaValue_of_ne_zero
#print axioms
  Bong.BONG.GoodBONG.lemma79_typeIII_pair_of_sourceAlpha_le_mixedShift
#print axioms Bong.BONG.GoodBONG.lemma79_typeIII_interiorPair
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma79_i_typeIII_nonterminal
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma79_i_typeIII_overlap_terminal
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma79_i_typeIII_overlap_orderCondition
#print axioms
  Bong.BONG.GoodBONG.lemma79_typeI_even_primary_defect_core_of_sourcePrefix
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma79_i_typeI_terminalSwitch
#print axioms Bong.BONG.GoodBONG.beli2019Lemma79_i_typeI
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma79_i_typeI_orderCondition
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma79_typeIII_nonoverlap_even_beta_bound
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma79_typeIII_nonoverlap_odd_beta_bound
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma79_ii_typeIII_caseEight_gapOne
#print axioms Bong.Lattice.CommonNormGeneratorExtension.lattice_eq
#print axioms Bong.BONG.PrefixLatticeExtension.lattice_eq
#print axioms Bong.BONG.PrefixLatticeExtension.cons_lattice_eq
#print axioms
  Bong.BONG.GoodBONG.order_le_of_lt_cut_of_last_two_le
#print axioms Bong.BONG.GoodBONG.beli2019Lemma710_prefix_order_le
#print axioms Bong.Lattice.normIdeal_orthogonalProduct
#print axioms Bong.Lattice.IsNormGenerator.orthogonalProduct_left
#print axioms Bong.Lattice.IsNormGenerator.orthogonalProduct_right
#print axioms Bong.BONG.normIdeal_le_of_head_order_le
#print axioms Bong.BONG.head_order_le_of_normIdeal_le
#print axioms Bong.BONG.head_isNormGenerator_orthogonalProduct_left
#print axioms Bong.QuadraticSpace.IsAnisotropic.orthogonalSum_inl
#print axioms Bong.QuadraticSpace.orthogonalProjection_orthogonalSum_inl
#print axioms
  Bong.QuadraticSpace.orthogonalSpaceOrthogonalSumInlIsometry
#print axioms Bong.Lattice.map_projectedLattice_orthogonalProduct
#print axioms Bong.Lattice.projectedOrthogonalProductIsometry
#print axioms Bong.BONG.value_orthogonalProductRight_left
#print axioms Bong.BONG.value_orthogonalProductRight_right
#print axioms Bong.BONG.order_orthogonalProductRight_left
#print axioms Bong.BONG.order_orthogonalProductRight_right
#print axioms Bong.BONG.orthogonalProductBoundaryGood_of_endpoints
#print axioms Bong.BONG.isGood_orthogonalProductRight
#print axioms Bong.BONG.OrthogonalPrefixData.consOfHeadOrder
#print axioms Bong.BONG.OrthogonalPrefixData.steps_le_length
#print axioms Bong.BONG.OrthogonalPrefixData.value_result_left
#print axioms Bong.BONG.OrthogonalPrefixData.value_result_right
#print axioms Bong.BONG.OrthogonalPrefixData.ambientVector_result_left
#print axioms Bong.BONG.OrthogonalPrefixData.ambientVector_result_right
#print axioms Bong.BONG.OrthogonalPrefixData.lattice_eq_of_matching_vectors
#print axioms Bong.BONG.OrthogonalPrefixData.order_result_left
#print axioms Bong.BONG.OrthogonalPrefixData.order_result_right
#print axioms Bong.BONG.OrthogonalPrefixData.toGoodBONG
#print axioms Bong.BONG.OrthogonalPrefixSeed.stopOfLatticeIsometry
#print axioms Bong.BONG.OrthogonalPrefixSeed.stopOfSegmentWitness
#print axioms Bong.BONG.OrthogonalPrefixSeed.steps_le_length
#print axioms Bong.BONG.OrthogonalPrefixSeed.toData
#print axioms Bong.BONG.OrthogonalPrefixSeed.baseValue
#print axioms Bong.BONG.OrthogonalPrefixSeed.baseOrder
#print axioms Bong.BONG.OrthogonalPrefixSeed.baseAmbientVector
#print axioms Bong.BONG.OrthogonalPrefixSeed.quadratic_baseAmbientVector
#print axioms Bong.BONG.OrthogonalPrefixSeed.coe_baseOrder
#print axioms Bong.BONG.OrthogonalPrefixSeed.baseOrder_zero_le_right
#print axioms
  Bong.BONG.OrthogonalPrefixSeed.order_eq_baseOrder_of_ambientVector_eq
#print axioms Bong.BONG.OrthogonalPrefixSeed.baseValue_toData
#print axioms Bong.BONG.OrthogonalPrefixSeed.baseOrder_toData
#print axioms Bong.BONG.OrthogonalPrefixSeed.baseAmbientVector_toData
#print axioms Bong.BONG.OrthogonalPrefixSeed.value_result_left
#print axioms Bong.BONG.OrthogonalPrefixSeed.ambientVector_result_left
#print axioms Bong.BONG.OrthogonalPrefixSeed.ambientVector_result_right
#print axioms Bong.BONG.OrthogonalPrefixSeed.lattice_eq_of_matching_vectors
#print axioms Bong.BONG.OrthogonalPrefixSeed.order_result_left
#print axioms Bong.BONG.OrthogonalPrefixSeed.toGoodBONG
#print axioms Bong.BONG.GoodBONG.beli2019Lemma710RightEndData
#print axioms Bong.BONG.GoodBONG.beli2019Lemma710RightEnd
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma710_previous_order_le_right_of_good
#print axioms Bong.BONG.GoodBONG.beli2019Lemma710RightEnd_of_good
#print axioms Bong.BONG.GoodBONG.beli2019Lemma710RightEnd_all_of_good
#print axioms Bong.BONG.GoodBONG.beli2019Lemma710RightEnd_steps_of_good
#print axioms Bong.Lattice.Isometry.ofLatticeEq
#print axioms Bong.Lattice.Isometry.ofLatticeEq_apply
#print axioms Bong.Lattice.Isometry.dual
#print axioms Bong.Lattice.eq_of_dualLattice_eq
#print axioms Bong.Lattice.dualLattice_orthogonalProduct
#print axioms Bong.Lattice.dualOrthogonalProductIsometry
#print axioms
  Bong.BONG.GoodBONG.exists_reverseDualOrthogonalProduct_with_values
#print axioms Bong.BONG.GoodBONG.exists_reverseDualOrthogonalProduct
#print axioms Bong.BONG.GoodBONG.beli2019Lemma710DualRightEnd_all_of_good
#print axioms Bong.BONG.GoodBONG.beli2019Lemma710DualRightEnd_steps_of_good
#print axioms Bong.QuadraticSpace.orthogonalSumSwapIsometry
#print axioms Bong.Lattice.swapLattice
#print axioms Bong.Lattice.orthogonalSumSwapLatticeIsometry
#print axioms Bong.Lattice.swapLattice_product
#print axioms Bong.Lattice.eq_product_of_swapLattice_eq
#print axioms Bong.BONG.GoodBONG.exists_swappedReverseDual_with_values
#print axioms Bong.BONG.OrthogonalPrefixRawSeed.StopLatticeEq
#print axioms Bong.BONG.OrthogonalPrefixRawSeed.steps_le_length
#print axioms Bong.BONG.OrthogonalPrefixRawSeed.sourceIndex
#print axioms Bong.BONG.OrthogonalPrefixRawSeed.baseAmbientVector
#print axioms Bong.BONG.OrthogonalPrefixRawSeed.toSeed
#print axioms Bong.BONG.OrthogonalPrefixRawSeed.sourceIndex_toSeed
#print axioms Bong.BONG.OrthogonalPrefixRawSeed.baseAmbientVector_toSeed
#print axioms Bong.BONG.OrthogonalPrefixRawSeed.DualEndpointCertificate
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma710SwappedDualRightEnd_all_of_good
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma710SwappedDualRightEnd_steps_of_good
#print axioms
  Bong.BONG.GoodBONG.rawStopLatticeEq_of_swappedDualRightEnd_all_of_good
#print axioms Bong.BONG.GoodBONG.beli2019Lemma710General_of_tailIdentity
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.DualEndpointCertificate.tailIdentity
#print axioms Bong.BONG.GoodBONG.beli2019Lemma710General
#print axioms Bong.BONG.OrthogonalPrefixRawSeed.prefixSourceIndex
#print axioms Bong.BONG.OrthogonalPrefixRawSeed.TargetPrefixExtraction
#print axioms Bong.BONG.OrthogonalPrefixRawSeed.extractTargetPrefix
#print axioms Bong.BONG.OrthogonalPrefixRawSeed.ofTargetPrefix
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.baseAmbientVector_ofTargetPrefix
#print axioms Bong.BONG.OrthogonalPrefixRawSeed.StopDualEndpointData
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.dualEndpointCertificateOfStopData
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.DualEndpointCertificate.stopOfTargetPrefix
#print axioms
  Bong.BONG.swappedReverseDualVector_prefix_eq_of_suffixVectors
#print axioms
  Bong.BONG.swappedReverseDual_prefixVectors_of_suffixVectors
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.DualEndpointCertificate.stopOfSuffixVectors
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma710General_of_targetPrefix
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma710General_of_targetPrefixStop
#print axioms Bong.BONG.SegmentWitness.unmap
#print axioms Bong.BONG.SegmentWitness.unmapLatticeIsometry
#print axioms Bong.BONG.OrthogonalPrefixRawSeed.StopSegmentIsometry
#print axioms Bong.BONG.OrthogonalPrefixRawSeed.StopSegmentProductEq
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.stopLatticeEq_of_segmentProductEq
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.TargetPrefixSegmentExtraction
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.extractTargetPrefixSegment
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.TargetPrefixSegmentProductEq
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.stopLatticeEq_of_targetPrefixSegmentProductEq
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.DualEndpointCertificate.stopOfTargetPrefixSegmentProductEq
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.DualEndpointCertificate.stopOfSuffixVectorsSegmentProductEq
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma710General_of_targetPrefixSegmentProductEq
#print axioms Bong.Lattice.OrthogonalDecomposition.reverseDual
#print axioms Bong.Lattice.MaximalNormSplitting.reverseDual
#print axioms
  Bong.Lattice.MaximalNormSplitting.ambientVector_eq_reverseDualVector_of_putTogether
#print axioms Bong.BONG.GoodBONG.exists_reverseDual_of_beli
#print axioms Bong.bongReverseDualLawsOfBeli
#print axioms Bong.BONG.SegmentWitness.coe_reverseDualVector_prefix_eq
#print axioms
  Bong.BONG.SegmentWitness.reverseDualLatticeIsometry_apply_reverseDualVector
#print axioms Bong.Lattice.Isometry.map_reverseDualVector_of_ambientVector_eq
#print axioms Bong.Lattice.Isometry.orthogonalProduct
#print axioms Bong.Lattice.Isometry.swappedDualOrthogonalProduct_apply
#print axioms Bong.Lattice.Isometry.dualReplacementOrthogonalProduct
#print axioms Bong.Lattice.Isometry.dualReplacementOrthogonalProduct_apply
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.factorVectors_of_consecutiveBONGs
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.DualReplacementAtStop.ofBONGDiagram
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.DualReplacementAtStop.ofConsecutiveBONGDiagram
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.stopSegmentProductEq_of_segmentProductIsometry
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.TargetPrefixSegmentProductIsometryData.segmentProductEq
#print axioms
  Bong.BONG.OrthogonalPrefixRawSeed.targetPrefixSegmentProductIsometryDataOfDualReplacement
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma710General_of_targetPrefixSegmentProductIsometryData
#print axioms Bong.BONG.GoodBONG.beli2019Lemma714_i
#print axioms Bong.BONG.GoodBONG.beli2019Lemma714_type_dichotomy
#print axioms Bong.BONG.GoodBONG.lemma714_type_disjoint
#print axioms Bong.BONG.GoodBONG.lemma714_stopOrder_ge
#print axioms Bong.BONG.GoodBONG.lemma714_typeI_nextOrder_ge
#print axioms Bong.BONG.GoodBONG.lemma714_typeII_stopOrder_ge
#print axioms Bong.BONG.GoodBONG.beli2019Lemma66_i
#print axioms Bong.BONG.GoodBONG.beli2019Lemma66_ii
#print axioms Bong.BONG.GoodBONG.beli2019Lemma65
#print axioms Bong.BeliOrderLE.gapTwoAnchorConsequences
#print axioms Bong.BeliOrderLE.prefixGapTransitionConsequences
#print axioms Bong.BeliOrderLE.noGapTwoOuterConsequences
#print axioms Bong.BeliOrderLE.middle_eq_leftTarget_of_seed_of_cross
#print axioms Bong.BONG.GoodBONG.lemma65_cross_of_prefixGapTransition
#print axioms Bong.BONG.GoodBONG.middleSeed_eq_leftTarget
#print axioms Bong.BONG.GoodBONG.middle_order_eq_leftTarget
#print axioms Bong.BONG.GoodBONG.rightBoundarySource_eq_leftTarget
#print axioms Bong.BONG.GoodBONG.beli2019Lemma67
#print axioms Bong.BeliOrderSequence.prefixSum_modEq_add_mul_of_tail
#print axioms Bong.BONG.GoodBONG.lemma67TypeICanonicalData
#print axioms Bong.BONG.GoodBONG.entryOrZero_modEq_of_equal_even_endpoints
#print axioms Bong.BONG.GoodBONG.lemma611TypeI
#print axioms Bong.BONG.GoodBONG.lemma611TypeII
#print axioms Bong.BONG.GoodBONG.orderGap_le_one_of_alphaValue_le_one
#print axioms Bong.BONG.GoodBONG.lemma611TypeIII
#print axioms Bong.BONG.GoodBONG.alpha_le_order_sub_add_cappedAdjacent
#print axioms Bong.BONG.GoodBONG.beli2019Lemma69_i_typeIII
#print axioms Bong.BONG.GoodBONG.lemma611TypeIII_of_defect
#print axioms Bong.BONG.GoodBONG.beli2019Lemma72_i
#print axioms Bong.BONG.GoodBONG.beli2019Lemma72_ii
#print axioms Bong.BONG.GoodBONG.beli2019Lemma72_iii
#print axioms Bong.BONG.GoodBONG.beli2019Lemma72_iii_of_defect
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma79_ii_typeIII_pointwise_complete_local
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma79_normalizedClassification
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma79_ii_of_normalizedClassification
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma79_ii_of_fullSpanClassification
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma79_representationConditions
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma79_representationConditionsPrime
#print axioms Bong.QuadraticSpace.headExtensionIsometry
#print axioms
  Bong.QuadraticSpace.projectionToOrthogonal_headExtensionLinearEquiv
#print axioms
  Bong.Lattice.Representation.toQuadraticSpaceIsometryOfFinrankEq
#print axioms Bong.Beli2019SolvedHeadData.ofProjectedRepresentation
#print axioms Bong.Beli2019SolvedHeadData.represents_of_projected
#print axioms
  Bong.Beli2019RepresentationProblem.SolvedHead.represents
#print axioms
  Bong.Beli2019RepresentationProblem.solvedHead_of_projected
#print axioms
  Bong.BONG.GoodBONG.representationConditions_tail
#print axioms
  Bong.Beli2019RepresentationProblem.lemma93HeadReduction
#print axioms
  Bong.Beli2019RepresentationProblem.representationConditions_castIndices
#print axioms
  Bong.Beli2019RepresentationProblem.Lemma93Input.headReduction
#print axioms Bong.BONG.beli2019Lemma81_i
#print axioms Bong.BONG.beli2019Lemma81_ii_strict
#print axioms Bong.BONG.beli2019Lemma81_ii_iff
#print axioms Bong.BONG.beli2019Lemma82_i
#print axioms Bong.BONG.beli2019Lemma82_ii
#print axioms Bong.BONG.beli2019Lemma82_iii
#print axioms Bong.BONG.exists_valuationUnit_same_defect_same_hilbert
#print axioms Bong.BONG.beli2019Lemma82_ii_unit
#print axioms Bong.BONG.beli2019Lemma82_iii_unit
#print axioms Bong.BONG.GoodBONG.beli2019Lemma84_i_left
#print axioms Bong.BONG.GoodBONG.beli2019Lemma84_i_right
#print axioms Bong.BONG.GoodBONG.beli2019Lemma84_ii
#print axioms Bong.BONG.GoodBONG.beli2019Lemma84_iii
#print axioms Bong.BONG.GoodBONG.beli2019Lemma85_candidate_of_A
#print axioms Bong.BONG.GoodBONG.beli2019Lemma85_rawWitness
#print axioms Bong.BONG.GoodBONG.beli2019Lemma85_exists_leftBoundary
#print axioms Bong.BONG.GoodBONG.beli2019Lemma85_exists_rightBoundary
#print axioms Bong.BONG.GoodBONG.beli2019Lemma85
#print axioms
  Bong.Dyadic.hasNonnegativeAbsoluteQuadraticDefect_of_nonneg_add_defectOrder
#print axioms Bong.BONG.OrthogonalBasisData.beli2019Lemma86_i
#print axioms Bong.BONG.GoodBONG.beli2019Lemma86_adjacent
#print axioms Bong.BONG.GoodBONG.beli2019Lemma86_leftCandidate
#print axioms Bong.BONG.GoodBONG.beli2019Lemma86_rightCandidate
#print axioms Bong.BONG.GoodBONG.beli2019Lemma86_ii
#print axioms
  Bong.BONG.GoodBONG.adjacentDefect_eq_target_of_beli2019Lemma85C
#print axioms Bong.BONG.GoodBONG.beli2019Lemma86_iii
#print axioms Bong.BONG.GoodBONG.beli2019Remark87
#print axioms Bong.BONG.GoodBONG.determinantCompletion_represents_base
#print axioms
  Bong.BONG.GoodBONG.completedTernary_hilbertSymbol_ne_one_of_lemma88ExceptionC
#print axioms
  Bong.BONG.GoodBONG.firstComparisonDefect_lt_product_of_lemma88ExceptionC
#print axioms Bong.BONG.GoodBONG.Beli2019FirstValueTransform.not_exceptionC
#print axioms Bong.BONG.GoodBONG.beli2019Lemma88_necessity
#print axioms
  Bong.BONG.OrthogonalBasisData.alphaValue_eq_of_isRealizedBy
#print axioms
  Bong.BONG.GoodBONG.sameAlphas_of_quaternaryAlternating
#print axioms Bong.QuaternaryFirstScalingCertificate.exists_transformed
#print axioms Bong.BONG.GoodBONG.beli2019Lemma83
#print axioms Bong.BinaryFirstScalingCertificate.exists_transformed
#print axioms
  Bong.BONG.GoodBONG.firstValueTransform_of_firstBinaryAlpha
#print axioms
  Bong.BONG.GoodBONG.tailReplacementData_of_firstValueTransform
#print axioms
  Bong.BONG.GoodBONG.Beli2019TailReplacementData.firstBinaryAlpha_eq_of_strict_tail
#print axioms
  Bong.BONG.quadraticDefect_add_lt_twoE_of_defectOrder_add_lt_twoE
#print axioms
  Bong.BONG.exists_valuationUnit_same_defect_hilbert_one_of_defectOrder_add_ne_twoE
#print axioms Bong.BONG.GoodBONG.exists_firstAlphaUnit_of_lt_halfGap
#print axioms Bong.BONG.GoodBONG.beli2019Lemma88_strict_binary
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma88_halfGap_binary_of_notExceptional
#print axioms
  Bong.BONG.GoodBONG.suffixAlphaSegmentWitness_zero_scalarAgreement
#print axioms
  Bong.BONG.GoodBONG.alpha_zero_eq_min_firstBinary_orderGap_add_tailAlpha
#print axioms
  Bong.BONG.GoodBONG.firstBinaryAlpha_eq_alpha_of_adjacentDefect_le_tailAlpha
#print axioms
  Bong.BONG.GoodBONG.alpha_zero_eq_orderGap_add_tailAlpha_of_tailAlpha_lt_adjacentDefect
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma88_strict_of_adjacentDefect_le_tailAlpha
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma88_strict_tail_of_tailTransform
#print axioms
  Bong.BONG.GoodBONG.tailExceptionB_implies_exceptionC
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma88_critical_of_tailTransform
#print axioms
  Bong.BONG.GoodBONG.firstValueTransform_of_firstQuaternarySegment
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma88_critical_of_tailExceptionC
#print axioms
  Bong.BONG.GoodBONG.firstAlpha_eq_twoE_of_tailExceptionA
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma88_critical_of_tailExceptionA
#print axioms
  Bong.BONG.GoodBONG.tailAlpha_lt_halfGap_of_global_strict
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma88_rankTwo_sufficiency
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma88_sufficiency
#print axioms Bong.BONG.GoodBONG.beli2019Lemma88_i
#print axioms Bong.BONG.GoodBONG.beli2019Corollary810
#print axioms
  Bong.BONG.GoodBONG.alpha_eq_min_prefixSuffixSegmentAlpha
#print axioms Bong.BONG.GoodBONG.beli2019Corollary810_right
#print axioms Bong.BONG.GoodBONG.beli2019Corollary811
#print axioms
  Bong.BONG.GoodBONG.firstThirdCappedDefect_shift_le_firstAdjacent
#print axioms Bong.BONG.GoodBONG.beli2019Lemma812_i_prime
#print axioms Bong.BONG.GoodBONG.beli2019Lemma812_i
#print axioms Bong.BONG.GoodBONG.beli2019Lemma812_ii_prime
#print axioms Bong.BONG.GoodBONG.beli2019Lemma812_ii
#print axioms Bong.BONG.GoodBONG.beli2019Lemma812_ii_rankOne
#print axioms Bong.BONG.diagonalRepresents_of_ambient
#print axioms Bong.BONG.GoodBONG.lemma813_defectCondition_iff
#print axioms Bong.BONG.GoodBONG.lemma813_defectEquality_iff_raw
#print axioms Bong.BONG.GoodBONG.lemma813_centralCondition_iff
#print axioms Bong.BONG.GoodBONG.lemma813_longCondition_iff
#print axioms Bong.BONG.GoodBONG.representationConditions_iff_lemma813
#print axioms Bong.BONG.GoodBONG.beli2019Lemma813
#print axioms Bong.BONG.GoodBONG.Beli2019Lemma814Claim
#print axioms Bong.BONG.GoodBONG.Beli2019Lemma814Statement
#print axioms Bong.BONG.GoodBONG.Beli2019Lemma814ExplicitStatement
#print axioms Bong.BONG.GoodBONG.lemma814Statement_of_explicit
#print axioms
  Bong.BONG.GoodBONG.not_firstThreeIsotropic_iff_anisotropic
#print axioms Bong.BONG.GoodBONG.lemma814_exceptionA_not_exceptionB
#print axioms Bong.BONG.GoodBONG.not_lemma814ExceptionC_of_rank_three
#print axioms
  Bong.BONG.GoodBONG.lemma814FirstThirdCappedDefect_invariant
#print axioms
  Bong.BONG.GoodBONG.lemma814FirstFourCappedDefect_invariant
#print axioms
  Bong.BONG.GoodBONG.lemma814ThirdComplementaryDefect_invariant
#print axioms Bong.BONG.GoodBONG.lemma814Exceptional_changeBONG_iff
#print axioms
  Bong.BONG.GoodBONG.lemma814Exceptional_changeBONG_iff_rankThree
#print axioms
  Bong.BONG.GoodBONG.lemma814FirstFourComplementAnisotropic_changeBONG_iff_rankFour
#print axioms
  Bong.BONG.GoodBONG.lemma814ExceptionC_changeBONG_iff_rankFour
#print axioms
  Bong.diagonalUnitTernary_isotropic_iff_adjacentHilbertOne
#print axioms
  Bong.BONG.GoodBONG.lemma814FirstThreeIsotropic_changeBONG_iff_of_alphaSum
#print axioms
  Bong.BONG.GoodBONG.alphaTwo_add_alphaThree_strict_of_lemma814ExceptionA
#print axioms
  Bong.BONG.GoodBONG.lemma814FirstThreeIsotropic_changeBONG_iff_of_exceptionA
#print axioms
  Bong.BONG.GoodBONG.lemma814FirstThreeIsotropic_changeBONG_iff_of_exceptionB
#print axioms
  Bong.BONG.GoodBONG.lemma814ExceptionAB_changeBONG_iff_ge_four
#print axioms
  Bong.BONG.GoodBONG.prefixValueUnits_succ_eq_snoc
#print axioms Bong.diagonalHasse_extensionFactor_eq
#print axioms Bong.diagonalTernaryComplementAnisotropic_iff_of_hilbert
#print axioms Bong.diagonalQuaternary_hasComplement
#print axioms
  Bong.BONG.GoodBONG.lemma814ComplementResidual_hilbert_eq_one
#print axioms
  Bong.BONG.GoodBONG.lemma814FirstFourComplementAnisotropic_of_changeBONG_ge_five
#print axioms
  Bong.BONG.GoodBONG.lemma814ExceptionC_of_changeBONG_ge_five
#print axioms
  Bong.BONG.GoodBONG.lemma814ExceptionC_changeBONG_iff
#print axioms
  Bong.BONG.GoodBONG.adjacentDefect_zero_eq_secondAlpha_of_firstBinary
#print axioms
  Bong.BONG.GoodBONG.not_lemma814ExceptionA_of_firstValue_eq
#print axioms
  Bong.BONG.GoodBONG.not_lemma814ExceptionB_of_firstValue_eq_of_firstBinary
#print axioms
  Bong.BONG.GoodBONG.lemma814TailFirstThreeAnisotropic_of_firstValue_eq
#print axioms
  Bong.BONG.GoodBONG.not_lemma814ExceptionC_of_firstValue_eq_of_firstBinary
#print axioms
  Bong.BONG.GoodBONG.not_lemma814Exceptional_of_firstValue_eq
#print axioms Bong.BONG.GoodBONG.beli2019Lemma814_necessity
#print axioms Bong.BONG.GoodBONG.beli2019Lemma814_rankFour_alternating
#print axioms Bong.BONG.GoodBONG.beli2019Lemma814_rankFour_complete
#print axioms Bong.BONG.GoodBONG.beli2019Lemma814_higherRank_complete
#print axioms Bong.BONG.GoodBONG.beli2019Lemma814Explicit
#print axioms
  Bong.BONG.GoodBONG.not_lemma814Exceptional_of_firstThird_lt
#print axioms
  Bong.BONG.GoodBONG.not_lemma814Exceptional_of_secondFourth_eq
#print axioms
  Bong.BONG.GoodBONG.not_lemma814Exceptional_of_firstThirdDefect_eq_firstAlpha
#print axioms
  Bong.BONG.GoodBONG.lemma814FirstThirdCappedDefect_eq_firstAlpha_of_fullSource
#print axioms Bong.BONG.GoodBONG.firstUnarySegment_prefixProduct_one
#print axioms Bong.BONG.GoodBONG.firstUnarySegment_order_zero
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma91_of_fullSource_firstThirdDefect
#print axioms
  Bong.BONG.GoodBONG.lemma814Epsilon_firstAdjacent_hilbert_one_of_firstGap_eq_twoE
#print axioms Bong.BONG.GoodBONG.beli2019Lemma91_of_firstGap_eq_twoE
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma91_of_firstThird_lt_or_secondFourth_eq
#print axioms
  Bong.BONG.GoodBONG.firstAlpha_le_sourceFirstAlpha_of_representationConditions
#print axioms
  Bong.BONG.GoodBONG.fullFirstThirdDefect_eq_min_unary_sourceFirstAlpha
#print axioms
  Bong.BONG.GoodBONG.secondRepresentationAlpha_le_targetSecond_of_conditions
#print axioms
  Bong.BONG.GoodBONG.secondRepresentationAlpha_eq_targetSecond_and_sourceFirst_eq_targetFirst
#print axioms
  Bong.BONG.GoodBONG.fullFirstThirdDefect_eq_sourceFirstAlpha_of_exceptionBC
#print axioms Bong.BONG.GoodBONG.secondOrderRigidity_of_exceptionBC
#print axioms
  Bong.BONG.GoodBONG.sourceFirstAdjacent_firstThirdProduct_hilbert_one_of_exceptionA
#print axioms
  Bong.BONG.GoodBONG.not_lemma814ExceptionA_of_binaryPrefixRepresentation
#print axioms
  Bong.BONG.GoodBONG.not_lemma814ExceptionB_of_equalSecondOrder
#print axioms
  Bong.BONG.GoodBONG.not_lemma814ExceptionC_of_equalSecondOrder
#print axioms
  Bong.BONG.GoodBONG.lemma813Conditions_firstUnarySegment_of_representation
#print axioms Bong.BONG.GoodBONG.beli2019Lemma91_of_equalSecondOrder
#print axioms Bong.BONG.GoodBONG.beli2019Lemma91
#print axioms Bong.Beli2019RankVolumeMeasure.smaller_wellFounded
#print axioms Bong.Beli2019FinalStepData.sectionNine
#print axioms
  Bong.BONG.GoodBONG.exists_beli2019Lemma912_indexPReduction_of_sectionNineResidual
#print axioms
  Bong.BONG.GoodBONG.beli2019Lemma912_counterexampleDescent_of_sectionNineResidual
#print axioms Bong.Beli2019FinalStepData.descend
#print axioms Bong.Beli2019FinalStepData.not_counterexample
#print axioms Bong.Beli2019FinalStepData.represents
#print axioms Bong.beli2019_sufficiency_complete

-- Theorem 2.1
#print axioms Bong.beli2019_necessity
#print axioms Bong.beli2019Theorem21
#print axioms Bong.beli2019Theorem21_prime
