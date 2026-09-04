/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Papers.He2022Classic

/-! Kernel and trust-boundary audit for He's classic paper entry. -/

#check Bong.Lattice.IsClassicIntegral
#check Bong.Lattice.IsClassicNUniversal
#check Bong.Lattice.IsClassicMaximal
#check Bong.Lattice.exists_classicMaximal_superlattice
#check Bong.Lattice.RepresentsAllClassicMaximalOfRank
#check Bong.Lattice.heClassicMaximalTestingReduction
#check Bong.BONG.GoodBONG.HeClassicEvenConditions
#check Bong.BONG.GoodBONG.HeClassicOddConditions
#check Bong.BONG.GoodBONG.HeClassicTheorem11Conditions
#check Bong.BONG.GoodBONG.HeClassicTheorem11Statement
#check Bong.BONG.GoodBONG.he2022ClassicProposition22
#check Bong.BONG.GoodBONG.he2022ClassicProposition23
#check Bong.BONG.GoodBONG.he2022ClassicProposition24
#check Bong.BONG.GoodBONG.he2022ClassicTheorem25
#check Bong.heClassicEvenH
#check Bong.heClassicEvenC1
#check Bong.heClassicEvenC2
#check Bong.heClassicOddC1
#check Bong.heClassicOddC2Odd
#check Bong.heClassicOddC2Even
#check Bong.heClassicEvenC1GoodBONG
#check Bong.heClassicEvenC2GoodBONG
#check Bong.heClassicOddC1GoodBONG
#check Bong.heClassicOddC2OddGoodBONG
#check Bong.heClassicOddC2EvenGoodBONG
#check Bong.heClassicEvenHGoodBONG
#check Bong.heClassicEvenC1_isClassicIntegral
#check Bong.heClassicEvenC2_isClassicIntegral
#check Bong.heClassicOddC1_isClassicIntegral
#check Bong.heClassicOddC2Odd_isClassicIntegral
#check Bong.heClassicOddC2Even_isClassicIntegral
#check Bong.heClassicEvenH_isClassicIntegral
#check Bong.BONG.GoodBONG.he2022ClassicLemma29iii_alpha
#check Bong.BONG.GoodBONG.he2022ClassicLemma29iii_alpha_of_zero_orders
#check Bong.heClassicEvenC1_alpha_eq_one
#check Bong.heClassicEvenC2_alpha_eq_one
#check Bong.heClassicOddC1_alpha_eq_one
#check Bong.heClassicOddC2Odd_alpha_eq_one
#check Bong.heClassicOddC2Even_alpha_eq_one
#check Bong.he2022ClassicProposition210
#check Bong.he2022ClassicProposition210_anisotropic
#check Bong.HeClassicDefectOneIndex
#check Bong.HeClassicExceptionalIndex
#check Bong.HeClassicPublishedEvenTestingIndex
#check Bong.HeClassicPublishedOddTestingIndex
#check Bong.HeClassicPublishedCountingLaws
#check Bong.card_heClassicExceptionalIndex
#check Bong.card_heClassicPublishedEvenTestingIndex
#check Bong.he2022ClassicProposition28ii_even_gt_one
#check Bong.he2022ClassicProposition28ii_even_eq_one
#check Bong.he2022ClassicProposition28ii_odd
#check Bong.HeClassicOmegaData
#check Bong.heClassicOmega
#check Bong.heClassicOmega_value
#check Bong.heClassicOmega_order
#check Bong.heClassicOmega_quadraticDefect
#check Bong.heClassicOmega_defect
#check Bong.heClassicOmegaSharp
#check Bong.heClassicOmegaSharp_value
#check Bong.heClassicOmegaSharp_order
#check Bong.heClassicCanonicalOmegaData
#check Bong.HeClassicPublishedEvenTestingIndex.model
#check Bong.HeClassicPublishedEvenTestingIndex.model_rank
#check Bong.HeClassicPublishedEvenTestingIndex.model_isClassicIntegral
#check Bong.HeClassicPublishedOddTestingIndex.model
#check Bong.HeClassicPublishedOddTestingIndex.model_rank
#check Bong.HeClassicPublishedOddTestingIndex.model_isClassicIntegral
#check Bong.heClassicRamifiedBinary
#check Bong.heClassicRamifiedBinary_determinant_order
#check Bong.heClassicRamifiedSnoc_anisotropic
#check Bong.heClassicHyperbolicPair_represents_iff_isotropic
#check Bong.heClassicRamifiedBinary_represents_iff_anisotropic
#check Bong.he2022ClassicLemma211i_ternary
#check Bong.he2022ClassicLemma211ii_ternary
#check Bong.he2022ClassicLemma211iii_ternary
#check Bong.heClassicLemma211First
#check Bong.heClassicLemma211Second
#check Bong.he2022ClassicLemma211i
#check Bong.he2022ClassicLemma211ii
#check Bong.he2022ClassicLemma211iii
#check Bong.BONG.GoodBONG.HeClassicOrderConditionAt
#check Bong.BONG.GoodBONG.HeClassicDefectConditionAt
#check Bong.BONG.GoodBONG.HeClassicCentralConditionAt
#check Bong.BONG.GoodBONG.HeClassicLongConditionAt
#check Bong.BONG.GoodBONG.heClassicOrderCondition_iff_forall_at
#check Bong.BONG.GoodBONG.heClassicDefectCondition_iff_forall_at
#check Bong.BONG.GoodBONG.heClassicCentralConditions_iff_forall_at
#check Bong.BONG.GoodBONG.heClassicLongConditions_iff_forall_at
#check Bong.BONG.GoodBONG.he2022ClassicLemma31i
#check Bong.BONG.GoodBONG.he2022ClassicLemma31ii
#check Bong.BONG.GoodBONG.he2022ClassicLemma31iii
#check Bong.BONG.GoodBONG.he2022ClassicLemma31iv_corrected
#check Bong.BONG.GoodBONG.he2022ClassicLemma31v
#check Bong.BONG.GoodBONG.HeClassicCurrentEssentialAt
#check Bong.BONG.GoodBONG.HeClassicNextEssentialAt
#check Bong.BONG.GoodBONG.representationDefectAt_of_not_heClassicEssential
#check Bong.BONG.GoodBONG.he2022ClassicLemma32
#check Bong.BONG.GoodBONG.he2022ClassicLemma33
#check Bong.BONG.GoodBONG.he2022ClassicLemma34
#check Bong.BONG.GoodBONG.he2022ClassicLemma35
#check Bong.BONG.GoodBONG.he2022ClassicLemma36LongSource
#check Bong.BONG.GoodBONG.he2022ClassicLemma36DefectConditionLongSource
#check Bong.BONG.GoodBONG.he2022ClassicLemma36
#check Bong.BONG.GoodBONG.he2022ClassicLemma36DefectCondition

#print Bong.BONG.GoodBONG.HeClassicTheorem11Statement
#print axioms Bong.Lattice.exists_classicMaximal_superlattice
#print axioms Bong.Lattice.heClassicMaximalTestingReduction
#print axioms Bong.BONG.GoodBONG.he2022ClassicProposition22
#print axioms Bong.BONG.GoodBONG.he2022ClassicProposition23
#print axioms Bong.BONG.GoodBONG.he2022ClassicProposition24
#print axioms Bong.BONG.GoodBONG.he2022ClassicTheorem25
#print axioms Bong.heClassicEvenC1GoodBONG
#print axioms Bong.heClassicEvenC2GoodBONG
#print axioms Bong.heClassicOddC1GoodBONG
#print axioms Bong.heClassicOddC2OddGoodBONG
#print axioms Bong.heClassicOddC2EvenGoodBONG
#print axioms Bong.heClassicEvenHGoodBONG
#print axioms Bong.BONG.GoodBONG.he2022ClassicLemma29iii_alpha
#print axioms Bong.BONG.GoodBONG.he2022ClassicLemma29iii_alpha_of_zero_orders
#print axioms Bong.heClassicEvenC1_alpha_eq_one
#print axioms Bong.heClassicEvenC2_alpha_eq_one
#print axioms Bong.heClassicOddC1_alpha_eq_one
#print axioms Bong.heClassicOddC2Odd_alpha_eq_one
#print axioms Bong.heClassicOddC2Even_alpha_eq_one
#print axioms Bong.he2022ClassicProposition210
#print axioms Bong.card_heClassicPublishedEvenTestingIndex
#print axioms Bong.he2022ClassicProposition28ii_even_gt_one
#print axioms Bong.he2022ClassicProposition28ii_even_eq_one
#print axioms Bong.he2022ClassicProposition28ii_odd
#print axioms Bong.heClassicOmega_quadraticDefect
#print axioms Bong.heClassicCanonicalOmegaData
#print axioms Bong.HeClassicPublishedEvenTestingIndex.model_isClassicIntegral
#print axioms Bong.HeClassicPublishedOddTestingIndex.model_isClassicIntegral
#print axioms Bong.heClassicRamifiedBinary_determinant_order
#print axioms Bong.heClassicRamifiedSnoc_anisotropic
#print axioms Bong.heClassicHyperbolicPair_represents_iff_isotropic
#print axioms Bong.heClassicRamifiedBinary_represents_iff_anisotropic
#print axioms Bong.he2022ClassicLemma211i
#print axioms Bong.he2022ClassicLemma211ii
#print axioms Bong.he2022ClassicLemma211iii
#print axioms Bong.BONG.GoodBONG.he2022ClassicLemma31i
#print axioms Bong.BONG.GoodBONG.he2022ClassicLemma31ii
#print axioms Bong.BONG.GoodBONG.he2022ClassicLemma31iii
#print axioms Bong.BONG.GoodBONG.he2022ClassicLemma31iv_corrected
#print axioms Bong.BONG.GoodBONG.he2022ClassicLemma31v
#print axioms Bong.BONG.GoodBONG.representationDefectAt_of_not_heClassicEssential
#print axioms Bong.BONG.GoodBONG.he2022ClassicLemma32
#print axioms Bong.BONG.GoodBONG.he2022ClassicLemma33
#print axioms Bong.BONG.GoodBONG.he2022ClassicLemma34
#print axioms Bong.BONG.GoodBONG.he2022ClassicLemma35
#print axioms Bong.BONG.GoodBONG.he2022ClassicLemma36LongSource
#print axioms Bong.BONG.GoodBONG.he2022ClassicLemma36DefectConditionLongSource
#print axioms Bong.BONG.GoodBONG.he2022ClassicLemma36
#print axioms Bong.BONG.GoodBONG.he2022ClassicLemma36DefectCondition
