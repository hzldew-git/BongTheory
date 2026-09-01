/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Papers.Beli2020

/-! Kernel/trust smoke test for Beli 2020, *Universal integral quadratic forms over
dyadic local fields*. -/

open Bong.Lattice.JordanDecomposition

#check Bong.BONG.beliUniversalLemma22
#check Bong.beliUniversalLemma23
#check Bong.beliUniversalLemma24
#check Bong.BONG.GoodBONG.universalUnaryOrderConditions_iff_order_zero
#check Bong.BONG.GoodBONG.alphaValue_eq_one_consequences
#check Bong.BONG.GoodBONG.firstBinary_endpoint_signedProduct_cases
#check Bong.BONG.GoodBONG.UniversalTheorem21Conditions.isLineUniversal
#check Bong.BONG.GoodBONG.universalTheorem21Statement_iff_caseAnalysis
#check Bong.BONG.GoodBONG.universalUnaryDefectConditions_iff_alphaZero_or_caseIIPrime
#check Bong.BONG.GoodBONG.universalAllUnaryCentralConditions_iff_caseI
#check Bong.BONG.GoodBONG.universalAllUnaryCentralConditions_iff_caseII
#check Bong.BONG.GoodBONG.universalAllUnaryLongConditions_iff_caseI
#check Bong.BONG.GoodBONG.universalAllUnaryLongConditions_iff_caseII
#check Bong.BONG.GoodBONG.universalTheorem21CaseAnalysis_proved
#check Bong.BONG.GoodBONG.beliUniversalTheorem21
#check Bong.BONG.GoodBONG.isUniversal_iff_universalTheorem21Conditions
#check isUniversal_iff_universalTheorem31DirectConditions
#check isUniversal_iff_universalTheorem31Conditions_of_firstScaleOrder_eq_zero
#check Bong.Lattice.beliUniversalLemma41
#check Bong.Lattice.beliUniversalLemma42
#check Bong.Lattice.beliUniversalLemma43
#check Bong.Lattice.beliUniversalLemma44
#check Bong.Lattice.beliUniversalCorollary45i
#check Bong.Lattice.beliUniversalCorollary45ii
#check Bong.Lattice.beliUniversalCorollary45iii
#check Bong.Lattice.beliUniversalCorollary45iv
#check Bong.BONG.GoodBONG.beliUniversalLemma46
#check Bong.BONG.GoodBONG.beliUniversalLemma47
#check Bong.BONG.GoodBONG.beliUniversalLemma48
#check Bong.BONG.GoodBONG.beliUniversalLemma49
#check Bong.BONG.GoodBONG.beliUniversalCorollary410

#print axioms Bong.BONG.beliUniversalLemma22
#print axioms Bong.beliUniversalLemma23
#print axioms Bong.beliUniversalLemma24
#print axioms Bong.BONG.GoodBONG.alphaValue_eq_one_consequences
#print axioms Bong.BONG.GoodBONG.firstThree_isotropic_of_endpoint_order_two_zero
#print axioms Bong.BONG.GoodBONG.UniversalTheorem21Conditions.isLineUniversal
#print axioms Bong.BONG.GoodBONG.universalTheorem21Statement_iff_caseAnalysis
#print axioms Bong.BONG.GoodBONG.universalUnaryDefectConditions_iff_alphaZero_or_caseIIPrime
#print axioms Bong.BONG.GoodBONG.universalAllUnaryCentralConditions_iff_caseI
#print axioms Bong.BONG.GoodBONG.universalAllUnaryCentralConditions_iff_caseII
#print axioms Bong.BONG.GoodBONG.universalAllUnaryLongConditions_iff_caseI
#print axioms Bong.BONG.GoodBONG.universalAllUnaryLongConditions_iff_caseII
#print axioms Bong.BONG.GoodBONG.universalTheorem21CaseAnalysis_proved
#print axioms Bong.BONG.GoodBONG.beliUniversalTheorem21
#print axioms Bong.BONG.GoodBONG.isUniversal_iff_universalTheorem21Conditions
#print axioms isUniversal_iff_universalTheorem31DirectConditions
#print axioms isUniversal_iff_universalTheorem31Conditions_of_firstScaleOrder_eq_zero
#print axioms Bong.Lattice.beliUniversalLemma41
#print axioms Bong.Lattice.beliUniversalLemma42
#print axioms Bong.Lattice.beliUniversalLemma43
#print axioms Bong.Lattice.beliUniversalLemma44
#print axioms Bong.Lattice.beliUniversalCorollary45i
#print axioms Bong.Lattice.beliUniversalCorollary45ii
#print axioms Bong.Lattice.beliUniversalCorollary45iii
#print axioms Bong.Lattice.beliUniversalCorollary45iv
#print axioms Bong.BONG.GoodBONG.beliUniversalLemma46
#print axioms Bong.BONG.GoodBONG.beliUniversalLemma47
#print axioms Bong.BONG.GoodBONG.beliUniversalLemma48
#print axioms Bong.BONG.GoodBONG.beliUniversalLemma49
#print axioms Bong.BONG.GoodBONG.beliUniversalCorollary410

#print Bong.BONG.GoodBONG.UniversalTheorem21Statement
#print Bong.BONG.GoodBONG.UniversalTheorem21CaseAnalysisObligation
