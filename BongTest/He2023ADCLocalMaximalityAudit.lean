/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.He2023ADCSectionEight

/-!
# Audit: He (2025), local maximality and Theorem 1.5(i)

This focused audit exposes the lower maximal-extension interface and prints
the transitive axiom sets of the derived maximal-implies-ADC theorem, the
local Theorem 1.5 equivalence, and their Section 8 compatibility endpoints.
-/

#check Bong.HeADC2025GlobalData.LocalMaximalityLaws
#check Bong.HeADC2025GlobalData.LocalMaximalityLaws.localMaximal_isNADCAt
#check Bong.HeADC2025GlobalData.LocalMaximalityLaws.local_theorem15
#check Bong.HeADC2025GlobalData.SectionEightLaws.localMaximal_isNADCAt
#check Bong.HeADC2025GlobalData.SectionEightLaws.local_theorem15
#check Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Lemma81ii
#check Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Theorem15i
#check Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Theorem15ii

#print axioms Bong.HeADC2025GlobalData.LocalMaximalityLaws.localMaximal_isNADCAt
#print axioms Bong.HeADC2025GlobalData.LocalMaximalityLaws.local_theorem15
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.localMaximal_isNADCAt
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.local_theorem15
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Lemma81ii
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Theorem15i
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Theorem15ii
