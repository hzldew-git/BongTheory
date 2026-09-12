/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.He2023ADCSectionEight

/-!
# Audit: He (2025), O'Meara 82K global maximality

This focused audit checks the assembly of the global--local maximality
biconditional from its two directional arithmetic inputs and its downstream
uses in Lemma 8.1(ii), Theorem 1.5(ii), and Theorem 1.7.
-/

#check Bong.HeADC2025GlobalData.GlobalMaximalityLaws
#check Bong.HeADC2025GlobalData.GlobalMaximalityLaws.globalMaximal_iff_localMaximal
#check Bong.HeADC2025GlobalData.SectionEightLaws.globalMaximal_iff_localMaximal
#check Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Lemma81ii
#check Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Theorem15ii
#check Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Theorem17

#print axioms Bong.HeADC2025GlobalData.GlobalMaximalityLaws.globalMaximal_iff_localMaximal
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.globalMaximal_iff_localMaximal
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Lemma81ii
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Theorem15ii
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Theorem17
