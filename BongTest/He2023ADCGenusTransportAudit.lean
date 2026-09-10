/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.He2023ADCSectionEight

/-!
# Audit: He (2025), genus and local-equivalence transport

This focused audit checks that genus symmetry and preservation of global
rank are derived from the paper's placewise local-equivalence definition,
local equivalence symmetry, local-rank invariance, and localization of rank.
-/

#check Bong.HeADC2025GlobalData.GenusTransportLaws
#check Bong.HeADC2025GlobalData.GenusTransportLaws.inGenus_symm
#check Bong.HeADC2025GlobalData.GenusTransportLaws.localEquivalent_of_inGenus
#check Bong.HeADC2025GlobalData.GenusTransportLaws.rank_eq_of_inGenus
#check Bong.HeADC2025GlobalData.SectionEightLaws.isIsometric_symm
#check Bong.HeADC2025GlobalData.SectionEightLaws.inGenus_symm
#check Bong.HeADC2025GlobalData.SectionEightLaws.localEquivalent_of_inGenus
#check Bong.HeADC2025GlobalData.SectionEightLaws.rank_eq_of_inGenus
#check Bong.HeADC2025GlobalData.SectionEightLaws.local_represents_of_equivalent_target
#check Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Corollary83
#check Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Theorem17

#print axioms Bong.HeADC2025GlobalData.GenusTransportLaws.inGenus_symm
#print axioms Bong.HeADC2025GlobalData.GenusTransportLaws.localEquivalent_of_inGenus
#print axioms Bong.HeADC2025GlobalData.GenusTransportLaws.rank_eq_of_inGenus
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.isIsometric_symm
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.inGenus_symm
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.localEquivalent_of_inGenus
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.rank_eq_of_inGenus
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.local_represents_of_equivalent_target
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Corollary83
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Theorem17
