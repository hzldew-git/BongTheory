/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.He2023ADCSectionEight

/-!
# Audit: He (2025), Theorem 8.2 distinguishing sublattice

This focused audit exposes the definite Meyer and indefinite Xu--O'Meara
inputs, then prints the transitive axiom sets of the derived Theorem 8.2 and
its principal downstream consequences.
-/

#check Bong.HeADC2025GlobalData.DistinguishingSublatticeLaws
#check Bong.HeADC2025GlobalData.DistinguishingSublatticeLaws.distinguishing_rank_sublattice
#check Bong.HeADC2025GlobalData.SectionEightLaws.distinguishing_rank_sublattice
#check Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Theorem82
#check Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Corollary83
#check Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Theorem17

#print axioms Bong.HeADC2025GlobalData.DistinguishingSublatticeLaws.distinguishing_rank_sublattice
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.distinguishing_rank_sublattice
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Theorem82
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Corollary83
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Theorem17
