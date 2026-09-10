/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.He2023ADCSectionEight

/-!
# Audit: He (2025), Lemma 8.1 class-number-one regularity step

This focused audit exposes the lower-level genus-lifting interface and prints
the transitive axiom sets of both the derived regularity theorem and the
Section 8 compatibility endpoint.
-/

#check Bong.HeADC2025GlobalData.ClassNumberRegularityLaws
#check Bong.HeADC2025GlobalData.ClassNumberRegularityLaws.classNumberOne_implies_nRegular
#check Bong.HeADC2025GlobalData.SectionEightLaws.classNumberOne_implies_nRegular
#check Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Lemma81i

#print axioms Bong.HeADC2025GlobalData.ClassNumberRegularityLaws.classNumberOne_implies_nRegular
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.classNumberOne_implies_nRegular
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Lemma81i
