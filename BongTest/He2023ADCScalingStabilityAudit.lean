/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.He2023ADCSectionEight

/-!
# Audit: He (2025), Lemma 8.4 local stability deduction

This focused audit exposes the local normal-form, scaling, and placewise
stability inputs and prints the transitive axiom sets of the derived
stability conclusion and its downstream numbered results.
-/

#check Bong.HeADC2025GlobalData.ScalingStabilityLaws
#check Bong.HeADC2025GlobalData.ScalingStabilityLaws.locallyTwoADC_scaleTwo_stable
#check Bong.HeADC2025GlobalData.SectionEightLaws.locallyTwoADC_scaleTwo_stable
#check Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Lemma84
#check Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Corollary85

#print axioms Bong.HeADC2025GlobalData.ScalingStabilityLaws.locallyTwoADC_scaleTwo_stable
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.locallyTwoADC_scaleTwo_stable
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Lemma84
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Corollary85
