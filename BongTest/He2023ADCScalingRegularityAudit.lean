/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.He2023ADCSectionEight

/-!
# Audit: He (2025), regularity under scaling

This focused audit checks the exact scaling biconditional and half-scale
orientation used to derive the remaining scaling steps in Lemma 8.4 and
Corollary 8.5.
-/

#check Bong.HeADC2025GlobalData.ScalingRegularityLaws
#check Bong.HeADC2025GlobalData.ScalingRegularityLaws.nRegular_scaleTwo
#check Bong.HeADC2025GlobalData.ScalingRegularityLaws.scaleTwo_halfScale
#check Bong.HeADC2025GlobalData.ScalingRegularityLaws.nRegular_of_halfScale
#check Bong.HeADC2025GlobalData.SectionEightLaws.nRegular_scaleTwo
#check Bong.HeADC2025GlobalData.SectionEightLaws.scaleTwo_halfScale
#check Bong.HeADC2025GlobalData.SectionEightLaws.nRegular_of_halfScale
#check Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Lemma84
#check Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Corollary85

#print axioms Bong.HeADC2025GlobalData.ScalingRegularityLaws.nRegular_scaleTwo
#print axioms Bong.HeADC2025GlobalData.ScalingRegularityLaws.scaleTwo_halfScale
#print axioms Bong.HeADC2025GlobalData.ScalingRegularityLaws.nRegular_of_halfScale
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.nRegular_scaleTwo
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.scaleTwo_halfScale
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.nRegular_of_halfScale
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Lemma84
#print axioms Bong.HeADC2025GlobalData.SectionEightLaws.heADC2025Corollary85
