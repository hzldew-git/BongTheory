/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.He2023ADCScalingTransport

/-!
# Audit: He (2025), primitive scaling transport

This focused audit checks that the regularity-scaling biconditional used in
Lemma 8.4 and Corollary 8.5 is derived from lower transport facts rather than
stored as a finished premise.
-/

#check Bong.HeADC2025GlobalData.ScalingTransportLaws
#check Bong.HeADC2025GlobalData.ScalingTransportLaws.nRegular_scaleTwo_iff
#check Bong.HeADC2025GlobalData.ScalingTransportLaws.toScalingRegularityLaws

#print axioms Bong.HeADC2025GlobalData.ScalingTransportLaws.nRegular_scaleTwo_iff
#print axioms Bong.HeADC2025GlobalData.ScalingTransportLaws.toScalingRegularityLaws
