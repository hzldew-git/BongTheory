/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.He2023ADCDyadicLocalModel

/-!
# Audit: He (2025), concrete dyadic local maximality model

This audit checks the actual one-place dyadic lattice instance behind the
local maximality derivation.  The intermediate constructor isolates the
rank-`n+1` classification necessity; the final instance discharges it by the
proved even/odd classification theorems.
-/

#check Bong.He2023ADCDyadicLocalModel.system
#check Bong.He2023ADCDyadicLocalModel.isNADCAt_iff_isNADC
#check Bong.He2023ADCDyadicLocalModel.exists_oMaximal_extension
#check Bong.He2023ADCDyadicLocalModel.oMaximal_represents_of_ambient
#check Bong.He2023ADCDyadicLocalModel.represents_trans
#check Bong.He2023ADCDyadicLocalModel.localMaximalityLaws_of_rank_succ_necessity
#check Bong.He2023ADCDyadicLocalModel.rank_succ_nADC_implies_oMaximal
#check Bong.He2023ADCDyadicLocalModel.localMaximalityLaws
#check Bong.He2023ADCDyadicLocalModel.local_theorem15
#check Bong.He2023ADCDyadicLocalModel.local_theorem15_of_rank_succ_necessity

#print axioms Bong.He2023ADCDyadicLocalModel.isNADCAt_iff_isNADC
#print axioms Bong.He2023ADCDyadicLocalModel.exists_oMaximal_extension
#print axioms Bong.He2023ADCDyadicLocalModel.oMaximal_represents_of_ambient
#print axioms Bong.He2023ADCDyadicLocalModel.represents_trans
#print axioms
  Bong.He2023ADCDyadicLocalModel.localMaximalityLaws_of_rank_succ_necessity
#print axioms Bong.He2023ADCDyadicLocalModel.rank_succ_nADC_implies_oMaximal
#print axioms Bong.He2023ADCDyadicLocalModel.localMaximalityLaws
#print axioms Bong.He2023ADCDyadicLocalModel.local_theorem15
#print axioms
  Bong.He2023ADCDyadicLocalModel.local_theorem15_of_rank_succ_necessity
