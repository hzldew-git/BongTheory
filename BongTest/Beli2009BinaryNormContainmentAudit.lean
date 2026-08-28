/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019MainTheorem

/-!
# Beli 2009 binary norm-containment audit

This test checks that the former binary containment interface is inferred
from the Hilbert-symbol laws and that its proof introduces no nonstandard
axioms into the Beli 2019 endpoints.
-/

namespace BongTest

open Bong Bong.Dyadic

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K] [HilbertSymbolLaws K]

example : Beli2009BinaryNormContainmentLaws (K := K) := inferInstance

#print axioms Bong.principalUnitValuationClassSubgroup_le_quadraticNorm_of_defect_sum_gt
#print axioms Bong.two_mul_e_lt_parameterDefect_add_highExponent
#print axioms Bong.beli2009BinaryNormContainmentLawsProved
#print axioms Bong.beli2019Theorem21
#print axioms Bong.beli2019Theorem21_prime

end BongTest
