/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem

/-!
# Quaternary-complement audit

This test checks that the former quaternary-complement and codimension-two
trust boundaries are inferred from the concrete Hilbert/quaternion proof.
It also records the axioms used by the concrete instances and by the Beli
2019 endpoints after those parameters have been removed.
-/

namespace BongTest

open Bong Bong.Dyadic

universe u

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example : DyadicQuaternaryComplementLaws K := inferInstance
example : DyadicDiagonalCodimensionTwoLaws K := inferInstance

#print axioms Bong.dyadicQuaternaryComplementLawsDirect
#print axioms Bong.dyadicDiagonalCodimensionTwoLawsProvedDirect
#print axioms Bong.beli2019Theorem21
#print axioms Bong.beli2019Theorem21_prime

end BongTest
