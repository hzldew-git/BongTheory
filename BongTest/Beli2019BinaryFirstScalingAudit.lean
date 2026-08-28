/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem

/-!
# Beli 2019 binary first-scaling audit

This test checks that the former rank-two local scaling interface is inferred
from the proved quadratic-defect laws and that the construction introduces no
nonstandard axioms into the Beli 2019 endpoints.
-/

namespace BongTest

open Bong Bong.Dyadic

universe u v

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K] [QuadraticDefectLaws K]

example : DyadicBinaryFirstScalingLaws.{u, v} K := inferInstance

#print axioms Bong.dyadicBinaryFirstScalingLawsProved
#print axioms Bong.BONG.GoodBONG.binaryFirstScaled_diagonalRepresents
#print axioms Bong.BONG.GoodBONG.binaryFirstScaled_alphaValue_eq
#print axioms Bong.beli2019Theorem21
#print axioms Bong.beli2019Theorem21_prime

end BongTest
