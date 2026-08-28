/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalLocalClassificationProof

/-! Independent compilation and axiom audit for the concrete local
classification theorem. -/

namespace BongTest

open Bong Bong.Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example : DyadicDiagonalClassificationLaws K := inferInstance

#print axioms Bong.dyadicDiagonalClassification_represents
#print axioms Bong.dyadicDiagonalClassificationLawsProved

end BongTest
