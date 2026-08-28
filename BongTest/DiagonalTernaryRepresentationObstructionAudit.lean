/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalTernaryRepresentationObstructionProof

/-! Independent synthesis and axiom audit for the concrete ternary
representation obstruction. -/

namespace BongTest

open Bong Bong.Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example : DyadicTernaryRepresentationObstructionLaws K := inferInstance

#print axioms Bong.dyadicTernaryRepresentation_obstruction
#print axioms Bong.dyadicTernaryRepresentation_isotropic_of_represents
#print axioms Bong.dyadicTernaryRepresentationObstructionLawsProved

end BongTest
