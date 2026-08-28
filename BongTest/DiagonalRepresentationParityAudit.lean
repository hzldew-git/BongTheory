/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalRepresentationParityProof

/-! Independent synthesis and axiom audit for the three concrete parity
cycles in Beli's Lemma 1.5. -/

namespace BongTest

open Bong Bong.Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example : DiagonalRepresentationParityLaws K := inferInstance

#print axioms Bong.diagonalCodimensionOneRepresents_iff_sign_eq_one
#print axioms Bong.diagonalRepresentationParity_caseI
#print axioms Bong.diagonalRepresentationParity_caseII
#print axioms Bong.diagonalRepresentationParity_caseIII
#print axioms Bong.diagonalRepresentationParityLawsProved

end BongTest
