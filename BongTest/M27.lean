/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M27 binary determinant-invariant smoke tests
-/

namespace BongTest.M27

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b : BONG V q L 2) :
    b.binaryDeterminantInvariant = b.binaryUnitSquareClass :=
  b.binaryDeterminantInvariant_eq_parameter

#print axioms Bong.BONG.binaryDeterminantInvariant_eq_parameter

end

end BongTest.M27
