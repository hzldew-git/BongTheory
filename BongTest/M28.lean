/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M28 binary-invariant independence smoke tests
-/

namespace BongTest.M28

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b c : BONG V q L 2) :
    b.binaryUnitSquareClass = c.binaryUnitSquareClass :=
  b.binaryUnitSquareClass_eq c

#print axioms Bong.Lattice.exists_valuationUnit_mul_eq_of_principalIdeal_eq
#print axioms Bong.BONG.binaryUnitSquareClass_eq

end

end BongTest.M28
