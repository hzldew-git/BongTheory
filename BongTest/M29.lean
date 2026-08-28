/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M29 binary relative-order smoke tests
-/

namespace BongTest.M29

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b : BONG V q L 2) :
    b.binaryRelativeOrder = b.binaryOrderGap :=
  b.binaryRelativeOrder_eq_orderGap

example (b c : BONG V q L 2) : b.binaryOrderGap = c.binaryOrderGap :=
  b.binaryOrderGap_eq c

#print axioms Bong.Dyadic.ordUnit_eq_of_unitSquareClass_eq
#print axioms Bong.BONG.binaryRelativeOrder_eq_orderGap
#print axioms Bong.BONG.binaryOrderGap_eq

end

end BongTest.M29
