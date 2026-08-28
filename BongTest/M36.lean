/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M36 binary inclusion criterion smoke tests
-/

namespace BongTest.M36

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

example (b : BONG V q L 1) (c : BONG V q M 1) :
    L ≤ M ↔ c.order 0 ≤ b.order 0 :=
  b.le_iff_order_ge c

example (b : BONG V q L 2) (c : BONG V q M 2)
    (hhead : b.head = c.head) :
    L ≤ M ↔ c.binaryOrderGap ≤ b.binaryOrderGap :=
  b.le_iff_binaryOrderGap_ge_of_head_eq c hhead

#print axioms Bong.BONG.le_iff_order_ge
#print axioms Bong.BONG.le_iff_binaryOrderGap_ge_of_head_eq

end

end BongTest.M36
