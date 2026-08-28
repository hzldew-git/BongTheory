/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M30 reverse-dual order smoke tests
-/

namespace BongTest.M30

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (b : BONG V q L n) (i : Fin n) :
    ord K (q.quadratic (b.reverseDualVector i)) =
      ((-b.order (Fin.rev i) : Int) : WithTop Int) :=
  b.ord_quadratic_reverseDualVector i

example (b : BONG V q L n) (hb : b.IsGood) :
    ∀ (i : Fin n) (hi : i.1 + 2 < n),
      -b.order (Fin.rev i) ≤
        -b.order (Fin.rev ⟨i.1 + 2, hi⟩) :=
  b.reverseDual_orders_good hb

#print axioms Bong.BONG.ord_quadratic_reverseDualVector
#print axioms Bong.BONG.reverseDual_orders_good

end

end BongTest.M30
