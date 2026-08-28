/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma411

/-!
# M91 Beli 2003, Definition 10, Lemma 4.11, and Remark 4.12 smoke tests
-/

namespace BongTest.M91

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n m start : Nat}

example (b : BONG V q L n) (i : Fin n) (hi : i.1 + 1 < n) :
    -(2 * (ramificationIndex K : Int)) ≤
      b.order ⟨i.1 + 1, hi⟩ - b.order i :=
  b.adjacentOrderGap_ge_neg_two_mul_e i hi

example {b : BONG V q L (n + 1)}
    {bound : start + (m + 1) ≤ n + 1}
    (w : BONG.SegmentWitness b start (m + 1) bound)
    (hb : b.HasPropertyB) :
    w.bong.HasPropertyB :=
  w.hasPropertyB hb

example {b : BONG V q L (n + 1)} (hb : b.HasPropertyB)
    (i : Fin (n + 1)) (hi : i.1 + 2 < n + 1) :
    b.order i + 2 ≤ b.order ⟨i.1 + 2, hi⟩ :=
  hb.twoStep_add_two_le i hi

variable [BeliLemma411Laws.{u, v} K]

example (b : BONG V q L (n + 1))
    (hA : b.HasPropertyA) (hnotB : ¬b.HasPropertyB) :
    Lattice.spinorNormImage (q := q) (L := L) = Set.univ :=
  b.beliLemma411 hA hnotB

#print axioms Bong.BONG.adjacentOrderGap_ge_neg_two_mul_e
#print axioms Bong.BONG.adjacentOrderGap_pos_of_odd
#print axioms Bong.BONG.SegmentWitness.hasPropertyB
#print axioms Bong.BONG.HasPropertyB.twoStep_add_two_le
#print axioms Bong.BONG.beliLemma411

end

end BongTest.M91
