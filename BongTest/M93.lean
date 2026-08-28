/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma61Proof

/-!
# M93 Beli 2003, Lemma 6.1 smoke tests
-/

namespace BongTest.M93

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (b : BONG V q L (n + 1)) (x : V) (hx : x ∈ L) :
    Lattice.IsNormGenerator q L x ↔
      ord K (q.quadratic x) = (b.order 0 : WithTop Int) :=
  b.isNormGenerator_iff_ord_quadratic_eq_head x hx

example (b : BONG V q L (n + 1)) (x : V) :
    (x ∈ L ∧ ¬Lattice.IsNormGenerator q L x) ↔
      x ∈ L ∧
        ((b.order 0 + 1 : Int) : WithTop Int) ≤ ord K (q.quadratic x) :=
  b.mem_and_not_isNormGenerator_iff_ord_ge_head_add_one x

example (b : BONG V q L (n + 2)) (hgood : b.IsGood)
    (hexists : b.HeadBinaryRescaleExists 1)
    (hthird : ∀ _h : 1 ≤ n, b.order 0 + 2 ≤ b.order ⟨2, by omega⟩) :
    ∃ w : b.HeadDepthWitness 1, ∀ x : V,
      x ∈ w.lattice ↔ x ∈ L ∧ ¬Lattice.IsNormGenerator q L x :=
  b.beliLemma61_i hgood hexists hthird

example (b : BONG V q L (n + 2)) (hcriterion : b.HeadRescaleCriterion) :
    b.HeadBinaryRescaleExists 1 ∧
      (b.HasPropertyB → ∀ _h : 1 ≤ n,
        b.order 0 + 2 ≤ b.order ⟨2, by omega⟩) :=
  b.beliLemma61_iii hcriterion

#print axioms Bong.BONG.isNormGenerator_iff_ord_quadratic_eq_head
#print axioms Bong.BONG.mem_and_not_isNormGenerator_iff_ord_ge_head_add_one
#print axioms Bong.BONG.beliLemma61_ii
#print axioms Bong.BONG.beliLemma61_i
#print axioms Bong.BONG.beliLemma61_iii

end

end BongTest.M93
