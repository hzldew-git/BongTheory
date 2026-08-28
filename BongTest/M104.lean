/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma73

/-!
# M104 Beli 2003, Lemma 7.3 smoke tests
-/

namespace BongTest.M104

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (b : BONG V q L (n + 3)) (i : Fin (n + 1)) :
    ordUnit K (b.lemma73ResidualValue i) =
      b.order (BONG.lemma73FirstIndex i) :=
  b.ordUnit_lemma73ResidualValue i

example {b : BONG V q L (n + 3)} {i : Fin (n + 1)}
    (w : b.Lemma73SplittingWitness i) :
    w.remainderBONG.order ⟨i.1, by omega⟩ =
      b.order (BONG.lemma73FirstIndex i) :=
  w.replacement_order

variable [BeliLemma73Laws.{u, v} K]

example (b : BONG V q L (n + 3)) (i : Fin (n + 1))
    (hgood : b.IsGood) (h : b.Lemma73Hypotheses i) :
    Nonempty (b.Lemma73SplittingWitness i) :=
  b.beliLemma73 i hgood h

#print axioms Bong.Dyadic.ordUnit_neg
#print axioms Bong.BONG.ordUnit_lemma73ResidualValue
#print axioms Bong.BONG.Lemma73SplittingWitness.replacement_order
#print axioms Bong.BONG.beliLemma73

end BongTest.M104
