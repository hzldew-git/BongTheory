/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma65

/-!
# M97 Beli 2003, Lemma 6.5 smoke tests
-/

namespace BongTest.M97

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (b : BONG V q L (n + 3)) (k : Nat) :
    ordUnit K (b.headSecondRescaledParameter k) =
      b.order 1 + 2 * (k : Int) - b.order 0 :=
  b.ordUnit_headSecondRescaledParameter k

example (b : BONG V q L (n + 3)) (S : b.Lemma65Setup)
    (j : Nat) (hj : j < S.k) :
    ¬b.HeadSecondRescaleAdmissible j :=
  S.not_admissible_of_lt j hj

example (b : BONG V q L (n + 3)) (x : V)
    (horder : ord K (q.quadratic (b.head - x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int)) :
    q.IsAnisotropic (b.head - x) :=
  BONG.lemma65Difference_isAnisotropic_of_order_eq b x horder

variable [BONG.BeliLemma65Laws.{u, v} K]

example (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head) :
    (¬b.Lemma65Exceptional → S.projection x ∈ S.tailRescale.lattice) ∧
      (b.Lemma65Exceptional →
        S.k = 2 ∧
          Nonempty (BONG.Lemma65ExceptionalProjectionWitness b x)) :=
  b.beliLemma65_i hB S x hx heq

example (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x)) :
    Nonempty (BONG.Lemma65DifferenceReflectionWitness b x) :=
  b.beliLemma65_ii hB S x hx heq hlow hgenerator

example (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x x' : V) (hx : x ∈ L) (hx' : x' ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (heq' : q.quadratic x' = q.quadratic b.head)
    (hlow : b.Lemma65LowRange S)
    (hgenerator : Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x))
    (hnotGenerator : ¬Lattice.IsNormGenerator
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      S.tailRescale.lattice (S.projection x')) :
    ∃ w : BONG.Lemma65DifferenceReflectionWitness b x,
      Lattice.IsNormGenerator
        (q.orthogonalSpace b.head b.head_isAnisotropic)
        S.tailRescale.lattice
        (S.projection
          (q.reflectionLinearEquiv (b.head - x) w.anisotropic x')) :=
  b.beliLemma65_iii hB S x hx heq hlow hgenerator
    x' hx' heq' hnotGenerator

example (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (S : b.Lemma65Setup) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hhigh : b.Lemma65HighRange S)
    (horder : ord K (q.quadratic (b.head - x)) =
      ((b.order 0 + 2 * (ramificationIndex K : Int) : Int) :
        WithTop Int)) :
    Lattice.IsIntegralReflection (L := L)
      (BONG.lemma65Difference_isAnisotropic_of_order_eq b x horder) :=
  b.beliLemma65_iv hB S x hx heq hhigh horder

#print axioms Bong.BONG.ordUnit_headSecondRescaledParameter
#print axioms Bong.BONG.Lemma65Setup.not_admissible_of_lt
#print axioms Bong.BONG.Lemma65Setup.coe_tailRescale_ambientVector_zero
#print axioms Bong.BONG.Lemma65DifferenceReflectionWitness.map_head
#print axioms Bong.BONG.lemma65Difference_isAnisotropic_of_order_eq
#print axioms Bong.BONG.beliLemma65_i
#print axioms Bong.BONG.beliLemma65_ii
#print axioms Bong.BONG.beliLemma65_iii
#print axioms Bong.BONG.beliLemma65_iv

end BongTest.M97
