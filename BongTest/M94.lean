/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma62

/-!
# M94 Beli 2003, Lemma 6.2 smoke tests
-/

namespace BongTest.M94

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (b : BONG V q L (n + 2)) (w : b.HeadInverseRescaleWitness) :
    w.bong.order 0 = b.order 0 - 2 :=
  w.order_zero

example (b : BONG V q L (n + 2)) (w : b.HeadInverseRescaleWitness)
    (hB : b.HasPropertyBOrInverse w) : b.IsGood :=
  hB.isGood

variable [BeliLemma62Laws.{u, v} K]

example (b : BONG V q L (n + 2)) : b.HeadInverseRescaleExists :=
  b.beliLemma62_i

example (b : BONG V q L (n + 2)) (w : b.HeadInverseRescaleWitness)
    (hB : b.HasPropertyBOrInverse w) (hgap : b.order 0 ≤ b.order 1) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.scaledIntegralSquareResidueSet (b.value 0)
        (Lattice.powerIdeal (K := K) (b.order 1)) :=
  b.beliLemma62_ii_a w hB hgap

#print axioms Bong.BONG.HeadInverseRescaleWitness.order_zero
#print axioms Bong.BONG.HasPropertyBOrInverse.isGood
#print axioms Bong.BONG.lemma62DefectCutoff_cast
#print axioms Bong.BONG.beliLemma62_i
#print axioms Bong.BONG.beliLemma62_ii_a
#print axioms Bong.BONG.beliLemma62_ii_b
#print axioms Bong.BONG.beliLemma62_ii_c

end

end BongTest.M94
