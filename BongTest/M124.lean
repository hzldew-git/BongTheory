/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019RepresentationParity

/-!
# M124 Beli 2019, Lemmas 1.3 and 1.5 and condition (iii') smoke tests
-/

namespace BongTest.M124

open Bong

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example (x y : ℚ) (z : WithTop ℚ) (a b : Kˣ)
    (hcase :
      (x < y ∧ min (BONG.GoodBONG.shiftedDefect (K := K) y b) z ≤
        BONG.GoodBONG.shiftedDefect (K := K) x a) ∨
      (x ≤ y ∧ min (BONG.GoodBONG.shiftedDefect (K := K) y b) z <
        BONG.GoodBONG.shiftedDefect (K := K) x a) ∨
      z ≤ BONG.GoodBONG.shiftedDefect (K := K) y a) :
    min (BONG.GoodBONG.shiftedDefect (K := K) y b) z =
      min (BONG.GoodBONG.shiftedDefect (K := K) y (a * b)) z :=
  BONG.GoodBONG.beli2019Lemma13 x y z a b hcase

example (c₁ c₂ c₃ c₄ : Bool) :
    EvenTruthParity (c₁ = c₂) (c₂ = c₃) (c₁ = c₄) (c₃ = c₄) := by
  let P : TwoClassPresentation Bool Eq :=
    ⟨id, fun _ _ ↦ Iff.rfl⟩
  exact P.cycle_even c₁ c₂ c₃ c₄

variable {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

example (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1)) (hRank : n ≤ m)
    (htrigger : a.CentralTriggerEquivalence b) :
    RepresentationConditions a b hRank ↔
      RepresentationConditionsPrime a b hRank :=
  representationConditions_iff_prime a b hRank htrigger

#print axioms Bong.BONG.GoodBONG.beli2019Lemma13
#print axioms Bong.TwoClassPresentation.cycle_even
#print axioms Bong.Beli2019RepresentationParityDiagram.evenTruthParity
#print axioms Bong.BONG.GoodBONG.centralRepresentationConditions_iff_prime
#print axioms Bong.representationConditions_iff_prime

end BongTest.M124
