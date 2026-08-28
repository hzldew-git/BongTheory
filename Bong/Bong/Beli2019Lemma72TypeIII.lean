/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma611TypeIII

/-!
# Beli (2019), Lemma 7.2(iii)

For a nonoverlapping type-III pair, Lemma 6.11 puts every source order up to
`u` in the class `R` and every target order in the class `S`.  Summing these
entrywise congruences gives part (iii) of Lemma 7.2.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The two cumulative-order congruences in Lemma 7.2(iii). -/
structure Lemma72TypeIIIConsequences
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeIII a b) : Prop where
  source (i : Nat) (hi : i ≤ D.outer.last + 1) :
    Int.ModEq 2 (a.orderSequence.prefixSum i)
      ((i : Int) * a.orderSequence.entryOrZero
        D.outer.transition.lastZero)
  target (i : Nat) (hi : i ≤ D.outer.last + 1) :
    Int.ModEq 2 (b.orderSequence.prefixSum i)
      ((i : Int) * b.orderSequence.entryOrZero
        (D.outer.transition.firstTwo - 1))

/-- Beli (2019), Lemma 7.2(iii), in the paper's nonoverlapping type-III
case. -/
theorem beli2019Lemma72_iii
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (halpha : a.alphaValue
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≤ 1)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1) :
    Lemma72TypeIIIConsequences a b D := by
  let C := a.lemma611TypeIII b D hfirst halpha hnotOverlap
  refine {
    source := ?_
    target := ?_ }
  · intro i hi
    apply a.orderSequence.prefixSum_modEq_mul
    intro k hk
    exact C.source k (by omega)
  · intro i hi
    apply b.orderSequence.prefixSum_modEq_mul
    intro k hk
    exact C.target k (by omega)

/-- Lemma 7.2(iii) with the boundary alpha bound obtained from Lemma 6.9(i). -/
theorem beli2019Lemma72_iii_of_defect
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1) :
    Lemma72TypeIIIConsequences a b D := by
  let C := a.lemma611TypeIII_of_defect
    (alphaV := alphaV) (alphaW := alphaW)
    b D hfirst hdefect hnotOverlap
  refine {
    source := ?_
    target := ?_ }
  · intro i hi
    apply a.orderSequence.prefixSum_modEq_mul
    intro k hk
    exact C.source k (by omega)
  · intro i hi
    apply b.orderSequence.prefixSum_modEq_mul
    intro k hk
    exact C.target k (by omega)

end BONG.GoodBONG

end Bong
