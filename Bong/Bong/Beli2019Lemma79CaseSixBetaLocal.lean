/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixProfile

/-!
# Beli (2019), Lemma 7.9(ii), case 6: local lower bound for the target cap

The closing argument in the first parity branch only needs `1 ≤ beta_i`.
The older right-alpha API proved the stronger equality `beta_i = 1` by
reverse duality and consequently required the last unequal coordinate to be
the last coordinate of the whole BONG.  Nonvanishing is local: away from the
right transition the target adjacent gap is the source adjacent gap plus two,
while at the transition it follows from the central gap.  This removes the
artificial full-span hypothesis from the part of Remark 6.13 used in case 6.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- On a non-boundary even coordinate of a no-gap-two right profile, the
preceding target alpha is nonzero and hence at least one. -/
theorem lemma79_caseSix_targetPreviousAlpha_one_le_of_interior
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hnoTwo : ∀ k, k < n + 2 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : O.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ O.last)
    (heven : Even (i.val - (O.transition.firstTwo - 1)))
    (hnotBoundary : i.val ≠ O.transition.firstTwo - 1) :
    (1 : ℚ) ≤ b.alphaValue ⟨i.val - 1, by
      have hlastBound := O.lastDifference.bound
      omega⟩ := by
  have hlastBound := O.lastDifference.bound
  rcases heven with ⟨d, hd⟩
  have hdPositive : 0 < d := by omega
  have hpreviousRight : O.transition.firstTwo - 1 ≤ i.val - 1 := by
    omega
  have hpreviousOdd : Odd
      ((i.val - 1) - (O.transition.firstTwo - 1)) :=
    ⟨d - 1, by omega⟩
  have hcurrentRaw := O.target_rightEven_eq_source_add_one
    hnoTwo i.val hright hthroughLast ⟨d, hd⟩
  have hpreviousRaw := O.source_rightOdd_eq_target_add_one
    hnoTwo (i.val - 1) hpreviousRight (by omega) hpreviousOdd
  have hcurrent : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hcurrentRaw
  have hprevious : a.order ⟨i.val - 1, by omega⟩ =
      b.order ⟨i.val - 1, by omega⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hpreviousRaw
  let p : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hpSucc : p.succ = (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have hpCast : p.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hsourceLower := a.orderGap_ge_neg_two_mul_e p
  have htargetGap : b.orderGap p = a.orderGap p + 2 := by
    unfold orderGap
    rw [hpSucc, hpCast, hcurrent, hprevious]
    omega
  have htargetStrict : -(2 * (ramificationIndex K : Int)) <
      b.orderGap p := by
    rw [htargetGap]
    omega
  have hne : b.alphaValue p ≠ 0 := by
    intro hzero
    have hgap := (b.alpha_p2 p).2.mp hzero
    omega
  simpa only [p] using b.one_le_alphaValue_of_ne_zero p hne

/-- The type-II case-6 target cap is locally at least one, without a
full-span or determinant hypothesis. -/
theorem beli2019Lemma79_typeII_caseSix_beta_one_le_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (1 : ℚ) ≤ b.alphaValue ⟨i.val - 1, by
      have hlastBound := D.outer.lastDifference.bound
      omega⟩ := by
  by_cases hboundary : i.val = D.outer.transition.firstTwo - 1
  · have hvalue := a.beli2019Lemma69_i_typeII_targetBoundary_eq_one b D
    have hbound := D.outer.transition.firstTwo_le_rank
    have hlong := D.long
    have hlastBound := D.outer.lastDifference.bound
    have hindex : (⟨i.val - 1, by omega⟩ : Fin (n + 1)) =
        ⟨D.outer.transition.firstTwo - 2, by
          omega⟩ := by
      apply Fin.ext
      change i.val - 1 = D.outer.transition.firstTwo - 2
      omega
    rw [hindex, hvalue]
  · exact lemma79_caseSix_targetPreviousAlpha_one_le_of_interior
      a b D.outer D.no_gap_two i hright hthroughLast heven hboundary

/-- A strict source central gap supplies the local target-cap lower bound
for a type-III case-6 profile. -/
theorem beli2019Lemma79_typeIII_caseSix_beta_one_le_of_centerGap
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hcenter : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (1 : ℚ) ≤ b.alphaValue ⟨i.val - 1, by
      have hlastBound := D.outer.lastDifference.bound
      omega⟩ := by
  by_cases hboundary : i.val = D.outer.transition.firstTwo - 1
  · let center : Fin (n + 1) :=
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩
    have htargetGap : b.orderGap center = a.orderGap center := by
      simpa only [center] using
        a.lemma78_typeIII_targetGap_eq_sourceGap b D
    have htargetStrict : -(2 * (ramificationIndex K : Int)) <
        b.orderGap center := by
      rw [htargetGap]
      simpa only [center] using hcenter
    have hne : b.alphaValue center ≠ 0 := by
      intro hzero
      have hgap := (b.alpha_p2 center).2.mp hzero
      omega
    have hone := b.one_le_alphaValue_of_ne_zero center hne
    have hlastBound := D.outer.lastDifference.bound
    have hindex : (⟨i.val - 1, by omega⟩ : Fin (n + 1)) = center := by
      apply Fin.ext
      dsimp only [center]
      rw [hboundary, D.adjacent]
      omega
    simpa only [hindex] using hone
  · exact lemma79_caseSix_targetPreviousAlpha_one_le_of_interior
      a b D.outer D.no_gap_two i hright hthroughLast heven hboundary

/-- The nonoverlapping type-III target cap is locally at least one. -/
theorem beli2019Lemma79_typeIII_caseSix_beta_one_le_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (1 : ℚ) ≤ b.alphaValue ⟨i.val - 1, by
      have hlastBound := D.outer.lastDifference.bound
      omega⟩ := by
  have hmono := lemma78_typeIII_initialGap_le_centralGap a b D hfirst
  apply beli2019Lemma79_typeIII_caseSix_beta_one_le_of_centerGap
    a b D (hinitial.trans_le hmono) i hright hthroughLast heven

/-- The overlapping type-III target cap is locally at least one. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_beta_one_le_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (1 : ℚ) ≤ b.alphaValue ⟨i.val - 1, by
      have hlastBound := D.outer.lastDifference.bound
      omega⟩ := by
  have hePos := ramificationIndex_pos (K := K)
  apply beli2019Lemma79_typeIII_caseSix_beta_one_le_of_centerGap
    a b D (by rw [hoverlap]; omega) i hright hthroughLast heven

end BONG.GoodBONG

end Bong
