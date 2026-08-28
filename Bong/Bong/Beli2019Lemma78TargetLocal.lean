/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma78Local
import Bong.Bong.Beli2019Lemma78TargetAlpha
import Bong.Bong.Beli2019Lemma63Right
import Bong.Bong.Beli2019Lemma79OrderRightAlternating
import Bong.Bong.Beli2019Remark616

/-!
# Beli (2019), Lemma 7.8: local target bounds and the first common prefix

The lower bound for the target alpha is an interval calculation and does
not require the last unequal coordinate to have full rank.  At the first
coordinate after the unequal interval, Lemma 6.3 supplies the right-branch
representation-alpha identity directly from the common suffix.  Together
with the local source-prefix theorem this gives the target-prefix equality
needed at a proper-suffix endpoint.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The target-alpha lower bound in Lemma 7.8, with no full-span
hypothesis. -/
theorem lemma78_typeIII_targetAlpha_ge_mixedShift_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (i : Nat) (hiStart : D.outer.transition.lastZero + 2 ≤ i)
    (hiLast : i ≤ D.outer.last + 1) (hiEven : Even i)
    (hiNonterminal : i < n + 2) :
    ((b.order ⟨D.outer.transition.lastZero, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ -
        a.order ⟨D.outer.transition.lastZero + 1, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ : Int) : ℚ) ≤
      b.alphaValue ⟨i - 1, by omega⟩ := by
  let left := D.outer.transition.lastZero
  let right := D.outer.transition.firstTwo - 1
  let center : Fin (n + 1) := ⟨left, by
    dsimp only [left]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  let p : Fin (n + 1) := ⟨i - 1, by omega⟩
  let c : Int := b.order ⟨left, by omega⟩ -
    a.order ⟨left + 1, by omega⟩
  have hrightEq : right = left + 1 := by
    simp only [right, left]
    rw [D.adjacent]
    omega
  have hleftEven : Even left := by
    by_cases heq : D.outer.first = left
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < left :=
        lt_of_le_of_ne D.outer.first_le_left heq
      simpa only [hfirst, left, Nat.sub_zero] using
        (D.outer.leftProfile hlt).1
  have hcentralEven : Even (a.orderGap center) := by
    simpa only [center, left] using
      a.lemma78_typeIII_centralGap_even
        (alphaV := alpha) (alphaW := alpha)
        b D hfirst hdefect hnotOverlap
  have hdata := a.beli2019Lemma78_sourceAlpha_and_gap
    (alphaV := alpha) (alphaW := alpha)
    b D hfirst hdefect hnotOverlap hinitial
  have hcentralLower : 3 - 2 * (ramificationIndex K : Int) ≤
      a.orderGap center + 1 := by
    simpa only [center, left] using hdata.2
  have hleftBoundary := D.outer.transition.leftBoundary
  have hleftGap : b.orderSequence.entryOrZero left =
      a.orderSequence.entryOrZero left + 1 := by
    simpa only [left] using hleftBoundary
  have haLeft : a.order ⟨left, by omega⟩ =
      a.orderSequence.entryOrZero left :=
    (a.orderSequence_entryOrZero_eq_order ⟨left, by omega⟩).symm
  have hbLeft : b.order ⟨left, by omega⟩ =
      b.orderSequence.entryOrZero left :=
    (b.orderSequence_entryOrZero_eq_order ⟨left, by omega⟩).symm
  have haRight : a.order ⟨left + 1, by omega⟩ =
      a.orderSequence.entryOrZero right := by
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
    apply congrArg a.order
    apply Fin.ext
    exact hrightEq.symm
  have hcentralFormula : a.orderGap center =
      a.orderSequence.entryOrZero right -
        a.orderSequence.entryOrZero left := by
    unfold orderGap
    change a.order ⟨left + 1, by omega⟩ -
      a.order ⟨left, by omega⟩ = _
    rw [haLeft, haRight]
  have hcFormula : c = 1 - a.orderGap center := by
    dsimp only [c]
    rw [hbLeft, haRight, hleftGap, hcentralFormula]
    ring
  have hcLtTwoE : c < 2 * (ramificationIndex K : Int) := by
    rw [hcFormula]
    omega
  have hcPredEven : Even (c - 1) := by
    rw [hcFormula]
    rcases hcentralEven with ⟨d, hd⟩
    exact ⟨-d, by omega⟩
  have hpRight : right ≤ i - 1 := by
    rw [hrightEq]
    omega
  have hpDistanceEven : Even ((i - 1) - right) := by
    rcases hiEven with ⟨d, hd⟩
    rcases hleftEven with ⟨e, he⟩
    refine ⟨d - e - 1, ?_⟩
    rw [hrightEq]
    omega
  have htargetCurrentRight : b.orderSequence.entryOrZero (i - 1) =
      b.orderSequence.entryOrZero right := by
    simpa only [right] using
      D.outer.target_rightEven_eq_boundary (i - 1) hpRight
        (by omega) (by simpa only [right] using hpDistanceEven)
  have htargetNext := b.orderSequence.entryOrZero_le_of_evenGap
    left i (by omega) hiNonterminal (by
      rcases hiEven with ⟨d, hd⟩
      rcases hleftEven with ⟨e, he⟩
      exact ⟨d - e, by omega⟩)
  have hbPrevious : b.order p.castSucc =
      b.orderSequence.entryOrZero (i - 1) := by
    exact (b.orderSequence_entryOrZero_eq_order p.castSucc).symm
  have hbNext : b.order p.succ =
      b.orderSequence.entryOrZero i := by
    calc
      b.order p.succ = b.order ⟨i, by omega⟩ := by
        apply congrArg b.order
        apply Fin.ext
        dsimp only [p]
        change i - 1 + 1 = i
        omega
      _ = b.orderSequence.entryOrZero i :=
        (b.orderSequence_entryOrZero_eq_order ⟨i, by omega⟩).symm
  have hrightGap : b.orderSequence.entryOrZero right =
      a.orderSequence.entryOrZero right + 1 := by
    simpa only [right] using D.outer.transition.rightBoundary
  have hgapLower : c - 1 ≤ b.orderGap p := by
    unfold orderGap
    rw [hbPrevious, hbNext, htargetCurrentRight]
    dsimp only [c]
    rw [hbLeft, haRight]
    omega
  rcases b.beli2009Corollary28_iii p with hsmall | hlarge
  · have hgapLe : b.orderGap p ≤
        2 * (ramificationIndex K : Int) :=
      (b.alphaValue_le_twoE_iff_orderGap_le_twoE p).mp hsmall.2.1
    have hbetaGap : (b.orderGap p : ℚ) ≤ b.alphaValue p :=
      (b.alpha_p3 p hgapLe).1
    by_cases hgapEq : b.orderGap p = c - 1
    · have hgapEven : Even (b.orderGap p) := by
        rw [hgapEq]
        exact hcPredEven
      have hbetaNe : b.alphaValue p ≠ (b.orderGap p : ℚ) := by
        intro heq
        rcases ((b.alpha_p3 p hgapLe).2.mp heq) with htwo | hodd
        · rw [hgapEq] at htwo
          omega
        · exact (Int.not_odd_iff_even.mpr hgapEven) hodd
      rcases hsmall.2.2 with ⟨z, hz⟩
      have hgapZ : b.orderGap p ≤ z := by
        exact_mod_cast (show (b.orderGap p : ℚ) ≤ (z : ℚ) by
          simpa only [hz] using hbetaGap)
      have hgapNeZ : b.orderGap p ≠ z := by
        intro heq
        apply hbetaNe
        rw [hz]
        exact_mod_cast heq.symm
      have hcZ : c ≤ z := by omega
      rw [hz]
      exact_mod_cast hcZ
    · have hcGap : c ≤ b.orderGap p := by omega
      exact (by exact_mod_cast hcGap : (c : ℚ) ≤ b.orderGap p).trans
        hbetaGap
  · have hcTwoEQ : (c : ℚ) <
        2 * (ramificationIndex K : ℚ) := by
      exact_mod_cast hcLtTwoE
    have hcBeta : (c : ℚ) < b.alphaValue p :=
      hcTwoEQ.trans hlarge.1
    exact hcBeta.le

set_option maxHeartbeats 5000000 in
-- The representation boundary is the first coordinate of the common suffix.
/-- The target self-prefix equality at the first coordinate after a
nonoverlapping type-III difference interval. -/
theorem beli2019Lemma78_targetPrefixDefect_firstCommon_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hproper : D.outer.last < n + 1)
    (hiEven : Even (D.outer.last + 1)) :
    b.truncatedPrefixDefect b ((-1) ^ ((D.outer.last + 1) / 2))
        0 (D.outer.last + 1) =
      ((((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : ℚ)) : WithTop ℚ) := by
  let length := D.outer.last + 1
  have hlengthBound : length < n + 2 := by
    simp only [length]
    omega
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨length, by
      have hright := D.outer.right_le_last
      have hseparated := D.outer.transition.separated
      simp only [length]
      omega, hlengthBound, hlengthBound.le⟩
  have hclassification := a.beli2019Lemma63_sameRank_right_value
    b hdefect idx (by
      intro k hk hkn
      exact D.outer.lastDifference.after k (by
        simp only [idx, length] at hk
        omega) hkn)
  have hremark := a.beli2019Remark616_rightPrefix
    b hdefect idx hclassification ((-1) ^ (length / 2))
  have hsource := a.beli2019Lemma78_sourcePrefixDefect_local
    b D hfirst hdefect hnotOverlap hinitial length (by
      simp only [length]
      have hright := D.outer.right_le_last
      rw [D.adjacent] at hright
      omega) (by
      change D.outer.last + 1 ≤ D.outer.last + 1
      exact le_rfl) (by simpa only [length] using hiEven)
  have hbeta := a.lemma78_typeIII_targetAlpha_ge_mixedShift_local
    b D hfirst hdefect hnotOverlap hinitial length (by
      simp only [length]
      have hright := D.outer.right_le_last
      rw [D.adjacent] at hright
      omega) (by
      change D.outer.last + 1 ≤ D.outer.last + 1
      exact le_rfl) (by simpa only [length] using hiEven)
      hlengthBound
  simp only [length] at hremark hsource hbeta ⊢
  rw [hremark, hsource]
  apply min_eq_left
  exact_mod_cast hbeta

end BONG.GoodBONG

end Bong
