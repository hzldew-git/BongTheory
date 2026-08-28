/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Remark616

/-!
# Beli (2019), Lemma 6.9(i) inside the type-III left profile

For every even boundary before the type-III transition, the preceding source
alpha is one.  This is the local input used by Lemma 6.9(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The source alpha immediately before an even boundary in the normalized
left type-III profile is exactly one. -/
theorem lemma78_typeIII_sourcePreviousAlpha_eq_one_of_center
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hcenter : a.alphaValue
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (i : Nat) (hiTwo : 2 ≤ i)
    (hiLeft : i ≤ D.outer.transition.lastZero) (hiEven : Even i) :
    a.alphaValue ⟨i - 2, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ = 1 := by
  let left := D.outer.transition.lastZero
  let center : Fin (n + 1) := ⟨left, by
    dsimp only [left]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  let previous : Fin (n + 1) := ⟨i - 2, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  have hleftEven : Even left := by
    by_cases heq : D.outer.first = left
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < left :=
        lt_of_le_of_ne D.outer.first_le_left heq
      simpa only [hfirst, left, Nat.sub_zero] using
        (D.outer.leftProfile hlt).1
  have hleftPos : 0 < left := by omega
  have hprofile := D.outer.leftProfile (by rw [hfirst]; omega)
  have hpreviousEven : Even (i - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hsourcePrevious : a.orderSequence.entryOrZero (i - 2) =
      a.orderSequence.entryOrZero left := by
    have hsame := hprofile.2.2 (i - 2) (by rw [hfirst]; omega)
      (by omega) (by simpa only [hfirst, Nat.sub_zero] using hpreviousEven)
    have hleftSame := hprofile.2.2 left D.outer.first_le_left le_rfl hprofile.1
    exact hsame.trans hleftSame.symm
  have hsourceCenter : a.order previous.castSucc =
      a.order center.castSucc := by
    rw [← a.orderSequence_entryOrZero_eq_order previous.castSucc,
      ← a.orderSequence_entryOrZero_eq_order center.castSucc]
    change a.orderSequence.entryOrZero (i - 2) =
      a.orderSequence.entryOrZero left
    exact hsourcePrevious
  have hcentralOne : a.alphaValue center = 1 := by
    simpa only [center, left] using hcenter
  have halphaLe : a.alphaValue previous ≤ 1 := by
    have hmono := a.alphaLeftEndpoint_monotone
      (show previous ≤ center by
        change i - 2 ≤ left
        omega)
    unfold alphaLeftEndpoint at hmono
    rw [hsourceCenter, hcentralOne] at hmono
    linarith
  have htargetPrevious : b.orderSequence.entryOrZero (i - 2) =
      b.orderSequence.entryOrZero left := by
    have hzeroTarget : b.orderSequence.entryOrZero 0 =
        b.orderSequence.entryOrZero left := by
      have hsourceLeft := hprofile.2.2 left D.outer.first_le_left
        le_rfl hprofile.1
      have hleftBoundary := D.outer.transition.leftBoundary
      have hleftGap : b.orderSequence.entryOrZero left =
          a.orderSequence.entryOrZero left + 1 := by
        simpa only [left] using hleftBoundary
      have hfirstStrict := hprofile.2.1
      rw [hfirst] at hfirstStrict
      have hfirstUpper := D.no_gap_two 0 (by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega)
      have hsourceFirst : a.orderSequence.entryOrZero 0 =
          a.orderSequence.entryOrZero left := by
        rw [hfirst] at hsourceLeft
        exact hsourceLeft.symm
      have hzeroGap : b.orderSequence.entryOrZero 0 =
          a.orderSequence.entryOrZero 0 + 1 := by omega
      omega
    have hzeroLe := b.orderSequence.entryOrZero_le_of_evenGap
      0 (i - 2) (Nat.zero_le _) (by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega) hpreviousEven
    have htoLeft := b.orderSequence.entryOrZero_le_of_evenGap
      (i - 2) left (by omega) (by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega) (by
          rcases hleftEven with ⟨d, hd⟩
          rcases hpreviousEven with ⟨e, he⟩
          exact ⟨d - e, by omega⟩)
    omega
  have hleftGap : b.orderSequence.entryOrZero (i - 2) =
      a.orderSequence.entryOrZero (i - 2) + 1 := by
    have hboundary := D.outer.transition.leftBoundary
    have hboundary' : b.orderSequence.entryOrZero left =
        a.orderSequence.entryOrZero left + 1 := by
      simpa only [left] using hboundary
    omega
  have hpair := D.outer.leftPairEq (i - 2) (by omega) (by
    rcases hleftEven with ⟨d, hd⟩
    rcases hiEven with ⟨e, he⟩
    exact ⟨d - e + 1, by omega⟩)
  have hrightGap : b.orderSequence.entryOrZero (i - 1) =
      a.orderSequence.entryOrZero (i - 1) - 1 := by
    have hnext : i - 2 + 1 = i - 1 := by omega
    rw [hnext] at hpair
    omega
  have htargetLower := b.orderGap_ge_neg_two_mul_e previous
  have hpreviousSuccVal : previous.succ.val = i - 1 := by
    dsimp only [previous]
    change i - 2 + 1 = i - 1
    omega
  have hpreviousCastVal : previous.castSucc.val = i - 2 := by
    rfl
  have hsourceGapStrict : -(2 * (ramificationIndex K : Int)) <
      a.orderGap previous := by
    unfold orderGap at htargetLower ⊢
    rw [← b.orderSequence_entryOrZero_eq_order previous.succ,
      ← b.orderSequence_entryOrZero_eq_order previous.castSucc]
      at htargetLower
    rw [← a.orderSequence_entryOrZero_eq_order previous.succ,
      ← a.orderSequence_entryOrZero_eq_order previous.castSucc]
    rw [hpreviousSuccVal, hpreviousCastVal] at htargetLower ⊢
    change -(2 * (ramificationIndex K : Int)) ≤
      b.orderSequence.entryOrZero (i - 1) -
        b.orderSequence.entryOrZero (i - 2) at htargetLower
    omega
  have halphaNe : a.alphaValue previous ≠ 0 := by
    intro hzero
    exact (ne_of_gt hsourceGapStrict) ((a.alpha_p2 previous).2.mp hzero)
  have halphaIntegral : IsRationalInteger (a.alphaValue previous) := by
    rcases a.beli2009Corollary28_iii previous with hsmall | hlarge
    · exact hsmall.2.2
    · have honeTwoE : (1 : ℚ) ≤ 2 * (ramificationIndex K : ℚ) := by
        have hePos := ramificationIndex_pos (K := K)
        exact_mod_cast (show (1 : Int) ≤
          2 * (ramificationIndex K : Int) by omega)
      exact (not_lt_of_ge (halphaLe.trans honeTwoE) hlarge.1).elim
  rcases halphaIntegral with ⟨z, hz⟩
  have hzNonnegative : (0 : Int) ≤ z := by
    exact_mod_cast (show (0 : ℚ) ≤ (z : ℚ) by
      simpa only [← hz] using (a.alpha_p2 previous).1)
  have hzLe : z ≤ (1 : Int) := by
    exact_mod_cast (show (z : ℚ) ≤ 1 by
      simpa only [← hz] using halphaLe)
  have hzNe : z ≠ 0 := by
    intro hzZero
    apply halphaNe
    rw [hz, hzZero]
    norm_num
  have hzOne : z = 1 := by omega
  simpa only [previous] using (show a.alphaValue previous = 1 by
    rw [hz, hzOne]
    norm_num)

/-- Section 7 wrapper, obtaining the central alpha from Lemma 7.8's
normalization. -/
theorem lemma78_typeIII_sourcePreviousAlpha_eq_one
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
    (i : Nat) (hiTwo : 2 ≤ i)
    (hiLeft : i ≤ D.outer.transition.lastZero) (hiEven : Even i) :
    a.alphaValue ⟨i - 2, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ = 1 := by
  have hdata := a.beli2019Lemma78_alphas_and_gap
    b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
  apply a.lemma78_typeIII_sourcePreviousAlpha_eq_one_of_center
    b D hfirst hdata.1 i hiTwo hiLeft hiEven

end BONG.GoodBONG

end Bong
