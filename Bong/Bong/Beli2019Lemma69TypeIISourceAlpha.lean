/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIICoreAlpha
import Bong.Bong.Beli2019Lemma69TypeIIDual

/-!
# Beli (2019), Lemma 6.9(i): type-II source alphas

The source alpha at the left boundary is one because its adjacent source
orders are `T - 1, T`.  Endpoint monotonicity propagates the upper bound
through the alternating left profile, while the target gap excludes zero.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The type-II source alpha at the left transition is exactly one. -/
theorem beli2019Lemma69_i_typeII_sourceBoundary_eq_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b) :
    a.alphaValue ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      have hlong := D.long
      omega⟩ = 1 := by
  let left := D.outer.transition.lastZero
  have hleftBound : left < n + 1 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    have hlong := D.long
    dsimp only [left]
    omega
  let center : Fin (n + 1) := ⟨left, hleftBound⟩
  let T := b.orderSequence.entryOrZero left
  have hsourceCurrent : a.orderSequence.entryOrZero left = T - 1 := by
    have hboundary := D.outer.transition.leftBoundary
    have hboundary' : b.orderSequence.entryOrZero left =
        a.orderSequence.entryOrZero left + 1 := by
      simpa only [left] using hboundary
    dsimp only [T]
    omega
  have hsourceNext : a.orderSequence.entryOrZero (left + 1) = T := by
    simpa only [T] using D.middle (left + 1) (by omega) (by
      have hlong := D.long
      omega)
  have hcurrentOrder : a.order center.castSucc = T - 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order center.castSucc]
    exact hsourceCurrent
  have hnextOrder : a.order center.succ = T := by
    rw [← a.orderSequence_entryOrZero_eq_order center.succ]
    change a.orderSequence.entryOrZero (left + 1) = T
    exact hsourceNext
  have hsumOdd : Odd (a.order center.castSucc + a.order center.succ) := by
    rw [hcurrentOrder, hnextOrder]
    exact ⟨T - 1, by omega⟩
  have hadjacent : a.adjacentDefect center = 0 :=
    a.adjacentDefect_eq_zero_of_order_sum_odd center hsumOdd
  have hgap : a.order center.succ - a.order center.castSucc = 1 := by
    rw [hcurrentOrder, hnextOrder]
    omega
  have hcandidate : a.leftDefectCandidate center center =
      (1 : WithTop ℚ) := by
    unfold leftDefectCandidate
    rw [hadjacent, hgap]
    norm_num
  have hupperTop := a.alpha_le_leftDefectCandidate
    (i := center) (j := center) le_rfl
  rw [← a.coe_alphaValue, hcandidate] at hupperTop
  have hupper : a.alphaValue center ≤ 1 := by
    exact_mod_cast hupperTop
  have hgapValue : a.orderGap center = 1 := by
    unfold orderGap
    rw [hcurrentOrder, hnextOrder]
    omega
  have hne : a.alphaValue center ≠ 0 := by
    intro hzero
    have hp2 := (a.alpha_p2 center).2.mp hzero
    rw [hgapValue] at hp2
    have hePos := ramificationIndex_pos (K := K)
    omega
  have hlower := a.one_le_alphaValue_of_ne_zero center hne
  have heq : a.alphaValue center = 1 := le_antisymm hupper hlower
  simpa only [center, left] using heq

/-- Every source alpha immediately before an even boundary in the normalized
type-II left profile is one. -/
theorem lemma69_typeII_sourcePreviousAlpha_eq_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (i : Nat) (hiTwo : 2 ≤ i)
    (hiLeft : i ≤ D.outer.transition.lastZero) (hiEven : Even i) :
    a.alphaValue ⟨i - 2, by
      have hbound := D.outer.transition.firstTwo_le_rank
      have hlong := D.long
      omega⟩ = 1 := by
  let left := D.outer.transition.lastZero
  let center : Fin (n + 1) := ⟨left, by
    dsimp only [left]
    have hbound := D.outer.transition.firstTwo_le_rank
    have hlong := D.long
    omega⟩
  let previous : Fin (n + 1) := ⟨i - 2, by
    have hbound := D.outer.transition.firstTwo_le_rank
    have hlong := D.long
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
    have hleftSame := hprofile.2.2 left D.outer.first_le_left
      le_rfl hprofile.1
    exact hsame.trans hleftSame.symm
  have hsourceCenter : a.order previous.castSucc =
      a.order center.castSucc := by
    rw [← a.orderSequence_entryOrZero_eq_order previous.castSucc,
      ← a.orderSequence_entryOrZero_eq_order center.castSucc]
    change a.orderSequence.entryOrZero (i - 2) =
      a.orderSequence.entryOrZero left
    exact hsourcePrevious
  have hcentralOne : a.alphaValue center = 1 := by
    simpa only [center, left] using
      a.beli2019Lemma69_i_typeII_sourceBoundary_eq_one b D
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
        have hlong := D.long
        omega) hpreviousEven
    have htoLeft := b.orderSequence.entryOrZero_le_of_evenGap
      (i - 2) left (by omega) (by
        have hbound := D.outer.transition.firstTwo_le_rank
        have hlong := D.long
        dsimp only [left]
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
  have hpreviousCastVal : previous.castSucc.val = i - 2 := by rfl
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

/-- Compatibility form of the type-II source-alpha propagation theorem.
The central hypothesis records the induction seed explicitly, as in the
type-III proof; for type II that seed is already a theorem of the profile. -/
theorem lemma69_typeII_sourcePreviousAlpha_eq_one_of_center
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (_hcenter : a.alphaValue
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        have hlong := D.long
        omega⟩ = 1)
    (i : Nat) (hiTwo : 2 ≤ i)
    (hiLeft : i ≤ D.outer.transition.lastZero) (hiEven : Even i) :
    a.alphaValue ⟨i - 2, by
      have hbound := D.outer.transition.firstTwo_le_rank
      have hlong := D.long
      omega⟩ = 1 := by
  exact a.lemma69_typeII_sourcePreviousAlpha_eq_one b D hfirst
    i hiTwo hiLeft hiEven

end BONG.GoodBONG

end Bong
