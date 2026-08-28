/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma92LowRank
import Bong.Bong.Beli2019Lemma84

/-!
# Beli (2019), Lemma 9.2: quaternary reduction arithmetic

This file formalizes the paragraph on pp. 34--35 beginning with the failure of
the original head-deletion equality in rank four.  That strict failure forces
the lost first left-defect candidate to attain the third alpha.  Endpoint
monotonicity then gives the common right endpoint, the two alpha recursions,
the strict last-adjacent defect, the strict alpha sum, and the odd unit-defect
depths used in the construction.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Strict failure of the rank-four head-deletion equality, in `WithTop`
form. -/
theorem rankFour_alphaTwo_lt_tailAlphaOne_of_ne
    (a : GoodBONG q L 4)
    (hne : a.alphaValue (2 : Fin 3) ≠
      a.tail.alphaValue (1 : Fin 2)) :
    a.alpha (2 : Fin 3) < a.tail.alpha (1 : Fin 2) := by
  have hle := a.alphaValue_shift_le_tail (1 : Fin 2)
  have hindex : Fin.succ (1 : Fin 2) = (2 : Fin 3) := Fin.ext rfl
  rw [hindex] at hle
  have hleQ : a.alphaValue (2 : Fin 3) ≤
      a.tail.alphaValue (1 : Fin 2) := WithTop.coe_le_coe.mp hle
  have hlt : a.alphaValue (2 : Fin 3) <
      a.tail.alphaValue (1 : Fin 2) := lt_of_le_of_ne hleQ hne
  rw [← a.coe_alphaValue, ← a.tail.coe_alphaValue]
  exact_mod_cast hlt

/-- The strict branch makes the unique candidate lost after deleting the
head attain the third alpha. -/
theorem rankFour_alphaTwo_eq_firstLeftCandidate_of_ne
    (a : GoodBONG q L 4)
    (hne : a.alphaValue (2 : Fin 3) ≠
      a.tail.alphaValue (1 : Fin 2)) :
    (a.alphaValue (2 : Fin 3) : WithTop ℚ) =
      a.leftDefectCandidate (2 : Fin 3) (0 : Fin 3) := by
  have hstrict := a.rankFour_alphaTwo_lt_tailAlphaOne_of_ne hne
  have hlost := a.firstLeftDefect_lt_tailAlpha_of_alpha_shift_lt
    (1 : Fin 2) hstrict
  rw [a.coe_alphaValue]
  exact a.alpha_shift_eq_firstLeftDefect_of_lt_tailAlpha
    (1 : Fin 2) hlost

set_option maxHeartbeats 800000 in
-- The proof combines `WithTop` finiteness extraction with several exact
-- rational endpoint calculations.
/-- Failure of the original equality and the early alternative produce
exactly one of the two rank-four numerical certificates used by the low-rank
construction. -/
theorem rankFour_reduction_of_early_of_ne
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 4) (hearly : a.Lemma92EarlyAlternative)
    (hne : a.alphaValue (2 : Fin 3) ≠
      a.tail.alphaValue (1 : Fin 2)) :
    Lemma92RankFourFirstData a ∨ Lemma92RankFourAlternatingData a := by
  have hstrictTop := a.rankFour_alphaTwo_lt_tailAlphaOne_of_ne hne
  have hstrict : a.alphaValue (2 : Fin 3) <
      a.tail.alphaValue (1 : Fin 2) := by
    rw [← a.coe_alphaValue, ← a.tail.coe_alphaValue] at hstrictTop
    exact_mod_cast hstrictTop
  have hlost := a.rankFour_alphaTwo_eq_firstLeftCandidate_of_ne hne
  have hadjacentFinite : a.adjacentDefect (0 : Fin 3) ≠ ⊤ := by
    intro htop
    rw [leftDefectCandidate, htop] at hlost
    simp only [add_top] at hlost
    exact WithTop.coe_ne_top hlost
  let delta : ℚ :=
    (a.adjacentDefect (0 : Fin 3)).untop hadjacentFinite
  have hdelta : (delta : WithTop ℚ) =
      a.adjacentDefect (0 : Fin 3) :=
    WithTop.coe_untop _ _
  have hlostQ : a.alphaValue (2 : Fin 3) =
      ((a.order (3 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ) + delta := by
    rw [leftDefectCandidate, ← hdelta, ← WithTop.coe_add] at hlost
    exact WithTop.coe_eq_coe.mp hlost
  have hfirstUpperTop :=
    a.alpha_le_leftDefectCandidate
      (i := (0 : Fin 3)) (j := (0 : Fin 3)) le_rfl
  have hfirstUpper : a.alphaValue (0 : Fin 3) ≤
      ((a.order (1 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ) + delta := by
    rw [← a.coe_alphaValue, leftDefectCandidate, ← hdelta,
      ← WithTop.coe_add] at hfirstUpperTop
    exact_mod_cast hfirstUpperTop
  have hendpoint02Le :=
    a.alphaRightEndpoint_antitone (show (0 : Fin 3) ≤ (2 : Fin 3) by omega)
  have hfirstLower :
      ((a.order (1 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ) + delta ≤
        a.alphaValue (0 : Fin 3) := by
    unfold alphaRightEndpoint at hendpoint02Le
    push_cast at hendpoint02Le hlostQ ⊢
    linarith
  have hfirstQ : a.alphaValue (0 : Fin 3) =
      ((a.order (1 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ) + delta :=
    le_antisymm hfirstUpper hfirstLower
  have hright02 : a.alphaRightEndpoint (2 : Fin 3) =
      a.alphaRightEndpoint (0 : Fin 3) := by
    unfold alphaRightEndpoint
    push_cast at hlostQ hfirstQ ⊢
    linarith
  have hsource : ∀ i : Fin 3,
      a.alphaRightEndpoint i = a.alphaRightEndpoint (0 : Fin 3) := by
    intro i
    exact a.beli2019Lemma84_i_right (0 : Fin 3) (2 : Fin 3)
      (Fin.zero_le _) hright02.symm i (Fin.zero_le _) (Fin.le_last i)
  have hright01 := hsource (1 : Fin 3)
  have hright02' := hsource (2 : Fin 3)
  have hsecondRecursion : a.alphaValue (1 : Fin 3) =
      ((a.order (2 : Fin 4) - a.order (1 : Fin 4) : Int) : ℚ) +
        a.alphaValue (0 : Fin 3) := by
    unfold alphaRightEndpoint at hright01
    push_cast at hright01 ⊢
    linarith
  have hthirdRecursion : a.alphaValue (2 : Fin 3) =
      ((a.orderGap (2 : Fin 3) : Int) : ℚ) +
        a.alphaValue (1 : Fin 3) := by
    unfold alphaRightEndpoint at hright01 hright02'
    unfold orderGap
    push_cast at hright01 hright02' ⊢
    linarith
  have htailLast := a.tail.alpha_le_leftDefectCandidate
    (i := (1 : Fin 2)) (j := (1 : Fin 2)) le_rfl
  rw [a.leftDefectCandidate_tail] at htailLast
  have hlastRaw : (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
      a.leftDefectCandidate (2 : Fin 3) (2 : Fin 3) := by
    have hraw := hstrictTop.trans_le htailLast
    have hindex : Fin.succ (1 : Fin 2) = (2 : Fin 3) := Fin.ext rfl
    rw [← a.coe_alphaValue (2 : Fin 3), hindex] at hraw
    exact hraw
  have hthirdTop := congrArg (fun x : ℚ => (x : WithTop ℚ)) hthirdRecursion
  rw [WithTop.coe_add] at hthirdTop
  have hlastAdjacent : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (2 : Fin 3) := by
    unfold leftDefectCandidate at hlastRaw
    unfold orderGap at hthirdTop
    rw [hthirdTop] at hlastRaw
    exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hlastRaw
  have hhalfTail :=
    a.tail.alphaValue_le_halfGapValue (1 : Fin 2)
  have htailHalfEq : a.tail.halfGapValue (1 : Fin 2) =
      a.halfGapValue (2 : Fin 3) := by
    unfold halfGapValue orderGap
    rw [a.order_goodTail (1 : Fin 2).succ,
      a.order_goodTail (1 : Fin 2).castSucc]
    congr 3
  have hthirdHalf : a.alphaValue (2 : Fin 3) <
      a.halfGapValue (2 : Fin 3) := by
    exact hstrict.trans_le (htailHalfEq ▸ hhalfTail)
  have hsum : a.alphaValue (1 : Fin 3) +
      a.alphaValue (2 : Fin 3) <
        2 * (ramificationIndex K : ℚ) := by
    unfold halfGapValue orderGap at hthirdHalf
    unfold orderGap at hthirdRecursion
    push_cast at hthirdHalf hthirdRecursion ⊢
    linarith
  have hthirdNonnegative := (a.beli2009Lemma27_i (2 : Fin 3)).1
  have hsecondNonnegative := (a.beli2009Lemma27_i (1 : Fin 3)).1
  have hthirdLt : a.alphaValue (2 : Fin 3) <
      2 * (ramificationIndex K : ℚ) := by linarith
  have hsecondLt : a.alphaValue (1 : Fin 3) <
      2 * (ramificationIndex K : ℚ) := by linarith
  have hthirdNotHalf : a.alphaValue (2 : Fin 3) ≠
      a.halfGapValue (2 : Fin 3) := ne_of_lt hthirdHalf
  have hsecondHalf : a.alphaValue (1 : Fin 3) <
      a.halfGapValue (1 : Fin 3) := by
    apply lt_of_le_of_ne (a.alphaValue_le_halfGapValue (1 : Fin 3))
    intro heq
    have hpropagate := a.beli2019Lemma84_iii
      (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (Fin.zero_le _)
      (Fin.zero_le _) (by decide) hright02.symm heq
    exact hthirdNotHalf (hpropagate.2 (2 : Fin 3) (by decide) le_rfl)
  have hfirstHalf : a.alphaValue (0 : Fin 3) <
      a.halfGapValue (0 : Fin 3) := by
    apply lt_of_le_of_ne (a.alphaValue_le_halfGapValue (0 : Fin 3))
    intro heq
    have hpropagate := a.beli2019Lemma84_iii
      (0 : Fin 3) (2 : Fin 3) (0 : Fin 3) (Fin.zero_le _) le_rfl
      (Fin.zero_le _) hright02.symm heq
    exact hthirdNotHalf (hpropagate.2 (2 : Fin 3) (Fin.zero_le _) le_rfl)
  have hsecondOdd : IsOddRationalInteger (a.alphaValue (1 : Fin 3)) :=
    a.beli2009Lemma27_iv (1 : Fin 3) (ne_of_lt hsecondHalf)
  have hthirdOdd : IsOddRationalInteger (a.alphaValue (2 : Fin 3)) :=
    a.beli2009Lemma27_iv (2 : Fin 3) hthirdNotHalf
  let C : Lemma92RankFourCommonData a := {
    secondAlpha_odd := hsecondOdd
    secondAlpha_nonnegative := hsecondNonnegative
    secondAlpha_lt_twoE := hsecondLt
    thirdAlpha_odd := hthirdOdd
    thirdAlpha_nonnegative := hthirdNonnegative
    thirdAlpha_lt_twoE := hthirdLt
    lastAdjacent_gt_secondAlpha := by
      have hindex : Fin.succ (1 : Fin 2) = (2 : Fin 3) := Fin.ext rfl
      rw [a.adjacentDefect_tail (1 : Fin 2), hindex]
      exact hlastAdjacent
    secondThird_sum_lt_twoE := hsum
    thirdAlpha_recursion := hthirdRecursion
  }
  have hfirstCandidate :
      (((a.orderGap (0 : Fin 3) : Int) : ℚ) : WithTop ℚ) +
          a.adjacentDefect (0 : Fin 3) =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
    unfold orderGap
    rw [← hdelta, ← WithTop.coe_add]
    exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hfirstQ.symm
  by_cases houter : a.order (0 : Fin 4) < a.order (2 : Fin 4)
  · have hdeltaLt : delta < a.alphaValue (1 : Fin 3) := by
      have houterQ : (a.order (0 : Fin 4) : ℚ) <
          a.order (2 : Fin 4) := by exact_mod_cast houter
      push_cast at hfirstQ hsecondRecursion
      linarith
    exact Or.inl {
      toLemma92RankFourCommonData := C
      firstAdjacent_lt_secondAlpha := by
        rw [← hdelta]
        exact_mod_cast hdeltaLt
      firstAlpha_candidate := hfirstCandidate
      commonRightEndpoint := hsource
    }
  · have houterLe : a.order (0 : Fin 4) ≤ a.order (2 : Fin 4) :=
      a.good (0 : Fin 4) (by omega)
    have houterEq : a.order (0 : Fin 4) = a.order (2 : Fin 4) :=
      le_antisymm houterLe (le_of_not_gt houter)
    have hsecondFourth : a.order (1 : Fin 4) = a.order (3 : Fin 4) := by
      rcases hearly with hlt | heq | hgap
      · exact (houter hlt).elim
      · exact heq
      · have hfirstAttains : a.alphaValue (0 : Fin 3) =
            a.halfGapValue (0 : Fin 3) :=
          a.alpha_p4 (0 : Fin 3) hgap.ge
        exact (ne_of_lt hfirstHalf hfirstAttains).elim
    exact Or.inr {
      toLemma92RankFourCommonData := C
      alternating := ⟨houterEq, hsecondFourth⟩
      firstAlpha_candidate := hfirstCandidate
      commonRightEndpoint := hsource
    }

/-- Complete rank-four reduction, including the identity branch. -/
theorem rankFour_reduction
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 4) (hearly : a.Lemma92EarlyAlternative) :
    a.alphaValue (2 : Fin 3) = a.tail.alphaValue (1 : Fin 2) ∨
      Lemma92RankFourFirstData a ∨
        Lemma92RankFourAlternatingData a := by
  by_cases heq : a.alphaValue (2 : Fin 3) =
      a.tail.alphaValue (1 : Fin 2)
  · exact Or.inl heq
  · exact Or.inr (a.rankFour_reduction_of_early_of_ne hearly heq)

/-- Beli (2019), Lemma 9.2 in rank four, with every branch discharged. -/
theorem beli2019Lemma92_rankFour
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 4) :
    Nonempty (Beli2019Lemma92Transform a) := by
  by_cases hearly : a.Lemma92EarlyAlternative
  · exact exists_lemma92Transform_rankFour_of_reduction
      a (a.rankFour_reduction hearly)
  · apply exists_lemma92Transform_identity a
    · intro i hi
      omega
    · intro hcase
      exact (hearly hcase).elim

end BONG.GoodBONG

end Bong
