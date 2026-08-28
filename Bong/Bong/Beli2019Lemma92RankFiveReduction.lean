/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma92RankFourReduction

/-!
# Beli (2019), Lemma 9.2: rank-five reduction arithmetic

This file formalizes the final low-rank paragraph in the proof of Lemma 9.2.
After Corollary 8.10 normalizes the first literal binary segment, strict
failure of the head-deletion equality makes the lost first left-defect
candidate attain the fourth alpha.  Endpoint monotonicity then yields the
common right endpoint, the three alpha recursions, the strict final adjacent
defect, and the odd unit-defect depths required by the rank-five scaling.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Strict failure of the rank-five head-deletion equality, in `WithTop`
form. -/
theorem rankFive_alphaThree_lt_tailAlphaTwo_of_ne
    (a : GoodBONG q L 5)
    (hne : a.alphaValue (3 : Fin 4) ≠
      a.tail.alphaValue (2 : Fin 3)) :
    a.alpha (3 : Fin 4) < a.tail.alpha (2 : Fin 3) := by
  have hle := a.alphaValue_shift_le_tail (2 : Fin 3)
  have hindex : Fin.succ (2 : Fin 3) = (3 : Fin 4) := Fin.ext rfl
  rw [hindex] at hle
  have hleQ : a.alphaValue (3 : Fin 4) ≤
      a.tail.alphaValue (2 : Fin 3) := WithTop.coe_le_coe.mp hle
  have hlt : a.alphaValue (3 : Fin 4) <
      a.tail.alphaValue (2 : Fin 3) := lt_of_le_of_ne hleQ hne
  rw [← a.coe_alphaValue, ← a.tail.coe_alphaValue]
  exact_mod_cast hlt

/-- The strict rank-five branch makes the unique candidate lost after
deleting the head attain the fourth alpha. -/
theorem rankFive_alphaThree_eq_firstLeftCandidate_of_ne
    (a : GoodBONG q L 5)
    (hne : a.alphaValue (3 : Fin 4) ≠
      a.tail.alphaValue (2 : Fin 3)) :
    (a.alphaValue (3 : Fin 4) : WithTop ℚ) =
      a.leftDefectCandidate (3 : Fin 4) (0 : Fin 4) := by
  have hstrict := a.rankFive_alphaThree_lt_tailAlphaTwo_of_ne hne
  have hlost := a.firstLeftDefect_lt_tailAlpha_of_alpha_shift_lt
    (2 : Fin 3) hstrict
  rw [a.coe_alphaValue]
  exact a.alpha_shift_eq_firstLeftDefect_of_lt_tailAlpha
    (2 : Fin 3) hlost

set_option maxHeartbeats 1000000 in
-- The proof combines finite `WithTop` extraction, endpoint calculations,
-- and dependent `Fin` transports through two projected tails.
/-- In the normalized complementary branch, failure of the original
head-deletion equality gives exactly the numerical rank-five certificate
used by the explicit scaling construction. -/
theorem rankFive_reduction_of_normalized_of_ne
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 5) (hnotEarly : ¬a.Lemma92EarlyAlternative)
    (hbinary : a.adjacentBinaryAlpha (0 : Fin 4) =
      (a.alphaValue (0 : Fin 4) : WithTop ℚ))
    (hne : a.alphaValue (3 : Fin 4) ≠
      a.tail.alphaValue (2 : Fin 3)) :
    Lemma92RankFiveData a := by
  have hstrictTop := a.rankFive_alphaThree_lt_tailAlphaTwo_of_ne hne
  have hstrict : a.alphaValue (3 : Fin 4) <
      a.tail.alphaValue (2 : Fin 3) := by
    rw [← a.coe_alphaValue, ← a.tail.coe_alphaValue] at hstrictTop
    exact_mod_cast hstrictTop
  have hlost := a.rankFive_alphaThree_eq_firstLeftCandidate_of_ne hne
  have hadjacentFinite : a.adjacentDefect (0 : Fin 4) ≠ ⊤ := by
    intro htop
    rw [leftDefectCandidate, htop] at hlost
    simp only [add_top] at hlost
    exact WithTop.coe_ne_top hlost
  let delta : ℚ :=
    (a.adjacentDefect (0 : Fin 4)).untop hadjacentFinite
  have hdelta : (delta : WithTop ℚ) =
      a.adjacentDefect (0 : Fin 4) :=
    WithTop.coe_untop _ _
  have hlostQ : a.alphaValue (3 : Fin 4) =
      ((a.order (4 : Fin 5) - a.order (0 : Fin 5) : Int) : ℚ) + delta := by
    rw [leftDefectCandidate, ← hdelta, ← WithTop.coe_add] at hlost
    exact WithTop.coe_eq_coe.mp hlost
  have hfirstUpperTop :=
    a.alpha_le_leftDefectCandidate
      (i := (0 : Fin 4)) (j := (0 : Fin 4)) le_rfl
  have hfirstUpper : a.alphaValue (0 : Fin 4) ≤
      ((a.order (1 : Fin 5) - a.order (0 : Fin 5) : Int) : ℚ) + delta := by
    rw [← a.coe_alphaValue, leftDefectCandidate, ← hdelta,
      ← WithTop.coe_add] at hfirstUpperTop
    exact_mod_cast hfirstUpperTop
  have hendpoint03Le :=
    a.alphaRightEndpoint_antitone (show (0 : Fin 4) ≤ (3 : Fin 4) by omega)
  have hfirstLower :
      ((a.order (1 : Fin 5) - a.order (0 : Fin 5) : Int) : ℚ) + delta ≤
        a.alphaValue (0 : Fin 4) := by
    unfold alphaRightEndpoint at hendpoint03Le
    push_cast at hendpoint03Le hlostQ ⊢
    linarith
  have hfirstQ : a.alphaValue (0 : Fin 4) =
      ((a.order (1 : Fin 5) - a.order (0 : Fin 5) : Int) : ℚ) + delta :=
    le_antisymm hfirstUpper hfirstLower
  have hright03 : a.alphaRightEndpoint (3 : Fin 4) =
      a.alphaRightEndpoint (0 : Fin 4) := by
    unfold alphaRightEndpoint
    push_cast at hlostQ hfirstQ ⊢
    linarith
  have hsource : ∀ i : Fin 4,
      a.alphaRightEndpoint i = a.alphaRightEndpoint (0 : Fin 4) := by
    intro i
    exact a.beli2019Lemma84_i_right (0 : Fin 4) (3 : Fin 4)
      (Fin.zero_le _) hright03.symm i (Fin.zero_le _) (Fin.le_last i)
  have hright01 := hsource (1 : Fin 4)
  have hright02 := hsource (2 : Fin 4)
  have hright03' := hsource (3 : Fin 4)
  have hsecondRecursion : a.alphaValue (1 : Fin 4) =
      ((a.orderGap (1 : Fin 4) : Int) : ℚ) +
        a.alphaValue (0 : Fin 4) := by
    unfold alphaRightEndpoint at hright01
    unfold orderGap
    push_cast at hright01 ⊢
    linarith
  have hthirdRecursion : a.alphaValue (2 : Fin 4) =
      ((a.orderGap (2 : Fin 4) : Int) : ℚ) +
        a.alphaValue (1 : Fin 4) := by
    unfold alphaRightEndpoint at hright01 hright02
    unfold orderGap
    push_cast at hright01 hright02 ⊢
    linarith
  have hfourthRecursion : a.alphaValue (3 : Fin 4) =
      ((a.orderGap (3 : Fin 4) : Int) : ℚ) +
        a.alphaValue (2 : Fin 4) := by
    unfold alphaRightEndpoint at hright02 hright03'
    unfold orderGap
    push_cast at hright02 hright03' ⊢
    linarith
  have htailLast := a.tail.alpha_le_leftDefectCandidate
    (i := (2 : Fin 3)) (j := (2 : Fin 3)) le_rfl
  rw [a.leftDefectCandidate_tail] at htailLast
  have hlastRaw : (a.alphaValue (3 : Fin 4) : WithTop ℚ) <
      a.leftDefectCandidate (3 : Fin 4) (3 : Fin 4) := by
    have hraw := hstrictTop.trans_le htailLast
    have hindex : Fin.succ (2 : Fin 3) = (3 : Fin 4) := Fin.ext rfl
    rw [← a.coe_alphaValue (3 : Fin 4), hindex] at hraw
    exact hraw
  have hfourthTop :=
    congrArg (fun x : ℚ => (x : WithTop ℚ)) hfourthRecursion
  rw [WithTop.coe_add] at hfourthTop
  have hlastAdjacent : (a.alphaValue (2 : Fin 4) : WithTop ℚ) <
      a.adjacentDefect (3 : Fin 4) := by
    unfold leftDefectCandidate at hlastRaw
    unfold orderGap at hfourthTop
    rw [hfourthTop] at hlastRaw
    exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hlastRaw
  have hhalfTail := a.tail.alphaValue_le_halfGapValue (2 : Fin 3)
  have htailHalfEq : a.tail.halfGapValue (2 : Fin 3) =
      a.halfGapValue (3 : Fin 4) := by
    unfold halfGapValue orderGap
    rw [a.order_goodTail (2 : Fin 3).succ,
      a.order_goodTail (2 : Fin 3).castSucc]
    congr 2
  have hfourthHalf : a.alphaValue (3 : Fin 4) <
      a.halfGapValue (3 : Fin 4) :=
    hstrict.trans_le (htailHalfEq ▸ hhalfTail)
  have hsum : a.alphaValue (2 : Fin 4) +
      a.alphaValue (3 : Fin 4) <
        2 * (ramificationIndex K : ℚ) := by
    unfold halfGapValue orderGap at hfourthHalf
    unfold orderGap at hfourthRecursion
    push_cast at hfourthHalf hfourthRecursion ⊢
    linarith
  have hthirdNonnegative := (a.beli2009Lemma27_i (2 : Fin 4)).1
  have hfourthNonnegative := (a.beli2009Lemma27_i (3 : Fin 4)).1
  have hthirdLt : a.alphaValue (2 : Fin 4) <
      2 * (ramificationIndex K : ℚ) := by linarith
  have hfourthLt : a.alphaValue (3 : Fin 4) <
      2 * (ramificationIndex K : ℚ) := by linarith
  have hfourthNotHalf : a.alphaValue (3 : Fin 4) ≠
      a.halfGapValue (3 : Fin 4) := ne_of_lt hfourthHalf
  have hthirdHalf : a.alphaValue (2 : Fin 4) <
      a.halfGapValue (2 : Fin 4) := by
    apply lt_of_le_of_ne (a.alphaValue_le_halfGapValue (2 : Fin 4))
    intro heq
    have hpropagate := a.beli2019Lemma84_iii
      (0 : Fin 4) (3 : Fin 4) (2 : Fin 4) (Fin.zero_le _)
      (Fin.zero_le _) (by decide) hright03.symm heq
    exact hfourthNotHalf
      (hpropagate.2 (3 : Fin 4) (by decide) le_rfl)
  have hthirdOdd : IsOddRationalInteger (a.alphaValue (2 : Fin 4)) :=
    a.beli2009Lemma27_iv (2 : Fin 4) (ne_of_lt hthirdHalf)
  have hfourthOdd : IsOddRationalInteger (a.alphaValue (3 : Fin 4)) :=
    a.beli2009Lemma27_iv (3 : Fin 4) hfourthNotHalf
  exact {
    thirdAlpha_odd := hthirdOdd
    thirdAlpha_nonnegative := hthirdNonnegative
    thirdAlpha_lt_twoE := hthirdLt
    fourthAlpha_odd := hfourthOdd
    fourthAlpha_nonnegative := hfourthNonnegative
    fourthAlpha_lt_twoE := hfourthLt
    lastAdjacent_gt_thirdAlpha := by
      have htailOne : a.tail.tail.adjacentDefect (1 : Fin 2) =
          a.tail.adjacentDefect (2 : Fin 3) := by
        rw [a.tail.adjacentDefect_tail (1 : Fin 2)]
        congr 1
      have htailTwo : a.tail.adjacentDefect (2 : Fin 3) =
          a.adjacentDefect (3 : Fin 4) := by
        rw [a.adjacentDefect_tail (2 : Fin 3)]
        congr 1
      rw [htailOne, htailTwo]
      exact hlastAdjacent
    thirdFourth_sum_lt_twoE := hsum
    fourthAlpha_recursion := hfourthRecursion
    firstBinary_normalized := hbinary
    commonRightEndpoint := hsource
    notEarly := hnotEarly
  }

/-- Exhaustion of the normalized rank-five branch. -/
theorem rankFive_reduction_of_normalized
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 5) (hnotEarly : ¬a.Lemma92EarlyAlternative)
    (hbinary : a.adjacentBinaryAlpha (0 : Fin 4) =
      (a.alphaValue (0 : Fin 4) : WithTop ℚ)) :
    a.alphaValue (3 : Fin 4) = a.tail.alphaValue (2 : Fin 3) ∨
      Lemma92RankFiveData a := by
  by_cases heq : a.alphaValue (3 : Fin 4) =
      a.tail.alphaValue (2 : Fin 3)
  · exact Or.inl heq
  · exact Or.inr
      (a.rankFive_reduction_of_normalized_of_ne hnotEarly hbinary heq)

/-- The early alternative is invariant under changing the good BONG of a
fixed rank-five lattice. -/
theorem lemma92EarlyAlternative_iff_of_sameLattice_rankFive
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a b : GoodBONG q L 5) :
    a.Lemma92EarlyAlternative ↔ b.Lemma92EarlyAlternative := by
  have horders := a.order_invariant b
  have hzero := horders (0 : Fin 5)
  have hone := horders (1 : Fin 5)
  have htwo := horders (2 : Fin 5)
  have hthree := horders (3 : Fin 5)
  have hgap : a.orderGap (0 : Fin 4) = b.orderGap (0 : Fin 4) := by
    unfold orderGap
    have hlocalSucc : Fin.succ (0 : Fin 4) = (1 : Fin 5) := Fin.ext rfl
    have hlocalCast : Fin.castSucc (0 : Fin 4) = (0 : Fin 5) := Fin.ext rfl
    rw [hlocalSucc, hlocalCast, hzero, hone]
  unfold Lemma92EarlyAlternative
  rw [hzero, hone, htwo, hthree, hgap]

/-- Beli (2019), Lemma 9.2 in rank five in the complement of the early
alternative.  Corollary 8.10 supplies the first-binary normalization and the
resulting transform is then rebased to the original good BONG. -/
theorem beli2019Lemma92_rankFive_of_notEarly
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 5) (hnotEarly : ¬a.Lemma92EarlyAlternative) :
    Nonempty (Beli2019Lemma92Transform a) := by
  rcases a.beli2019Corollary810 with ⟨D⟩
  let b : GoodBONG q L 5 := D.transformed
  have hbNotEarly : ¬b.Lemma92EarlyAlternative := by
    intro hb
    exact hnotEarly
      ((a.lemma92EarlyAlternative_iff_of_sameLattice_rankFive b).mpr hb)
  have hbinary : b.adjacentBinaryAlpha (0 : Fin 4) =
      (b.alphaValue (0 : Fin 4) : WithTop ℚ) := by
    rw [b.adjacentBinaryAlpha_zero]
    exact D.firstBinaryAlpha_eq
  rcases exists_lemma92Transform_rankFive_of_reduction b hbNotEarly
      (b.rankFive_reduction_of_normalized hbNotEarly hbinary) with ⟨T⟩
  exact ⟨{
    transformed := T.transformed
    firstValue_eq := T.firstValue_eq.trans D.headValue_eq
    laterAlpha_eq_tail := by
      intro i hi
      exact (a.alpha_invariant b i.succ).trans (T.laterAlpha_eq_tail i hi)
    earlyAlpha_eq_tail := by
      intro hearly
      exact (hnotEarly hearly).elim
  }⟩

end BONG.GoodBONG

end Bong
