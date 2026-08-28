/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814RankFourBoundary

/-!
# Beli (2019), Lemma 8.14: the preliminary rank-four normalization

This file formalizes the coordinate changes at the start of the equality-boundary
argument in the quaternary case.  Its first ingredients identify the first alpha
of the final ternary segment with the ambient middle alpha after Corollary 8.11.
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
  {L : Lattice K V} {M : Lattice K W}

/-- The final ternary block, viewed as a localization at the ambient second
alpha. -/
def rankFourLastThreeFirstAlphaLocalization : AlphaLocalizationIndex 3 where
  start := 1
  pivot := 1
  stop := 3
  start_le_pivot := le_rfl
  pivot_lt_stop := by omega
  stop_lt := by omega

/-- The literal first-binary alpha of the final ternary segment is the ambient
literal binary alpha at the middle adjacent pair. -/
theorem rankFour_lastThree_firstBinaryAlpha_eq
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 1 3 (by omega)) :
    (segment.toGoodBONG a.good).firstBinaryAlpha =
      a.adjacentBinaryAlpha (1 : Fin 3) := by
  let s := segment.toGoodBONG a.good
  have horder0 : s.order (0 : Fin 3) = a.order (1 : Fin 4) := by
    change segment.bong.order 0 = a.toBONG.order 1
    simp [BONG.SegmentWitness.sourceIndex]
  have horder1 : s.order (1 : Fin 3) = a.order (2 : Fin 4) := by
    change segment.bong.order 1 = a.toBONG.order 2
    simp [BONG.SegmentWitness.sourceIndex]
  have hadjacent : s.adjacentDefect (0 : Fin 2) =
      a.adjacentDefect (1 : Fin 3) := by
    unfold adjacentDefect adjacentProduct GoodBONG.valueUnit
    change defectOrder (K := K)
        (-(segment.bong.valueUnit 0 * segment.bong.valueUnit 1)) =
      defectOrder (K := K)
        (-(a.toBONG.valueUnit 1 * a.toBONG.valueUnit 2))
    rw [segment.valueUnit_eq, segment.valueUnit_eq]
    congr 4
  have hhalf : s.halfGapCandidate (0 : Fin 2) =
      a.halfGapCandidate (1 : Fin 3) := by
    unfold halfGapCandidate
    change
      (((((s.order (1 : Fin 3) - s.order (0 : Fin 3) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) =
        (((((a.order (2 : Fin 4) - a.order (1 : Fin 4) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ)
    rw [horder0, horder1]
  have hleft : s.leftDefectCandidate (0 : Fin 2) (0 : Fin 2) =
      a.leftDefectCandidate (1 : Fin 3) (1 : Fin 3) := by
    unfold leftDefectCandidate
    have hsCast : (0 : Fin 2).castSucc = (0 : Fin 3) := rfl
    have hsSucc : (0 : Fin 2).succ = (1 : Fin 3) := rfl
    have haCast : (1 : Fin 3).castSucc = (1 : Fin 4) := rfl
    have haSucc : (1 : Fin 3).succ = (2 : Fin 4) := rfl
    rw [hsCast, hsSucc, haCast, haSucc]
    rw [horder0, horder1, hadjacent]
  unfold firstBinaryAlpha adjacentBinaryAlpha
  rw [hhalf, hleft]

/-- Once Corollary 8.11 makes the middle literal binary alpha attain the
ambient second alpha, localization shows that the final ternary segment has
the same first alpha. -/
theorem rankFour_lastThree_firstAlpha_eq_of_adjacentBinaryAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 1 3 (by omega))
    (hbinary : a.adjacentBinaryAlpha (1 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ)) :
    (segment.toGoodBONG a.good).alphaValue (0 : Fin 2) =
        a.alphaValue (1 : Fin 3) ∧
      (segment.toGoodBONG a.good).firstBinaryAlpha =
        ((segment.toGoodBONG a.good).alphaValue (0 : Fin 2) : WithTop ℚ) := by
  let s := segment.toGoodBONG a.good
  let p := rankFourLastThreeFirstAlphaLocalization
  have hglobalLeLocalRaw := a.beli2009Lemma21_le_segmentAlpha p segment
  have hpivot : p.pivotFin = (1 : Fin 3) := by
    apply Fin.ext
    rfl
  have hlocalPivot : p.localPivot = (0 : Fin 2) := by
    apply Fin.ext
    rfl
  have hglobalLeLocal :
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
        (s.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    rw [a.coe_alphaValue, s.coe_alphaValue]
    rw [hpivot, hlocalPivot] at hglobalLeLocalRaw
    exact hglobalLeLocalRaw
  have hlocalLeBinary :
      (s.alphaValue (0 : Fin 2) : WithTop ℚ) ≤ s.firstBinaryAlpha := by
    unfold firstBinaryAlpha
    apply le_min
    · rw [s.coe_alphaValue]
      exact s.alpha_le_halfGapCandidate (0 : Fin 2)
    · rw [s.coe_alphaValue]
      exact s.alpha_le_leftDefectCandidate
        (i := (0 : Fin 2)) (j := (0 : Fin 2)) le_rfl
  have hlocalLeGlobal :
      (s.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    rw [rankFour_lastThree_firstBinaryAlpha_eq a segment, hbinary] at hlocalLeBinary
    exact hlocalLeBinary
  have hfirst : s.alphaValue (0 : Fin 2) = a.alphaValue (1 : Fin 3) := by
    exact_mod_cast le_antisymm hlocalLeGlobal hglobalLeLocal
  refine ⟨hfirst, ?_⟩
  rw [rankFour_lastThree_firstBinaryAlpha_eq a segment, hbinary]
  exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hfirst.symm

/-- The final alpha of the final ternary block, viewed as a localization at
the ambient third alpha. -/
def rankFourLastThreeSecondAlphaLocalization : AlphaLocalizationIndex 3 where
  start := 1
  pivot := 2
  stop := 3
  start_le_pivot := by omega
  pivot_lt_stop := by omega
  stop_lt := by omega

/-- The literal last-binary alpha of the final ternary segment is the ambient
literal final-binary alpha. -/
theorem rankFour_lastThree_lastBinaryAlpha_eq
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 1 3 (by omega)) :
    (segment.toGoodBONG a.good).lastBinaryAlpha = a.lastBinaryAlpha := by
  let s := segment.toGoodBONG a.good
  have horder1 : s.order (1 : Fin 3) = a.order (2 : Fin 4) := by
    change segment.bong.order 1 = a.toBONG.order 2
    simp [BONG.SegmentWitness.sourceIndex]
  have horder2 : s.order (2 : Fin 3) = a.order (3 : Fin 4) := by
    change segment.bong.order 2 = a.toBONG.order 3
    simp [BONG.SegmentWitness.sourceIndex]
  have hadjacent : s.adjacentDefect (1 : Fin 2) =
      a.adjacentDefect (2 : Fin 3) := by
    unfold adjacentDefect adjacentProduct GoodBONG.valueUnit
    change defectOrder (K := K)
        (-(segment.bong.valueUnit 1 * segment.bong.valueUnit 2)) =
      defectOrder (K := K)
        (-(a.toBONG.valueUnit 2 * a.toBONG.valueUnit 3))
    rw [segment.valueUnit_eq, segment.valueUnit_eq]
    congr 4
  have hhalf : s.halfGapCandidate (1 : Fin 2) =
      a.halfGapCandidate (2 : Fin 3) := by
    unfold halfGapCandidate
    change
      (((((s.order (2 : Fin 3) - s.order (1 : Fin 3) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) =
        (((((a.order (3 : Fin 4) - a.order (2 : Fin 4) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ)
    rw [horder1, horder2]
  have hleft : s.leftDefectCandidate (1 : Fin 2) (1 : Fin 2) =
      a.leftDefectCandidate (2 : Fin 3) (2 : Fin 3) := by
    unfold leftDefectCandidate
    have hsCast : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
    have hsSucc : (1 : Fin 2).succ = (2 : Fin 3) := rfl
    have haCast : (2 : Fin 3).castSucc = (2 : Fin 4) := rfl
    have haSucc : (2 : Fin 3).succ = (3 : Fin 4) := rfl
    rw [hsCast, hsSucc, haCast, haSucc]
    rw [horder1, horder2, hadjacent]
  have hsLast : (Fin.last 1 : Fin 2) = (1 : Fin 2) := by
    apply Fin.ext
    rfl
  have haLast : (Fin.last 2 : Fin 3) = (2 : Fin 3) := by
    apply Fin.ext
    rfl
  unfold lastBinaryAlpha adjacentBinaryAlpha
  rw [hsLast, haLast]
  rw [hhalf, hleft]

/-- On the equality boundary, the final ternary segment also retains the
ambient third alpha. -/
theorem rankFour_lastThree_secondAlpha_eq_of_boundary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 1 3 (by omega))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ)) :
    (segment.toGoodBONG a.good).alphaValue (1 : Fin 2) =
      a.alphaValue (2 : Fin 3) := by
  let s := segment.toGoodBONG a.good
  let p := rankFourLastThreeSecondAlphaLocalization
  have hglobalLeLocalRaw := a.beli2009Lemma21_le_segmentAlpha p segment
  have hpivot : p.pivotFin = (2 : Fin 3) := by
    apply Fin.ext
    rfl
  have hlocalPivot : p.localPivot = (1 : Fin 2) := by
    apply Fin.ext
    rfl
  have hglobalLeLocal :
      (a.alphaValue (2 : Fin 3) : WithTop ℚ) ≤
        (s.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    rw [a.coe_alphaValue, s.coe_alphaValue]
    rw [hpivot, hlocalPivot] at hglobalLeLocalRaw
    exact hglobalLeLocalRaw
  have hlocalLeBinary :
      (s.alphaValue (1 : Fin 2) : WithTop ℚ) ≤ s.lastBinaryAlpha := by
    unfold lastBinaryAlpha adjacentBinaryAlpha
    apply le_min
    · rw [s.coe_alphaValue]
      exact s.alpha_le_halfGapCandidate (1 : Fin 2)
    · rw [s.coe_alphaValue]
      exact s.alpha_le_leftDefectCandidate
        (i := (1 : Fin 2)) (j := (1 : Fin 2)) le_rfl
  have hlocalLeGlobal :
      (s.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
    rw [rankFour_lastThree_lastBinaryAlpha_eq a segment,
      rankFour_boundary_lastBinaryAlpha_eq a hsum] at hlocalLeBinary
    exact hlocalLeBinary
  exact_mod_cast le_antisymm hlocalLeGlobal hglobalLeLocal

/-- If a literal binary alpha is the ambient alpha and lies strictly below
the half-gap candidate, its raw adjacent defect is obtained by subtracting
the order gap. -/
theorem adjacentDefect_eq_orderDiff_add_of_adjacentBinaryAlpha_lt_halfGap
    {N : Nat} (a : GoodBONG q L (N + 2)) (i : Fin (N + 1))
    (hbinary : a.adjacentBinaryAlpha i =
      (a.alphaValue i : WithTop ℚ))
    (hstrict : a.alphaValue i < a.halfGapValue i) :
    a.adjacentDefect i =
      ((((a.order i.castSucc - a.order i.succ : Int) : ℚ) +
        a.alphaValue i : ℚ) : WithTop ℚ) := by
  have hhalf : (a.alphaValue i : WithTop ℚ) <
      a.halfGapCandidate i := by
    rw [← a.coe_halfGapValue]
    exact_mod_cast hstrict
  have hmin : min (a.halfGapCandidate i) (a.leftDefectCandidate i i) =
      (a.alphaValue i : WithTop ℚ) := by
    simpa only [adjacentBinaryAlpha] using hbinary
  have halphaLeLeft : (a.alphaValue i : WithTop ℚ) ≤
      a.leftDefectCandidate i i := by
    rw [← hmin]
    exact min_le_right _ _
  have hleftLeAlpha : a.leftDefectCandidate i i ≤
      (a.alphaValue i : WithTop ℚ) := by
    by_contra hnot
    have halphaLtLeft := lt_of_not_ge hnot
    have hcontra : (a.alphaValue i : WithTop ℚ) <
        min (a.halfGapCandidate i) (a.leftDefectCandidate i i) :=
      lt_min hhalf halphaLtLeft
    rw [hmin] at hcontra
    exact (lt_irrefl _ hcontra).elim
  have hleftEq : a.leftDefectCandidate i i =
      (a.alphaValue i : WithTop ℚ) :=
    le_antisymm hleftLeAlpha halphaLeLeft
  unfold leftDefectCandidate at hleftEq
  let gap : ℚ := ((a.order i.succ - a.order i.castSucc : Int) : ℚ)
  let raw : ℚ := ((a.order i.castSucc - a.order i.succ : Int) : ℚ) +
    a.alphaValue i
  have hleftEq' : (gap : WithTop ℚ) + a.adjacentDefect i =
      (a.alphaValue i : WithTop ℚ) := by
    simpa only [gap] using hleftEq
  have hcancel : a.adjacentDefect i = (raw : WithTop ℚ) := by
    apply (WithTop.add_left_inj (x := (gap : WithTop ℚ))
      WithTop.coe_ne_top).mp
    calc
      (gap : WithTop ℚ) + a.adjacentDefect i =
          (a.alphaValue i : WithTop ℚ) := hleftEq'
      _ = (gap : WithTop ℚ) + (raw : WithTop ℚ) := by
        norm_cast
        dsimp only [gap, raw]
        push_cast
        ring
  simpa only [raw] using hcancel

/-- If the third alpha attains its half-gap on the equality boundary, the
middle raw adjacent defect is the first alpha. -/
theorem rankFour_middleAdjacentDefect_eq_firstAlpha_of_third_eq_halfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hbinary : a.adjacentBinaryAlpha (1 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hthird : a.alphaValue (2 : Fin 3) =
      a.halfGapValue (2 : Fin 3)) :
    a.adjacentDefect (1 : Fin 3) =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
  have hmiddleStrict : a.alphaValue (1 : Fin 3) <
      a.halfGapValue (1 : Fin 3) := by
    unfold halfGapValue orderGap at hthird ⊢
    push_cast at hthird ⊢
    have hsecondFourthQ : (a.order (1 : Fin 4) : ℚ) <
        a.order (3 : Fin 4) := by
      exact_mod_cast hsecondFourth
    linarith
  have hraw :=
    adjacentDefect_eq_orderDiff_add_of_adjacentBinaryAlpha_lt_halfGap
      a (1 : Fin 3) hbinary hmiddleStrict
  rw [hraw]
  norm_cast
  have hrelation :=
    (a.beli2019Remark87 (0 : Fin 2) houter).currentAlpha_eq
  change a.alphaValue (1 : Fin 3) =
      ((a.order (0 : Fin 4) - a.order (1 : Fin 4) : Int) : ℚ) +
        a.alphaValue (0 : Fin 3) at hrelation
  push_cast at hrelation ⊢
  have houterQ : (a.order (0 : Fin 4) : ℚ) = a.order (2 : Fin 4) := by
    exact_mod_cast houter
  linarith

/-- If the ambient third alpha is strictly below its half-gap, the final raw
adjacent defect is the order difference plus that alpha, as in lines
8502--8503 of the paper. -/
theorem rankFour_lastAdjacentDefect_eq_of_thirdAlpha_lt_halfGap
    (a : GoodBONG q L 4)
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ))
    (hstrict : a.alphaValue (2 : Fin 3) <
      a.halfGapValue (2 : Fin 3)) :
    a.adjacentDefect (2 : Fin 3) =
      ((((a.order (2 : Fin 4) - a.order (3 : Fin 4) : Int) : ℚ) +
        a.alphaValue (2 : Fin 3) : ℚ) : WithTop ℚ) := by
  have hhalf : (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
      a.halfGapCandidate (2 : Fin 3) := by
    rw [← a.coe_halfGapValue]
    exact_mod_cast hstrict
  have hmin :
      min (a.halfGapCandidate (2 : Fin 3))
          (a.leftDefectCandidate (2 : Fin 3) (2 : Fin 3)) =
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
    have hlastIndex : (Fin.last 2 : Fin 3) = (2 : Fin 3) := by
      apply Fin.ext
      rfl
    unfold lastBinaryAlpha adjacentBinaryAlpha at hlast
    rw [hlastIndex] at hlast
    exact hlast
  have halphaLeLeft :
      (a.alphaValue (2 : Fin 3) : WithTop ℚ) ≤
        a.leftDefectCandidate (2 : Fin 3) (2 : Fin 3) := by
    rw [← hmin]
    exact min_le_right _ _
  have hleftLeAlpha :
      a.leftDefectCandidate (2 : Fin 3) (2 : Fin 3) ≤
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
    by_contra hnot
    have halphaLtLeft := lt_of_not_ge hnot
    have hcontra : (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
        min (a.halfGapCandidate (2 : Fin 3))
          (a.leftDefectCandidate (2 : Fin 3) (2 : Fin 3)) :=
      lt_min hhalf halphaLtLeft
    rw [hmin] at hcontra
    exact (lt_irrefl _ hcontra).elim
  have hleftEq :
      a.leftDefectCandidate (2 : Fin 3) (2 : Fin 3) =
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) :=
    le_antisymm hleftLeAlpha halphaLeLeft
  unfold leftDefectCandidate at hleftEq
  have hcast : (2 : Fin 3).castSucc = (2 : Fin 4) := rfl
  have hsucc : (2 : Fin 3).succ = (3 : Fin 4) := rfl
  rw [hcast, hsucc] at hleftEq
  let gap : ℚ :=
    ((a.order (3 : Fin 4) - a.order (2 : Fin 4) : Int) : ℚ)
  let raw : ℚ :=
    ((a.order (2 : Fin 4) - a.order (3 : Fin 4) : Int) : ℚ) +
      a.alphaValue (2 : Fin 3)
  have hleftEq' : (gap : WithTop ℚ) + a.adjacentDefect (2 : Fin 3) =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
    simpa only [gap] using hleftEq
  have hcancel : a.adjacentDefect (2 : Fin 3) = (raw : WithTop ℚ) := by
    apply (WithTop.add_left_inj (x := (gap : WithTop ℚ))
      WithTop.coe_ne_top).mp
    calc
      (gap : WithTop ℚ) + a.adjacentDefect (2 : Fin 3) =
          (a.alphaValue (2 : Fin 3) : WithTop ℚ) := hleftEq'
      _ = (gap : WithTop ℚ) + (raw : WithTop ℚ) := by
        norm_cast
        dsimp only [gap, raw]
        push_cast
        ring
  simpa only [raw] using hcancel

/-- The Hilbert-symbol identity needed by the ternary coefficient scaling is
purely multiplicative: two negative auxiliary pairings cancel. -/
theorem ternaryScaled_adjacentHilbert_eq_of_neg
    [HilbertSymbolLaws K]
    (a : GoodBONG q L 3) (ε η : Kˣ)
    (hεHilbert : hilbertSymbol K ε
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (hηHilbert : hilbertSymbol K η
      (ε * a.adjacentProduct (1 : Fin 2)) = -1) :
    hilbertSymbol K
        (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
        (-(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) =
      hilbertSymbol K
        (-(a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
        (-(a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) := by
  have hfirst :
      -(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)) =
        η * a.adjacentProduct (0 : Fin 2) := by
    unfold adjacentProduct
    have hcast : (0 : Fin 2).castSucc = (0 : Fin 3) := rfl
    have hsucc : (0 : Fin 2).succ = (1 : Fin 3) := rfl
    rw [hcast, hsucc]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    ring
  have hsecond :
      -(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3)) =
        ε * a.adjacentProduct (1 : Fin 2) := by
    unfold adjacentProduct
    have hcast : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
    have hsucc : (1 : Fin 2).succ = (2 : Fin 3) := rfl
    rw [hcast, hsucc]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    ring
  rw [hfirst, hsecond]
  change
    hilbertSymbol K (η * a.adjacentProduct (0 : Fin 2))
        (ε * a.adjacentProduct (1 : Fin 2)) =
      hilbertSymbol K (a.adjacentProduct (0 : Fin 2))
        (a.adjacentProduct (1 : Fin 2))
  rw [hilbertSymbol_mul_left, hηHilbert, hilbertSymbol_mul_right,
    hilbertSymbol_comm K (a.adjacentProduct (0 : Fin 2)) ε, hεHilbert]
  simp

/-- Data obtained by replacing the final ternary segment with a first-value
transform.  The ambient first value is fixed and the second value is multiplied
by the local transform's unit. -/
structure Beli2019Lemma814FirstAdjacentScalingData
    (a : GoodBONG q L 4) where
  epsilon : Kˣ
  epsilon_isValuationUnit : IsValuationUnit K (epsilon : K)
  epsilon_defect : defectOrder (K := K) epsilon =
    (a.alphaValue (1 : Fin 3) : WithTop ℚ)
  transformed : GoodBONG q L 4
  firstValue_eq : transformed.valueUnit (0 : Fin 4) =
    a.valueUnit (0 : Fin 4)
  secondValue_eq : transformed.valueUnit (1 : Fin 4) =
    epsilon * a.valueUnit (1 : Fin 4)

/-- Insert an already constructed first-value transform of the final ternary
segment into the ambient rank-four BONG. -/
theorem rankFour_firstAdjacentScalingData_of_transform
    [GoodBONGClassificationLaws.{u, v, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 1 3 (by omega))
    (T : (segment.toGoodBONG a.good).Beli2019FirstValueTransform)
    (halpha : (segment.toGoodBONG a.good).alphaValue (0 : Fin 2) =
      a.alphaValue (1 : Fin 3)) :
    ∃ D : Beli2019Lemma814FirstAdjacentScalingData a,
      D.epsilon = T.epsilon := by
  let s := segment.toGoodBONG a.good
  rcases a.toBONG.beliLemma49_ii a.good segment
      T.transformed.toBONG T.transformed.good with ⟨replacement⟩
  let transformed : GoodBONG q L 4 :=
    ⟨replacement.bong, replacement.good⟩
  have hfirst : transformed.valueUnit (0 : Fin 4) =
      a.valueUnit (0 : Fin 4) := by
    apply Units.ext
    change replacement.bong.value 0 = a.toBONG.value 0
    rw [← replacement.bong.quadratic_ambientVector,
      ← a.toBONG.quadratic_ambientVector]
    exact congrArg q.quadratic
      (replacement.before_eq (0 : Fin 4) (by omega))
  have hsecondLocal : transformed.valueUnit (1 : Fin 4) =
      T.transformed.valueUnit (0 : Fin 3) := by
    apply Units.ext
    change replacement.bong.value 1 = T.transformed.toBONG.value 0
    rw [← replacement.bong.quadratic_ambientVector,
      ← T.transformed.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector 1) =
      q.quadratic (T.transformed.toBONG.ambientVector 0 : V)
    have hinside := replacement.inside_eq (0 : Fin 3)
    simpa using congrArg q.quadratic hinside
  have hsegmentFirst : s.valueUnit (0 : Fin 3) =
      a.valueUnit (1 : Fin 4) := by
    change segment.bong.valueUnit 0 = a.toBONG.valueUnit 1
    simp [BONG.SegmentWitness.sourceIndex]
  exact ⟨{
    epsilon := T.epsilon
    epsilon_isValuationUnit := T.epsilon_isValuationUnit
    epsilon_defect := T.epsilon_defect.trans
      (congrArg (fun x : ℚ => (x : WithTop ℚ)) halpha)
    transformed := transformed
    firstValue_eq := hfirst
    secondValue_eq := hsecondLocal.trans <| T.firstValue_eq.trans <|
      congrArg (T.epsilon * ·) hsegmentFirst
  }, rfl⟩

/-- The first adjacent product after a tail scaling is the old product
multiplied by the scaling unit. -/
theorem Beli2019Lemma814FirstAdjacentScalingData.firstAdjacentProduct_eq
    {a : GoodBONG q L 4}
    (D : Beli2019Lemma814FirstAdjacentScalingData a) :
    D.transformed.adjacentProduct (0 : Fin 3) =
      D.epsilon * a.adjacentProduct (0 : Fin 3) := by
  unfold adjacentProduct
  have hcast : (0 : Fin 3).castSucc = (0 : Fin 4) := rfl
  have hsucc : (0 : Fin 3).succ = (1 : Fin 4) := rfl
  rw [hcast, hsucc]
  rw [D.firstValue_eq, D.secondValue_eq]
  apply Units.ext
  simp only [Units.val_neg, Units.val_mul]
  ring

/-- Consequently the first adjacent defect is the defect of the old adjacent
product multiplied by the scaling unit. -/
theorem Beli2019Lemma814FirstAdjacentScalingData.firstAdjacentDefect_eq
    {a : GoodBONG q L 4}
    (D : Beli2019Lemma814FirstAdjacentScalingData a) :
    D.transformed.adjacentDefect (0 : Fin 3) =
      defectOrder (K := K) (D.epsilon * a.adjacentProduct (0 : Fin 3)) := by
  unfold adjacentDefect
  rw [D.firstAdjacentProduct_eq]

/-- The first adjacent product of the final ternary segment is the ambient
middle adjacent product. -/
theorem rankFour_lastThree_firstAdjacentProduct_eq
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 1 3 (by omega)) :
    (segment.toGoodBONG a.good).adjacentProduct (0 : Fin 2) =
      a.adjacentProduct (1 : Fin 3) := by
  unfold adjacentProduct GoodBONG.valueUnit
  change -(segment.bong.valueUnit 0 * segment.bong.valueUnit 1) =
    -(a.toBONG.valueUnit 1 * a.toBONG.valueUnit 2)
  rw [segment.valueUnit_eq, segment.valueUnit_eq]
  congr 3

/-- The second adjacent product of the final ternary segment is the ambient
final adjacent product. -/
theorem rankFour_lastThree_secondAdjacentProduct_eq
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 1 3 (by omega)) :
    (segment.toGoodBONG a.good).adjacentProduct (1 : Fin 2) =
      a.adjacentProduct (2 : Fin 3) := by
  unfold adjacentProduct GoodBONG.valueUnit
  change -(segment.bong.valueUnit 1 * segment.bong.valueUnit 2) =
    -(a.toBONG.valueUnit 2 * a.toBONG.valueUnit 3)
  rw [segment.valueUnit_eq, segment.valueUnit_eq]
  congr 3

/-- A unit in the norm group of the first binary pair of the final ternary
segment gives the ambient first-adjacent scaling used in the preliminary
rank-four normalization. -/
theorem exists_rankFour_firstAdjacentScaling_of_unit
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L 4) (ε : Kˣ)
    (hbinary : a.adjacentBinaryAlpha (1 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hunit : IsValuationUnit K (ε : K))
    (hdefect : defectOrder (K := K) ε =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hhilbert : hilbertSymbol K ε (a.adjacentProduct (1 : Fin 3)) = 1) :
    ∃ D : Beli2019Lemma814FirstAdjacentScalingData a,
      D.epsilon = ε := by
  let segment := a.toBONG.segmentWitness 1 3 (by omega)
  let s := segment.toGoodBONG a.good
  have halphas :=
    rankFour_lastThree_firstAlpha_eq_of_adjacentBinaryAlpha a segment hbinary
  have hlocalDefect :
      (s.alphaValue (0 : Fin 2) : WithTop ℚ) ≤ defectOrder (K := K) ε := by
    rw [halphas.1, hdefect]
  have hlocalHilbert :
      hilbertSymbol K ε (s.adjacentProduct (0 : Fin 2)) = 1 := by
    rw [rankFour_lastThree_firstAdjacentProduct_eq a segment]
    exact hhilbert
  rcases s.exists_firstValueScaling_of_firstBinaryAlpha ε hunit hlocalDefect
      halphas.2 hlocalHilbert with ⟨transformed, hfirst⟩
  let T : s.Beli2019FirstValueTransform := {
    epsilon := ε
    epsilon_isValuationUnit := hunit
    epsilon_defect := hdefect.trans <|
      congrArg (fun x : ℚ => (x : WithTop ℚ)) halphas.1.symm
    transformed := transformed
    firstValue_eq := hfirst
  }
  rcases rankFour_firstAdjacentScalingData_of_transform a segment T halphas.1 with
    ⟨D, hD⟩
  exact ⟨D, hD⟩

/-- An even-order square class has a valuation-unit representative obtained by
removing a square of the uniformizer.  The explicit factorization is retained
for defect and Hilbert-symbol calculations. -/
theorem exists_valuationUnit_eq_mul_square_of_even_order
    (x : Kˣ) (hxEven : Even (ordUnit K x)) :
    ∃ u t : Kˣ, IsValuationUnit K (u : K) ∧ u = x * t ^ 2 := by
  rcases hxEven with ⟨k, hk⟩
  let t : Kˣ := uniformizerPowerUnit K (-k)
  let u : Kˣ := x * t ^ 2
  have huOrder : ordUnit K u = 0 := by
    simp only [u, t, ordUnit_mul, ordUnit_pow,
      ordUnit_uniformizerPowerUnit]
    omega
  exact ⟨u, t, (isValuationUnit_iff_ordUnit_eq_zero K u).2 huOrder, rfl⟩

/-- Under the outer-order equality, the first adjacent square class of a
rank-four good BONG has even valuation. -/
theorem rankFour_firstAdjacentOrder_even
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4)) :
    Even (ordUnit K (a.adjacentProduct (0 : Fin 3))) := by
  have hremark := a.beli2019Remark87 (0 : Fin 2) houter
  have hadjacentOrder :
      ordUnit K (a.adjacentProduct (0 : Fin 3)) =
        a.order (0 : Fin 4) + a.order (1 : Fin 4) := by
    have horderUnit (j : Fin 4) :
        ordUnit K (a.valueUnit j) = a.order j :=
      (a.toBONG.order_eq_ordUnit j).symm
    unfold adjacentProduct
    rw [ordUnit_neg, ordUnit_mul, horderUnit, horderUnit]
    congr 1
  have evenSum {x y : Int} (hxy : Int.ModEq 2 x y) : Even (x + y) := by
    rcases Int.modEq_iff_add_fac.mp hxy with ⟨t, ht⟩
    refine ⟨x + t, ?_⟩
    omega
  rw [hadjacentOrder]
  simpa [remark87PreviousValue, remark87MiddleValue] using
    evenSum hremark.previous_middle_modEq

/-- Remark 8.7 supplies the lower bound of the second alpha by the first raw
adjacent defect. -/
theorem rankFour_secondAlpha_le_firstAdjacentDefect
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4)) :
    (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
      a.adjacentDefect (0 : Fin 3) := by
  simpa [remark87CurrentAlpha, remark87PreviousAlpha] using
    (a.beli2019Remark87 (0 : Fin 2) houter).currentAlpha_le_previousRawDefect

/-- Hence failure of the desired strict inequality means exact equality of
the raw first adjacent defect with the second alpha. -/
theorem rankFour_firstAdjacentDefect_eq_secondAlpha_of_not_lt
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hnot : ¬(a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3)) :
    a.adjacentDefect (0 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
  exact le_antisymm (le_of_not_gt hnot)
    (rankFour_secondAlpha_le_firstAdjacentDefect a houter)

/-- The output of the preliminary coordinate normalization in the quaternary
equality-boundary argument. -/
structure Beli2019Lemma814FirstAdjacentNormalizationData
    (a : GoodBONG q L 4) where
  transformed : GoodBONG q L 4
  firstAdjacent_strict :
    (transformed.alphaValue (1 : Fin 3) : WithTop ℚ) <
      transformed.adjacentDefect (0 : Fin 3)

/-- If the valuation-unit representative of the first adjacent square class
already lies in the norm group of the middle binary pair, binary scaling of
the final ternary block makes the first raw defect strict. -/
theorem exists_rankFour_firstAdjacentNormalization_of_hilbert_one
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hbinary : a.adjacentBinaryAlpha (1 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hnot : ¬(a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3))
    (hhilbert : hilbertSymbol K (a.adjacentProduct (0 : Fin 3))
      (a.adjacentProduct (1 : Fin 3)) = 1) :
    Nonempty (Beli2019Lemma814FirstAdjacentNormalizationData a) := by
  let x := a.adjacentProduct (0 : Fin 3)
  let y := a.adjacentProduct (1 : Fin 3)
  have hxEven : Even (ordUnit K x) := by
    simpa only [x] using rankFour_firstAdjacentOrder_even a houter
  rcases BONG.exists_valuationUnit_multiplier_isSquare x hxEven with
    ⟨ε, hεUnit, hεxSquare, hεDefectRaw⟩
  have hxDefect : defectOrder (K := K) x =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    have h := rankFour_firstAdjacentDefect_eq_secondAlpha_of_not_lt
      a houter hnot
    simpa only [adjacentDefect, x] using h
  have hεDefect : defectOrder (K := K) ε =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    unfold defectOrder
    rw [hεDefectRaw]
    exact hxDefect
  have hεHilbert : hilbertSymbol K ε y = 1 := by
    calc
      hilbertSymbol K ε y = hilbertSymbol K x y :=
        hilbertSymbol_eq_of_isSquare_mul_left hεxSquare
      _ = 1 := by simpa only [x, y] using hhilbert
  rcases exists_rankFour_firstAdjacentScaling_of_unit a ε hbinary hεUnit
      hεDefect (by simpa only [y] using hεHilbert) with ⟨D, hDε⟩
  have halphas := a.alpha_invariant D.transformed
  have hstrict :
      (D.transformed.alphaValue (1 : Fin 3) : WithTop ℚ) <
        D.transformed.adjacentDefect (0 : Fin 3) := by
    rw [← halphas (1 : Fin 3), D.firstAdjacentDefect_eq, hDε,
      defectOrder_eq_top_of_isSquare hεxSquare]
    exact WithTop.coe_lt_top _
  exact ⟨{
    transformed := D.transformed
    firstAdjacent_strict := hstrict
  }⟩

/-- In the strict final-half-gap subcase, a negative Hilbert pairing is
handled by the ternary scaling construction.  The complementary-defect unit
is exactly the auxiliary unit chosen in the rank-three proof. -/
theorem exists_rankFour_firstAdjacentNormalization_of_third_lt_of_hilbert_neg
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [BeliLemma49Laws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hbinary : a.adjacentBinaryAlpha (1 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hnot : ¬(a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3))
    (hthird : a.alphaValue (2 : Fin 3) <
      a.halfGapValue (2 : Fin 3))
    (hhilbert : hilbertSymbol K (a.adjacentProduct (0 : Fin 3))
      (a.adjacentProduct (1 : Fin 3)) = -1) :
    Nonempty (Beli2019Lemma814FirstAdjacentNormalizationData a) := by
  let x := a.adjacentProduct (0 : Fin 3)
  let p := a.adjacentProduct (1 : Fin 3)
  let z := a.adjacentProduct (2 : Fin 3)
  have hxEven : Even (ordUnit K x) := by
    simpa only [x] using rankFour_firstAdjacentOrder_even a houter
  rcases BONG.exists_valuationUnit_multiplier_isSquare x hxEven with
    ⟨ε, hεUnit, hεxSquare, hεDefectRaw⟩
  have hxDefect : defectOrder (K := K) x =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    have h := rankFour_firstAdjacentDefect_eq_secondAlpha_of_not_lt
      a houter hnot
    simpa only [adjacentDefect, x] using h
  have hεDefect : defectOrder (K := K) ε =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    unfold defectOrder
    rw [hεDefectRaw]
    exact hxDefect
  have hεHilbert : hilbertSymbol K ε p = -1 := by
    calc
      hilbertSymbol K ε p = hilbertSymbol K x p :=
        hilbertSymbol_eq_of_isSquare_mul_left hεxSquare
      _ = -1 := by simpa only [x, p] using hhilbert
  let segment := a.toBONG.segmentWitness 1 3 (by omega)
  let s := segment.toGoodBONG a.good
  have hlocalFirst :=
    rankFour_lastThree_firstAlpha_eq_of_adjacentBinaryAlpha a segment hbinary
  have hlocalSecond :=
    rankFour_lastThree_secondAlpha_eq_of_boundary a segment hsum
  let d : ℚ :=
    ((a.order (2 : Fin 4) - a.order (3 : Fin 4) : Int) : ℚ) +
      a.alphaValue (2 : Fin 3)
  have hzDefect : defectOrder (K := K) z = (d : WithTop ℚ) := by
    have hlast := rankFour_boundary_lastBinaryAlpha_eq a hsum
    have hraw := rankFour_lastAdjacentDefect_eq_of_thirdAlpha_lt_halfGap
      a hlast hthird
    simpa only [adjacentDefect, z, d] using hraw
  have hdLtSecond : d < a.alphaValue (1 : Fin 3) := by
    dsimp only [d]
    unfold halfGapValue orderGap at hthird
    push_cast at hthird ⊢
    linarith
  have hzLtEpsilon : defectOrder (K := K) z <
      defectOrder (K := K) ε := by
    rw [hzDefect, hεDefect]
    exact_mod_cast hdLtSecond
  have hεzDefect : defectOrder (K := K) (ε * z) =
      (d : WithTop ℚ) := by
    rw [defectOrder_mul_eq_right_of_lt_left hzLtEpsilon, hzDefect]
  have hdNonnegative : 0 ≤ d := by
    have hnonnegative := defectOrder_nonneg (K := K) (ε * z)
    rw [hεzDefect] at hnonnegative
    exact_mod_cast hnonnegative
  have hboundaryAlpha := a.rankFour_boundaryAlphaData
    houter hsecondFourth hsum
  have hdLtTwoE : d < 2 * (ramificationIndex K : ℚ) :=
    hdLtSecond.trans hboundaryAlpha.second_lt_twoE
  rcases BONG.exists_complementaryDefect_hilbert_neg_of_nonnegative
      (K := K) (ε * z) d hεzDefect hdNonnegative hdLtTwoE with
    ⟨η, hηUnit, hηDefect, hηHilbert⟩
  have hηLowerRat : a.alphaValue (2 : Fin 3) ≤
      2 * (ramificationIndex K : ℚ) - d := by
    dsimp only [d]
    unfold halfGapValue orderGap at hthird
    push_cast at hthird ⊢
    linarith
  have hηDefectBound : (s.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      defectOrder (K := K) η := by
    rw [hlocalSecond, hηDefect]
    exact_mod_cast hηLowerRat
  have hεDefectBound : (s.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      defectOrder (K := K) ε := by
    rw [hlocalFirst.1, hεDefect]
  have hεLocal : hilbertSymbol K ε
      (s.adjacentProduct (0 : Fin 2)) = -1 := by
    rw [rankFour_lastThree_firstAdjacentProduct_eq a segment]
    exact hεHilbert
  have hηLocal : hilbertSymbol K η
      (ε * s.adjacentProduct (1 : Fin 2)) = -1 := by
    rw [rankFour_lastThree_secondAdjacentProduct_eq a segment]
    simpa only [z] using hηHilbert
  have hadjacent := ternaryScaled_adjacentHilbert_eq_of_neg
    s ε η hεLocal hηLocal
  have hproperty : s.toBONG.HasPropertyA := by
    intro i hi
    fin_cases i
    · change s.order (0 : Fin 3) < s.order (2 : Fin 3)
      have horder0 : s.order (0 : Fin 3) = a.order (1 : Fin 4) := by
        change segment.bong.order 0 = a.toBONG.order 1
        simp [BONG.SegmentWitness.sourceIndex]
      have horder2 : s.order (2 : Fin 3) = a.order (3 : Fin 4) := by
        change segment.bong.order 2 = a.toBONG.order 3
        simp [BONG.SegmentWitness.sourceIndex]
      rw [horder0, horder2]
      exact hsecondFourth
    · norm_num at hi
    · norm_num at hi
  have hAlphaSum : s.alphaValue (0 : Fin 2) + s.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) := by
    rw [hlocalFirst.1, hlocalSecond, hsum]
  rcases s.exists_goodBONG_ternaryScaled_of_propertyA ε η hεUnit hηUnit
      hεDefectBound hηDefectBound hadjacent hproperty hAlphaSum with
    ⟨transformed, hfirst⟩
  let T : s.Beli2019FirstValueTransform := {
    epsilon := ε
    epsilon_isValuationUnit := hεUnit
    epsilon_defect := hεDefect.trans <|
      congrArg (fun t : ℚ => (t : WithTop ℚ)) hlocalFirst.1.symm
    transformed := transformed
    firstValue_eq := hfirst
  }
  rcases rankFour_firstAdjacentScalingData_of_transform a segment T
      hlocalFirst.1 with ⟨D, hDε⟩
  have halphas := a.alpha_invariant D.transformed
  have hstrict :
      (D.transformed.alphaValue (1 : Fin 3) : WithTop ℚ) <
        D.transformed.adjacentDefect (0 : Fin 3) := by
    rw [← halphas (1 : Fin 3), D.firstAdjacentDefect_eq, hDε,
      defectOrder_eq_top_of_isSquare hεxSquare]
    exact WithTop.coe_lt_top _
  exact ⟨{
    transformed := D.transformed
    firstAdjacent_strict := hstrict
  }⟩

/-- In the attained final-half-gap subcase, the complementary Hilbert choice
produces a high-defect representative of the first adjacent square class.
The resulting valuation-unit multiplier lies in the middle binary norm group,
which is the content of the Beli (2003) step used in lines 8528--8540. -/
theorem exists_rankFour_firstAdjacentNormalization_of_third_eq_of_hilbert_neg
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hbinary : a.adjacentBinaryAlpha (1 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hnot : ¬(a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3))
    (hthird : a.alphaValue (2 : Fin 3) =
      a.halfGapValue (2 : Fin 3))
    (hhilbert : hilbertSymbol K (a.adjacentProduct (0 : Fin 3))
      (a.adjacentProduct (1 : Fin 3)) = -1) :
    Nonempty (Beli2019Lemma814FirstAdjacentNormalizationData a) := by
  let x := a.adjacentProduct (0 : Fin 3)
  let p := a.adjacentProduct (1 : Fin 3)
  have hxEven : Even (ordUnit K x) := by
    simpa only [x] using rankFour_firstAdjacentOrder_even a houter
  have hxDefect : defectOrder (K := K) x =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    have h := rankFour_firstAdjacentDefect_eq_secondAlpha_of_not_lt
      a houter hnot
    simpa only [adjacentDefect, x] using h
  have hpDefect : defectOrder (K := K) p =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
    have h := rankFour_middleAdjacentDefect_eq_firstAlpha_of_third_eq_halfGap
      a houter hsecondFourth hsum hbinary hthird
    simpa only [adjacentDefect, p] using h
  have hboundaryAlpha := a.rankFour_boundaryAlphaData
    houter hsecondFourth hsum
  have hfirstNonnegative : 0 ≤ a.alphaValue (0 : Fin 3) :=
    (a.beli2009Lemma27_i (0 : Fin 3)).1
  rcases BONG.exists_complementaryDefect_hilbert_neg_of_nonnegative
      (K := K) p (a.alphaValue (0 : Fin 3)) hpDefect hfirstNonnegative
      hboundaryAlpha.first_lt_twoE with
    ⟨w, hwUnit, hwDefect, hwHilbert⟩
  have hwEven : Even (ordUnit K w) := by
    have hwOrder : ordUnit K w = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K w).1 hwUnit
    rw [hwOrder]
    exact ⟨0, by simp⟩
  have hwNonzero : quadraticDefect K w ≠ 0 :=
    BONG.quadraticDefect_ne_zero_of_even_ordUnit w hwEven
  rcases BONG.exists_valuationUnit_multiplier_same_defect_same_hilbert
      p x w hxEven hwNonzero with
    ⟨ε, hεUnit, hεxDefectRaw, hεxHilbertRaw⟩
  let high : ℚ :=
    2 * (ramificationIndex K : ℚ) - a.alphaValue (0 : Fin 3)
  have hεxDefect : defectOrder (K := K) (ε * x) =
      (high : WithTop ℚ) := by
    have hwDefect' := hwDefect
    unfold defectOrder at hwDefect'
    unfold defectOrder
    rw [hεxDefectRaw]
    simpa only [high] using hwDefect'
  have hmiddleStrict : a.alphaValue (1 : Fin 3) <
      a.halfGapValue (1 : Fin 3) := by
    unfold halfGapValue orderGap at hthird ⊢
    push_cast at hthird ⊢
    have hsecondFourthQ : (a.order (1 : Fin 4) : ℚ) <
        a.order (3 : Fin 4) := by
      exact_mod_cast hsecondFourth
    linarith
  have hfirstSecondLt :
      a.alphaValue (0 : Fin 3) + a.alphaValue (1 : Fin 3) <
        2 * (ramificationIndex K : ℚ) := by
    have hrelation :=
      (a.beli2019Remark87 (0 : Fin 2) houter).currentAlpha_eq
    change a.alphaValue (1 : Fin 3) =
        ((a.order (0 : Fin 4) - a.order (1 : Fin 4) : Int) : ℚ) +
          a.alphaValue (0 : Fin 3) at hrelation
    unfold halfGapValue orderGap at hmiddleStrict
    push_cast at hmiddleStrict hrelation ⊢
    have houterQ : (a.order (0 : Fin 4) : ℚ) = a.order (2 : Fin 4) := by
      exact_mod_cast houter
    linarith
  have hhighGtSecond : a.alphaValue (1 : Fin 3) < high := by
    dsimp only [high]
    linarith
  have hxLtProduct : defectOrder (K := K) x <
      defectOrder (K := K) (ε * x) := by
    rw [hxDefect, hεxDefect]
    exact_mod_cast hhighGtSecond
  have hεSameDefect : defectOrder (K := K) ε =
      defectOrder (K := K) x := by
    by_contra hne
    have hproduct := defectOrder_mul_eq_min_of_ne (K := K) hne
    have hle : defectOrder (K := K) (ε * x) ≤
        defectOrder (K := K) x := by
      rw [hproduct]
      exact min_le_right _ _
    exact (not_lt_of_ge hle hxLtProduct)
  have hεDefect : defectOrder (K := K) ε =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) :=
    hεSameDefect.trans hxDefect
  have hpεx : hilbertSymbol K p (ε * x) = -1 := by
    calc
      hilbertSymbol K p (ε * x) = hilbertSymbol K p w := hεxHilbertRaw
      _ = hilbertSymbol K w p := hilbertSymbol_comm K p w
      _ = -1 := hwHilbert
  have hpε : hilbertSymbol K p ε = 1 := by
    rw [hilbertSymbol_mul_right, hilbertSymbol_comm K p x, hhilbert] at hpεx
    simpa using hpεx
  have hεHilbert : hilbertSymbol K ε p = 1 := by
    rw [hilbertSymbol_comm K ε p]
    exact hpε
  rcases exists_rankFour_firstAdjacentScaling_of_unit a ε hbinary hεUnit
      hεDefect (by simpa only [p] using hεHilbert) with ⟨D, hDε⟩
  have halphas := a.alpha_invariant D.transformed
  have hstrict :
      (D.transformed.alphaValue (1 : Fin 3) : WithTop ℚ) <
        D.transformed.adjacentDefect (0 : Fin 3) := by
    rw [← halphas (1 : Fin 3), D.firstAdjacentDefect_eq, hDε, hεxDefect]
    exact_mod_cast hhighGtSecond
  exact ⟨{
    transformed := D.transformed
    firstAdjacent_strict := hstrict
  }⟩

/-- Completion of the preliminary normalization once Corollary 8.11 has made
the middle literal binary alpha equal to the ambient second alpha. -/
theorem exists_rankFour_firstAdjacentNormalization_of_middleBinary
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hbinary : a.adjacentBinaryAlpha (1 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ)) :
    Nonempty (Beli2019Lemma814FirstAdjacentNormalizationData a) := by
  by_cases hstrict : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3)
  · exact ⟨{
      transformed := a
      firstAdjacent_strict := hstrict
    }⟩
  · let x := a.adjacentProduct (0 : Fin 3)
    let p := a.adjacentProduct (1 : Fin 3)
    rcases Int.units_eq_one_or (hilbertSymbol K x p) with hhilbert | hhilbert
    · apply exists_rankFour_firstAdjacentNormalization_of_hilbert_one
        a houter hbinary hstrict
      simpa only [x, p] using hhilbert
    · rcases lt_or_eq_of_le
          (a.alphaValue_le_halfGapValue (2 : Fin 3)) with hthird | hthird
      · apply
          exists_rankFour_firstAdjacentNormalization_of_third_lt_of_hilbert_neg
            a houter hsecondFourth hsum hbinary hstrict hthird
        simpa only [x, p] using hhilbert
      · apply
          exists_rankFour_firstAdjacentNormalization_of_third_eq_of_hilbert_neg
            a houter hsecondFourth hsum hbinary hstrict hthird
        simpa only [x, p] using hhilbert

/-- Corollary 8.11 first normalizes the middle literal binary segment; the
preceding theorem then makes the first raw adjacent defect strict. -/
theorem exists_rankFour_firstAdjacentNormalization
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
    [BONGStructuralLaws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ)) :
    Nonempty (Beli2019Lemma814FirstAdjacentNormalizationData a) := by
  rcases a.beli2019Corollary811 (1 : Fin 3) with ⟨C⟩
  let changed := C.transformed
  have horders := a.order_invariant changed
  have halphas := a.alpha_invariant changed
  have houter' : changed.order (0 : Fin 4) = changed.order (2 : Fin 4) := by
    rw [← horders (0 : Fin 4), ← horders (2 : Fin 4)]
    exact houter
  have hsecondFourth' : changed.order (1 : Fin 4) <
      changed.order (3 : Fin 4) := by
    rw [← horders (1 : Fin 4), ← horders (3 : Fin 4)]
    exact hsecondFourth
  have hsum' : changed.alphaValue (1 : Fin 3) +
      changed.alphaValue (2 : Fin 3) = 2 * (ramificationIndex K : ℚ) := by
    rw [← halphas (1 : Fin 3), ← halphas (2 : Fin 3)]
    exact hsum
  rcases exists_rankFour_firstAdjacentNormalization_of_middleBinary
      changed houter' hsecondFourth' hsum' C.adjacentBinaryAlpha_eq with ⟨D⟩
  exact ⟨{
    transformed := D.transformed
    firstAdjacent_strict := D.firstAdjacent_strict
  }⟩

/-- Beli (2019), Lemma 8.14, quaternary equality boundary, with the
preliminary normalization fully discharged. -/
theorem beli2019Lemma814_rankFour_boundary
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
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (a original : GoodBONG q L 4) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ)) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases exists_rankFour_firstAdjacentNormalization
      a houter hsecondFourth hsum with ⟨D⟩
  let changed := D.transformed
  have horders := a.order_invariant changed
  have halphas := a.alpha_invariant changed
  have horder' : changed.order (0 : Fin 4) = b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin 4)]
    exact horder
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classificationV)
    (classificationW := classificationW) changed b horder conditions
  have hinvariant := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) changed b
  have hnotExceptional' : ¬changed.Beli2019Lemma814Exceptional b :=
    fun E ↦ hnotExceptional (hinvariant.mpr E)
  have houter' : changed.order (0 : Fin 4) = changed.order (2 : Fin 4) := by
    rw [← horders (0 : Fin 4), ← horders (2 : Fin 4)]
    exact houter
  have hsecondFourth' : changed.order (1 : Fin 4) <
      changed.order (3 : Fin 4) := by
    rw [← horders (1 : Fin 4), ← horders (3 : Fin 4)]
    exact hsecondFourth
  have hsum' : changed.alphaValue (1 : Fin 3) +
      changed.alphaValue (2 : Fin 3) = 2 * (ramificationIndex K : ℚ) := by
    rw [← halphas (1 : Fin 3), ← halphas (2 : Fin 3)]
    exact hsum
  exact changed.beli2019Lemma814_rankFour_boundary_of_firstAdjacent
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW)
    original b horder' hconditions hnotExceptional' houter' hsecondFourth'
      hsum' D.firstAdjacent_strict

end BONG.GoodBONG

end Bong
