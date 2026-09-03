/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Theorem53

/-!
# He--Hu 2022, Section 6

This file eliminates the alpha invariants from the even- and odd-rank
criteria of Sections 4 and 5, following Section 6 of Zilong He and Yong Hu,
*On n-universal quadratic forms over dyadic local fields*, Sci. China Math.
67 (2024), 1481--1506.  Paper indices are one based; `Fin` indices are zero
based.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

private theorem min_three_eq_iff_extreme
    {t cap x y : WithTop ℚ} (htCap : t < cap)
    (hLower : t ≤ min x (min cap y)) :
    min x (min cap y) = t ↔ x = t ∨ y = t := by
  have htx : t ≤ x := hLower.trans (min_le_left _ _)
  have hty : t ≤ y :=
    hLower.trans ((min_le_right _ _).trans (min_le_right _ _))
  constructor
  · intro hMin
    by_cases hx : x ≤ min cap y
    · left
      simpa only [min_eq_left hx] using hMin
    · have hInnerLe : min cap y ≤ x := le_of_not_ge hx
      have hInner : min cap y = t := by
        simpa only [min_eq_right hInnerLe] using hMin
      by_cases hcap : cap ≤ y
      · have hcapEq : cap = t := by
          simpa only [min_eq_left hcap] using hInner
        exact False.elim ((ne_of_gt htCap) hcapEq)
      · right
        have hycap : y ≤ cap := le_of_not_ge hcap
        simpa only [min_eq_right hycap] using hInner
  · rintro (hx | hy)
    · rw [hx]
      exact min_eq_left (hLower.trans (min_le_right _ _))
    · have htCapLe : t ≤ cap := le_of_lt htCap
      rw [hy, min_eq_right htCapLe]
      exact min_eq_right htx

private theorem rightCandidate_eq_one_iff_tailDefect
    {m : Nat} (a : GoodBONG q L (m + 1)) (i j : Fin m)
    (hPivotOrder : a.order i.castSucc = 0) :
    a.rightDefectCandidate i j = (1 : WithTop ℚ) ↔
      a.heHuAdjacentDefectAt j =
        (((1 - a.heHuOrderAfterAdjacent j : Int) : ℚ) : WithTop ℚ) := by
  have hRaw : a.heHuAdjacentDefectAt j = a.adjacentDefect j := by
    rfl
  have hOrderAfter : a.heHuOrderAfterAdjacent j = a.order j.succ := by
    rfl
  rw [hRaw, hOrderAfter]
  unfold rightDefectCandidate
  rw [hPivotOrder, sub_zero]
  let orderAfter : Int := a.order j.succ
  have hOne :
      (((orderAfter : ℚ) : WithTop ℚ) +
          (((1 - orderAfter : Int) : ℚ) : WithTop ℚ)) = 1 := by
    rw [← WithTop.coe_add]
    congr 1
    push_cast
    ring
  constructor
  · intro h
    have hOne' : (1 : WithTop ℚ) =
        (((a.order j.succ : Int) : ℚ) : WithTop ℚ) +
          (((1 - a.order j.succ : Int) : ℚ) : WithTop ℚ) := by
      simpa only [orderAfter] using hOne.symm
    exact WithTop.add_left_cancel (by simp :
      ((a.order j.succ : ℚ) : WithTop ℚ) ≠ ⊤) (h.trans hOne')
  · intro h
    rw [h]
    simpa only [orderAfter] using hOne

/-- Equation (6.1): at the exceptional even-rank boundary
`R_(n+2)=2-2e`, the next alpha is `2e-1` exactly when
`R_(n+3)` is zero or one. -/
theorem heHu2022Lemma61_equation61
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hnEven : Even n) (hmStable : n + 2 ≤ m)
    (hIntegral : Lattice.IsIntegral q L)
    (hBoundaryOrder : a.order ⟨n + 1, by omega⟩ =
      2 - 2 * (ramificationIndex K : Int)) :
    a.alphaValue ⟨n + 1, by omega⟩ =
        2 * (ramificationIndex K : ℚ) - 1 ↔
      HeHuZeroOrOne (a.order ⟨n + 2, by omega⟩) := by
  let next : Fin m := ⟨n + 1, by omega⟩
  have hGap : a.orderGap next =
      a.order ⟨n + 2, by omega⟩ -
        a.order ⟨n + 1, by omega⟩ := by
    rfl
  have hNextPaperOdd : Even (n + 2) := by
    rcases hnEven with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩
  have hNextNonnegative : 0 ≤ a.order ⟨n + 2, by omega⟩ :=
    (a.heHu2022Proposition27i hIntegral).oddIndexed
      ⟨n + 2, by omega⟩ ⟨n + 2, by omega⟩ (le_refl _)
      hNextPaperOdd hNextPaperOdd |>.1
  constructor
  · intro hAlpha
    have hAlphaLt : a.alphaValue next <
        2 * (ramificationIndex K : ℚ) := by
      rw [hAlpha]
      norm_num
    have hGapLt : a.orderGap next <
        2 * (ramificationIndex K : Int) :=
      ((a.heHu2022Proposition26 next).compareTwoE.1).mp hAlphaLt
    rw [hGap, hBoundaryOrder] at hGapLt
    unfold HeHuZeroOrOne
    omega
  · intro hOrder
    rcases hOrder with hZero | hOne
    · have hGapValue : a.orderGap next =
          2 * (ramificationIndex K : Int) - 2 := by
        rw [hGap, hZero, hBoundaryOrder]
        ring
      have hHalf := (a.heHu2022Proposition26 next).halfGap
        (Or.inr (Or.inr (Or.inr hGapValue)))
      rw [hHalf]
      unfold halfGapValue
      rw [hGapValue]
      push_cast
      ring
    · have hGapValue : a.orderGap next =
          2 * (ramificationIndex K : Int) - 1 := by
        rw [hGap, hOne, hBoundaryOrder]
        ring
      have hGapLe : a.orderGap next ≤
          2 * (ramificationIndex K : Int) := by
        rw [hGapValue]
        omega
      have hGapOdd : Odd (a.orderGap next) := by
        rw [hGapValue]
        refine ⟨(ramificationIndex K : Int) - 1, ?_⟩
        ring
      have hEq := ((a.heHu2022Proposition26 next).lowerBound hGapLe).2.mpr
        (Or.inr hGapOdd)
      rw [hEq, hGapValue]
      push_cast
      ring

/-- He--Hu, Lemma 6.1(i).  This is exactly clause (ii)(1)(a) of
Theorem 1.1, including the disjunction between the raw adjacent defect and
the two possible next orders. -/
theorem heHu2022Lemma61i
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hnTwo : 2 ≤ n) (hnEven : Even n) (hmStable : n + 2 ≤ m)
    (hIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E n (by omega))
    (hBoundaryOrder : a.order ⟨n + 1, by omega⟩ =
      2 - 2 * (ramificationIndex K : Int)) :
    (a.heHuAdjacentDefectAt ⟨n, by omega⟩ =
          (((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) : WithTop ℚ) ∨
        HeHuZeroOrOne (a.order ⟨n + 2, by omega⟩)) ↔
      a.HeHuI2E n (by omega) := by
  let previous : Fin m := ⟨n - 1, by omega⟩
  let boundary : Fin m := ⟨n, by omega⟩
  let next : Fin m := ⟨n + 1, by omega⟩
  let threshold : WithTop ℚ :=
    ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ)
  let cap : WithTop ℚ :=
    ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
  have hPreviousOrder : a.order ⟨n - 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) :=
    hI1.evenOrder ⟨n - 1, by omega⟩ (by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnEven)
  have hMiddleOrder : a.order ⟨n, by omega⟩ = 0 :=
    hI1.oddOrder ⟨n, by omega⟩ (Even.add_one hnEven)
  have hPreviousGap : a.orderGap previous =
      2 * (ramificationIndex K : Int) := by
    unfold orderGap
    rw [show previous.succ = (⟨n, by omega⟩ : Fin (m + 1)) by
      ext
      simp only [previous, Fin.val_succ]
      omega]
    rw [show previous.castSucc =
        (⟨n - 1, by omega⟩ : Fin (m + 1)) by
      ext
      rfl]
    rw [hMiddleOrder, hPreviousOrder]
    omega
  have hPreviousAlpha : a.alphaValue previous =
      2 * (ramificationIndex K : ℚ) :=
    ((a.heHu2022Proposition26 previous).compareTwoE.2.1).2 hPreviousGap
  have hBoundaryGap : a.orderGap boundary =
      2 - 2 * (ramificationIndex K : Int) := by
    unfold orderGap
    rw [show boundary.succ = (⟨n + 1, by omega⟩ : Fin (m + 1)) by
      ext
      rfl]
    rw [show boundary.castSucc = (⟨n, by omega⟩ : Fin (m + 1)) by
      ext
      rfl]
    rw [hMiddleOrder, hBoundaryOrder, sub_zero]
  have hBoundaryAlpha : a.alphaValue boundary = 1 :=
    a.alphaValue_eq_one_of_orderGap_eq_endpoint boundary (Or.inl hBoundaryGap)
  have hLeftCap : a.prefixAlphaCap n = cap := by
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
    rw [show (⟨n - 1, by omega⟩ : Fin m) = previous by ext; rfl]
    rw [hPreviousAlpha]
  have hRightCap : a.prefixAlphaCap (n + 2) =
      (a.alphaValue next : WithTop ℚ) := by
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
    congr 2
  have hRaw : defectOrder (K := K)
      ((-1) * a.prefixProduct n * a.prefixProduct (n + 2)) =
      a.adjacentDefect boundary := by
    simpa only [boundary] using
      a.defectOrder_prefixPair_eq_adjacentDefect boundary
  have hRawAt : a.heHuAdjacentDefectAt ⟨n, by omega⟩ =
      a.adjacentDefect boundary := by
    rfl
  have hThresholdCast :
      (((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) : WithTop ℚ) =
        threshold := by
    congr 2
    push_cast
    rfl
  have hTarget :
      ((((1 : ℚ) - (a.order ⟨n + 1, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ) =
        threshold := by
    apply congrArg (fun x : ℚ => (x : WithTop ℚ))
    rw [hBoundaryOrder]
    push_cast
    ring
  have hCappedLower : threshold ≤ a.heHuAdjacentCappedDefect boundary := by
    have h := (a.heHu2022Proposition26 boundary).alphaOne hBoundaryAlpha |>.2.1
    rw [hBoundaryGap] at h
    have hEq :
        ((((1 : ℚ) - ((2 - 2 * (ramificationIndex K : Int) : Int) : ℚ)) : ℚ) :
            WithTop ℚ) = threshold := by
      apply congrArg (fun x : ℚ => (x : WithTop ℚ))
      push_cast
      ring
    rw [← hEq]
    exact h
  have hThresholdLtCap : threshold < cap := by
    dsimp only [threshold, cap]
    exact_mod_cast (show
      (2 * (ramificationIndex K : ℚ) - 1 : ℚ) <
        2 * (ramificationIndex K : ℚ) by linarith)
  have hCappedFormula : a.heHuAdjacentCappedDefect boundary =
      min (a.adjacentDefect boundary)
        (min cap (a.alphaValue next : WithTop ℚ)) := by
    unfold heHuAdjacentCappedDefect truncatedPrefixDefect
    rw [show boundary.val = n by rfl,
      show boundary.val + 2 = n + 2 by rfl,
      hRaw, hLeftCap, hRightCap]
  have hCappedIff : a.heHuAdjacentCappedDefect boundary = threshold ↔
      a.adjacentDefect boundary = threshold ∨
        a.alphaValue next = 2 * (ramificationIndex K : ℚ) - 1 := by
    rw [hCappedFormula]
    have hMin := min_three_eq_iff_extreme hThresholdLtCap (by
      simpa only [hCappedFormula] using hCappedLower)
    rw [hMin]
    exact or_congr Iff.rfl WithTop.coe_eq_coe
  have hNextIff := a.heHu2022Lemma61_equation61 hnEven hmStable
    hIntegral hBoundaryOrder
  unfold HeHuI2E
  dsimp only
  rw [show (⟨n, by omega⟩ : Fin m) = boundary by ext; rfl]
  rw [hBoundaryAlpha, hTarget, hRawAt, hThresholdCast]
  norm_num
  rw [← hNextIff]
  exact hCappedIff.symm

/-- The minimum calculation in Lemma 6.1(ii), isolated at the nontrivial
even interval.  It is the source identity `alpha_(n+1)=1` iff one of the
tail candidates `T_j`, `j >= n+1`, is one. -/
theorem heHu2022Lemma61ii_middle
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hnEven : Even n) (hmStable : n + 2 ≤ m)
    (hI1 : a.HeHuI1E n (by omega))
    (hBoundaryRange : HeHuInEvenInterval
      (a.order ⟨n + 1, by omega⟩)
      (4 - 2 * (ramificationIndex K : Int)) 0) :
    a.alphaValue ⟨n, by omega⟩ = 1 ↔
      ∃ j : Fin m, n ≤ j.1 ∧
        a.heHuAdjacentDefectAt j =
          (((1 - a.heHuOrderAfterAdjacent j : Int) : ℚ) : WithTop ℚ) := by
  let boundary : Fin m := ⟨n, by omega⟩
  have hMiddleOrder : a.order ⟨n, by omega⟩ = 0 :=
    hI1.oddOrder ⟨n, by omega⟩ (Even.add_one hnEven)
  have hBoundaryGap : a.orderGap boundary =
      a.order ⟨n + 1, by omega⟩ := by
    unfold orderGap
    rw [show boundary.succ = (⟨n + 1, by omega⟩ : Fin (m + 1)) by
      ext
      rfl]
    rw [show boundary.castSucc = (⟨n, by omega⟩ : Fin (m + 1)) by
      ext
      rfl]
    rw [hMiddleOrder, sub_zero]
  have hBoundaryStrict :
      -(2 * (ramificationIndex K : Int)) <
        a.order ⟨n + 1, by omega⟩ := by
    exact lt_of_lt_of_le (by omega) hBoundaryRange.1
  have hAlphaNe : a.alphaValue boundary ≠ 0 := by
    intro hZero
    have hGapZero := ((a.heHu2022Proposition26 boundary).alphaZero).mp hZero
    rw [hBoundaryGap] at hGapZero
    omega
  have hAlphaLower : 1 ≤ a.alphaValue boundary :=
    a.heHuOne_le_alphaValue_of_ne_zero boundary hAlphaNe
  have hHalfGt : (1 : WithTop ℚ) < a.halfGapCandidate boundary := by
    rw [← a.coe_halfGapValue]
    exact_mod_cast (show (1 : ℚ) < a.halfGapValue boundary by
      unfold halfGapValue
      rw [hBoundaryGap]
      have hLowerQ :
          (4 - 2 * (ramificationIndex K : ℚ) : ℚ) ≤
            (a.order ⟨n + 1, by omega⟩ : ℚ) := by
        exact_mod_cast hBoundaryRange.1
      linarith)
  have hEarlyDefect (j : Fin m) (hj : j.1 < n) :
      ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
        (((-a.order j.castSucc : Int) : ℚ) : WithTop ℚ) +
          a.adjacentDefect j := by
    rcases Nat.even_or_odd j.1 with hEven | hOdd
    · have hCurrent : a.order j.castSucc = 0 := by
        have h := hI1.oddOrder ⟨j.1, by omega⟩ (Even.add_one hEven)
        simpa only [show j.castSucc =
          (⟨j.1, by omega⟩ : Fin (m + 1)) by ext; rfl] using h
      have hNextParity : Even (j.1 + 2) := by
        rcases hEven with ⟨k, hk⟩
        exact ⟨k + 1, by omega⟩
      have hNextBound : j.1 + 1 < n := by
        rcases hEven with ⟨k, hk⟩
        rcases hnEven with ⟨r, hr⟩
        omega
      have hNext : a.order j.succ =
          -(2 * (ramificationIndex K : Int)) := by
        have h := hI1.evenOrder ⟨j.1 + 1, hNextBound⟩ hNextParity
        simpa only [show j.succ =
          (⟨j.1 + 1, by omega⟩ : Fin (m + 1)) by ext; rfl] using h
      have hGap : a.orderGap j =
          -(2 * (ramificationIndex K : Int)) := by
        unfold orderGap
        rw [hCurrent, hNext]
        omega
      have hRaw := (a.heHu2022Corollary23ii j hGap).rawDefectLower
      rw [hCurrent]
      norm_num
      exact hRaw
    · have hCurrentParity : Even (j.1 + 1) := by
        rcases hOdd with ⟨k, hk⟩
        exact ⟨k + 1, by omega⟩
      have hCurrent : a.order j.castSucc =
          -(2 * (ramificationIndex K : Int)) := by
        have h := hI1.evenOrder ⟨j.1, by omega⟩ hCurrentParity
        simpa only [show j.castSucc =
          (⟨j.1, by omega⟩ : Fin (m + 1)) by ext; rfl] using h
      have hNonnegative : (0 : WithTop ℚ) ≤ a.adjacentDefect j :=
        defectOrder_nonneg_for_alpha (K := K) (a.adjacentProduct j)
      rw [hCurrent]
      have hCast :
          (((2 * (ramificationIndex K : Int) : Int) : ℚ) : WithTop ℚ) =
            ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
        congr 2
        push_cast
        rfl
      rw [show -( -(2 * (ramificationIndex K : Int))) =
          2 * (ramificationIndex K : Int) by ring, hCast]
      exact le_add_of_nonneg_right hNonnegative
  have hEarlyCandidate (j : Fin m) (hj : j.1 < n) :
      (1 : WithTop ℚ) < a.leftDefectCandidate boundary j := by
    have hOrderLowerQ : (4 : ℚ) ≤
        (a.order ⟨n + 1, by omega⟩ : ℚ) +
          2 * (ramificationIndex K : ℚ) := by
      have hLowerQ :
          (4 - 2 * (ramificationIndex K : ℚ) : ℚ) ≤
            (a.order ⟨n + 1, by omega⟩ : ℚ) := by
        exact_mod_cast hBoundaryRange.1
      linarith
    have hOrderLower : ((4 : ℚ) : WithTop ℚ) ≤
        ((a.order ⟨n + 1, by omega⟩ : ℚ) : WithTop ℚ) +
          ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
      exact_mod_cast hOrderLowerQ
    have hAdd :
        (((a.order ⟨n + 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
            ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
          (((a.order ⟨n + 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
            (((( -a.order j.castSucc : Int) : ℚ) : WithTop ℚ) +
              a.adjacentDefect j) :=
      by
        simpa only [add_comm] using
          (add_le_add_left (hEarlyDefect j hj)
            (((a.order ⟨n + 1, by omega⟩ : Int) : ℚ) : WithTop ℚ))
    have hCandidateForm : a.leftDefectCandidate boundary j =
        (((a.order ⟨n + 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          ((((-a.order j.castSucc : Int) : ℚ) : WithTop ℚ) +
            a.adjacentDefect j) := by
      unfold leftDefectCandidate
      rw [show boundary.succ =
          (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl]
      rw [← add_assoc, ← WithTop.coe_add]
      congr 2
      push_cast
      ring
    have hCandidateLower : ((4 : ℚ) : WithTop ℚ) ≤
        a.leftDefectCandidate boundary j := by
      rw [hCandidateForm]
      exact hOrderLower.trans hAdd
    exact (by norm_num : (1 : WithTop ℚ) < (4 : ℚ)).trans_le
      hCandidateLower
  constructor
  · intro hAlpha
    have hPivotOrder : a.order boundary.castSucc = 0 := by
      rw [show boundary.castSucc =
          (⟨n, by omega⟩ : Fin (m + 1)) by ext; rfl]
      exact hMiddleOrder
    have hMinMem := Finset.min'_mem
      (a.alphaCandidates boundary) (a.alphaCandidates_nonempty boundary)
    have hCandidateMem : (1 : WithTop ℚ) ∈ a.alphaCandidates boundary := by
      change a.alpha boundary ∈ a.alphaCandidates boundary at hMinMem
      rw [← a.coe_alphaValue boundary, hAlpha] at hMinMem
      exact hMinMem
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hCandidateMem
    rcases hCandidateMem with hHalf | hDefect
    · exact False.elim ((ne_of_gt hHalfGt) hHalf.symm)
    · rcases hDefect with hLeft | hRight
      · rcases hLeft with ⟨j, hjLe, hjEq⟩
        by_cases hjBoundary : j = boundary
        · subst j
          refine ⟨boundary, le_rfl, ?_⟩
          exact (rightCandidate_eq_one_iff_tailDefect a boundary boundary
            hPivotOrder).mp (by
              simpa only [leftDefectCandidate, rightDefectCandidate] using hjEq)
        · have hjLt : j.1 < n := by
            have hjNatLe : j.1 ≤ n := by
              have h : j.1 ≤ boundary.1 := hjLe
              simpa only [boundary] using h
            have hjNatNe : j.1 ≠ n := by
              intro hEq
              apply hjBoundary
              apply Fin.ext
              simpa only [boundary] using hEq
            omega
          exact False.elim ((ne_of_gt (hEarlyCandidate j hjLt)) hjEq)
      · rcases hRight with ⟨j, hij, hjEq⟩
        refine ⟨j, ?_,
          (rightCandidate_eq_one_iff_tailDefect a boundary j
            hPivotOrder).mp hjEq⟩
        have h : boundary.1 ≤ j.1 := hij
        simpa only [boundary] using h
  · rintro ⟨j, hj, hDefect⟩
    have hPivotOrder : a.order boundary.castSucc = 0 := by
      rw [show boundary.castSucc =
          (⟨n, by omega⟩ : Fin (m + 1)) by ext; rfl]
      exact hMiddleOrder
    have hCandidate : a.rightDefectCandidate boundary j =
        (1 : WithTop ℚ) :=
      (rightCandidate_eq_one_iff_tailDefect a boundary j
        hPivotOrder).mpr hDefect
    have hAlphaUpper : a.alphaValue boundary ≤ 1 := by
      have h := a.alpha_le_rightDefectCandidate
        (i := boundary) (j := j) (by
          exact Fin.mk_le_mk.mpr hj)
      rw [← a.coe_alphaValue boundary, hCandidate] at h
      exact_mod_cast h
    exact le_antisymm hAlphaUpper hAlphaLower

/-- Clause (ii)(1)(b) of Theorem 1.1, separated from its surrounding
range condition.  At `R_(n+2)=-2e` or `1` its antecedent is false, exactly
as in the published statement. -/
def HeHuTheorem11EvenClause1b
    {m : Nat} (a : GoodBONG q L (m + 1)) (n : Nat)
    (hmStable : n + 2 ≤ m) : Prop :=
  HeHuInEvenInterval (a.order ⟨n + 1, by omega⟩)
      (2 - 2 * (ramificationIndex K : Int)) 0 →
    ∃ j : Fin m, n ≤ j.1 ∧
      a.heHuAdjacentDefectAt j =
        (((1 - a.heHuOrderAfterAdjacent j : Int) : ℚ) : WithTop ℚ)

/-- He--Hu, Lemma 6.1(ii), including the two automatic boundary cases and
the full quantified tail alternative in Theorem 1.1(ii)(1)(b). -/
theorem heHu2022Lemma61ii
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (_hnTwo : 2 ≤ n) (hnEven : Even n) (hmStable : n + 2 ≤ m)
    (hI1 : a.HeHuI1E n (by omega))
    (hRange : HeHuInEvenInterval (a.order ⟨n + 1, by omega⟩)
        (-(2 * (ramificationIndex K : Int))) 0 ∨
      a.order ⟨n + 1, by omega⟩ = 1)
    (hNotExceptional : a.order ⟨n + 1, by omega⟩ ≠
      2 - 2 * (ramificationIndex K : Int)) :
    a.HeHuTheorem11EvenClause1b n hmStable ↔ a.HeHuI2E n (by omega) := by
  let boundary : Fin m := ⟨n, by omega⟩
  have hMiddleOrder : a.order ⟨n, by omega⟩ = 0 :=
    hI1.oddOrder ⟨n, by omega⟩ (Even.add_one hnEven)
  have hBoundaryGap : a.orderGap boundary =
      a.order ⟨n + 1, by omega⟩ := by
    unfold orderGap
    rw [show boundary.succ = (⟨n + 1, by omega⟩ : Fin (m + 1)) by
      ext
      rfl]
    rw [show boundary.castSucc = (⟨n, by omega⟩ : Fin (m + 1)) by
      ext
      rfl]
    rw [hMiddleOrder, sub_zero]
  have hCappedOfAlphaOne
      (hAlpha : a.alphaValue boundary = 1) :
      a.heHuAdjacentCappedDefect boundary =
        ((((1 : ℚ) - (a.order ⟨n + 1, by omega⟩ : ℚ)) : ℚ) :
          WithTop ℚ) := by
    exact a.cappedBoundary_eq_of_i1E_alpha_one_of_order_ne
      (by omega) hnEven hI1 hAlpha hNotExceptional
  by_cases hOuter : HeHuInEvenInterval
      (a.order ⟨n + 1, by omega⟩)
      (2 - 2 * (ramificationIndex K : Int)) 0
  · have hMiddleRange : HeHuInEvenInterval
        (a.order ⟨n + 1, by omega⟩)
        (4 - 2 * (ramificationIndex K : Int)) 0 := by
      refine ⟨?_, hOuter.2.1, hOuter.2.2⟩
      rcases hOuter.2.2 with ⟨k, hk⟩
      by_contra hNot
      have hLe : a.order ⟨n + 1, by omega⟩ ≤
          2 - 2 * (ramificationIndex K : Int) := by omega
      have hEq : a.order ⟨n + 1, by omega⟩ =
          2 - 2 * (ramificationIndex K : Int) := by
        exact le_antisymm hLe hOuter.1
      exact hNotExceptional hEq
    have hAlphaIff := a.heHu2022Lemma61ii_middle hnEven hmStable
      hI1 hMiddleRange
    constructor
    · intro hClause
      have hWitness := hClause hOuter
      have hAlpha : a.alphaValue boundary = 1 := by
        have h := hAlphaIff.mpr hWitness
        simpa only [boundary] using h
      unfold HeHuI2E
      dsimp only
      rw [show (⟨n, by omega⟩ : Fin m) = boundary by ext; rfl]
      exact Or.inr ⟨hAlpha, hCappedOfAlphaOne hAlpha⟩
    · intro hI2
      intro _
      unfold HeHuI2E at hI2
      dsimp only at hI2
      rw [show (⟨n, by omega⟩ : Fin m) = boundary by ext; rfl] at hI2
      rcases hI2 with hZero | ⟨hOne, _⟩
      · have hGapZero := ((a.heHu2022Proposition26 boundary).alphaZero).mp hZero
        rw [hBoundaryGap] at hGapZero
        have hLow := hOuter.1
        rw [hGapZero] at hLow
        omega
      · exact hAlphaIff.mp (by simpa only [boundary] using hOne)
  · have hClause : a.HeHuTheorem11EvenClause1b n hmStable := by
      intro h
      exact False.elim (hOuter h)
    have hI2 : a.HeHuI2E n (by omega) := by
      rcases hRange with hEvenRange | hOne
      · have hBoundaryOrder : a.order ⟨n + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int)) := by
          have hLt : a.order ⟨n + 1, by omega⟩ <
              2 - 2 * (ramificationIndex K : Int) := by
            have hNotLe : ¬ 2 - 2 * (ramificationIndex K : Int) ≤
                a.order ⟨n + 1, by omega⟩ := by
              intro hLe
              exact hOuter ⟨hLe, hEvenRange.2.1, hEvenRange.2.2⟩
            omega
          rcases hEvenRange.2.2 with ⟨k, hk⟩
          have hLow := hEvenRange.1
          omega
        have hGap : a.orderGap boundary =
            -(2 * (ramificationIndex K : Int)) := by
          rw [hBoundaryGap, hBoundaryOrder]
        have hAlpha := ((a.heHu2022Proposition26 boundary).alphaZero).mpr hGap
        unfold HeHuI2E
        dsimp only
        rw [show (⟨n, by omega⟩ : Fin m) = boundary by ext; rfl]
        exact Or.inl hAlpha
      · have hGap : a.orderGap boundary = 1 := by
          rw [hBoundaryGap, hOne]
        have hAlpha := a.alphaValue_eq_one_of_orderGap_eq_endpoint boundary
          (Or.inr hGap)
        unfold HeHuI2E
        dsimp only
        rw [show (⟨n, by omega⟩ : Fin m) = boundary by ext; rfl]
        exact Or.inr ⟨hAlpha, hCappedOfAlphaOne hAlpha⟩
    exact ⟨fun _ => hI2, fun _ => hClause⟩

/-- Clause (ii)(1)(a) of Theorem 1.1. -/
def HeHuTheorem11EvenClause1a
    {m : Nat} (a : GoodBONG q L (m + 1)) (n : Nat)
    (hmStable : n + 2 ≤ m) : Prop :=
  a.heHuAdjacentDefectAt ⟨n, by omega⟩ =
        (((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) : WithTop ℚ) ∨
    HeHuZeroOrOne (a.order ⟨n + 2, by omega⟩)

/-- He--Hu, Lemma 6.1, with both published clauses assembled under the
range condition in Theorem 1.1(ii)(1). -/
theorem heHu2022Lemma61
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hnTwo : 2 ≤ n) (hnEven : Even n) (hmStable : n + 2 ≤ m)
    (hIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E n (by omega))
    (hRange : HeHuInEvenInterval (a.order ⟨n + 1, by omega⟩)
        (-(2 * (ramificationIndex K : Int))) 0 ∨
      a.order ⟨n + 1, by omega⟩ = 1) :
    (a.order ⟨n + 1, by omega⟩ =
          2 - 2 * (ramificationIndex K : Int) →
        (a.HeHuTheorem11EvenClause1a n hmStable ↔
          a.HeHuI2E n (by omega))) ∧
      (a.order ⟨n + 1, by omega⟩ ≠
            2 - 2 * (ramificationIndex K : Int) →
        (a.HeHuTheorem11EvenClause1b n hmStable ↔
          a.HeHuI2E n (by omega))) := by
  constructor
  · intro hExceptional
    simpa only [HeHuTheorem11EvenClause1a] using
      a.heHu2022Lemma61i hnTwo hnEven hmStable hIntegral hI1 hExceptional
  · intro hNotExceptional
    exact a.heHu2022Lemma61ii hnTwo hnEven hmStable hI1 hRange
      hNotExceptional

/-- The conjunction of Theorem 1.1(i) and (iii)(1), with the latter kept in
its two printed clauses. -/
structure HeHuTheorem11OddInitialConditions
    {m : Nat} (a : GoodBONG q L (m + 1)) (n : Nat)
    (hmStable : n + 2 ≤ m) : Prop where
  initial : a.HeHuAlternatingInitialOrders n (by omega)
  orderRange :
    HeHuInEvenInterval (a.order ⟨n, by omega⟩)
        (-(2 * (ramificationIndex K : Int))) 0 ∨
      a.order ⟨n, by omega⟩ = 1
  middle :
    HeHuInEvenInterval (a.order ⟨n, by omega⟩)
        (4 - 2 * (ramificationIndex K : Int)) 0 →
      ∃ j : Fin m, n - 1 ≤ j.1 ∧
        a.heHuAdjacentDefectAt j =
          (((1 - a.heHuOrderAfterAdjacent j : Int) : ℚ) : WithTop ℚ)

/-- He--Hu, Corollary 6.2: for odd `n >= 3`, Theorem 1.1(i) together
with (iii)(1) is equivalent to `I1^O(n)`. -/
theorem heHu2022Corollary62
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hnThree : 3 ≤ n) (hnOdd : Odd n) (hmStable : n + 2 ≤ m) :
    a.HeHuTheorem11OddInitialConditions n hmStable ↔
      a.HeHuI1O n hnThree hmStable := by
  let boundary : Fin m := ⟨n - 1, by omega⟩
  have hnMinusEven : Even (n - 1) := by
    rcases hnOdd with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    omega
  have makeI1E
      (hInitial : a.HeHuAlternatingInitialOrders n (by omega)) :
      a.HeHuI1E (n - 1) (by omega) := by
    constructor
    · intro i hi
      exact hInitial.1 ⟨i.1, by omega⟩ hi
    · intro i hi
      exact hInitial.2 ⟨i.1, by omega⟩ hi
  have boundaryOrder
      (hInitial : a.HeHuAlternatingInitialOrders n (by omega)) :
      a.order ⟨n - 1, by omega⟩ = 0 := by
    have h := hInitial.1 ⟨n - 1, by omega⟩ (by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnOdd)
    exact h
  constructor
  · intro h11
    have hI1E := makeI1E h11.initial
    have hRn : a.order ⟨n - 1, by omega⟩ = 0 :=
      boundaryOrder h11.initial
    have hGap : a.orderGap boundary = a.order ⟨n, by omega⟩ := by
      unfold orderGap
      rw [show boundary.succ = (⟨n, by omega⟩ : Fin (m + 1)) by
        ext
        simp only [boundary, Fin.val_succ]
        omega]
      rw [show boundary.castSucc =
          (⟨n - 1, by omega⟩ : Fin (m + 1)) by ext; rfl]
      rw [hRn, sub_zero]
    refine ⟨h11.initial.1, h11.initial.2, ?_⟩
    rcases h11.orderRange with hEvenRange | hOne
    · by_cases hBottom : a.order ⟨n, by omega⟩ =
          -(2 * (ramificationIndex K : Int))
      · left
        apply ((a.heHu2022Proposition26 boundary).alphaZero).mpr
        rw [hGap, hBottom]
      · by_cases hEndpoint : a.order ⟨n, by omega⟩ =
            2 - 2 * (ramificationIndex K : Int)
        · right
          apply a.alphaValue_eq_one_of_orderGap_eq_endpoint boundary
          left
          rw [hGap, hEndpoint]
        · have hMiddleRange : HeHuInEvenInterval
              (a.order ⟨n, by omega⟩)
              (4 - 2 * (ramificationIndex K : Int)) 0 := by
            refine ⟨?_, hEvenRange.2.1, hEvenRange.2.2⟩
            rcases hEvenRange.2.2 with ⟨k, hk⟩
            have hLow := hEvenRange.1
            omega
          right
          have hMiddleIff := a.heHu2022Lemma61ii_middle
            hnMinusEven (by omega) hI1E (by
              simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
                hMiddleRange)
          apply hMiddleIff.mpr
          simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
            h11.middle hMiddleRange
    · right
      apply a.alphaValue_eq_one_of_orderGap_eq_endpoint boundary
      right
      rw [hGap, hOne]
  · intro hI1O
    have hInitial : a.HeHuAlternatingInitialOrders n (by omega) :=
      ⟨hI1O.1, hI1O.2.1⟩
    have hI1E : a.HeHuI1E (n - 1) (by omega) := hI1O.toI1E
    have hRn : a.order ⟨n - 1, by omega⟩ = 0 :=
      boundaryOrder hInitial
    have hGap : a.orderGap boundary = a.order ⟨n, by omega⟩ := by
      unfold orderGap
      rw [show boundary.succ = (⟨n, by omega⟩ : Fin (m + 1)) by
        ext
        simp only [boundary, Fin.val_succ]
        omega]
      rw [show boundary.castSucc =
          (⟨n - 1, by omega⟩ : Fin (m + 1)) by ext; rfl]
      rw [hRn, sub_zero]
    refine { initial := hInitial, orderRange := ?_, middle := ?_ }
    · rcases hI1O.2.2 with hZero | hOne
      · left
        have hBottom := ((a.heHu2022Proposition26 boundary).alphaZero).mp hZero
        rw [hGap] at hBottom
        refine ⟨?_, ?_, ?_⟩
        · rw [hBottom]
        · rw [hBottom]
          omega
        · exact ⟨-(ramificationIndex K : Int), by rw [hBottom]; ring⟩
      · have hShape := (a.heHu2022Proposition26 boundary).alphaOne hOne |>.1
        rw [hGap] at hShape
        rcases hShape with hOrderOne | hEven
        · exact Or.inr hOrderOne
        · exact Or.inl ⟨by omega, hEven.2.2, hEven.1⟩
    · intro hMiddleRange
      rcases hI1O.2.2 with hZero | hOne
      · have hBottom := ((a.heHu2022Proposition26 boundary).alphaZero).mp hZero
        rw [hGap] at hBottom
        have hLow := hMiddleRange.1
        rw [hBottom] at hLow
        omega
      · have hMiddleIff := a.heHu2022Lemma61ii_middle
          hnMinusEven (by omega) hI1E (by
            simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
              hMiddleRange)
        have hWitness := hMiddleIff.mp (by
          simpa only [boundary] using hOne)
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hWitness

/-- The second implication in `I2^O(n)`, named separately because Lemma 6.3
identifies precisely this part with Theorem 1.1(iii)(2). -/
noncomputable def HeHuI2OSecondPart
    {m : Nat} (a : GoodBONG q L (m + 1)) (n : Nat)
    (hn : 3 ≤ n) (hmStable : n + 2 ≤ m) : Prop :=
  a.alphaValue ⟨n - 1, by omega⟩ = 1 →
    (a.order ⟨n, by omega⟩ = 1 ∨
      1 < a.order ⟨n + 1, by omega⟩) →
    a.alphaValue ⟨n + 1, by omega⟩ ≤
      (a.heHuOddThreshold n hmStable : ℚ)

/-- Theorem 1.1(iii)(2), exactly as printed, including its outer trigger
and its even/odd subclauses. -/
def HeHuTheorem11OddClause2
    {m : Nat} (a : GoodBONG q L (m + 1)) (n : Nat)
    (_hn : 3 ≤ n) (hmStable : n + 2 ≤ m) : Prop :=
  (a.order ⟨n, by omega⟩ = 1 ∨
      (a.order ⟨n, by omega⟩ ≠
          -(2 * (ramificationIndex K : Int)) ∧
        1 < a.order ⟨n + 1, by omega⟩)) →
    ((Even (a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩) →
      (a.order ⟨n + 2, by omega⟩ + a.order ⟨n + 1, by omega⟩ -
            2 * a.order ⟨n, by omega⟩ ≤
          2 * (ramificationIndex K : Int) - 2 ∨
        ∃ j : Fin m, n + 1 ≤ j.1 ∧
          a.heHuAdjacentDefectAt j ≤
            ((2 * (ramificationIndex K : Int) +
              a.order ⟨n, by omega⟩ - a.heHuOrderAfterAdjacent j - 1 : Int) :
                ℚ))) ∧
    (Odd (a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩) →
      (a.order ⟨n + 2, by omega⟩ + a.order ⟨n + 1, by omega⟩ -
            2 * a.order ⟨n, by omega⟩ ≤
          2 * (ramificationIndex K : Int) ∨
        ∃ j : Fin m, n + 1 ≤ j.1 ∧
          a.heHuAdjacentDefectAt j ≤
            ((2 * (ramificationIndex K : Int) +
              a.order ⟨n, by omega⟩ - a.heHuOrderAfterAdjacent j : Int) :
                ℚ))))

/-- One parity row of the conclusion of Lemma 6.3.  The parameter `t` is
one in the even-gap row and zero in the odd-gap row. -/
def HeHuLemma63Branch
    {m : Nat} (a : GoodBONG q L (m + 1)) (n : Nat)
    (hmStable : n + 2 ≤ m) (t : Int) : Prop :=
  a.order ⟨n + 2, by omega⟩ + a.order ⟨n + 1, by omega⟩ -
        2 * a.order ⟨n, by omega⟩ ≤
      2 * (ramificationIndex K : Int) - 2 * t ∨
    ∃ j : Fin m, n + 1 ≤ j.1 ∧
      a.heHuAdjacentDefectAt j ≤
        ((2 * (ramificationIndex K : Int) +
          a.order ⟨n, by omega⟩ - a.heHuOrderAfterAdjacent j - t : Int) : ℚ)

/-- The finite-minimum calculation at the heart of Lemma 6.3. -/
theorem heHuLemma63_alphaNext_le_iff_branch
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hnThree : 3 ≤ n) (hnOdd : Odd n) (hmStable : n + 2 ≤ m)
    (hIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1O n hnThree hmStable)
    (hAlpha : a.alphaValue ⟨n - 1, by omega⟩ = 1)
    (hTrigger : a.order ⟨n, by omega⟩ = 1 ∨
      1 < a.order ⟨n + 1, by omega⟩)
    (t : Int) (_htNonnegative : 0 ≤ t) (htOne : t ≤ 1)
    (hThreshold : a.heHuOddThreshold n hmStable =
      2 * (ramificationIndex K : Int) - a.order ⟨n + 1, by omega⟩ +
        a.order ⟨n, by omega⟩ - t)
    (hMiddleRaw : ((t : Int) : ℚ) ≤
      a.adjacentDefect ⟨n, by omega⟩) :
    a.alphaValue ⟨n + 1, by omega⟩ ≤
        (a.heHuOddThreshold n hmStable : ℚ) ↔
      a.HeHuLemma63Branch n hmStable t := by
  let alphaBoundary : Fin m := ⟨n - 1, by omega⟩
  let middle : Fin m := ⟨n, by omega⟩
  let pivot : Fin m := ⟨n + 1, by omega⟩
  let threshold : Int := a.heHuOddThreshold n hmStable
  have hRn : a.order ⟨n - 1, by omega⟩ = 0 := by
    exact hI1.1 ⟨n - 1, by omega⟩ (by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnOdd)
  have hR1Lower : -(2 * (ramificationIndex K : Int)) ≤
      a.order ⟨n, by omega⟩ := by
    exact (a.heHu2022Proposition27i hIntegral).evenIndexed
      ⟨n, by omega⟩ ⟨n, by omega⟩ (le_refl _) hnOdd hnOdd |>.1
  have hnPlusTwoOdd : Odd (n + 2) := by
    rcases hnOdd with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩
  have hR3GeR1 : a.order ⟨n, by omega⟩ ≤
      a.order ⟨n + 2, by omega⟩ :=
    (a.heHu2022Proposition27i hIntegral).evenIndexed
      ⟨n, by omega⟩ ⟨n + 2, by omega⟩ (Fin.mk_le_mk.mpr (by omega))
      hnOdd hnPlusTwoOdd |>.2
  have hR2GeOne : 1 ≤ a.order ⟨n + 1, by omega⟩ := by
    rcases hTrigger with hR1One | hR2Gt
    · exact a.heHu2022Remark52_order_ge_one hnThree hnOdd hmStable
        hIntegral hR1One
    · omega
  have hPivotGap : a.orderGap pivot =
      a.order ⟨n + 2, by omega⟩ - a.order ⟨n + 1, by omega⟩ := by
    rfl
  have hThresholdValue : threshold =
      2 * (ramificationIndex K : Int) - a.order ⟨n + 1, by omega⟩ +
        a.order ⟨n, by omega⟩ - t := by
    exact hThreshold
  have hHalfIff :
      a.halfGapCandidate pivot ≤ (((threshold : Int) : ℚ) : WithTop ℚ) ↔
        a.order ⟨n + 2, by omega⟩ + a.order ⟨n + 1, by omega⟩ -
              2 * a.order ⟨n, by omega⟩ ≤
            2 * (ramificationIndex K : Int) - 2 * t := by
    rw [← a.coe_halfGapValue]
    constructor
    · intro h
      have hQ : a.halfGapValue pivot ≤ (threshold : ℚ) := by
        exact_mod_cast h
      unfold halfGapValue at hQ
      rw [hPivotGap, hThresholdValue] at hQ
      push_cast at hQ
      have hQ' :
          ((a.order ⟨n + 2, by omega⟩ + a.order ⟨n + 1, by omega⟩ -
              2 * a.order ⟨n, by omega⟩ : Int) : ℚ) ≤
            ((2 * (ramificationIndex K : Int) - 2 * t : Int) : ℚ) := by
        push_cast
        linarith
      exact_mod_cast hQ'
    · intro h
      have hQ :
          ((a.order ⟨n + 2, by omega⟩ + a.order ⟨n + 1, by omega⟩ -
              2 * a.order ⟨n, by omega⟩ : Int) : ℚ) ≤
            ((2 * (ramificationIndex K : Int) - 2 * t : Int) : ℚ) := by
        exact_mod_cast h
      have hHalfQ : a.halfGapValue pivot ≤ (threshold : ℚ) := by
        unfold halfGapValue
        rw [hPivotGap, hThresholdValue]
        push_cast at hQ ⊢
        linarith
      exact_mod_cast hHalfQ
  have hRightIff (j : Fin m) :
      a.rightDefectCandidate pivot j ≤
          (((threshold : Int) : ℚ) : WithTop ℚ) ↔
        a.heHuAdjacentDefectAt j ≤
          (((2 * (ramificationIndex K : Int) +
            a.order ⟨n, by omega⟩ - a.heHuOrderAfterAdjacent j - t : Int) :
              ℚ) : WithTop ℚ) := by
    have hRaw : a.heHuAdjacentDefectAt j = a.adjacentDefect j := by rfl
    have hAfter : a.heHuOrderAfterAdjacent j = a.order j.succ := by rfl
    rw [hRaw, hAfter]
    let shift : Int := a.order j.succ - a.order ⟨n + 1, by omega⟩
    let bound : Int := 2 * (ramificationIndex K : Int) +
      a.order ⟨n, by omega⟩ - a.order j.succ - t
    have hPivotCast : pivot.castSucc =
        (⟨n + 1, by omega⟩ : Fin (m + 1)) := by ext; rfl
    have hShift : a.rightDefectCandidate pivot j =
        (((shift : Int) : ℚ) : WithTop ℚ) + a.adjacentDefect j := by
      unfold rightDefectCandidate
      rw [hPivotCast]
    have hSum :
        (((shift : Int) : ℚ) : WithTop ℚ) +
            (((bound : Int) : ℚ) : WithTop ℚ) =
          (((threshold : Int) : ℚ) : WithTop ℚ) := by
      rw [← WithTop.coe_add]
      apply congrArg (fun x : ℚ => (x : WithTop ℚ))
      rw [hThresholdValue]
      dsimp only [shift, bound]
      push_cast
      ring
    rw [hShift]
    constructor
    · intro h
      apply (WithTop.add_le_add_iff_left (x :=
        (((shift : Int) : ℚ) : WithTop ℚ)) WithTop.coe_ne_top).mp
      rw [hSum]
      exact h
    · intro h
      have hAdd := (WithTop.add_le_add_iff_left (x :=
        (((shift : Int) : ℚ) : WithTop ℚ)) WithTop.coe_ne_top).mpr h
      rw [hSum] at hAdd
      exact hAdd
  have hEarlyDefect (j : Fin m) (hj : j.1 < n - 1) :
      ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
        (((-a.order j.castSucc : Int) : ℚ) : WithTop ℚ) +
          a.adjacentDefect j := by
    rcases Nat.even_or_odd j.1 with hEven | hOdd
    · have hCurrent : a.order j.castSucc = 0 := by
        have h := hI1.1 ⟨j.1, by omega⟩ (Even.add_one hEven)
        simpa only [show j.castSucc =
          (⟨j.1, by omega⟩ : Fin (m + 1)) by ext; rfl] using h
      have hNextParity : Even (j.1 + 2) := by
        rcases hEven with ⟨k, hk⟩
        exact ⟨k + 1, by omega⟩
      have hNext : a.order j.succ =
          -(2 * (ramificationIndex K : Int)) := by
        have h := hI1.2.1 ⟨j.1 + 1, by omega⟩ hNextParity
        simpa only [show j.succ =
          (⟨j.1 + 1, by omega⟩ : Fin (m + 1)) by ext; rfl] using h
      have hGap : a.orderGap j =
          -(2 * (ramificationIndex K : Int)) := by
        unfold orderGap
        rw [hCurrent, hNext]
        omega
      have hRaw := (a.heHu2022Corollary23ii j hGap).rawDefectLower
      rw [hCurrent]
      norm_num
      exact hRaw
    · have hCurrentParity : Even (j.1 + 1) := by
        rcases hOdd with ⟨k, hk⟩
        exact ⟨k + 1, by omega⟩
      have hCurrent : a.order j.castSucc =
          -(2 * (ramificationIndex K : Int)) := by
        have h := hI1.2.1 ⟨j.1, by omega⟩ hCurrentParity
        simpa only [show j.castSucc =
          (⟨j.1, by omega⟩ : Fin (m + 1)) by ext; rfl] using h
      have hNonnegative : (0 : WithTop ℚ) ≤ a.adjacentDefect j :=
        defectOrder_nonneg_for_alpha (K := K) (a.adjacentProduct j)
      rw [hCurrent]
      have hCast :
          (((2 * (ramificationIndex K : Int) : Int) : ℚ) : WithTop ℚ) =
            ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
        congr 2
        push_cast
        rfl
      rw [show -( -(2 * (ramificationIndex K : Int))) =
          2 * (ramificationIndex K : Int) by ring, hCast]
      exact le_add_of_nonneg_right hNonnegative
  have hHalfLeBase : a.halfGapCandidate pivot ≤
      (((a.order ⟨n + 2, by omega⟩ +
        2 * (ramificationIndex K : Int) : Int) : ℚ) : WithTop ℚ) := by
    rw [← a.coe_halfGapValue]
    exact_mod_cast (show a.halfGapValue pivot ≤
        (a.order ⟨n + 2, by omega⟩ +
          2 * (ramificationIndex K : Int) : Int) by
      unfold halfGapValue
      rw [hPivotGap]
      push_cast
      have hR3Lower := hR1Lower.trans hR3GeR1
      have hR3LowerQ : -(2 * (ramificationIndex K : ℚ)) ≤
          (a.order ⟨n + 2, by omega⟩ : ℚ) := by
        exact_mod_cast hR3Lower
      have hR2GeOneQ : (1 : ℚ) ≤
          (a.order ⟨n + 1, by omega⟩ : ℚ) := by
        exact_mod_cast hR2GeOne
      linarith)
  have hEarlyCandidate (j : Fin m) (hj : j.1 < n - 1) :
      a.halfGapCandidate pivot ≤ a.leftDefectCandidate pivot j := by
    have hAdd :
        (((a.order ⟨n + 2, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
            ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
          (((a.order ⟨n + 2, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
            ((((-a.order j.castSucc : Int) : ℚ) : WithTop ℚ) +
              a.adjacentDefect j) := by
      simpa only [add_comm] using
        (add_le_add_left (hEarlyDefect j hj)
          (((a.order ⟨n + 2, by omega⟩ : Int) : ℚ) : WithTop ℚ))
    have hCandidateForm : a.leftDefectCandidate pivot j =
        (((a.order ⟨n + 2, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          ((((-a.order j.castSucc : Int) : ℚ) : WithTop ℚ) +
            a.adjacentDefect j) := by
      unfold leftDefectCandidate
      rw [show pivot.succ =
          (⟨n + 2, by omega⟩ : Fin (m + 1)) by ext; rfl]
      rw [← add_assoc, ← WithTop.coe_add]
      congr 2
      push_cast
      ring
    apply hHalfLeBase.trans
    rw [hCandidateForm]
    convert hAdd using 1 <;> push_cast <;> ring
  have hFirstMiddleLower :
      ((((t - a.order ⟨n, by omega⟩ : Int) : ℚ)) : WithTop ℚ) ≤
        a.adjacentDefect alphaBoundary := by
    have hAlphaCandidate := a.alpha_le_rightDefectCandidate
      (i := alphaBoundary) (j := alphaBoundary) (le_refl _)
    have hAlphaCandidate' : (1 : WithTop ℚ) ≤
        a.rightDefectCandidate alphaBoundary alphaBoundary := by
      rw [← a.coe_alphaValue alphaBoundary] at hAlphaCandidate
      have hAlpha' : a.alphaValue alphaBoundary = 1 := by
        simpa only [alphaBoundary] using hAlpha
      rw [hAlpha'] at hAlphaCandidate
      exact hAlphaCandidate
    have hCandidateForm : a.rightDefectCandidate alphaBoundary alphaBoundary =
        (((a.order ⟨n, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.adjacentDefect alphaBoundary := by
      unfold rightDefectCandidate
      rw [show alphaBoundary.succ =
          (⟨n, by omega⟩ : Fin (m + 1)) by
        ext
        simp only [alphaBoundary, Fin.val_succ]
        omega]
      rw [show alphaBoundary.castSucc =
          (⟨n - 1, by omega⟩ : Fin (m + 1)) by ext; rfl]
      rw [hRn]
      push_cast
      norm_num
    have htLe : (((t : Int) : ℚ) : WithTop ℚ) ≤ (1 : WithTop ℚ) := by
      exact_mod_cast htOne
    have hSumLe : (((t : Int) : ℚ) : WithTop ℚ) ≤
        (((a.order ⟨n, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.adjacentDefect alphaBoundary := by
      rw [← hCandidateForm]
      exact htLe.trans hAlphaCandidate'
    apply (WithTop.add_le_add_iff_left (x :=
      (((a.order ⟨n, by omega⟩ : Int) : ℚ) : WithTop ℚ))
      WithTop.coe_ne_top).mp
    have hCancelLeft :
        (((a.order ⟨n, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
            ((((t - a.order ⟨n, by omega⟩ : Int) : ℚ)) : WithTop ℚ) =
          (((t : Int) : ℚ) : WithTop ℚ) := by
      rw [← WithTop.coe_add]
      congr 2
      push_cast
      ring
    rw [hCancelLeft]
    exact hSumLe
  have hMiddleLower (j : Fin m)
      (hj : j = alphaBoundary ∨ j = middle) :
      ((((t - a.order ⟨n, by omega⟩ + a.order j.castSucc : Int) : ℚ)) :
          WithTop ℚ) ≤ a.adjacentDefect j := by
    rcases hj with rfl | rfl
    · rw [show alphaBoundary.castSucc =
          (⟨n - 1, by omega⟩ : Fin (m + 1)) by ext; rfl, hRn]
      simpa only [add_zero] using hFirstMiddleLower
    · rw [show middle.castSucc =
          (⟨n, by omega⟩ : Fin (m + 1)) by ext; rfl]
      convert hMiddleRaw using 1
      · congr 2
        push_cast
        ring
  have hMiddleCandidateToHalf (j : Fin m)
      (hj : j = alphaBoundary ∨ j = middle)
      (hCandidate : a.leftDefectCandidate pivot j ≤
        (((threshold : Int) : ℚ) : WithTop ℚ)) :
      a.halfGapCandidate pivot ≤
        (((threshold : Int) : ℚ) : WithTop ℚ) := by
    have hCandidateForm : a.leftDefectCandidate pivot j =
        ((((a.order ⟨n + 2, by omega⟩ - a.order j.castSucc : Int) : ℚ)) :
            WithTop ℚ) + a.adjacentDefect j := by
      unfold leftDefectCandidate
      rw [show pivot.succ =
          (⟨n + 2, by omega⟩ : Fin (m + 1)) by ext; rfl]
    have hFinite :
        ((((a.order ⟨n + 2, by omega⟩ + t -
            a.order ⟨n, by omega⟩ : Int) : ℚ)) : WithTop ℚ) =
          ((((a.order ⟨n + 2, by omega⟩ - a.order j.castSucc : Int) : ℚ)) :
              WithTop ℚ) +
            ((((t - a.order ⟨n, by omega⟩ + a.order j.castSucc : Int) : ℚ)) :
              WithTop ℚ) := by
      rw [← WithTop.coe_add]
      congr 2
      push_cast
      ring
    have hLower :
        ((((a.order ⟨n + 2, by omega⟩ + t -
            a.order ⟨n, by omega⟩ : Int) : ℚ)) : WithTop ℚ) ≤
          a.leftDefectCandidate pivot j := by
      rw [hFinite, hCandidateForm]
      exact add_le_add_right (hMiddleLower j hj)
        ((((a.order ⟨n + 2, by omega⟩ - a.order j.castSucc : Int) : ℚ)) :
          WithTop ℚ)
    have hIntCast :
        ((((a.order ⟨n + 2, by omega⟩ + t -
            a.order ⟨n, by omega⟩ : Int) : ℚ)) : WithTop ℚ) ≤
          (((threshold : Int) : ℚ) : WithTop ℚ) :=
      hLower.trans hCandidate
    have hInt : a.order ⟨n + 2, by omega⟩ + t -
        a.order ⟨n, by omega⟩ ≤ threshold := by
      exact_mod_cast hIntCast
    apply hHalfIff.mpr
    rw [hThresholdValue] at hInt
    omega
  constructor
  · intro hAlphaLe
    have hAlphaLeTop :
        (a.alphaValue pivot : WithTop ℚ) ≤
          (((threshold : Int) : ℚ) : WithTop ℚ) := by
      exact_mod_cast hAlphaLe
    have hMinMem := Finset.min'_mem
      (a.alphaCandidates pivot) (a.alphaCandidates_nonempty pivot)
    have hCandidateMem :
        (a.alphaValue pivot : WithTop ℚ) ∈ a.alphaCandidates pivot := by
      change a.alpha pivot ∈ a.alphaCandidates pivot at hMinMem
      rw [← a.coe_alphaValue pivot] at hMinMem
      exact hMinMem
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hCandidateMem
    unfold HeHuLemma63Branch
    rcases hCandidateMem with hHalf | hDefect
    · left
      apply hHalfIff.mp
      exact hHalf.symm.trans_le hAlphaLeTop
    · rcases hDefect with hLeft | hRight
      · rcases hLeft with ⟨j, hjLe, hjEq⟩
        have hCandidateLe : a.leftDefectCandidate pivot j ≤
            (((threshold : Int) : ℚ) : WithTop ℚ) :=
          hjEq.trans_le hAlphaLeTop
        by_cases hEarly : j.1 < n - 1
        · left
          exact hHalfIff.mp ((hEarlyCandidate j hEarly).trans hCandidateLe)
        · by_cases hTail : n + 1 ≤ j.1
          · right
            have hjPivot : j = pivot := by
              apply Fin.ext
              have hUpper : j.1 ≤ n + 1 := by
                have h : j.1 ≤ pivot.1 := hjLe
                simpa only [pivot] using h
              simp only [pivot]
              omega
            subst j
            refine ⟨pivot, by simp only [pivot]; exact le_rfl, ?_⟩
            apply (hRightIff pivot).mp
            simpa only [leftDefectCandidate, rightDefectCandidate] using hCandidateLe
          · left
            have hCases : j = alphaBoundary ∨ j = middle := by
              have hLower : n - 1 ≤ j.1 := by omega
              have hUpper : j.1 ≤ n + 1 := by
                have h : j.1 ≤ pivot.1 := hjLe
                simpa only [pivot] using h
              have hLt : j.1 < n + 1 := by omega
              by_cases hEq : j.1 = n - 1
              · left
                apply Fin.ext
                simpa only [alphaBoundary] using hEq
              · right
                apply Fin.ext
                simp only [middle]
                omega
            exact hHalfIff.mp
              (hMiddleCandidateToHalf j hCases hCandidateLe)
      · rcases hRight with ⟨j, hij, hjEq⟩
        right
        refine ⟨j, ?_, (hRightIff j).mp (hjEq.trans_le hAlphaLeTop)⟩
        have h : pivot.1 ≤ j.1 := hij
        simpa only [pivot] using h
  · intro hBranch
    unfold HeHuLemma63Branch at hBranch
    rcases hBranch with hFirst | hTail
    · have hHalfLe := hHalfIff.mpr hFirst
      have hAlphaCandidate := a.alpha_le_halfGapCandidate pivot
      rw [← a.coe_alphaValue pivot] at hAlphaCandidate
      have hTop := hAlphaCandidate.trans hHalfLe
      exact_mod_cast hTop
    · rcases hTail with ⟨j, hj, hDefect⟩
      have hCandidateLe := (hRightIff j).mpr hDefect
      have hAlphaCandidate := a.alpha_le_rightDefectCandidate
        (i := pivot) (j := j) (Fin.mk_le_mk.mpr hj)
      rw [← a.coe_alphaValue pivot] at hAlphaCandidate
      have hTop := hAlphaCandidate.trans hCandidateLe
      exact_mod_cast hTop

/-- The parity-specialized form of the preceding minimum calculation. -/
theorem heHuLemma63_alphaNext_le_iff_rows
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hnThree : 3 ≤ n) (hnOdd : Odd n) (hmStable : n + 2 ≤ m)
    (hIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1O n hnThree hmStable)
    (hAlpha : a.alphaValue ⟨n - 1, by omega⟩ = 1)
    (hTrigger : a.order ⟨n, by omega⟩ = 1 ∨
      1 < a.order ⟨n + 1, by omega⟩) :
    a.alphaValue ⟨n + 1, by omega⟩ ≤
        (a.heHuOddThreshold n hmStable : ℚ) ↔
      ((Even (a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩) →
        (a.order ⟨n + 2, by omega⟩ + a.order ⟨n + 1, by omega⟩ -
              2 * a.order ⟨n, by omega⟩ ≤
            2 * (ramificationIndex K : Int) - 2 ∨
          ∃ j : Fin m, n + 1 ≤ j.1 ∧
            a.heHuAdjacentDefectAt j ≤
              ((2 * (ramificationIndex K : Int) +
                a.order ⟨n, by omega⟩ - a.heHuOrderAfterAdjacent j - 1 : Int) :
                  ℚ))) ∧
      (Odd (a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩) →
        (a.order ⟨n + 2, by omega⟩ + a.order ⟨n + 1, by omega⟩ -
              2 * a.order ⟨n, by omega⟩ ≤
            2 * (ramificationIndex K : Int) ∨
          ∃ j : Fin m, n + 1 ≤ j.1 ∧
            a.heHuAdjacentDefectAt j ≤
              ((2 * (ramificationIndex K : Int) +
                a.order ⟨n, by omega⟩ - a.heHuOrderAfterAdjacent j : Int) :
                  ℚ)))) := by
  let middle : Fin m := ⟨n, by omega⟩
  have hGap : a.orderGap middle =
      a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩ := by rfl
  rcases Int.even_or_odd
      (a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩) with
    hEven | hOdd
  · have hNotOdd : ¬ Odd
        (a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩) :=
      Int.not_odd_iff_even.mpr hEven
    have hThreshold : a.heHuOddThreshold n hmStable =
        2 * (ramificationIndex K : Int) - a.order ⟨n + 1, by omega⟩ +
          a.order ⟨n, by omega⟩ - 1 := by
      simp only [heHuOddThreshold, hEven, if_pos]
    have hProductEven : Even (ordUnit K (a.adjacentProduct middle)) :=
      a.even_ordUnit_adjacentProduct_of_even_orderGap middle (by
        simpa only [hGap] using hEven)
    have hRaw : (((1 : Int) : ℚ) : WithTop ℚ) ≤
        a.adjacentDefect middle := by
      exact defectOrder_one_le_of_even (a.adjacentProduct middle) hProductEven
    have hCore := a.heHuLemma63_alphaNext_le_iff_branch hnThree hnOdd
      hmStable hIntegral hI1 hAlpha hTrigger 1 (by omega) (by omega)
      hThreshold (by simpa only [middle] using hRaw)
    simpa only [hEven, hNotOdd, true_implies, false_implies, and_true,
      HeHuLemma63Branch, mul_one, sub_zero] using hCore
  · have hNotEven : ¬ Even
        (a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩) :=
      Int.not_even_iff_odd.mpr hOdd
    have hThreshold : a.heHuOddThreshold n hmStable =
        2 * (ramificationIndex K : Int) - a.order ⟨n + 1, by omega⟩ +
          a.order ⟨n, by omega⟩ - 0 := by
      simp [heHuOddThreshold, hNotEven]
    have hRaw : ((((0 : Int) : ℚ)) : WithTop ℚ) ≤
        a.adjacentDefect middle :=
      defectOrder_nonneg_for_alpha (K := K) (a.adjacentProduct middle)
    have hCore := a.heHuLemma63_alphaNext_le_iff_branch hnThree hnOdd
      hmStable hIntegral hI1 hAlpha hTrigger 0 (by omega) (by omega)
      hThreshold (by simpa only [middle] using hRaw)
    simpa only [hOdd, hNotEven, true_implies, false_implies, true_and,
      HeHuLemma63Branch, mul_zero, sub_zero] using hCore

/-- He--Hu, Lemma 6.3: under `I1^O(n)`, Theorem 1.1(iii)(2) is
equivalent to the second implication in `I2^O(n)`. -/
theorem heHu2022Lemma63
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hnThree : 3 ≤ n) (hnOdd : Odd n) (hmStable : n + 2 ≤ m)
    (hIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1O n hnThree hmStable) :
    a.HeHuTheorem11OddClause2 n hnThree hmStable ↔
      a.HeHuI2OSecondPart n hnThree hmStable := by
  let boundary : Fin m := ⟨n - 1, by omega⟩
  have hRn : a.order ⟨n - 1, by omega⟩ = 0 :=
    hI1.1 ⟨n - 1, by omega⟩ (by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnOdd)
  have hGap : a.orderGap boundary = a.order ⟨n, by omega⟩ := by
    unfold orderGap
    rw [show boundary.succ = (⟨n, by omega⟩ : Fin (m + 1)) by
      ext
      simp only [boundary, Fin.val_succ]
      omega]
    rw [show boundary.castSucc =
        (⟨n - 1, by omega⟩ : Fin (m + 1)) by ext; rfl]
    rw [hRn, sub_zero]
  have hAlphaOneIff : a.alphaValue boundary = 1 ↔
      a.order ⟨n, by omega⟩ ≠
        -(2 * (ramificationIndex K : Int)) := by
    constructor
    · intro hOne hBottom
      have hZero := ((a.heHu2022Proposition26 boundary).alphaZero).mpr (by
        rw [hGap, hBottom])
      rw [hOne] at hZero
      norm_num at hZero
    · intro hNotBottom
      rcases hI1.2.2 with hZero | hOne
      · have hBottom := ((a.heHu2022Proposition26 boundary).alphaZero).mp hZero
        rw [hGap] at hBottom
        exact False.elim (hNotBottom hBottom)
      · simpa only [boundary] using hOne
  constructor
  · intro hClause
    unfold HeHuI2OSecondPart
    intro hAlpha hTrigger
    have hAlpha' : a.alphaValue boundary = 1 := by
      simpa only [boundary] using hAlpha
    have hNotBottom := hAlphaOneIff.mp hAlpha'
    have hOuter : a.order ⟨n, by omega⟩ = 1 ∨
        (a.order ⟨n, by omega⟩ ≠
            -(2 * (ramificationIndex K : Int)) ∧
          1 < a.order ⟨n + 1, by omega⟩) := by
      rcases hTrigger with hOne | hUpper
      · exact Or.inl hOne
      · exact Or.inr ⟨hNotBottom, hUpper⟩
    have hRows := hClause hOuter
    exact (a.heHuLemma63_alphaNext_le_iff_rows hnThree hnOdd hmStable
      hIntegral hI1 hAlpha hTrigger).mpr hRows
  · intro hSecond
    unfold HeHuTheorem11OddClause2
    intro hOuter
    have hNotBottom : a.order ⟨n, by omega⟩ ≠
        -(2 * (ramificationIndex K : Int)) := by
      rcases hOuter with hOne | hUpper
      · intro hBottom
        have hePos := ramificationIndex_pos (K := K)
        rw [hOne] at hBottom
        omega
      · exact hUpper.1
    have hAlpha' : a.alphaValue boundary = 1 := hAlphaOneIff.mpr hNotBottom
    have hAlpha : a.alphaValue ⟨n - 1, by omega⟩ = 1 := by
      simpa only [boundary] using hAlpha'
    have hTrigger : a.order ⟨n, by omega⟩ = 1 ∨
        1 < a.order ⟨n + 1, by omega⟩ := by
      rcases hOuter with hOne | hUpper
      · exact Or.inl hOne
      · exact Or.inr hUpper.2
    have hAlphaLe := hSecond hAlpha hTrigger
    exact (a.heHuLemma63_alphaNext_le_iff_rows hnThree hnOdd hmStable
      hIntegral hI1 hAlpha hTrigger).mp hAlphaLe

end BONG.GoodBONG

end Bong
