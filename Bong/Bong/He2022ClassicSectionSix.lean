/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicTheorem51
import Bong.Bong.He2022ClassicConditions
import Bong.Bong.Beli2019DominationWitness
import Bong.Bong.HeHu2022SectionSix

/-!
# He (2024), Section 6

This file eliminates the alpha invariants from the even- and odd-rank
criteria and proves Theorem 1.1 of Zilong He, *On classic n-universal
quadratic forms over dyadic local fields*, manuscripta math. 174 (2024),
559--595.  The publisher version of record is the semantic authority.

Paper indices are one based; bounded Lean indices are zero based.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-! ## The even-rank condition in Theorem 1.1(ii)(1) -/

/-- The complete condition (ii)(1), separated from the parity and final-gap
conditions.  For a BONG of length `m+1`, its adjacent indices form `Fin m`.
-/
def HeClassicTheorem11EvenClauseOne {m : Nat}
    (a : GoodBONG q L (m + 1)) (n : Nat) (hmStable : n + 2 ≤ m) : Prop :=
  HeClassicZeroOrOne (a.order ⟨n + 1, by omega⟩) ∧
    (a.order ⟨n + 1, by omega⟩ = 0 →
      ((a.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2) =
          (1 : ℚ) ∨
        HeClassicZeroOrOne (a.order ⟨n + 2, by omega⟩)) ∧
      ((1 : Nat) < ramificationIndex K ∧
          a.order ⟨n + 1, by omega⟩ = 0 ∧
          a.order ⟨n + 2, by omega⟩ = 0 ∧
          (1 : ℚ) <
            a.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2) →
        ∃ j : Fin m,
          a.heClassicAdjacentDefectAt j =
            ((1 - a.heClassicOrderAfterAdjacent j : Int) : ℚ))))

/-- The square-bracket prefix defect occurring in `J2_E` is the minimum of
the raw signed-prefix defect and the next alpha invariant. -/
theorem heClassic_evenCappedPrefix_eq_min {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hmStable : n + 2 ≤ m) :
    a.truncatedPrefixDefect a ((-1) ^ ((n + 2) / 2)) 0 (n + 2) =
      min (a.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2))
        (a.alphaValue ⟨n + 1, by omega⟩ : WithTop ℚ) := by
  unfold truncatedPrefixDefect heClassicSignedPrefixDefect
  rw [a.prefixAlphaCap_zero,
    a.prefixAlphaCap_of_internal (i := n + 2) (by omega) (by omega)]
  simp only [GoodBONG.prefixProduct, BONG.prefixProduct_zero, mul_one,
    min_top_left]
  congr 2

/-- Under `J1_E(n)`, the prefix sum through the first `n+1` entries is zero.
-/
theorem heClassic_prefixSum_eq_zero_of_j1E {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hm : n + 1 ≤ m)
    (hJ1 : a.HeClassicJ1E n hm)
    (r : Nat) (hr : r ≤ n + 1) :
    a.orderSequence.prefixSum r = 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [a.orderSequence.prefixSum_succ, ih (by omega)]
      rw [a.orderSequence_entryOrZero_eq_order ⟨r, by omega⟩]
      have h := hJ1 ⟨r, by omega⟩
      simpa using h

/-- If the first `n+1` orders vanish and `R_(n+2)=1`, the relevant signed
prefix has odd order. -/
theorem heClassic_evenPrefixOrder_odd_of_boundary_one {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hmStable : n + 2 ≤ m)
    (hJ1 : a.HeClassicJ1E n (by omega))
    (hBoundary : a.order ⟨n + 1, by omega⟩ = 1) :
    Odd (ordUnit K
      (((-1 : Kˣ) ^ ((n + 2) / 2)) * a.prefixProduct 0 *
        a.prefixProduct (n + 2))) := by
  rw [GoodBONG.prefixProduct, BONG.prefixProduct_zero, mul_one,
    ordUnit_mul, ordUnit_pow,
    a.ordUnit_prefixProduct_eq_orderSequence_prefixSum (n + 2) (by omega),
    a.orderSequence.prefixSum_succ,
    a.orderSequence_entryOrZero_eq_order ⟨n + 1, by omega⟩,
    a.heClassic_prefixSum_eq_zero_of_j1E (by omega) hJ1 (n + 1) (by omega),
    hBoundary, zero_add]
  have hNeg : ordUnit K (-1 : Kˣ) = 0 := by
    rw [ordUnit_neg]
    simp [ordUnit]
  rw [hNeg, mul_zero, zero_add]
  exact odd_one

/-- With a zero source prefix, the alpha invariant at its terminal gap cannot
vanish. -/
theorem heClassic_one_le_alpha_of_zero_boundaryGap {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hmStable : n + 1 ≤ m)
    (hJ1 : a.HeClassicJ1E n hmStable)
    (hNext : a.order ⟨n + 1, by omega⟩ = 0) :
    1 ≤ a.alphaValue ⟨n, by omega⟩ := by
  let boundary : Fin m := ⟨n, by omega⟩
  have hGap : a.orderGap boundary = 0 := by
    unfold orderGap
    rw [show boundary.castSucc =
        (⟨n, by omega⟩ : Fin (m + 1)) by ext; rfl,
      show boundary.succ =
        (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl,
      hJ1 ⟨n, by omega⟩, hNext]
    omega
  have hNe : a.alphaValue boundary ≠ 0 := by
    intro hZero
    have hEndpoint := (a.he2022ClassicProposition23 boundary).alphaZero.mp hZero
    rw [hGap] at hEndpoint
    have hePos := ramificationIndex_pos (K := K)
    omega
  simpa only [boundary] using a.heHuOne_le_alphaValue_of_ne_zero boundary hNe

/-- A raw defect-one alternating prefix supplies a defect-one alpha candidate
at the boundary.  This is the domination-principle step in Lemma 6.1. -/
theorem heClassic_boundaryAlpha_eq_one_of_rawPrefix_eq_one {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hmStable : n + 2 ≤ m)
    (hnEven : Even n) (hJ1 : a.HeClassicJ1E n (by omega))
    (hBoundary : a.order ⟨n + 1, by omega⟩ = 0)
    (hRaw : a.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2) = 1) :
    a.alphaValue ⟨n, by omega⟩ = 1 := by
  let boundary : Fin m := ⟨n, by omega⟩
  have hLower : 1 ≤ a.alphaValue boundary := by
    simpa only [boundary] using
      a.heClassic_one_le_alpha_of_zero_boundaryGap (by omega) hJ1 hBoundary
  have hnTwoEven : Even (n + 2) := by
    rcases hnEven with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩
  have hRaw' : a.alternatingPrefixDefect (n + 2) = 1 := by
    simpa only [alternatingPrefixDefect, heClassicSignedPrefixDefect] using hRaw
  rcases a.exists_even_adjacentDefect_le_alternatingPrefixDefect_fixedRank
      (n + 2) (by omega) (by omega) hnTwoEven with
    ⟨j, _hjEven, hjPrefix, hjDefect⟩
  have hZeroThrough (i : Fin (m + 1)) (hi : i.val ≤ n + 1) :
      a.order i = 0 := by
    by_cases hin : i.val ≤ n
    · have h := hJ1 ⟨i.val, by omega⟩
      simpa only [show (⟨i.val, by omega⟩ : Fin (m + 1)) = i by ext; rfl]
        using h
    · have hiEq : i.val = n + 1 := by omega
      simpa only [show i = (⟨n + 1, by omega⟩ : Fin (m + 1)) by
        ext; exact hiEq] using hBoundary
  have hjCurrent : a.order j.castSucc = 0 :=
    hZeroThrough j.castSucc (by
      have h : j.val + 1 ≤ n + 1 := by omega
      simpa only [Fin.val_castSucc] using Nat.le_trans (Nat.le_succ _) h)
  have hjNext : a.order j.succ = 0 :=
    hZeroThrough j.succ (by simpa only [Fin.val_succ] using
      (show j.val + 1 ≤ n + 1 by omega))
  have hProductEven : Even (ordUnit K (a.adjacentProduct j)) := by
    rw [a.ordUnit_adjacentProduct_eq_adjacentOrderSum j,
      hjCurrent, hjNext]
    exact Even.zero
  have hjLower : (1 : WithTop ℚ) ≤ a.adjacentDefect j := by
    exact defectOrder_one_le_of_even (a.adjacentProduct j) hProductEven
  have hjUpper : a.adjacentDefect j ≤ 1 := by
    simpa only [hRaw'] using hjDefect
  have hjOne : a.adjacentDefect j = 1 := le_antisymm hjUpper hjLower
  have hCandidate : a.leftDefectCandidate boundary j = 1 := by
    unfold leftDefectCandidate
    rw [show boundary.succ =
        (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl,
      hBoundary, hjCurrent, hjOne]
    norm_num
  have hUpperTop : (a.alphaValue boundary : WithTop ℚ) ≤ 1 := by
    rw [a.coe_alphaValue, ← hCandidate]
    apply a.alpha_le_leftDefectCandidate
    exact Fin.mk_le_mk.mpr (by omega)
  have hUpper : a.alphaValue boundary ≤ 1 := by exact_mod_cast hUpperTop
  simpa only [boundary] using le_antisymm hUpper hLower

/-- In the exceptional zero-zero case of Lemma 6.1, alpha one is equivalent
to the explicit adjacent-defect witness printed in Theorem 1.1(ii)(1)(b). -/
theorem heClassic_boundaryAlpha_eq_one_iff_adjacentWitness {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hmStable : n + 2 ≤ m)
    (hJ1 : a.HeClassicJ1E n (by omega))
    (hBoundary : a.order ⟨n + 1, by omega⟩ = 0)
    (heLarge : 1 < ramificationIndex K) :
    a.alphaValue ⟨n, by omega⟩ = 1 ↔
      ∃ j : Fin m, a.heClassicAdjacentDefectAt j =
        ((1 - a.heClassicOrderAfterAdjacent j : Int) : ℚ) := by
  let boundary : Fin m := ⟨n, by omega⟩
  have hCurrent : a.order boundary.castSucc = 0 := by
    rw [show boundary.castSucc =
        (⟨n, by omega⟩ : Fin (m + 1)) by ext; rfl]
    exact hJ1 ⟨n, by omega⟩
  have hLower : 1 ≤ a.alphaValue boundary := by
    simpa only [boundary] using
      a.heClassic_one_le_alpha_of_zero_boundaryGap (by omega) hJ1 hBoundary
  have hHalfGt : (1 : WithTop ℚ) < a.halfGapCandidate boundary := by
    rw [← a.coe_halfGapValue]
    exact_mod_cast (show (1 : ℚ) < a.halfGapValue boundary by
      unfold halfGapValue orderGap
      rw [hCurrent,
        show boundary.succ =
          (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl,
        hBoundary]
      push_cast
      norm_num
      exact heLarge)
  have hLeftToWitness (j : Fin m) (hj : j ≤ boundary)
      (hCandidate : a.leftDefectCandidate boundary j = 1) :
      a.heClassicAdjacentDefectAt j =
        ((1 - a.heClassicOrderAfterAdjacent j : Int) : ℚ) := by
    have hjCurrent : a.order j.castSucc = 0 := by
      have hjVal : j.val ≤ n := by
        simpa only [boundary] using (Fin.mk_le_mk.mp hj)
      have h := hJ1 ⟨j.val, by omega⟩
      simpa only [show (⟨j.val, by omega⟩ : Fin (m + 1)) =
          j.castSucc by ext; rfl] using h
    have hjNext : a.order j.succ = 0 := by
      by_cases hjLt : j.val < n
      · have h := hJ1 ⟨j.val + 1, by omega⟩
        simpa only [show (⟨j.val + 1, by omega⟩ : Fin (m + 1)) =
            j.succ by ext; rfl] using h
      · have hjEq : j.val = n := by
          have hjVal : j.val ≤ n := by
            simpa only [boundary] using (Fin.mk_le_mk.mp hj)
          omega
        simpa only [show j.succ =
            (⟨n + 1, by omega⟩ : Fin (m + 1)) by
              ext; simpa only [Fin.val_succ] using congrArg (· + 1) hjEq]
          using hBoundary
    change a.adjacentDefect j =
      (((1 - a.order j.succ : Int) : ℚ) : WithTop ℚ)
    unfold leftDefectCandidate at hCandidate
    rw [show boundary.succ =
        (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl,
      hBoundary, hjCurrent] at hCandidate
    rw [hjNext]
    simpa using hCandidate
  have hRightToWitness (j : Fin m) (hj : boundary ≤ j)
      (hCandidate : a.rightDefectCandidate boundary j = 1) :
      a.heClassicAdjacentDefectAt j =
        ((1 - a.heClassicOrderAfterAdjacent j : Int) : ℚ) := by
    change a.adjacentDefect j =
      (((1 - a.order j.succ : Int) : ℚ) : WithTop ℚ)
    unfold rightDefectCandidate at hCandidate
    rw [hCurrent] at hCandidate
    apply WithTop.add_left_cancel (x :=
      (((a.order j.succ : Int) : ℚ) : WithTop ℚ)) WithTop.coe_ne_top
    calc
      (((a.order j.succ : Int) : ℚ) : WithTop ℚ) + a.adjacentDefect j = 1 := by
        simpa only [zero_sub, Int.cast_zero, WithTop.coe_zero, sub_zero,
          zero_add] using hCandidate
      _ = (((a.order j.succ : Int) : ℚ) : WithTop ℚ) +
          (((1 - a.order j.succ : Int) : ℚ) : WithTop ℚ) := by
        norm_cast
        ring
  have hWitnessToCandidate (j : Fin m)
      (hDefect : a.heClassicAdjacentDefectAt j =
        ((1 - a.heClassicOrderAfterAdjacent j : Int) : ℚ)) :
      (j ≤ boundary ∧ a.leftDefectCandidate boundary j = 1) ∨
        (boundary ≤ j ∧ a.rightDefectCandidate boundary j = 1) := by
    rcases le_total j boundary with hj | hj
    · left
      refine ⟨hj, ?_⟩
      have hjCurrent : a.order j.castSucc = 0 := by
        have hjVal : j.val ≤ n := by
          simpa only [boundary] using (Fin.mk_le_mk.mp hj)
        have h := hJ1 ⟨j.val, by omega⟩
        simpa only [show (⟨j.val, by omega⟩ : Fin (m + 1)) =
            j.castSucc by ext; rfl] using h
      have hjNext : a.order j.succ = 0 := by
        by_cases hjLt : j.val < n
        · have h := hJ1 ⟨j.val + 1, by omega⟩
          simpa only [show (⟨j.val + 1, by omega⟩ : Fin (m + 1)) =
              j.succ by ext; rfl] using h
        · have hjEq : j.val = n := by
            have hjVal : j.val ≤ n := by
              simpa only [boundary] using (Fin.mk_le_mk.mp hj)
            omega
          simpa only [show j.succ =
              (⟨n + 1, by omega⟩ : Fin (m + 1)) by
                ext; simpa only [Fin.val_succ] using congrArg (· + 1) hjEq]
            using hBoundary
      change a.adjacentDefect j =
        (((1 - a.order j.succ : Int) : ℚ) : WithTop ℚ) at hDefect
      unfold leftDefectCandidate
      rw [show boundary.succ =
          (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl,
        hBoundary, hjCurrent]
      rw [hjNext] at hDefect
      norm_num
      simpa using hDefect
    · right
      refine ⟨hj, ?_⟩
      change a.adjacentDefect j =
        (((1 - a.order j.succ : Int) : ℚ) : WithTop ℚ) at hDefect
      unfold rightDefectCandidate
      rw [hCurrent, hDefect]
      norm_cast
      ring
  constructor
  · intro hAlpha
    have hMinMem := Finset.min'_mem
      (a.alphaCandidates boundary) (a.alphaCandidates_nonempty boundary)
    have hCandidateMem : (1 : WithTop ℚ) ∈ a.alphaCandidates boundary := by
      change a.alpha boundary ∈ a.alphaCandidates boundary at hMinMem
      rw [← a.coe_alphaValue boundary, show a.alphaValue boundary = 1 by
        simpa only [boundary] using hAlpha] at hMinMem
      exact hMinMem
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hCandidateMem
    rcases hCandidateMem with hHalf | hDefect
    · exact False.elim ((ne_of_gt hHalfGt) hHalf.symm)
    · rcases hDefect with hLeft | hRight
      · rcases hLeft with ⟨j, hj, hEq⟩
        exact ⟨j, hLeftToWitness j hj hEq⟩
      · rcases hRight with ⟨j, hj, hEq⟩
        exact ⟨j, hRightToWitness j hj hEq⟩
  · rintro ⟨j, hjDefect⟩
    rcases hWitnessToCandidate j hjDefect with hLeft | hRight
    · have hUpperTop : (a.alphaValue boundary : WithTop ℚ) ≤ 1 := by
        rw [a.coe_alphaValue, ← hLeft.2]
        exact a.alpha_le_leftDefectCandidate hLeft.1
      have hUpper : a.alphaValue boundary ≤ 1 := by exact_mod_cast hUpperTop
      simpa only [boundary] using le_antisymm hUpper hLower
    · have hUpperTop : (a.alphaValue boundary : WithTop ℚ) ≤ 1 := by
        rw [a.coe_alphaValue, ← hRight.2]
        exact a.alpha_le_rightDefectCandidate hRight.1
      have hUpper : a.alphaValue boundary ≤ 1 := by exact_mod_cast hUpperTop
      simpa only [boundary] using le_antisymm hUpper hLower

/-- The alpha immediately after the even boundary is at least one whenever
the next order is nonnegative. -/
theorem heClassic_one_le_nextAlpha_of_nonnegative_nextOrder {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hmStable : n + 2 ≤ m)
    (hBoundary : a.order ⟨n + 1, by omega⟩ = 0)
    (hNextNonnegative : 0 ≤ a.order ⟨n + 2, by omega⟩) :
    1 ≤ a.alphaValue ⟨n + 1, by omega⟩ := by
  let next : Fin m := ⟨n + 1, by omega⟩
  have hGap : 0 ≤ a.orderGap next := by
    unfold orderGap
    rw [show next.castSucc =
        (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl,
      show next.succ =
        (⟨n + 2, by omega⟩ : Fin (m + 1)) by ext; rfl,
      hBoundary]
    omega
  have hNe : a.alphaValue next ≠ 0 := by
    intro hZero
    have hBottom := (a.he2022ClassicProposition23 next).alphaZero.mp hZero
    have hePos := ramificationIndex_pos (K := K)
    omega
  simpa only [next] using a.heHuOne_le_alphaValue_of_ne_zero next hNe

/-- Once the current boundary alpha is one, a following order zero or one
forces the next alpha to be one. -/
theorem heClassic_nextAlpha_eq_one_of_zeroOrOne {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hmStable : n + 2 ≤ m)
    (hJ1 : a.HeClassicJ1E n (by omega))
    (hBoundary : a.order ⟨n + 1, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨n, by omega⟩ = 1)
    (hNext : HeClassicZeroOrOne (a.order ⟨n + 2, by omega⟩)) :
    a.alphaValue ⟨n + 1, by omega⟩ = 1 := by
  let current : Fin m := ⟨n, by omega⟩
  let next : Fin m := ⟨n + 1, by omega⟩
  rcases hNext with hNextZero | hNextOne
  · have hSum : a.adjacentOrderSum current = a.adjacentOrderSum next := by
      unfold adjacentOrderSum
      rw [show current.castSucc =
          (⟨n, by omega⟩ : Fin (m + 1)) by ext; rfl,
        show current.succ =
          (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl,
        show next.castSucc =
          (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl,
        show next.succ =
          (⟨n + 2, by omega⟩ : Fin (m + 1)) by ext; rfl,
        hJ1 ⟨n, by omega⟩, hBoundary, hNextZero]
    have hCurrentNext : current ≤ next := Fin.mk_le_mk.mpr (by omega)
    have hLeft : a.alphaLeftEndpoint current ≤
        a.alphaLeftEndpoint next :=
      a.alphaLeftEndpoint_monotone_fixedRank hCurrentNext
    have hRight : a.alphaRightEndpoint next ≤
        a.alphaRightEndpoint current :=
      a.alphaRightEndpoint_antitone_fixedRank hCurrentNext
    have hSumQ := congrArg (fun z : Int => (z : ℚ)) hSum
    have hConst : a.alphaLeftEndpoint next =
        a.alphaLeftEndpoint current := by
      apply le_antisymm
      · unfold alphaLeftEndpoint at hLeft
        unfold alphaRightEndpoint at hRight
        unfold adjacentOrderSum at hSumQ
        unfold alphaLeftEndpoint
        push_cast at hLeft hRight hSumQ
        push_cast
        linarith
      · exact hLeft
    unfold alphaLeftEndpoint at hConst
    rw [show current.castSucc =
        (⟨n, by omega⟩ : Fin (m + 1)) by ext; rfl,
      show next.castSucc =
        (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl,
      hJ1 ⟨n, by omega⟩, hBoundary,
      show a.alphaValue current = 1 by simpa only [current] using hAlpha]
      at hConst
    norm_num at hConst
    simpa only [next] using hConst
  · apply a.alphaValue_eq_one_of_orderGap_eq_endpoint next
    right
    unfold orderGap
    rw [show next.castSucc =
        (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl,
      show next.succ =
        (⟨n + 2, by omega⟩ : Fin (m + 1)) by ext; rfl,
      hBoundary, hNextOne]
    omega

/-- Proposition 2.4(vi) in the fixed ambient-rank indexing used in Section 6.
If all orders through a boundary vanish and one alpha in that prefix is at
most one, then every earlier alpha is one. -/
theorem heClassic_alphaOneOnZeroPrefix_fixedRank {m : Nat}
    (a : GoodBONG q L (m + 1)) (j : Fin m)
    (horders : ∀ i : Fin (m + 1), i ≤ j.castSucc → a.order i = 0)
    (k : Fin m) (hkj : k ≤ j) (halpha : a.alphaValue k ≤ 1)
    (i : Fin m) (hij : i < j) :
    a.alphaValue i = 1 := by
  have hiSuccLe : i.succ ≤ j.castSucc := Fin.mk_le_mk.mpr hij
  have hiOrder := horders i.castSucc
    (Fin.mk_le_mk.mpr (Nat.le_of_lt hij))
  have hiSuccOrder := horders i.succ hiSuccLe
  have hiGap : a.orderGap i = 0 := by
    unfold orderGap
    rw [hiOrder, hiSuccOrder]
    omega
  have hiAlphaNe : a.alphaValue i ≠ 0 := by
    intro hzero
    have hendpoint := (a.he2022ClassicProposition23 i).alphaZero.mp hzero
    rw [hiGap] at hendpoint
    have hePos := ramificationIndex_pos (K := K)
    omega
  have hiLower := a.heHuOne_le_alphaValue_of_ne_zero i hiAlphaNe
  have hiUpper : a.alphaValue i ≤ a.alphaValue k := by
    by_cases hik : i ≤ k
    · have hmono := a.alphaLeftEndpoint_monotone_fixedRank hik
      have hkOrder := horders k.castSucc (Fin.mk_le_mk.mpr hkj)
      unfold alphaLeftEndpoint at hmono
      rw [hiOrder, hkOrder] at hmono
      norm_num at hmono
      exact hmono
    · have hki : k ≤ i := le_of_not_ge hik
      have hkLtJ : k < j := hki.trans_lt hij
      have hkSuccOrder := horders k.succ (Fin.mk_le_mk.mpr hkLtJ)
      have hmono := a.alphaRightEndpoint_antitone_fixedRank hki
      unfold alphaRightEndpoint at hmono
      rw [hkSuccOrder, hiSuccOrder] at hmono
      norm_num at hmono
      exact hmono
  exact le_antisymm (hiUpper.trans halpha) hiLower

/-- Under `J1_E(n)` and `R_(n+2)=0`, the raw alternating prefix defect is
at least one. -/
theorem heClassic_one_le_evenRawPrefix_of_j1E {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hmStable : n + 2 ≤ m)
    (hJ1 : a.HeClassicJ1E n (by omega))
    (hBoundary : a.order ⟨n + 1, by omega⟩ = 0) :
    (1 : WithTop ℚ) ≤
      a.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2) := by
  have hProductEven : Even (ordUnit K
      (((-1 : Kˣ) ^ ((n + 2) / 2)) * a.prefixProduct (n + 2))) := by
    rw [ordUnit_mul, ordUnit_pow,
      a.ordUnit_prefixProduct_eq_orderSequence_prefixSum (n + 2) (by omega),
      a.orderSequence.prefixSum_succ,
      a.orderSequence_entryOrZero_eq_order ⟨n + 1, by omega⟩,
      a.heClassic_prefixSum_eq_zero_of_j1E (by omega) hJ1
        (n + 1) (by omega), hBoundary, zero_add]
    have hNeg : ordUnit K (-1 : Kˣ) = 0 := by
      rw [ordUnit_neg]
      simp [ordUnit]
    rw [hNeg, mul_zero, zero_add]
    exact Even.zero
  unfold heClassicSignedPrefixDefect
  exact defectOrder_one_le_of_even _ hProductEven

/-- With a zero boundary order, alpha one at the next gap forces the next
order itself to be zero or one. -/
theorem heClassic_nextOrder_zeroOrOne_of_nextAlpha_one {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hmStable : n + 2 ≤ m)
    (hBoundary : a.order ⟨n + 1, by omega⟩ = 0)
    (hNextNonnegative : 0 ≤ a.order ⟨n + 2, by omega⟩)
    (hNextAlpha : a.alphaValue ⟨n + 1, by omega⟩ = 1) :
    HeClassicZeroOrOne (a.order ⟨n + 2, by omega⟩) := by
  let next : Fin m := ⟨n + 1, by omega⟩
  have hGap : a.orderGap next = a.order ⟨n + 2, by omega⟩ := by
    unfold orderGap
    rw [show next.castSucc =
        (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl,
      show next.succ =
        (⟨n + 2, by omega⟩ : Fin (m + 1)) by ext; rfl,
      hBoundary, sub_zero]
  have hShape := (a.he2022ClassicProposition23 next).alphaOne.mp (by
    simpa only [next] using hNextAlpha)
  unfold HeClassicZeroOrOne
  rcases hShape with hEndpoint | hInterior
  · rcases hEndpoint with hLower | hOne
    · left
      rw [hGap] at hLower
      have hePos := ramificationIndex_pos (K := K)
      omega
    · right
      simpa only [hGap] using hOne
  · left
    rw [hGap] at hInterior
    omega

/-- He (2024), Lemma 6.1.  Under `J1_E(n)`, the complete printed clause
Theorem 1.1(ii)(1) is equivalent to `J2_E(n)`. -/
theorem he2022ClassicLemma61 {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hnTwo : 2 ≤ n) (hnEven : Even n)
    (hmStable : n + 2 ≤ m) (hJ1 : a.HeClassicJ1E n (by omega)) :
    a.HeClassicTheorem11EvenClauseOne n hmStable ↔
      a.HeClassicJ2E n (by omega) := by
  let current : Fin m := ⟨n, by omega⟩
  let next : Fin m := ⟨n + 1, by omega⟩
  have hCurrentOrder : a.order ⟨n, by omega⟩ = 0 :=
    hJ1 ⟨n, by omega⟩
  have hBoundaryNonnegative : 0 ≤ a.order ⟨n + 1, by omega⟩ := by
    have hmono := a.orderSequence.twoStep (n - 1) (by omega)
    have hPrevious : a.order ⟨n - 1, by omega⟩ = 0 :=
      hJ1 ⟨n - 1, by omega⟩
    change a.order ⟨n - 1, by omega⟩ ≤
      a.order ⟨n - 1 + 2, by omega⟩ at hmono
    have hindex : n - 1 + 2 = n + 1 := by omega
    simpa only [hPrevious, hindex] using hmono
  have hNextNonnegative : 0 ≤ a.order ⟨n + 2, by omega⟩ := by
    have hmono := a.orderSequence.twoStep n (by omega)
    change a.order ⟨n, by omega⟩ ≤ a.order ⟨n + 2, by omega⟩ at hmono
    simpa only [hCurrentOrder] using hmono
  have hBinary : n = 2 → 4 ≤ m := by omega
  constructor
  · intro hClause
    unfold HeClassicJ2E
    rcases hClause with ⟨hBoundaryCases, hZeroClause⟩
    rcases hBoundaryCases with hBoundaryZero | hBoundaryOne
    · have hZeroData := hZeroClause hBoundaryZero
      have hRawLower := a.heClassic_one_le_evenRawPrefix_of_j1E
        hmStable hJ1 hBoundaryZero
      have hAlphaCurrent : a.alphaValue current = 1 := by
        by_cases heOne : ramificationIndex K = 1
        · apply (a.he2022ClassicProposition23 current).alphaOne_ramificationOne
              heOne |>.mpr
          left
          unfold orderGap
          rw [show current.castSucc =
              (⟨n, by omega⟩ : Fin (m + 1)) by ext; rfl,
            show current.succ =
              (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl,
            hCurrentOrder, hBoundaryZero]
          omega
        · have heLarge : 1 < ramificationIndex K := by
            have hePos := ramificationIndex_pos (K := K)
            omega
          rcases hZeroData.1 with hRawOne | hNextCases
          · simpa only [current] using
              a.heClassic_boundaryAlpha_eq_one_of_rawPrefix_eq_one
                hmStable hnEven hJ1 hBoundaryZero hRawOne
          · rcases hNextCases with hNextZero | hNextOne
            · by_cases hRawEq :
                  a.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2) = 1
              · simpa only [current] using
                  a.heClassic_boundaryAlpha_eq_one_of_rawPrefix_eq_one
                    hmStable hnEven hJ1 hBoundaryZero hRawEq
              · have hRawGt : (1 : WithTop ℚ) <
                    a.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2) :=
                  lt_of_le_of_ne hRawLower (Ne.symm hRawEq)
                have hWitness := hZeroData.2
                  ⟨heLarge, hBoundaryZero, hNextZero, hRawGt⟩
                exact (a.heClassic_boundaryAlpha_eq_one_iff_adjacentWitness
                  hmStable hJ1 hBoundaryZero heLarge).mpr hWitness
            · have hNextGap : a.orderGap next = 1 := by
                unfold orderGap
                rw [show next.castSucc =
                    (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl,
                  show next.succ =
                    (⟨n + 2, by omega⟩ : Fin (m + 1)) by ext; rfl,
                  hBoundaryZero, hNextOne]
                omega
              have hNextAlpha : a.alphaValue next = 1 :=
                a.alphaValue_eq_one_of_orderGap_eq_endpoint next
                  (Or.inr hNextGap)
              have horders : ∀ i : Fin (m + 1), i ≤ next.castSucc →
                  a.order i = 0 := by
                intro i hi
                have hiVal : i.val ≤ n + 1 := by
                  simpa only [next] using Fin.mk_le_mk.mp hi
                by_cases hin : i.val ≤ n
                · have h := hJ1 ⟨i.val, by omega⟩
                  simpa only [show (⟨i.val, by omega⟩ : Fin (m + 1)) = i by
                    ext; rfl] using h
                · have hiEq : i.val = n + 1 := by omega
                  simpa only [show i =
                      (⟨n + 1, by omega⟩ : Fin (m + 1)) by
                        ext; exact hiEq] using hBoundaryZero
              exact a.heClassic_alphaOneOnZeroPrefix_fixedRank next horders
                next le_rfl (by rw [hNextAlpha]) current (by
                  exact Fin.mk_lt_mk.mpr (by omega))
      have hAlphaNextLower := a.heClassic_one_le_nextAlpha_of_nonnegative_nextOrder
        hmStable hBoundaryZero hNextNonnegative
      have hCapped : a.truncatedPrefixDefect a
          ((-1) ^ ((n + 2) / 2)) 0 (n + 2) = 1 := by
        rw [a.heClassic_evenCappedPrefix_eq_min hmStable]
        rcases hZeroData.1 with hRawOne | hNextCases
        · rw [hRawOne]
          exact min_eq_left (by exact_mod_cast hAlphaNextLower)
        · have hAlphaNext : a.alphaValue next = 1 :=
            a.heClassic_nextAlpha_eq_one_of_zeroOrOne hmStable hJ1
              hBoundaryZero (by simpa only [current] using hAlphaCurrent)
              hNextCases
          rw [show a.alphaValue ⟨n + 1, by omega⟩ = 1 by
            simpa only [next] using hAlphaNext]
          exact min_eq_right hRawLower
      refine ⟨by simpa only [current] using hAlphaCurrent, ?_, hBinary⟩
      rw [hBoundaryZero, hCapped]
      norm_num
    · have hCurrentGap : a.orderGap current = 1 := by
        unfold orderGap
        rw [show current.castSucc =
            (⟨n, by omega⟩ : Fin (m + 1)) by ext; rfl,
          show current.succ =
            (⟨n + 1, by omega⟩ : Fin (m + 1)) by ext; rfl,
          hCurrentOrder, hBoundaryOne]
        omega
      have hAlpha : a.alphaValue current = 1 :=
        a.alphaValue_eq_one_of_orderGap_eq_endpoint current (Or.inr hCurrentGap)
      have hOdd := a.heClassic_evenPrefixOrder_odd_of_boundary_one
        hmStable hJ1 hBoundaryOne
      have hCapped := a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed
        a ((-1) ^ ((n + 2) / 2)) 0 (n + 2) hOdd
      refine ⟨by simpa only [current] using hAlpha, ?_, hBinary⟩
      rw [hBoundaryOne, hCapped]
      norm_num
  · intro hJ2
    unfold HeClassicJ2E at hJ2
    unfold HeClassicTheorem11EvenClauseOne
    have hAlphaCurrent : a.alphaValue current = 1 := by
      simpa only [current] using hJ2.1
    have hCappedEquality := hJ2.2.1
    have hCappedNonnegative : (0 : WithTop ℚ) ≤
        a.truncatedPrefixDefect a ((-1) ^ ((n + 2) / 2)) 0 (n + 2) :=
      a.truncatedPrefixDefect_nonneg _ _ _ _
    have hBoundaryLe : a.order ⟨n + 1, by omega⟩ ≤ 1 := by
      have hCastLe :
          (((a.order ⟨n + 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) ≤ 1 := by
        calc
          (((a.order ⟨n + 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) ≤
              (((a.order ⟨n + 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
                a.truncatedPrefixDefect a ((-1) ^ ((n + 2) / 2)) 0 (n + 2) :=
            le_add_of_nonneg_right hCappedNonnegative
          _ = 1 := hCappedEquality
      exact_mod_cast hCastLe
    have hBoundaryCases : HeClassicZeroOrOne
        (a.order ⟨n + 1, by omega⟩) := by
      unfold HeClassicZeroOrOne
      omega
    refine ⟨hBoundaryCases, ?_⟩
    intro hBoundaryZero
    have hRawLower := a.heClassic_one_le_evenRawPrefix_of_j1E
      hmStable hJ1 hBoundaryZero
    have hNextAlphaLower := a.heClassic_one_le_nextAlpha_of_nonnegative_nextOrder
      hmStable hBoundaryZero hNextNonnegative
    have hCappedOne : a.truncatedPrefixDefect a
        ((-1) ^ ((n + 2) / 2)) 0 (n + 2) = 1 := by
      rw [hBoundaryZero] at hCappedEquality
      simpa using hCappedEquality
    have hMinOne : min
        (a.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2))
        (a.alphaValue ⟨n + 1, by omega⟩ : WithTop ℚ) = 1 := by
      rw [← a.heClassic_evenCappedPrefix_eq_min hmStable]
      exact hCappedOne
    have hExtreme :
        a.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2) = 1 ∨
          a.alphaValue ⟨n + 1, by omega⟩ = 1 := by
      by_cases hRawLe :
          a.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2) ≤
            (a.alphaValue ⟨n + 1, by omega⟩ : WithTop ℚ)
      · left
        simpa only [min_eq_left hRawLe] using hMinOne
      · right
        have hAlphaLe := le_of_not_ge hRawLe
        have hCoe : (a.alphaValue ⟨n + 1, by omega⟩ : WithTop ℚ) = 1 := by
          simpa only [min_eq_right hAlphaLe] using hMinOne
        exact WithTop.coe_eq_coe.mp hCoe
    have hFirst :
        a.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2) = 1 ∨
          HeClassicZeroOrOne (a.order ⟨n + 2, by omega⟩) := by
      rcases hExtreme with hRaw | hAlpha
      · exact Or.inl hRaw
      · exact Or.inr (a.heClassic_nextOrder_zeroOrOne_of_nextAlpha_one
          hmStable hBoundaryZero hNextNonnegative hAlpha)
    refine ⟨hFirst, ?_⟩
    intro hExceptional
    have heLarge := hExceptional.1
    exact (a.heClassic_boundaryAlpha_eq_one_iff_adjacentWitness
      hmStable hJ1 hBoundaryZero heLarge).mp (by
        simpa only [current] using hAlphaCurrent)

end BONG.GoodBONG

end Bong
