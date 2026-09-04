/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicTheorem11
import Bong.Bong.BinaryDiagonalEvenSpinorUpper

/-!
# He (2024), Theorem 1.5 and Corollary 6.3

This file proves the local ramification obstruction in Theorem 1.5.  The
unsigned adjacent defects in the hypothesis are converted to the signed
defects occurring in Theorem 1.1 by the quadratic-defect domination
principle and the lower bound `e ≤ d(-1)`.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The unsigned defect `d(a_j a_(j+1))` in Theorem 1.5, with zero-based
adjacent index. -/
noncomputable def heClassicUnsignedAdjacentDefect {m : Nat}
    (a : GoodBONG q L (m + 1)) (j : Fin m) : WithTop ℚ :=
  defectOrder (K := K) (a.valueUnit j.castSucc * a.valueUnit j.succ)

private theorem even_order_of_one_lt_defectOrder (x : Kˣ)
    (hx : (1 : WithTop ℚ) < defectOrder (K := K) x) :
    Even (ordUnit K x) := by
  rcases Int.even_or_odd (ordUnit K x) with heven | hodd
  · exact heven
  · have hzero : defectOrder (K := K) x = 0 := by
      unfold defectOrder
      rw [quadraticDefect_eq_zero_of_odd_ordUnit x hodd]
      rfl
    rw [hzero] at hx
    exact False.elim ((not_lt_of_ge (by norm_num :
      (0 : WithTop ℚ) ≤ 1)) hx)

/-- Coercion of a finite quadratic-defect lower bound to the rational
defect-order scale used by good BONG invariants. -/
private theorem natCast_le_defectOrder_of_natCast_le_quadraticDefect_local
    (x : Kˣ) (r : Nat) (h : (r : ℕ∞) ≤ quadraticDefect K x) :
    (((r : Nat) : ℚ) : WithTop ℚ) ≤ defectOrder (K := K) x := by
  by_cases htop : quadraticDefect K x = ⊤
  · unfold defectOrder
    rw [htop]
    exact le_top
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
    have hrd : r ≤ d := by
      rw [← hd] at h
      exact WithTop.coe_le_coe.mp h
    unfold defectOrder
    rw [← hd]
    change (((r : Nat) : ℚ) : WithTop ℚ) ≤ ((d : ℚ) : WithTop ℚ)
    exact_mod_cast hrd

private theorem adjacentDefect_gt_one_of_unsigned {m : Nat}
    (a : GoodBONG q L (m + 1))
    (he : 1 < ramificationIndex K)
    (hUnsigned : ∀ j : Fin m,
      (1 : WithTop ℚ) < a.heClassicUnsignedAdjacentDefect j) :
    ∀ j : Fin m, (1 : WithTop ℚ) < a.adjacentDefect j := by
  have hE : ((((ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) ≤
      defectOrder (K := K) (-1 : Kˣ) :=
    natCast_le_defectOrder_of_natCast_le_quadraticDefect_local (-1 : Kˣ)
      (ramificationIndex K)
      (ramificationIndex_le_quadraticDefect_neg_one (K := K))
  have hNegOne : (1 : WithTop ℚ) < defectOrder (K := K) (-1 : Kˣ) := by
    have hOneE : (1 : WithTop ℚ) <
        (((ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      exact_mod_cast he
    exact hOneE.trans_le hE
  intro j
  have hmin : (1 : WithTop ℚ) <
      min (defectOrder (K := K) (-1 : Kˣ))
        (defectOrder (K := K)
          (a.valueUnit j.castSucc * a.valueUnit j.succ)) :=
    lt_min hNegOne (hUnsigned j)
  have hdom := defectOrder_mul_ge_min (K := K) (-1 : Kˣ)
    (a.valueUnit j.castSucc * a.valueUnit j.succ)
  unfold adjacentDefect adjacentProduct
  exact hmin.trans_le (by simpa using hdom)

private theorem nextOrder_even_of_unsigned {m : Nat}
    (a : GoodBONG q L (m + 1)) (j : Fin m)
    (hCurrent : a.order j.castSucc = 0)
    (hUnsigned : (1 : WithTop ℚ) <
      a.heClassicUnsignedAdjacentDefect j) :
    Even (a.order j.succ) := by
  have hEven := even_order_of_one_lt_defectOrder
    (a.valueUnit j.castSucc * a.valueUnit j.succ) hUnsigned
  have hOrderSum : Even (a.order j.castSucc + a.order j.succ) := by
    rw [ordUnit_mul] at hEven
    change Even (a.order j.castSucc + a.order j.succ) at hEven
    exact hEven
  rw [hCurrent, zero_add] at hOrderSum
  exact hOrderSum

private theorem signedPrefixDefect_gt_one {m i : Nat}
    (a : GoodBONG q L (m + 1)) (hiPos : 0 < i)
    (hiBound : i ≤ m + 1) (hiEven : Even i)
    (hAdjacent : ∀ j : Fin m,
      (1 : WithTop ℚ) < a.adjacentDefect j) :
    (1 : WithTop ℚ) < a.heClassicSignedPrefixDefect (i / 2) i := by
  change (1 : WithTop ℚ) < a.alternatingPrefixDefect i
  by_contra hnot
  have hle : a.alternatingPrefixDefect i ≤ (1 : WithTop ℚ) :=
    le_of_not_gt hnot
  obtain ⟨j, _, _, hj⟩ :=
    a.exists_even_adjacentDefect_le_alternatingPrefixDefect_fixedRank
      i hiPos hiBound hiEven
  exact (not_lt_of_ge (hj.trans hle)) (hAdjacent j)

private theorem allOrders_nonnegative {m : Nat}
    (a : GoodBONG q L (m + 1)) (hm : 1 ≤ m)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hFirst : a.order (0 : Fin (m + 1)) = 0) :
    ∀ i : Fin (m + 1), 0 ≤ a.order i := by
  let b : GoodBONG q L ((m - 1) + 2) := a.castLength (by omega)
  have hFirstB : b.order (0 : Fin ((m - 1) + 2)) = 0 := by
    dsimp only [b]
    rw [order_castLength]
    simpa using hFirst
  have hAll :=
    (b.he2022ClassicProposition24 hClassic).nonnegativeOfFirstZero hFirstB
  intro i
  have hi := hAll ⟨i.1, by omega⟩
  simpa only [b, order_castLength] using hi

private theorem contradiction_of_adjacent_witness {m : Nat}
    (a : GoodBONG q L (m + 1))
    (hAdjacent : ∀ j : Fin m,
      (1 : WithTop ℚ) < a.adjacentDefect j)
    (hNonnegative : ∀ i : Fin (m + 1), 0 ≤ a.order i)
    (j : Fin m)
    (hj : a.heClassicAdjacentDefectAt j =
      (((1 - a.heClassicOrderAfterAdjacent j : Int) : ℚ) : WithTop ℚ)) :
    False := by
  have hOrder : 0 ≤ a.heClassicOrderAfterAdjacent j := by
    unfold heClassicOrderAfterAdjacent
    exact hNonnegative ⟨j.1 + 1, by omega⟩
  have hleInt : 1 - a.heClassicOrderAfterAdjacent j ≤ (1 : Int) := by
    omega
  have hle :
      ((((1 - a.heClassicOrderAfterAdjacent j : Int) : ℚ) : WithTop ℚ)) ≤
        (1 : WithTop ℚ) := by
    exact_mod_cast hleInt
  have hgt : (1 : WithTop ℚ) < a.heClassicAdjacentDefectAt j := by
    have hAj := hAdjacent j
    unfold adjacentDefect adjacentProduct at hAj
    unfold heClassicAdjacentDefectAt
    simpa only [
      show (⟨j.1, by omega⟩ : Fin (m + 1)) = j.castSucc by ext; rfl,
      show (⟨j.1 + 1, by omega⟩ : Fin (m + 1)) = j.succ by ext; rfl]
      using hAj
  rw [hj] at hgt
  exact (not_lt_of_ge hle) hgt

/-- He (2024), Theorem 1.5, in its local form at the chosen dyadic prime.
The rank is written as `m+1`, so the adjacent indices are exactly `Fin m`. -/
theorem he2022ClassicTheorem15
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hn : 2 ≤ n) (hRank : n + 3 ≤ m + 1)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hUniversal : Lattice.IsClassicNUniversal.{u, v, u} q L n)
    (hUnsigned : ∀ j : Fin m,
      (1 : WithTop ℚ) < a.heClassicUnsignedAdjacentDefect j) :
    ramificationIndex K = 1 := by
  by_contra heNe
  have he : 1 < ramificationIndex K := by
    have hePos := ramificationIndex_pos (K := K)
    omega
  have hConditions :=
    (a.he2022ClassicTheorem11 hn hClassic).mp hUniversal
  have hAdjacent := a.adjacentDefect_gt_one_of_unsigned he hUnsigned
  have hFirst : a.order (0 : Fin (m + 1)) = 0 := by
    simpa using hConditions.initial_orders ⟨0, by omega⟩
  have hNonnegative := a.allOrders_nonnegative (by omega) hClassic hFirst
  rcases hConditions.parity_branch with hEven | hOdd
  · have hPrefix : (1 : WithTop ℚ) <
        a.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2) := by
      apply a.signedPrefixDefect_gt_one (i := n + 2) (by omega) (by omega)
      · rcases hEven.parity with ⟨k, hk⟩
        exact ⟨k + 1, by omega⟩
      · exact hAdjacent
    have hOrderN2 : a.order ⟨n + 1, by omega⟩ = 0 := by
      have hPairEven := a.nextOrder_even_of_unsigned ⟨n, by omega⟩
        hEven.order_n1 (hUnsigned ⟨n, by omega⟩)
      rcases hEven.order_n2 with hzero | hone
      · exact hzero
      · have hOneEven : Even (1 : Int) := by simpa [hone] using hPairEven
        norm_num at hOneEven
    have hZeroBranch := hEven.zero_branch hOrderN2
    have hOrderN3Option :
        HeClassicZeroOrOne (a.order ⟨n + 2, by omega⟩) :=
      hZeroBranch.1.resolve_left (ne_of_gt hPrefix)
    have hOrderN3 : a.order ⟨n + 2, by omega⟩ = 0 := by
      have hPairEven := a.nextOrder_even_of_unsigned ⟨n + 1, by omega⟩
        hOrderN2 (hUnsigned ⟨n + 1, by omega⟩)
      rcases hOrderN3Option with hzero | hone
      · exact hzero
      · have hOneEven : Even (1 : Int) := by simpa [hone] using hPairEven
        norm_num at hOneEven
    obtain ⟨j, hj⟩ := hZeroBranch.2
      ⟨he, hOrderN2, hOrderN3, hPrefix⟩
    exact a.contradiction_of_adjacent_witness hAdjacent hNonnegative j hj
  · have hPrefix : (1 : WithTop ℚ) <
        a.heClassicSignedPrefixDefect ((n + 1) / 2) (n + 1) := by
      apply a.signedPrefixDefect_gt_one (i := n + 1) (by omega) (by omega)
      · rcases hOdd.parity with ⟨k, hk⟩
        exact ⟨k + 1, by omega⟩
      · exact hAdjacent
    have hOrderN1 : a.order ⟨n, by omega⟩ = 0 := by
      have hPrevious : a.order ⟨n - 1, by omega⟩ = 0 :=
        hConditions.initial_orders ⟨n - 1, by omega⟩
      have hPairEven := a.nextOrder_even_of_unsigned ⟨n - 1, by omega⟩
        hPrevious (hUnsigned ⟨n - 1, by omega⟩)
      have hPairEven' : Even (a.order ⟨n, by omega⟩) := by
        rw [show (⟨n - 1, by omega⟩ : Fin m).succ =
          (⟨n, by omega⟩ : Fin (m + 1)) by
            apply Fin.ext
            simp only [Fin.val_succ]
            omega] at hPairEven
        exact hPairEven
      rcases hOdd.order_n1 with hzero | hone
      · exact hzero
      · have hOneEven : Even (1 : Int) := by simpa [hone] using hPairEven'
        norm_num at hOneEven
    have hZeroBranch := hOdd.zero_branch hOrderN1
    have hOrderN2Option :
        HeClassicZeroOrOne (a.order ⟨n + 1, by omega⟩) :=
      hZeroBranch.1.resolve_left (ne_of_gt hPrefix)
    have hOrderN2 : a.order ⟨n + 1, by omega⟩ = 0 := by
      have hPairEven := a.nextOrder_even_of_unsigned ⟨n, by omega⟩
        hOrderN1 (hUnsigned ⟨n, by omega⟩)
      rcases hOrderN2Option with hzero | hone
      · exact hzero
      · have hOneEven : Even (1 : Int) := by simpa [hone] using hPairEven
        norm_num at hOneEven
    obtain ⟨j, hj⟩ := hZeroBranch.2
      ⟨he, hOrderN1, hOrderN2, hPrefix⟩
    exact a.contradiction_of_adjacent_witness hAdjacent hNonnegative j hj

end BONG.GoodBONG

end Bong
