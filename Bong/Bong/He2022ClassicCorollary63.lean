/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicTheorem15
import Bong.Bong.MonotoneDiagonalization

/-!
# He (2024), Corollary 6.3

The publisher proof treats the even-rank branch explicitly.  This file first
records that branch with the exact rank `n + 3`: Theorem 1.1 makes all but the
last two orders zero, Proposition 2.4 makes every order nonnegative, and
Proposition 2.2(iv) excludes the only possible drop from one to zero.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

private theorem heClassicOrder_eq_zero_through_evenBoundary
    {n : Nat} (a : GoodBONG q L (n + 3))
    (hInitial : ∀ i : Fin n, a.order ⟨i.1, by omega⟩ = 0)
    (hBoundary : a.order ⟨n, by omega⟩ = 0) :
    ∀ i : Fin (n + 3), i.1 ≤ n → a.order i = 0 := by
  intro i hi
  by_cases hin : i.1 < n
  · have h := hInitial ⟨i.1, hin⟩
    simpa only [show (⟨i.1, by omega⟩ : Fin (n + 3)) = i by ext; rfl]
      using h
  · have hieq : i.1 = n := by omega
    simpa only [show i = (⟨n, by omega⟩ : Fin (n + 3)) by
      ext; exact hieq] using hBoundary

/-- The even-parity case of He, Corollary 6.3, with the displayed BONG
itself shown to be an integral orthogonal basis. -/
theorem he2022ClassicCorollary63_even
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {n : Nat} (a : GoodBONG q L (n + 3))
    (hn : 2 ≤ n) (hnEven : Even n)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hUniversal : Lattice.IsClassicNUniversal.{u, v, u} q L n) :
    L = Lattice.basisLattice a.toBONG.basis := by
  have hConditions :=
    (a.he2022ClassicTheorem11 hn hClassic).mp hUniversal
  obtain hEven | hOdd := hConditions.parity_branch
  · have hZeroThrough : ∀ i : Fin (n + 3), i.1 ≤ n →
        a.order i = 0 :=
      a.heClassicOrder_eq_zero_through_evenBoundary
        hConditions.initial_orders hEven.order_n1
    have hFirst : a.order (0 : Fin (n + 3)) = 0 :=
      hZeroThrough (0 : Fin (n + 3)) (Nat.zero_le n)
    have hNonnegative : ∀ i : Fin (n + 3), 0 ≤ a.order i :=
      (a.he2022ClassicProposition24 hClassic).nonnegativeOfFirstZero hFirst
    have hAdjacent : ∀ k : Fin (n + 2),
        a.order k.castSucc ≤ a.order k.succ := by
      intro k
      by_cases hkInitial : k.1 < n
      · rw [hZeroThrough k.castSucc (by
            simpa only [Fin.val_castSucc] using Nat.le_of_lt hkInitial),
          hZeroThrough k.succ (by
            simp only [Fin.val_succ]
            omega)]
      · by_cases hkBoundary : k.1 = n
        · have hkCast : k.castSucc = (⟨n, by omega⟩ : Fin (n + 3)) := by
            ext
            exact hkBoundary
          rw [hkCast, hEven.order_n1]
          exact hNonnegative k.succ
        · have hkLast : k.1 = n + 1 := by omega
          have hkCast : k.castSucc =
              (⟨n + 1, by omega⟩ : Fin (n + 3)) := by
            ext
            exact hkLast
          have hkSucc : k.succ =
              (⟨n + 2, by omega⟩ : Fin (n + 3)) := by
            ext
            simp only [Fin.val_succ]
            omega
          rcases hEven.order_n2 with hzero | hone
          · rw [hkCast, hzero]
            exact hNonnegative k.succ
          · rw [hkCast, hkSucc, hone]
            by_contra hnot
            have hLastZero : a.order ⟨n + 2, by omega⟩ = 0 := by
              have hLastNonnegative := hNonnegative ⟨n + 2, by omega⟩
              omega
            let gap : Fin (n + 2) := ⟨n + 1, by omega⟩
            have hGap : a.orderGap gap = -1 := by
              unfold orderGap
              rw [show gap.castSucc =
                    (⟨n + 1, by omega⟩ : Fin (n + 3)) by ext; rfl,
                show gap.succ =
                    (⟨n + 2, by omega⟩ : Fin (n + 3)) by ext; rfl,
                hone, hLastZero]
              norm_num
            have hPositive :=
              (a.he2022ClassicProposition22.oddGapFormula gap (by
                rw [hGap]
                exact odd_neg.mpr odd_one)).2
            rw [hGap] at hPositive
            omega
    apply a.toBONG.lattice_eq_basisLattice_of_order_monotone
    have hMonotone : Monotone (fun i : Fin (n + 3) ↦ a.order i) := by
      rw [Fin.monotone_iff_le_succ]
      exact hAdjacent
    intro i j hij
    let i' : Fin (n + 3) := ⟨i.1, by omega⟩
    let j' : Fin (n + 3) := ⟨j.1, by omega⟩
    have hij' : i' ≤ j' := Fin.mk_le_mk.mpr (Fin.mk_le_mk.mp hij)
    have h := hMonotone hij'
    simpa only [i', j', GoodBONG.order] using h
  · exact False.elim ((Nat.not_even_iff_odd.mpr hOdd.parity) hnEven)

end BONG.GoodBONG

end Bong
