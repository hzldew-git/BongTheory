/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma719Core
import Bong.Bong.HeHu2022Lemma310

/-!
# He (2025), Lemma 7.19: a binary tail below a hyperbolic tower

The explicit binary row has orders `0, 1-d` and adjacent defect `d`.
Lemma 3.10 preserves those final values after adjoining the standard
half-hyperbolic tower, so the invariant core of Lemma 7.19 applies.
-/

namespace Bong

open Dyadic Module

universe u


namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The tower BONG retains the precise profile and final adjacent defect of
its binary tail. -/
theorem heADC2025Lemma719_towerBaseConditions (k : Nat) (d : Int)
    (b : GoodBONG q L 2) (hIntegral : Lattice.IsIntegral q L)
    (hzero : b.order 0 = 0) (hlast : b.order 1 = 1 - d)
    (hadjacent : b.adjacentDefect 0 =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    let raw := heHu2022Lemma310BONG b hIntegral (k + 1)
    let base := raw.castLength (by omega : 2 + 2 * (k + 1) = 2 * k + 4)
    HeADC719BaseConditions k d base := by
  dsimp only
  let raw := heHu2022Lemma310BONG b hIntegral (k + 1)
  let base := raw.castLength (by omega : 2 + 2 * (k + 1) = 2 * k + 4)
  have hbaseOrder (i : Fin (2 * k + 4)) :
      base.order i = raw.order ⟨i.val, by omega⟩ := by
    unfold base
    rw [order_castLength]
  have htailOrder (j : Fin 2) :
      raw.order ⟨2 * (k + 1) + j.val, by omega⟩ = b.order j := by
    exact heHu2022Lemma310TailOrders b hIntegral (k + 1) j
  have hinitial : base.HeHuI1E (2 * k + 2) (by omega) := by
    constructor
    · intro i hi
      have hiEven : Even i.val := by
        rcases hi with ⟨t, ht⟩
        exact ⟨t, by omega⟩
      by_cases hlt : i.val < 2 * (k + 1)
      · rcases hiEven with ⟨t, ht⟩
        have htLt : t < k + 1 := by omega
        have hindex : i.val = 2 * t := by omega
        rw [hbaseOrder, show (⟨i.val, by omega⟩ : Fin (2 + 2 * (k + 1))) =
          ⟨2 * t, by omega⟩ by apply Fin.ext; exact hindex]
        exact (heHu2022Lemma310HyperbolicOrders b hIntegral
          (k + 1) ⟨t, htLt⟩).1
      · have hiLast : i.val = 2 * (k + 1) := by omega
        rw [hbaseOrder, show (⟨i.val, by omega⟩ : Fin (2 + 2 * (k + 1))) =
          ⟨2 * (k + 1) + (0 : Fin 2).val, by omega⟩ by
            apply Fin.ext
            simpa only [Fin.val_zero, add_zero] using hiLast]
        rw [htailOrder, hzero]
    · intro i hi
      have hiOdd : Odd i.val := by
        rcases hi with ⟨t, ht⟩
        exact ⟨t - 1, by omega⟩
      rcases hiOdd with ⟨t, ht⟩
      have htLt : t < k + 1 := by omega
      have hindex : i.val = 2 * t + 1 := by omega
      rw [hbaseOrder, show (⟨i.val, by omega⟩ : Fin (2 + 2 * (k + 1))) =
        ⟨2 * t + 1, by omega⟩ by apply Fin.ext; exact hindex]
      exact (heHu2022Lemma310HyperbolicOrders b hIntegral
        (k + 1) ⟨t, htLt⟩).2
  have hbaseLast : base.order ⟨2 * k + 3, by omega⟩ = 1 - d := by
    rw [hbaseOrder]
    have hindex :
        (⟨2 * k + 3, by omega⟩ : Fin (2 + 2 * (k + 1))) =
          ⟨2 * (k + 1) + (1 : Fin 2).val, by omega⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hindex, htailOrder, hlast]
  have hvalueZero : base.valueUnit ⟨2 * k + 2, by omega⟩ =
      b.valueUnit 0 := by
    unfold base
    rw [valueUnit_castLength_heHu]
    have hindex :
        (⟨2 * k + 2, by omega⟩ : Fin (2 + 2 * (k + 1))) =
          ⟨2 * (k + 1) + (0 : Fin 2).val, by omega⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hindex]
    exact heHu2022Lemma310TailValues b hIntegral (k + 1) 0
  have hvalueOne : base.valueUnit ⟨2 * k + 3, by omega⟩ =
      b.valueUnit 1 := by
    unfold base
    rw [valueUnit_castLength_heHu]
    have hindex :
        (⟨2 * k + 3, by omega⟩ : Fin (2 + 2 * (k + 1))) =
          ⟨2 * (k + 1) + (1 : Fin 2).val, by omega⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hindex]
    exact heHu2022Lemma310TailValues b hIntegral (k + 1) 1
  have hbaseAdjacent : base.adjacentDefect ⟨2 * k + 2, by omega⟩ =
      (((d : Int) : ℚ) : WithTop ℚ) := by
    let boundary : Fin (2 * k + 3) := ⟨2 * k + 2, by omega⟩
    have hcast : boundary.castSucc =
        (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 4)) := Fin.ext (by rfl)
    have hsucc : boundary.succ =
        (⟨2 * k + 3, by omega⟩ : Fin (2 * k + 4)) := Fin.ext (by rfl)
    unfold adjacentDefect adjacentProduct
    rw [show (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 3)) = boundary by rfl,
      hcast, hsucc, hvalueZero, hvalueOne]
    let zeroBoundary : Fin 1 := 0
    have hbcast : zeroBoundary.castSucc = (0 : Fin 2) := Fin.ext (by rfl)
    have hbsucc : zeroBoundary.succ = (1 : Fin 2) := Fin.ext (by rfl)
    rw [← hbcast, ← hbsucc]
    simpa only [adjacentDefect, adjacentProduct, zeroBoundary] using hadjacent
  exact
    { initial := hinitial
      last := hbaseLast
      adjacent := hbaseAdjacent }

/-- Lemma 7.19 for an explicit binary tail beneath `k+1` standard
half-hyperbolic planes. -/
theorem heADC2025Lemma719_fromBinaryTail (k : Nat) (d : Int) (c : Kˣ)
    (b : GoodBONG q L 2) (hIntegral : Lattice.IsIntegral q L)
    (hzero : b.order 0 = 0) (hlast : b.order 1 = 1 - d)
    (hadjacent : b.adjacentDefect 0 =
      (((d : Int) : ℚ) : WithTop ℚ))
    (hdOdd : Odd d) (hdNonnegative : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    Lattice.IsNADC.{u, u, u}
      ((Lattice.halfHyperbolicExtensionForm q (k + 1)).orthogonalSum
        ((QuadraticSpace.line K).rescaleUnit c))
      (Lattice.product
        (Lattice.halfHyperbolicExtensionLattice L (k + 1))
        (BONG.unaryModelLattice (K := K)))
      (2 * k + 3) := by
  let raw := heHu2022Lemma310BONG b hIntegral (k + 1)
  let base := raw.castLength (by omega : 2 + 2 * (k + 1) = 2 * k + 4)
  have B : HeADC719BaseConditions k d base :=
    heADC2025Lemma719_towerBaseConditions k d b hIntegral
      hzero hlast hadjacent
  exact base.heADC2025Lemma719Core k d c B hdOdd hdNonnegative hdLt hcOrder

end BONG.GoodBONG

end Bong
