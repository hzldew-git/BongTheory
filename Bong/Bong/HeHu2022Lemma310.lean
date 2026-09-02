/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022ExactModels
import Bong.Bong.Beli2019Lemma718HyperbolicBlock
import Bong.Lattice.ScaledHyperbolicChangeScale

/-!
# He--Hu (2024), Lemma 3.10

This file first puts the exact good BONG
`<1,-pi^(-2e)>` on the literal half-hyperbolic plane.  It then prepends any
number of those planes to an integral lattice and proves that the resulting
concatenated BONG has precisely the coefficient sequence stated in Lemma
3.10.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Integral isometry from the exact binary model with values
`1,-pi^(-2e)` to the literal lattice `2^-1 A(0,0)`. -/
noncomputable def heHuHyperbolicHeadIsometry :
    Lattice.Isometry
      (BONG.binaryDiagonalModelSpace
        (BONG.lemma718IndexPHigh (K := K) (-1))
        (BONG.lemma718IndexPLow (K := K) (-1))
        (BONG.lemma718IndexPParameter_admissible (K := K) (-1)))
      ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
        (Lattice.dyadicHalfUnit (K := K)))
      (BONG.binaryDiagonalModelLattice (K := K))
      (Lattice.hyperbolicPlaneLattice (K := K)) := by
  let sourceScale : Kˣ := uniformizerPowerUnit K
    ((-1 : Int) + 1 - ramificationIndex K)
  let first : Lattice.Isometry
      (BONG.binaryDiagonalModelSpace
        (BONG.lemma718IndexPHigh (K := K) (-1))
        (BONG.lemma718IndexPLow (K := K) (-1))
        (BONG.lemma718IndexPParameter_admissible (K := K) (-1)))
      (QuadraticSpace.hyperbolicPlane sourceScale)
      (BONG.binaryDiagonalModelLattice (K := K))
      (Lattice.hyperbolicPlaneLattice (K := K)) :=
    Classical.choice
      (BONG.lemma718IndexPModel_isIsometric_hyperbolic
        (K := K) (-1))
  have hscale : ordUnit K sourceScale =
      ordUnit K (Lattice.dyadicHalfUnit (K := K)) := by
    dsimp only [sourceScale]
    rw [ordUnit_uniformizerPowerUnit]
    have hhalf : ordUnit K (Lattice.dyadicHalfUnit (K := K)) =
        -(ramificationIndex K : Int) := by
      rw [Lattice.dyadicHalfUnit, ordUnit_inv]
      congr 1
      apply WithTop.coe_injective
      rw [coe_ordUnit]
      exact (ramificationIndex_spec K).symm
    rw [hhalf]
    omega
  let changeScale := Lattice.scaledHyperbolicChangeScaleIsometry
    sourceScale (Lattice.dyadicHalfUnit (K := K)) hscale
  let identify := (Lattice.scaledZeroOmearaPlaneLatticeIsometry
    (Lattice.dyadicHalfUnit (K := K))).symm
  exact first.trans changeScale |>.trans identify

/-- The literal half-hyperbolic plane equipped with the exact good BONG of
He--Hu, Lemma 3.9(i). -/
noncomputable def heHuHyperbolicHeadGoodBONG :
    BONG.GoodBONG
      ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
        (Lattice.dyadicHalfUnit (K := K)))
      (Lattice.hyperbolicPlaneLattice (K := K)) 2 :=
  (BONG.lemma718IndexPModelGoodBONG (K := K) (-1)).mapLatticeIsometry
    (heHuHyperbolicHeadIsometry (K := K))

@[simp]
theorem heHuHyperbolicHeadGoodBONG_value_zero :
    (heHuHyperbolicHeadGoodBONG (K := K)).valueUnit 0 = 1 := by
  rw [heHuHyperbolicHeadGoodBONG,
    BONG.GoodBONG.valueUnit_mapLatticeIsometry]
  have hv := BONG.binaryDiagonalExactGoodBONG_valueUnit
    (BONG.lemma718IndexPHigh (K := K) (-1))
    (BONG.lemma718IndexPLow (K := K) (-1))
    (BONG.lemma718IndexPParameter_admissible (K := K) (-1))
    (0 : Fin 2)
  change
    (BONG.lemma718IndexPModelGoodBONG (K := K) (-1)).valueUnit 0 =
      BONG.lemma718IndexPHigh (K := K) (-1) at hv
  rw [hv]
  simp [BONG.lemma718IndexPHigh, uniformizerPowerUnit]

@[simp]
theorem heHuHyperbolicHeadGoodBONG_value_one :
    (heHuHyperbolicHeadGoodBONG (K := K)).valueUnit 1 =
      -(uniformizerPowerUnit K
        (-(2 * (ramificationIndex K : Int)))) := by
  rw [heHuHyperbolicHeadGoodBONG,
    BONG.GoodBONG.valueUnit_mapLatticeIsometry]
  have hv := BONG.binaryDiagonalExactGoodBONG_valueUnit
    (BONG.lemma718IndexPHigh (K := K) (-1))
    (BONG.lemma718IndexPLow (K := K) (-1))
    (BONG.lemma718IndexPParameter_admissible (K := K) (-1))
    (1 : Fin 2)
  change
    (BONG.lemma718IndexPModelGoodBONG (K := K) (-1)).valueUnit 1 =
      BONG.lemma718IndexPLow (K := K) (-1) at hv
  rw [hv]
  unfold BONG.lemma718IndexPLow
  rw [show (-1 : Int) - 2 * (ramificationIndex K : Int) + 1 =
      -(2 * (ramificationIndex K : Int)) by omega]

@[simp]
theorem heHuHyperbolicHeadGoodBONG_order_zero :
    (heHuHyperbolicHeadGoodBONG (K := K)).order 0 = 0 := by
  rw [heHuHyperbolicHeadGoodBONG,
    BONG.GoodBONG.order_mapLatticeIsometry]
  have ho := BONG.binaryDiagonalExactGoodBONG_order
    (BONG.lemma718IndexPHigh (K := K) (-1))
    (BONG.lemma718IndexPLow (K := K) (-1))
    (BONG.lemma718IndexPParameter_admissible (K := K) (-1))
    (0 : Fin 2)
  change
    (BONG.lemma718IndexPModelGoodBONG (K := K) (-1)).order 0 =
      ordUnit K (BONG.lemma718IndexPHigh (K := K) (-1)) at ho
  rw [ho]
  rw [BONG.lemma718IndexPHigh, ordUnit_uniformizerPowerUnit]
  omega

@[simp]
theorem heHuHyperbolicHeadGoodBONG_order_one :
    (heHuHyperbolicHeadGoodBONG (K := K)).order 1 =
      -(2 * (ramificationIndex K : Int)) := by
  rw [heHuHyperbolicHeadGoodBONG,
    BONG.GoodBONG.order_mapLatticeIsometry]
  have ho := BONG.binaryDiagonalExactGoodBONG_order
    (BONG.lemma718IndexPHigh (K := K) (-1))
    (BONG.lemma718IndexPLow (K := K) (-1))
    (BONG.lemma718IndexPParameter_admissible (K := K) (-1))
    (1 : Fin 2)
  change
    (BONG.lemma718IndexPModelGoodBONG (K := K) (-1)).order 1 =
      ordUnit K (BONG.lemma718IndexPLow (K := K) (-1)) at ho
  rw [ho]
  rw [BONG.lemma718IndexPLow, ordUnit_neg,
    ordUnit_uniformizerPowerUnit]
  omega

/-- Integrality is preserved after adjoining the literal half-hyperbolic
tower. -/
theorem heHuHalfHyperbolicExtension_isIntegral
    (hIntegral : Lattice.IsIntegral q L) (k : Nat) :
    Lattice.IsIntegral (Lattice.halfHyperbolicExtensionForm q k)
      (Lattice.halfHyperbolicExtensionLattice L k) := by
  let X : Lattice.QuadraticLatticeModel (K := K) :=
    { Carrier := V
      form := q
      lattice := L }
  have hX : X.IsIntegral := hIntegral
  exact hX.adjoinHalfHyperbolic k

private theorem heHuHyperbolicHead_orderBounds
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} {m : Nat}
    (c : BONG.GoodBONG r M (m + 1))
    (hIntegral : Lattice.IsIntegral r M) :
    ∀ i : Fin 2,
      (heHuHyperbolicHeadGoodBONG (K := K)).order i ≤ c.order 0 := by
  have hzero : 0 ≤ c.order 0 :=
    (c.toBONG.beliUniversalLemma22).1 hIntegral
  intro i
  fin_cases i
  · rw [show (⟨0, by omega⟩ : Fin 2) = 0 by apply Fin.ext; rfl,
      heHuHyperbolicHeadGoodBONG_order_zero]
    exact hzero
  · rw [show (⟨1, by omega⟩ : Fin 2) = 1 by apply Fin.ext; rfl,
      heHuHyperbolicHeadGoodBONG_order_one]
    have hepos : 0 < ramificationIndex K := ramificationIndex_pos K
    omega

private theorem heHuHyperbolicHead_lastSecond
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} {m : Nat}
    (c : BONG.GoodBONG r M (m + 1))
    (hIntegral : Lattice.IsIntegral r M) :
    ∀ (_hhead : 0 < 2) (hm : 1 < m + 1),
      (heHuHyperbolicHeadGoodBONG (K := K)).order
          ⟨2 - 1, by omega⟩ ≤ c.order ⟨1, hm⟩ := by
  intro _hhead hm
  let C := c.heHu2022Proposition27i hIntegral
  have hlower := (C.evenIndexed
    ⟨1, hm⟩ ⟨1, hm⟩ le_rfl (by norm_num) (by norm_num)).1
  have hindex : (⟨2 - 1, by omega⟩ : Fin 2) = 1 := by
    apply Fin.ext
    norm_num
  rw [hindex, heHuHyperbolicHeadGoodBONG_order_one]
  exact hlower

/-- Prepend one exact half-hyperbolic good-BONG block to a nonempty
integral good BONG. -/
noncomputable def heHuPrependHyperbolicBONG
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} {m : Nat}
    (c : BONG.GoodBONG r M (m + 1))
    (hIntegral : Lattice.IsIntegral r M) :
    BONG.GoodBONG
      (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
        (Lattice.dyadicHalfUnit (K := K))).orthogonalSum r)
      (Lattice.product (Lattice.hyperbolicPlaneLattice (K := K)) M)
      ((m + 1) + 2) :=
  (heHuHyperbolicHeadGoodBONG (K := K)).orthogonalProductRight_of_orderBounds
    c (heHuHyperbolicHead_orderBounds c hIntegral)
      (heHuHyperbolicHead_lastSecond c hIntegral)

@[simp]
theorem heHuPrependHyperbolicBONG_value_zero
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} {m : Nat}
    (c : BONG.GoodBONG r M (m + 1))
    (hIntegral : Lattice.IsIntegral r M) :
    (heHuPrependHyperbolicBONG c hIntegral).valueUnit 0 = 1 := by
  rw [heHuPrependHyperbolicBONG]
  have hindex : (0 : Fin ((m + 1) + 2)) =
      BONG.orthogonalProductLeftIndex (m + 1) (0 : Fin 2) := by
    apply Fin.ext
    rfl
  rw [hindex,
    BONG.GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_left]
  exact heHuHyperbolicHeadGoodBONG_value_zero (K := K)

@[simp]
theorem heHuPrependHyperbolicBONG_value_one
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} {m : Nat}
    (c : BONG.GoodBONG r M (m + 1))
    (hIntegral : Lattice.IsIntegral r M) :
    (heHuPrependHyperbolicBONG c hIntegral).valueUnit 1 =
      -(uniformizerPowerUnit K
        (-(2 * (ramificationIndex K : Int)))) := by
  rw [heHuPrependHyperbolicBONG]
  have hindex : (1 : Fin ((m + 1) + 2)) =
      BONG.orthogonalProductLeftIndex (m + 1) (1 : Fin 2) := by
    apply Fin.ext
    rfl
  rw [hindex,
    BONG.GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_left]
  exact heHuHyperbolicHeadGoodBONG_value_one (K := K)

@[simp]
theorem heHuPrependHyperbolicBONG_value_tail
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} {m : Nat}
    (c : BONG.GoodBONG r M (m + 1))
    (hIntegral : Lattice.IsIntegral r M) (j : Fin (m + 1)) :
    (heHuPrependHyperbolicBONG c hIntegral).valueUnit
        ⟨2 + j.val, by omega⟩ = c.valueUnit j := by
  rw [heHuPrependHyperbolicBONG]
  have hindex : (⟨2 + j.val, by omega⟩ : Fin ((m + 1) + 2)) =
      BONG.orthogonalProductRightIndex 2 j := by
    apply Fin.ext
    rfl
  rw [hindex,
    BONG.GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_right]

/-- The good BONG obtained by prepending `k` literal copies of
`2^-1 A(0,0)` to an integral lattice.  Its length is written in the same
left-to-right order as the published coefficient list. -/
noncomputable def heHu2022Lemma310BONG {n : Nat}
    (b : BONG.GoodBONG q L (n + 1))
    (hIntegral : Lattice.IsIntegral q L) :
    (k : Nat) →
      BONG.GoodBONG
        (Lattice.halfHyperbolicExtensionForm q k)
        (Lattice.halfHyperbolicExtensionLattice L k)
        ((n + 1) + 2 * k)
  | 0 => b.castLength (by omega)
  | k + 1 => by
      let tailRaw := heHu2022Lemma310BONG b hIntegral k
      let tail := tailRaw.castLength
        (show (n + 1) + 2 * k = (n + 2 * k) + 1 by omega)
      have htailIntegral : Lattice.IsIntegral
          (Lattice.halfHyperbolicExtensionForm q k)
          (Lattice.halfHyperbolicExtensionLattice L k) := by
        exact heHuHalfHyperbolicExtension_isIntegral hIntegral k
      let joined := heHuPrependHyperbolicBONG tail htailIntegral
      exact joined.castLength (by omega)

/-- Lemma 3.10, value form: every prepended hyperbolic pair has the exact
displayed values.  Lean indices are zero-based. -/
theorem heHu2022Lemma310HyperbolicValues {n : Nat}
    (b : BONG.GoodBONG q L (n + 1))
    (hIntegral : Lattice.IsIntegral q L) (k : Nat) (t : Fin k) :
    (heHu2022Lemma310BONG b hIntegral k).valueUnit
        ⟨2 * t.val, by omega⟩ = 1 ∧
      (heHu2022Lemma310BONG b hIntegral k).valueUnit
        ⟨2 * t.val + 1, by omega⟩ =
          -(uniformizerPowerUnit K
            (-(2 * (ramificationIndex K : Int)))) := by
  induction k with
  | zero => exact Fin.elim0 t
  | succ k ih =>
      let tailRaw := heHu2022Lemma310BONG b hIntegral k
      let tail := tailRaw.castLength
        (show (n + 1) + 2 * k = (n + 2 * k) + 1 by omega)
      have htailIntegral : Lattice.IsIntegral
          (Lattice.halfHyperbolicExtensionForm q k)
          (Lattice.halfHyperbolicExtensionLattice L k) :=
        heHuHalfHyperbolicExtension_isIntegral hIntegral k
      let joined := heHuPrependHyperbolicBONG tail htailIntegral
      change (joined.castLength (by omega)).valueUnit
          ⟨2 * t.val, by omega⟩ = 1 ∧
        (joined.castLength (by omega)).valueUnit
          ⟨2 * t.val + 1, by omega⟩ = _
      cases t using Fin.cases with
      | zero =>
          constructor
          · rw [BONG.GoodBONG.valueUnit_castLength_heHu]
            exact heHuPrependHyperbolicBONG_value_zero tail htailIntegral
          · rw [BONG.GoodBONG.valueUnit_castLength_heHu]
            exact heHuPrependHyperbolicBONG_value_one tail htailIntegral
      | succ t =>
          have old := ih t
          constructor
          · rw [BONG.GoodBONG.valueUnit_castLength_heHu]
            rw [show (⟨2 * t.succ.val, by omega⟩ :
                Fin ((n + 2 * k) + 1 + 2)) =
              ⟨2 + 2 * t.val, by omega⟩ by
                apply Fin.ext
                simp
                omega]
            change (heHuPrependHyperbolicBONG tail htailIntegral).valueUnit
              ⟨2 + 2 * t.val, by omega⟩ = 1
            calc
              _ = tail.valueUnit
                  ⟨2 * t.val, by omega⟩ := by
                simpa only using
                  heHuPrependHyperbolicBONG_value_tail tail htailIntegral
                    (⟨2 * t.val, by omega⟩ : Fin ((n + 2 * k) + 1))
              _ = 1 := by
                dsimp only [tail]
                rw [BONG.GoodBONG.valueUnit_castLength_heHu]
                exact old.1
          · rw [BONG.GoodBONG.valueUnit_castLength_heHu]
            rw [show (⟨2 * t.succ.val + 1, by omega⟩ :
                Fin ((n + 2 * k) + 1 + 2)) =
              ⟨2 + (2 * t.val + 1), by omega⟩ by
                apply Fin.ext
                simp
                omega]
            change (heHuPrependHyperbolicBONG tail htailIntegral).valueUnit
              ⟨2 + (2 * t.val + 1), by omega⟩ = _
            calc
              _ = tail.valueUnit
                  ⟨2 * t.val + 1, by omega⟩ := by
                simpa only using
                  heHuPrependHyperbolicBONG_value_tail tail htailIntegral
                    (⟨2 * t.val + 1, by omega⟩ :
                      Fin ((n + 2 * k) + 1))
              _ = _ := by
                dsimp only [tail]
                rw [BONG.GoodBONG.valueUnit_castLength_heHu]
                exact old.2

/-- Lemma 3.10, tail form: after the `k` hyperbolic pairs, the original
good-BONG values occur unchanged. -/
theorem heHu2022Lemma310TailValues {n : Nat}
    (b : BONG.GoodBONG q L (n + 1))
    (hIntegral : Lattice.IsIntegral q L) (k : Nat) (j : Fin (n + 1)) :
    (heHu2022Lemma310BONG b hIntegral k).valueUnit
        ⟨2 * k + j.val, by omega⟩ = b.valueUnit j := by
  induction k with
  | zero =>
      change (b.castLength (by omega)).valueUnit
        ⟨2 * 0 + j.val, by omega⟩ = _
      calc
        _ = b.valueUnit ⟨2 * 0 + j.val, by omega⟩ :=
          BONG.GoodBONG.valueUnit_castLength_heHu _ _ _
        _ = b.valueUnit j := by
          congr 1
          apply Fin.ext
          simp
  | succ k ih =>
      let tailRaw := heHu2022Lemma310BONG b hIntegral k
      let tail := tailRaw.castLength
        (show (n + 1) + 2 * k = (n + 2 * k) + 1 by omega)
      have htailIntegral : Lattice.IsIntegral
          (Lattice.halfHyperbolicExtensionForm q k)
          (Lattice.halfHyperbolicExtensionLattice L k) :=
        heHuHalfHyperbolicExtension_isIntegral hIntegral k
      let joined := heHuPrependHyperbolicBONG tail htailIntegral
      change (joined.castLength (by omega)).valueUnit
          ⟨2 * (k + 1) + j.val, by omega⟩ = _
      rw [BONG.GoodBONG.valueUnit_castLength_heHu]
      have hindex : (⟨2 * (k + 1) + j.val, by omega⟩ :
          Fin ((n + 2 * k) + 1 + 2)) =
          ⟨2 + (2 * k + j.val), by omega⟩ := by
        apply Fin.ext
        simp
        omega
      rw [hindex]
      change (heHuPrependHyperbolicBONG tail htailIntegral).valueUnit
        ⟨2 + (2 * k + j.val), by omega⟩ = _
      calc
        _ = tail.valueUnit ⟨2 * k + j.val, by omega⟩ := by
          simpa only using
            heHuPrependHyperbolicBONG_value_tail tail htailIntegral
              (⟨2 * k + j.val, by omega⟩ : Fin ((n + 2 * k) + 1))
        _ = b.valueUnit j := by
          dsimp only [tail]
          rw [BONG.GoodBONG.valueUnit_castLength_heHu]
          exact ih

/-- Order form of the hyperbolic part of Lemma 3.10.  These are precisely
the alternating `0,-2e` entries used throughout Lemma 3.11. -/
theorem heHu2022Lemma310HyperbolicOrders {n : Nat}
    (b : BONG.GoodBONG q L (n + 1))
    (hIntegral : Lattice.IsIntegral q L) (k : Nat) (t : Fin k) :
    (heHu2022Lemma310BONG b hIntegral k).order
        ⟨2 * t.val, by omega⟩ = 0 ∧
      (heHu2022Lemma310BONG b hIntegral k).order
        ⟨2 * t.val + 1, by omega⟩ =
          -(2 * (ramificationIndex K : Int)) := by
  have hvalues := heHu2022Lemma310HyperbolicValues b hIntegral k t
  constructor
  · calc
      (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val, by omega⟩ =
          ordUnit K
            ((heHu2022Lemma310BONG b hIntegral k).valueUnit
              ⟨2 * t.val, by omega⟩) :=
        (heHu2022Lemma310BONG b hIntegral k).toBONG.order_eq_ordUnit _
      _ = ordUnit K (1 : Kˣ) := by rw [hvalues.1]
      _ = 0 := by
        have h := ordUnit_mul K (1 : Kˣ) 1
        simp only [mul_one] at h
        omega
  · calc
      (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val + 1, by omega⟩ =
          ordUnit K
            ((heHu2022Lemma310BONG b hIntegral k).valueUnit
              ⟨2 * t.val + 1, by omega⟩) :=
        (heHu2022Lemma310BONG b hIntegral k).toBONG.order_eq_ordUnit _
      _ = ordUnit K
          (-(uniformizerPowerUnit K
            (-(2 * (ramificationIndex K : Int))))) := by rw [hvalues.2]
      _ = -(2 * (ramificationIndex K : Int)) := by
        rw [ordUnit_neg, ordUnit_uniformizerPowerUnit]

/-- Order form of tail preservation in Lemma 3.10. -/
theorem heHu2022Lemma310TailOrders {n : Nat}
    (b : BONG.GoodBONG q L (n + 1))
    (hIntegral : Lattice.IsIntegral q L) (k : Nat) (j : Fin (n + 1)) :
    (heHu2022Lemma310BONG b hIntegral k).order
        ⟨2 * k + j.val, by omega⟩ = b.order j := by
  calc
    (heHu2022Lemma310BONG b hIntegral k).order
        ⟨2 * k + j.val, by omega⟩ =
        ordUnit K
          ((heHu2022Lemma310BONG b hIntegral k).valueUnit
            ⟨2 * k + j.val, by omega⟩) :=
      (heHu2022Lemma310BONG b hIntegral k).toBONG.order_eq_ordUnit _
    _ = ordUnit K (b.valueUnit j) := by
      rw [heHu2022Lemma310TailValues]
    _ = b.order j := (b.toBONG.order_eq_ordUnit j).symm

/-- Direct checked endpoint for He--Hu, Lemma 3.10. -/
theorem heHu2022Lemma310 {n : Nat}
    (b : BONG.GoodBONG q L (n + 1))
    (hIntegral : Lattice.IsIntegral q L) (k : Nat) :
    (∀ t : Fin k,
      (heHu2022Lemma310BONG b hIntegral k).valueUnit
          ⟨2 * t.val, by omega⟩ = 1 ∧
        (heHu2022Lemma310BONG b hIntegral k).valueUnit
          ⟨2 * t.val + 1, by omega⟩ =
            -(uniformizerPowerUnit K
              (-(2 * (ramificationIndex K : Int))))) ∧
      ∀ j : Fin (n + 1),
        (heHu2022Lemma310BONG b hIntegral k).valueUnit
          ⟨2 * k + j.val, by omega⟩ = b.valueUnit j := by
  exact ⟨heHu2022Lemma310HyperbolicValues b hIntegral k,
    heHu2022Lemma310TailValues b hIntegral k⟩

end Bong
