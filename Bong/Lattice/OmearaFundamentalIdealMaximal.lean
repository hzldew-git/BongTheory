/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaFundamentalIdeals

/-!
# O'Meara fundamental ideals are proper

At every proper boundary the next Jordan scale is strictly larger than the
current one.  O'Meara's formulas 93:25--93:26 therefore put the boundary
ideal `f_i` inside the maximal ideal.  This elementary but important bound
turns square-class congruences modulo `f_i` into congruences with an actual
valuation-unit square multiplier.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The norm order of a fundamental lattice is at least its scale order. -/
theorem fundamentalScaleOrder_le_normGeneratorOrder
    (J : JordanDecomposition q L t) (i : Fin t) :
    J.fundamentalScaleOrder i ≤
      ordUnit K (J.fundamentalNormGenerator i) := by
  have h := normIdeal_le_scaleIdeal q (J.fundamentalLattice i)
  rw [(J.fundamentalNormGenerator_spec i).2] at h
  unfold fundamentalLattice fundamentalScaleOrder at h
  unfold fundamentalScaleOrder
  rw [
    J.scaleIdeal_scaleTruncation_at_component,
    principalIdeal_eq_powerIdeal, powerIdeal_le_iff] at h
  exact h

/-- Across a proper boundary the sum of the two fundamental norm orders is
at least one more than twice the left scale order. -/
theorem twoScaleOrder_add_one_le_boundaryNormOrderSum
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    2 * J.fundamentalScaleOrder (boundaryLeftIndex i) + 1 ≤
      J.boundaryNormOrderSum i := by
  let li := boundaryLeftIndex i
  let ri := boundaryRightIndex i
  have hleft := J.fundamentalScaleOrder_le_normGeneratorOrder li
  have hright := J.fundamentalScaleOrder_le_normGeneratorOrder ri
  have hscale : J.fundamentalScaleOrder li <
      J.fundamentalScaleOrder ri := by
    exact J.scaleOrder_strict (by
      apply Fin.lt_def.mpr
      simp [li, ri, boundaryLeftIndex, boundaryRightIndex])
  unfold boundaryNormOrderSum
  dsimp only [li, ri] at hleft hright hscale ⊢
  omega

/-- The defect sum of two norm groups is always contained in the product
of their principal norm ideals.  Odd parity is needed only for the reverse
containment in 93:26. -/
theorem productDefectSum_le_principalIdeal_of_normGenerators
    {A B : Lattice K V} (a b : Kˣ)
    (ha : IsNormGeneratorValue q A a)
    (hb : IsNormGeneratorValue q B b) :
    productDefectSum (normGroupSet q A) (normGroupSet q B) ≤
      principalIdeal (K := K) ((a * b : Kˣ) : K) := by
  apply iSup_le
  intro x
  apply iSup_le
  intro y
  by_cases hx : (x.1 : K) = 0
  · simp [scalarQuadraticDefectIdeal, hx]
  by_cases hy : (y.1 : K) = 0
  · simp [scalarQuadraticDefectIdeal, hy]
  let xu : Kˣ := Units.mk0 x.1 hx
  let yu : Kˣ := Units.mk0 y.1 hy
  have hxIdeal : (x.1 : K) ∈ normIdeal q A :=
    normGroupSet_subset_normIdeal q A x.2
  have hyIdeal : (y.1 : K) ∈ normIdeal q B :=
    normGroupSet_subset_normIdeal q B y.2
  have hax : ordUnit K a ≤ ordUnit K xu := by
    rw [ha.2, principalIdeal_eq_powerIdeal,
      mem_powerIdeal_iff] at hxIdeal
    change ((ordUnit K a : Int) : WithTop Int) ≤ ord K (xu : K) at hxIdeal
    rw [← coe_ordUnit] at hxIdeal
    exact WithTop.coe_le_coe.mp hxIdeal
  have hby : ordUnit K b ≤ ordUnit K yu := by
    rw [hb.2, principalIdeal_eq_powerIdeal,
      mem_powerIdeal_iff] at hyIdeal
    change ((ordUnit K b : Int) : WithTop Int) ≤ ord K (yu : K) at hyIdeal
    rw [← coe_ordUnit] at hyIdeal
    exact WithTop.coe_le_coe.mp hyIdeal
  have hdefect : scalarQuadraticDefectIdeal (x.1 * y.1) =
      quadraticDefectIdeal (xu * yu) := by
    change scalarQuadraticDefectIdeal ((xu : K) * (yu : K)) = _
    rw [← Units.val_mul]
    exact scalarQuadraticDefectIdeal_eq_quadraticDefectIdeal (xu * yu)
  rw [hdefect]
  exact (quadraticDefectIdeal_le_principalIdeal (xu * yu)).trans <| by
    rw [principalIdeal_eq_powerIdeal, principalIdeal_eq_powerIdeal,
      powerIdeal_le_iff, ordUnit_mul, ordUnit_mul]
    omega

private theorem coefficientIdeal_sup_le
    {I₁ I₂ H : CoefficientIdeal (K := K)}
    (h₁ : I₁ ≤ H) (h₂ : I₂ ≤ H) : I₁ ⊔ I₂ ≤ H :=
  _root_.sup_le h₁ h₂

/-- The product-defect part of `s_i² f_i` has order at least `2s_i+1`. -/
theorem boundaryProductDefectSum_le_nextPower
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    J.boundaryProductDefectSum i ≤
      powerIdeal (K := K)
        (2 * J.fundamentalScaleOrder (boundaryLeftIndex i) + 1) := by
  let li := boundaryLeftIndex i
  let ri := boundaryRightIndex i
  let a := J.fundamentalNormGenerator li
  let b := J.fundamentalNormGenerator ri
  let s := J.fundamentalScaleOrder li
  change J.boundaryProductDefectSum i ≤
    powerIdeal (K := K) (2 * s + 1)
  have hsum : 2 * s + 1 ≤ ordUnit K a + ordUnit K b := by
    simpa only [s, a, b, li, ri, boundaryNormOrderSum] using
      J.twoScaleOrder_add_one_le_boundaryNormOrderSum i
  unfold boundaryProductDefectSum fundamentalNormGroup
  exact (productDefectSum_le_principalIdeal_of_normGenerators a b
    (J.fundamentalNormGenerator_spec li)
    (J.fundamentalNormGenerator_spec ri)).trans <| by
      rw [principalIdeal_eq_powerIdeal, powerIdeal_le_iff, ordUnit_mul]
      exact hsum

/-- In the even branch, the parity part of `s_i² f_i` also has order at
least `2s_i+1`. -/
theorem boundaryParityIdeal_le_nextPower_of_even
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (heven : Even (J.boundaryNormOrderSum i)) :
    J.boundaryParityIdeal i ≤
      powerIdeal (K := K)
        (2 * J.fundamentalScaleOrder (boundaryLeftIndex i) + 1) := by
  unfold boundaryParityIdeal
  rw [twiceIdeal_powerIdeal, powerIdeal_le_iff]
  have hePos : 0 < (ramificationIndex K : Int) := by
    exact_mod_cast ramificationIndex_pos (K := K)
  have hsum := J.twoScaleOrder_add_one_le_boundaryNormOrderSum i
  have heq : J.boundaryNormOrderSum i =
      2 * (J.boundaryNormOrderSum i / 2) := by
    rcases heven with ⟨m, hm⟩
    omega
  have hhalf :
      J.fundamentalScaleOrder (boundaryLeftIndex i) + 1 ≤
        J.boundaryNormOrderSum i / 2 := by
    omega
  omega

/-- Before removing the square of the left scale, the ideal
`s_i² f_i` has order at least `2s_i+1`. -/
theorem scaledFundamentalIdeal_le_nextPower
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    J.scaledFundamentalIdeal i ≤
      powerIdeal (K := K)
        (2 * J.fundamentalScaleOrder (boundaryLeftIndex i) + 1) := by
  by_cases heven : Even (J.boundaryNormOrderSum i)
  · rw [scaledFundamentalIdeal, if_pos heven]
    exact coefficientIdeal_sup_le
      (J.boundaryProductDefectSum_le_nextPower i)
      (J.boundaryParityIdeal_le_nextPower_of_even i heven)
  · rw [scaledFundamentalIdeal, if_neg heven]
    exact J.boundaryProductDefectSum_le_nextPower i

/-- Every fundamental boundary ideal is contained in the maximal ideal
`p = powerIdeal 1`. -/
theorem fundamentalIdeal_le_maximal
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    J.fundamentalIdeal i ≤ powerIdeal (K := K) 1 := by
  let sUnit := J.scaleGenerator (boundaryLeftIndex i)
  let s := J.fundamentalScaleOrder (boundaryLeftIndex i)
  have hscaled := J.scaledFundamentalIdeal_le_nextPower i
  calc
    J.fundamentalIdeal i =
        scalarIdeal ((sUnit⁻¹ ^ 2 : Kˣ) : K)
          (J.scaledFundamentalIdeal i) := rfl
    _ ≤ scalarIdeal ((sUnit⁻¹ ^ 2 : Kˣ) : K)
          (powerIdeal (K := K) (2 * s + 1)) :=
      Submodule.map_mono hscaled
    _ = powerIdeal (K := K) 1 := by
      rw [scalarIdeal_powerIdeal_units, ordUnit_pow, ordUnit_inv]
      have hs : ordUnit K sUnit = s := rfl
      rw [hs]
      congr 1
      omega

/-- Membership in a fundamental ideal implies positive valuation. -/
theorem isInMaximalIdeal_of_mem_fundamentalIdeal
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    {x : K} (hx : x ∈ J.fundamentalIdeal i) :
    IsInMaximalIdeal K x := by
  have hx' : x ∈ powerIdeal (K := K) 1 :=
    J.fundamentalIdeal_le_maximal i hx
  rw [mem_powerIdeal_iff] at hx'
  change (0 : WithTop Int) < ord K x
  exact (show (0 : WithTop Int) < (1 : Int) by norm_num).trans_le hx'

end Lattice.JordanDecomposition

end Bong
