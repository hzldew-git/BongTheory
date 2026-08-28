/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma65Proof
import Bong.Dyadic.UnitDefectClassification

/-!
# Quadratic-defect bounds for perturbed square differences

These lemmas package the valuation calculation repeatedly expanded in Xu
(1993), Proposition 2.3.  If `u` is close to a square, then `1-u` is close
to the square difference built from the same approximation.  Factoring that
square difference gives the second, dyadic contribution to its defect.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- An even-order square class with defect at least `k` belongs to the
depth-`k` principal-unit square-class subgroup. -/
theorem squareClass_mem_principalUnitSquareClassSubgroup_of_even_order_of_defect
    (a : Kˣ) (k : Nat) (hEven : Even (ordUnit K a))
    (hdefect : (k : ℕ∞) ≤ quadraticDefect K a) :
    squareClass K a ∈ principalUnitSquareClassSubgroup K k := by
  rcases hEven with ⟨r, hr⟩
  let s : Kˣ := uniformizerPowerUnit K r
  let v : Kˣ := a / s ^ 2
  have hsOrder : ordUnit K s = r :=
    ordUnit_uniformizerPowerUnit (K := K) r
  have hvOrder : ordUnit K v = 0 := by
    dsimp only [v]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow,
      hsOrder]
    omega
  have hvUnit : IsValuationUnit K (v : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K v).2 hvOrder
  have hvDefect : quadraticDefect K v = quadraticDefect K a := by
    have hfactor : v * s ^ 2 = a := by simp [v]
    calc
      quadraticDefect K v = quadraticDefect K (v * s ^ 2) :=
        (quadraticDefect_mul_square K v s).symm
      _ = quadraticDefect K a := congrArg (quadraticDefect K) hfactor
  let vu : valuationUnitSubgroup K := ⟨v, hvUnit⟩
  have hclassUnit : valuationUnitClassHom K vu ∈
      principalUnitValuationClassSubgroup K k := by
    apply valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
    rwa [hvDefect]
  have hmapped := valuationUnitClassToSquareClass_mem_image
    (K := K) hclassUnit
  rw [valuationUnitClassSubgroupSquareImage_principalUnit] at hmapped
  have hclass : squareClass K v = squareClass K a := by
    have hfactor : v * s ^ 2 = a := by simp [v]
    rw [← hfactor, squareClass_mul_square]
  simpa only [valuationUnitClassToSquareClass_apply, vu, hclass] using hmapped

/-- If `ord(1-u)=n` is strictly below the available quadratic-defect
depth of the unit `u`, then `n` is even below the dyadic endpoint. -/
theorem even_order_one_sub_unit_of_succ_le_defect
    (u : Kˣ) (hu : IsValuationUnit K (u : K)) (n : Nat)
    (horder : ord K (1 - (u : K)) = ((n : Int) : WithTop Int))
    (hpos : 0 < n) (hlt : n < 2 * ramificationIndex K)
    (hnext : ((n + 1 : Nat) : ℕ∞) ≤ quadraticDefect K u) :
    Even n := by
  rcases (isQuadraticApproximation_iff_le_defect K).2 hnext with
    ⟨x, hx⟩
  have hdeep : (((n + 1 : Nat) : Int) : WithTop Int) ≤
      ord K ((u : K) - x ^ 2) := by
    have hfield : (u : K) - x ^ 2 =
        (u : K) * (1 - x ^ 2 / (u : K)) := by
      field_simp [Units.ne_zero u]
    rw [hfield, ord_mul, hu]
    simp only [zero_add]
    exact_mod_cast hx
  have hstrict : ord K (1 - (u : K)) <
      ord K ((u : K) - x ^ 2) := by
    rw [horder]
    exact lt_of_lt_of_le (by exact_mod_cast (show n < n + 1 by omega)) hdeep
  have hsum := (ord K).map_add_eq_of_lt_left hstrict
  have hfield :
      (1 - (u : K)) + ((u : K) - x ^ 2) = 1 - x ^ 2 := by ring
  have horderSquare : ord K (1 - x ^ 2) =
      ((n : Int) : WithTop Int) := by
    rw [← hfield, hsum, horder]
  have hevenInt := even_order_one_sub_sq_of_lt_two_mul_e_proved
    x (n : Int) horderSquare (by exact_mod_cast hpos)
      (by exact_mod_cast hlt)
  exact_mod_cast hevenInt

/-- If `u` has positive even order and defect at least `k`, then the square
difference `1-u` has defect at least `k` as soon as the elementary dyadic
factor bound `k ≤ e + ord(u)/2` holds. -/
theorem quadraticDefect_one_sub_of_positive_even_order
    [QuadraticDefectLaws K]
    (u : Kˣ) (h : Int) (k : Nat)
    (huOrder : ordUnit K u = h) (hpos : 0 < h) (hEven : Even h)
    (hdefect : (k : ℕ∞) ≤ quadraticDefect K u)
    (hkBound : (k : Int) ≤
      (ramificationIndex K : Int) + h / 2)
    (hdelta0 : 1 - (u : K) ≠ 0) :
    (k : ℕ∞) ≤ quadraticDefect K
      (Units.mk0 (1 - (u : K)) hdelta0) := by
  let delta : K := 1 - (u : K)
  have hdelta0' : delta ≠ 0 := by simpa [delta] using hdelta0
  let deltaU : Kˣ := Units.mk0 delta hdelta0'
  change (k : ℕ∞) ≤ quadraticDefect K deltaU
  by_cases hk0 : k = 0
  · subst k
    exact bot_le
  have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
  rcases (isQuadraticApproximation_iff_le_defect K).2 hdefect with
    ⟨x, hx⟩
  have herrorPos : (0 : WithTop Int) <
      ord K (1 - x ^ 2 / (u : K)) := by
    have hzeroLt : (0 : WithTop Int) < (k : WithTop Int) := by
      exact_mod_cast hkPos
    exact hzeroLt.trans_le hx
  have hratioOrder : ord K (x ^ 2 / (u : K)) = 0 := by
    have hlt : ord K (1 : K) < ord K (1 - x ^ 2 / (u : K)) := by
      simpa only [ord_one] using herrorPos
    have hsub := (ord K).map_sub_eq_of_lt_left hlt
    have heq : 1 - (1 - x ^ 2 / (u : K)) = x ^ 2 / (u : K) := by ring
    rw [heq] at hsub
    simpa using hsub
  have hx0 : x ≠ 0 := by
    intro hxzero
    rw [hxzero] at hratioOrder
    simp at hratioOrder
  let xu : Kˣ := Units.mk0 x hx0
  have hratioUnitOrder : ordUnit K (xu ^ 2 * u⁻¹) = 0 := by
    apply (isValuationUnit_iff_ordUnit_eq_zero K (xu ^ 2 * u⁻¹)).1
    rw [IsValuationUnit]
    have hfield : ((xu ^ 2 * u⁻¹ : Kˣ) : K) =
        x ^ 2 / (u : K) := by simp [xu, div_eq_mul_inv]
    rw [hfield]
    exact hratioOrder
  have hxOrder : ordUnit K xu = h / 2 := by
    rw [ordUnit_mul, ordUnit_pow, ordUnit_inv, huOrder] at hratioUnitOrder
    rcases hEven with ⟨r, hr⟩
    omega
  have hxOrderPos : 0 < ordUnit K xu := by
    rw [hxOrder]
    rcases hEven with ⟨r, hr⟩
    omega
  have hxOrdTop : ord K x = ((h / 2 : Int) : WithTop Int) := by
    simpa [xu, hxOrder] using (coe_ordUnit K xu).symm
  have hdeltaOrder : ord K delta = 0 := by
    have hlt : ord K (1 : K) < ord K (u : K) := by
      rw [ord_one, ← coe_ordUnit, huOrder]
      exact_mod_cast hpos
    dsimp only [delta]
    simpa only [ord_one] using (ord K).map_sub_eq_of_lt_left hlt
  have hdeltaUnitOrder : ordUnit K deltaU = 0 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    simpa [deltaU] using hdeltaOrder
  let v : K := 1 - x ^ 2
  have hvOrder : ord K v = 0 := by
    have hxSqPos : (0 : WithTop Int) < ord K (x ^ 2) := by
      rw [ord_pow, hxOrdTop]
      exact_mod_cast (show (0 : Int) < 2 * (h / 2) by
        rcases hEven with ⟨r, hr⟩
        omega)
    have hlt : ord K (1 : K) < ord K (x ^ 2) := by
      simpa only [ord_one] using hxSqPos
    dsimp only [v]
    simpa only [ord_one] using (ord K).map_sub_eq_of_lt_left hlt
  have hv0 : v ≠ 0 := by
    apply (ord_eq_top_iff K).not.mp
    rw [hvOrder]
    exact WithTop.coe_ne_top
  let vU : Kˣ := Units.mk0 v hv0
  have hvUnitOrder : ordUnit K vU = 0 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    simpa [vU] using hvOrder
  have hdeep : ((k : Int) : WithTop Int) ≤
      ord K (delta - v) := by
    have hnormalized : (u : K) - x ^ 2 =
        (u : K) * (1 - x ^ 2 / (u : K)) := by
      field_simp [Units.ne_zero u]
    have hraw : (((h + (k : Int) : Int)) : WithTop Int) ≤
        ord K ((u : K) - x ^ 2) := by
      rw [hnormalized, ord_mul, ← coe_ordUnit, huOrder]
      have hxCast : ((k : Int) : WithTop Int) ≤
          ord K (1 - x ^ 2 / (u : K)) := by
        exact_mod_cast hx
      calc
        ((h + (k : Int) : Int) : WithTop Int) =
            (h : WithTop Int) + (k : Int) := by norm_cast
        _ ≤ (h : WithTop Int) +
            ord K (1 - x ^ 2 / (u : K)) := by
          simpa [add_comm] using
            (add_le_add_left hxCast (h : WithTop Int))
    have hdiff : delta - v = x ^ 2 - (u : K) := by
      dsimp only [delta, v]
      ring
    rw [hdiff, show x ^ 2 - (u : K) =
        -((u : K) - x ^ 2) by ring, ord_neg]
    exact (show ((k : Int) : WithTop Int) ≤
        ((h + (k : Int) : Int) : WithTop Int) by
          exact_mod_cast (show (k : Int) ≤ h + k by omega)).trans hraw
  have hratioDefect : (k : ℕ∞) ≤
      quadraticDefect K (deltaU * vU⁻¹) := by
    apply quadraticDefect_div_ge_of_sub_order deltaU vU k
    · rw [hdeltaUnitOrder, hvUnitOrder]
    · rw [hdeltaUnitOrder, zero_add]
      simpa [deltaU, vU] using hdeep
  have hplusOrder : ord K (1 + x) = 0 := by
    have hlt : ord K (1 : K) < ord K x := by
      rw [ord_one, hxOrdTop]
      exact_mod_cast (show 0 < h / 2 by simpa [hxOrder] using hxOrderPos)
    simpa only [ord_one] using (ord K).map_add_eq_of_lt_left hlt
  have hplus0 : 1 + x ≠ 0 := by
    apply (ord_eq_top_iff K).not.mp
    rw [hplusOrder]
    exact WithTop.coe_ne_top
  have hvDefect : (k : ℕ∞) ≤ quadraticDefect K vU := by
    apply natCast_le_quadraticDefect K
    refine ⟨1 - x, ?_⟩
    have hfield : 1 - (1 - x) ^ 2 / (vU : K) =
        (2 : K) * x / (1 + x) := by
      dsimp only [vU, v]
      simp only [Units.val_mk0]
      have hx2 : 1 - x ^ 2 ≠ 0 := by
        simpa only [v] using hv0
      field_simp [hx2, hplus0]
      ring
    rw [hfield, div_eq_mul_inv, ord_mul, ord_mul,
      AddValuation.map_inv, ← ramificationIndex_spec,
      hxOrdTop, hplusOrder]
    simp only [neg_zero, add_zero]
    exact_mod_cast hkBound
  have hdom := quadraticDefect_mul_ge_min K (deltaU * vU⁻¹) vU
  have hfactor : (deltaU * vU⁻¹) * vU = deltaU := by simp
  rw [hfactor] at hdom
  exact (le_min hratioDefect hvDefect).trans hdom

/-- Unit-cancellation companion to
`quadraticDefect_one_sub_of_positive_even_order`.  Suppose that `u` is a
valuation unit and `ord(1-u)=n` is positive, even, and below the dyadic
endpoint.  If `u` is a square to depth `n+k`, then `1-u` is a square to
depth `k`, provided the remaining linear factor contributes at least `k`.

This is the equal-valuation calculation used in Xu (1993), Proposition 2.3:
an approximation `x²` to `u` first gives
`ord(1-x²)=ord(1-u)=n`; Beli's Lemma 6.5 then gives
`ord(1±x)=n/2`. -/
theorem quadraticDefect_one_sub_of_unit_cancellation
    [QuadraticDefectLaws K]
    (u : Kˣ) (n k : Nat)
    (hu : IsValuationUnit K (u : K))
    (horder : ord K (1 - (u : K)) = ((n : Int) : WithTop Int))
    (hnEven : Even n)
    (hnLt : n < 2 * ramificationIndex K)
    (hdefect : ((n + k : Nat) : ℕ∞) ≤ quadraticDefect K u)
    (hkBound : (k : Int) ≤
      (ramificationIndex K : Int) - (n : Int) / 2)
    (hdelta0 : 1 - (u : K) ≠ 0) :
    (k : ℕ∞) ≤ quadraticDefect K
      (Units.mk0 (1 - (u : K)) hdelta0) := by
  by_cases hk0 : k = 0
  · subst k
    exact bot_le
  have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
  let delta : K := 1 - (u : K)
  have hdelta0' : delta ≠ 0 := by simpa [delta] using hdelta0
  let deltaU : Kˣ := Units.mk0 delta hdelta0'
  change (k : ℕ∞) ≤ quadraticDefect K deltaU
  have huOrder : ordUnit K u = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K u).1 hu
  have hdeltaUnitOrder : ordUnit K deltaU = n := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    simpa [deltaU, delta] using horder
  rcases (isQuadraticApproximation_iff_le_defect K).2 hdefect with
    ⟨x, hx⟩
  have herrorPos : (0 : WithTop Int) <
      ord K (1 - x ^ 2 / (u : K)) := by
    have hzeroLt : (0 : WithTop Int) <
        (((n + k : Nat) : Int) : WithTop Int) := by
      exact_mod_cast (show 0 < n + k by omega)
    exact hzeroLt.trans_le hx
  have hratioOrder : ord K (x ^ 2 / (u : K)) = 0 := by
    have hlt : ord K (1 : K) < ord K (1 - x ^ 2 / (u : K)) := by
      simpa only [ord_one] using herrorPos
    have hsub := (ord K).map_sub_eq_of_lt_left hlt
    have heq : 1 - (1 - x ^ 2 / (u : K)) = x ^ 2 / (u : K) := by
      ring
    rw [heq] at hsub
    simpa using hsub
  have hx0 : x ≠ 0 := by
    intro hxzero
    rw [hxzero] at hratioOrder
    simp at hratioOrder
  let xu : Kˣ := Units.mk0 x hx0
  have hxUnitOrder : ordUnit K xu = 0 := by
    have hratioUnitOrder : ordUnit K (xu ^ 2 * u⁻¹) = 0 := by
      apply (isValuationUnit_iff_ordUnit_eq_zero K (xu ^ 2 * u⁻¹)).1
      rw [IsValuationUnit]
      have hfield : ((xu ^ 2 * u⁻¹ : Kˣ) : K) =
          x ^ 2 / (u : K) := by simp [xu, div_eq_mul_inv]
      rw [hfield]
      exact hratioOrder
    rw [ordUnit_mul, ordUnit_pow, ordUnit_inv, huOrder] at hratioUnitOrder
    omega
  have hxOrder : ord K x = 0 := by
    simpa [xu, hxUnitOrder] using (coe_ordUnit K xu).symm
  have hdeepRaw : ((((n + k : Nat) : Int)) : WithTop Int) ≤
      ord K ((u : K) - x ^ 2) := by
    have hnormalized : (u : K) - x ^ 2 =
        (u : K) * (1 - x ^ 2 / (u : K)) := by
      field_simp [Units.ne_zero u]
    rw [hnormalized, ord_mul, hu]
    simp only [zero_add]
    exact_mod_cast hx
  let v : K := 1 - x ^ 2
  have hvOrder : ord K v = ((n : Int) : WithTop Int) := by
    have hstrict : ord K delta < ord K ((u : K) - x ^ 2) := by
      rw [show ord K delta = ((n : Int) : WithTop Int) by
        simpa [delta] using horder]
      exact lt_of_lt_of_le
        (by exact_mod_cast (show n < n + k by omega)) hdeepRaw
    have hsum := (ord K).map_add_eq_of_lt_left hstrict
    have hfield : delta + ((u : K) - x ^ 2) = v := by
      dsimp only [delta, v]
      ring
    rw [hfield] at hsum
    simpa [delta, horder] using hsum
  have hv0 : v ≠ 0 := by
    apply (ord_eq_top_iff K).not.mp
    rw [hvOrder]
    exact WithTop.coe_ne_top
  let vU : Kˣ := Units.mk0 v hv0
  have hvUnitOrder : ordUnit K vU = n := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    simpa [vU] using hvOrder
  have hdeep : (((n + k : Nat) : Int) : WithTop Int) ≤
      ord K (delta - v) := by
    have hdiff : delta - v = -((u : K) - x ^ 2) := by
      dsimp only [delta, v]
      ring
    rw [hdiff, ord_neg]
    exact hdeepRaw
  have hratioDefect : (k : ℕ∞) ≤
      quadraticDefect K (deltaU * vU⁻¹) := by
    apply quadraticDefect_div_ge_of_sub_order deltaU vU k
    · rw [hdeltaUnitOrder, hvUnitOrder]
    · rw [hdeltaUnitOrder]
      simpa [deltaU, vU] using hdeep
  have hfactorOrders :=
    ord_one_sub_and_add_eq_half_of_order_one_sub_sq
      (K := K) x (n : Int) (by exact_mod_cast hnEven)
        (by exact_mod_cast (Nat.le_of_lt hnLt)) (by simpa [v] using hvOrder)
  have hminusOrder : ord K (1 - x) =
      (((n : Int) / 2 : Int) : WithTop Int) := hfactorOrders.1
  have hplusOrder : ord K (1 + x) =
      (((n : Int) / 2 : Int) : WithTop Int) := hfactorOrders.2
  have hplus0 : 1 + x ≠ 0 := by
    apply (ord_eq_top_iff K).not.mp
    rw [hplusOrder]
    exact WithTop.coe_ne_top
  have hvDefect : (k : ℕ∞) ≤ quadraticDefect K vU := by
    apply natCast_le_quadraticDefect K
    refine ⟨1 - x, ?_⟩
    have hfield : 1 - (1 - x) ^ 2 / (vU : K) =
        (2 : K) * x / (1 + x) := by
      dsimp only [vU, v]
      simp only [Units.val_mk0]
      have hx2 : 1 - x ^ 2 ≠ 0 := by
        simpa only [v] using hv0
      field_simp [hx2, hplus0]
      ring
    rw [hfield, div_eq_mul_inv, ord_mul, ord_mul,
      AddValuation.map_inv, ← ramificationIndex_spec,
      hxOrder, hplusOrder]
    simp only [add_zero]
    rw [← sub_eq_add_neg]
    have hright :
        ((ramificationIndex K : Int) : WithTop Int) -
            (((n : Int) / 2 : Int) : WithTop Int) =
          (((ramificationIndex K : Int) - (n : Int) / 2 : Int) :
            WithTop Int) :=
      (WithTop.LinearOrderedAddCommGroup.coe_sub _ _).symm
    rw [hright]
    exact WithTop.coe_le_coe.mpr hkBound
  have hdom := quadraticDefect_mul_ge_min K (deltaU * vU⁻¹) vU
  have hfactor : (deltaU * vU⁻¹) * vU = deltaU := by simp
  rw [hfactor] at hdom
  exact (le_min hratioDefect hvDefect).trans hdom

end BONG

end Bong
