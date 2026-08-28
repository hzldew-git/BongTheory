/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009AlphaCompression
import Bong.Lattice.PowerIdeal

/-!
# Defect bounds from a perfect dyadic residue field

This file isolates two paper-independent arithmetic facts used throughout the
Beli formalization: valuation units have quadratic-defect order at least one,
and the same conclusion holds for every square class of even valuation.
-/

namespace Bong

open Dyadic

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

theorem defectOrder_one_le_of_valuationUnit
    [PerfectResidueFieldLaws K]
    (x : Kˣ) (hx : IsValuationUnit K (x : K)) :
    (1 : WithTop ℚ) ≤ defectOrder (K := K) x := by
  rcases exists_unit_squareRoot_mod_maximal K x hx with
    ⟨z, hzUnit, hzError⟩
  have happrox : IsQuadraticApproximation K x 1 := by
    refine ⟨z, ?_⟩
    have hnormalized :
        1 - z ^ 2 / (x : K) = ((x : K) - z ^ 2) / (x : K) := by
      field_simp [Units.ne_zero x]
    rw [hnormalized, div_eq_mul_inv, ord_mul,
      AddValuation.map_inv, hx]
    simp only [neg_zero, add_zero]
    have hpositive : 0 < ord K ((x : K) - z ^ 2) := by
      rw [show (x : K) - z ^ 2 = -(z ^ 2 - (x : K)) by ring,
        ord_neg]
      exact hzError
    have hone : (1 : WithTop ℤ) ≤ ord K ((x : K) - z ^ 2) := by
      by_cases htop : ord K ((x : K) - z ^ 2) = ⊤
      · rw [htop]
        exact le_top
      · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
        rw [← hd] at hpositive ⊢
        have hdPositive : (0 : ℤ) < d := by
          exact_mod_cast hpositive
        exact_mod_cast (show (1 : ℤ) ≤ d by omega)
    exact hone
  have hdefect := natCast_le_quadraticDefect K happrox
  by_cases htop : quadraticDefect K x = ⊤
  · unfold defectOrder
    rw [htop]
    exact le_top
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
    have hdOne : 1 ≤ d := by
      rw [← hd] at hdefect
      apply ENat.coe_le_coe.mp
      exact hdefect
    unfold defectOrder
    rw [← hd]
    change (1 : WithTop ℚ) ≤ (d : ℚ)
    exact_mod_cast hdOne

theorem defectOrder_one_le_of_even
    [PerfectResidueFieldLaws K]
    (x : Kˣ) (heven : Even (ordUnit K x)) :
    (1 : WithTop ℚ) ≤ defectOrder (K := K) x := by
  rcases heven with ⟨k, hk⟩
  let s : Kˣ := uniformizerPowerUnit K k
  let unitPart : Kˣ := x / s ^ 2
  have hsOrder : ordUnit K s = k := by
    simpa only [s] using ordUnit_uniformizerPowerUnit (K := K) k
  have hunitPartOrder : ordUnit K unitPart = 0 := by
    dsimp only [unitPart]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow,
      hsOrder]
    omega
  have hunitPart : IsValuationUnit K (unitPart : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K unitPart).2 hunitPartOrder
  have hlower := defectOrder_one_le_of_valuationUnit unitPart hunitPart
  calc
    (1 : WithTop ℚ) ≤ defectOrder (K := K) unitPart := hlower
    _ = defectOrder (K := K) (unitPart * s ^ 2) :=
      (IsCoefficientScale.defectOrder_mul_square unitPart s).symm
    _ = defectOrder (K := K) x := by
      congr 1
      simp [unitPart]

end BONG.GoodBONG

end Bong
