/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma317

/-!
# Defect-adapted shears for binary models

Beli (2003), paragraph 3.9 does not assert that an arbitrary lift of the
projected BONG vector has the required coefficient orders.  It asserts the
existence of an integral shear with those orders.  This file records and
proves that existential statement.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG

/-- A shear whose two correction terms have the exact orders used in Beli's
even-parameter calculation. -/
def DefectAdaptedShearData (a : Kˣ) : Prop :=
  ∃ c : K,
    (2 : K) * c ∈ IntegerRing K ∧
    c ^ 2 + (a : K) ∈ IntegerRing K ∧
    ord K ((2 : K) * c) =
      (((ramificationIndex K : Int) + ordUnit K a / 2 : Int) : WithTop Int) ∧
    ((beliParameterDefect K a = ⊤ ∧ c ^ 2 + (a : K) = 0) ∨
      (beliParameterDefect K a ≠ ⊤ ∧
        ord K (c ^ 2 + (a : K)) =
          ((ordUnit K a +
            (beliParameterDefectNat K a : Int) : Int) : WithTop Int)))

/-- Beli (2003), paragraph 3.9: every admissible binary parameter of even
order admits a defect-adapted integral shear. -/
theorem exists_defectAdaptedShear
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    (a : Kˣ) (ha : IsBinaryParameterAdmissible a)
    (hEven : Even (ordUnit K a)) :
    DefectAdaptedShearData a := by
  let R : Int := ordUnit K a
  let d : Nat := (quadraticDefect K (-a)).toNat
  have hRlower : -(2 * (ramificationIndex K : Int)) ≤ R := by
    exact ha.ordUnit_ge_neg_two_mul_e
  have hRDouble : R = 2 * (R / 2) := by
    rcases hEven with ⟨r, hr⟩
    omega
  have hmNonneg : 0 ≤ (ramificationIndex K : Int) + R / 2 := by
    omega
  by_cases htop : quadraticDefect K (-a) = ⊤
  · rcases (quadraticDefect_eq_top_iff_isSquare (K := K) (-a)).1 htop with
      ⟨s, hs⟩
    have hnegOrder : ordUnit K (-a) = R := by
      apply WithTop.coe_injective
      rw [coe_ordUnit, coe_ordUnit]
      simpa only [Units.val_neg, ord_neg]
    have hsOrder : ordUnit K s = R / 2 := by
      have h := congrArg (ordUnit K) hs
      rw [ordUnit_mul, hnegOrder] at h
      omega
    let c : K := (s : K)
    have htwoOrder : ord K ((2 : K) * c) =
        (((ramificationIndex K : Int) + R / 2 : Int) : WithTop Int) := by
      dsimp [c]
      rw [ord_mul, ← ramificationIndex_spec, ← coe_ordUnit, hsOrder]
      norm_cast
    have htwoIntegral : (2 : K) * c ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      rw [Dyadic.IsIntegral, htwoOrder]
      exact_mod_cast hmNonneg
    have hdiag : c ^ 2 + (a : K) = 0 := by
      have hsVal := congrArg Units.val hs
      dsimp [c]
      simp only [Units.val_mul, Units.val_neg] at hsVal
      rw [pow_two, ← hsVal]
      ring
    refine ⟨c, htwoIntegral, ?_, ?_, Or.inl ?_⟩
    · rw [hdiag]
      exact (IntegerRing K).zero_mem
    · change ord K ((2 : K) * c) =
        (((ramificationIndex K : Int) + ordUnit K a / 2 : Int) : WithTop Int)
      simpa only [R] using htwoOrder
    · exact ⟨by simpa [beliParameterDefect] using htop, hdiag⟩
  · have hfinite : quadraticDefect K (-a) ≠ ⊤ := htop
    have hdefectEq : quadraticDefect K (-a) = (d : ℕ∞) := by
      simpa [d] using (ENat.coe_toNat hfinite).symm
    let ε : Kˣ := normalizedUnitPart K a
    have hε : IsValuationUnit K (ε : K) :=
      normalizedUnitPart_isValuationUnit K a
    have hfactor : uniformizerPowerUnit K R * ε = a := by
      simpa [R, ε] using uniformizerPower_mul_normalizedUnitPart K a
    have hdefectUnit : quadraticDefect K (-ε) = quadraticDefect K (-a) := by
      have h := beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
        (K := K) R ε hε (by simpa [R] using hEven)
      rw [hfactor] at h
      simpa [beliParameterDefect] using h.symm
    have hfiniteUnit : quadraticDefect K (-ε) ≠ ⊤ := by
      rw [hdefectUnit]
      exact hfinite
    have hnegεUnit : IsValuationUnit K ((-ε : Kˣ) : K) := by
      change ord K (-(ε : K)) = 0
      simpa only [ord_neg] using (show ord K (ε : K) = 0 from hε)
    have hdPos : 0 < d := by
      have hpos := quadraticDefect_toNat_pos_of_unit_of_ne_top
        (-ε) hnegεUnit hfiniteUnit
      rw [hdefectUnit] at hpos
      simpa [d] using hpos
    rcases exists_quadraticApproximation_exact_order (-a) hfinite with
      ⟨x, hxError⟩
    let err : K := 1 - x ^ 2 / ((-a : Kˣ) : K)
    have herrOrder : ord K err = ((d : Int) : WithTop Int) := by
      simpa [err, d] using hxError
    have herrPos : 0 < ord K err := by
      rw [herrOrder]
      exact_mod_cast hdPos
    have hratioOrder : ord K (x ^ 2 / ((-a : Kˣ) : K)) = 0 := by
      have hlt : ord K (1 : K) < ord K err := by
        simpa only [ord_one] using herrPos
      have hsub := (ord K).map_sub_eq_of_lt_left hlt
      have heq : 1 - err = x ^ 2 / ((-a : Kˣ) : K) := by
        dsimp [err]
        ring
      rw [heq] at hsub
      simpa using hsub
    have hxNe : x ≠ 0 := by
      intro hx
      rw [hx] at hratioOrder
      simp at hratioOrder
    let xu : Kˣ := Units.mk0 x hxNe
    have hnegOrder : ordUnit K (-a) = R := by
      apply WithTop.coe_injective
      rw [coe_ordUnit, coe_ordUnit]
      simpa only [Units.val_neg, ord_neg]
    have hratioUnitOrder : ordUnit K (xu ^ 2 * (-a)⁻¹) = 0 := by
      apply (isValuationUnit_iff_ordUnit_eq_zero K _).1
      rw [IsValuationUnit]
      have hval : ((xu ^ 2 * (-a)⁻¹ : Kˣ) : K) =
          x ^ 2 / ((-a : Kˣ) : K) := by
        simp [xu, div_eq_mul_inv]
      rw [hval]
      exact hratioOrder
    have hxOrder : ordUnit K xu = R / 2 := by
      rw [ordUnit_mul, ordUnit_pow, ordUnit_inv, hnegOrder]
        at hratioUnitOrder
      omega
    let c : K := x
    have hcOrder : ord K c = ((R / 2 : Int) : WithTop Int) := by
      dsimp [c]
      rw [← show (xu : K) = x by rfl, ← coe_ordUnit, hxOrder]
    have htwoOrder : ord K ((2 : K) * c) =
        (((ramificationIndex K : Int) + R / 2 : Int) : WithTop Int) := by
      rw [ord_mul, ← ramificationIndex_spec, hcOrder]
      norm_cast
    let D : K := c ^ 2 + (a : K)
    have hDEq : D = (a : K) * err := by
      dsimp [D, c, err]
      field_simp [Units.ne_zero a]
      ring
    have hDOrder : ord K D =
        ((R + (d : Int) : Int) : WithTop Int) := by
      rw [hDEq, ord_mul, ← coe_ordUnit, herrOrder]
      norm_cast
    have hDNonneg : 0 ≤ R + (d : Int) := by
      have hbase := order_add_defect_nonneg_of_admissible_even
        (K := K) R ε hε (by simpa [hfactor] using ha)
        hfiniteUnit (by simpa [R] using hEven)
      rw [hdefectUnit] at hbase
      simpa [d] using hbase
    have htwoIntegral : (2 : K) * c ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      rw [Dyadic.IsIntegral, htwoOrder]
      exact_mod_cast hmNonneg
    have hDIntegral : D ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      rw [Dyadic.IsIntegral, hDOrder]
      exact_mod_cast hDNonneg
    refine ⟨c, htwoIntegral, ?_, ?_, Or.inr ?_⟩
    · simpa [D] using hDIntegral
    · change ord K ((2 : K) * c) =
        (((ramificationIndex K : Int) + ordUnit K a / 2 : Int) : WithTop Int)
      simpa only [R] using htwoOrder
    · refine ⟨by simpa [beliParameterDefect] using hfinite, ?_⟩
      simpa [D, R, d, beliParameterDefectNat, beliParameterDefect] using hDOrder

end BONG

end Bong
