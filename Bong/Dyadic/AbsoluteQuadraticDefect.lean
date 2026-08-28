/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.QuadraticDefect
import Bong.Lattice.Basic

/-!
# Nonnegative absolute quadratic defect

For `a ∈ Kˣ`, Beli writes the integrality of the absolute defect as
`ord(a) + d(a) ≥ 0`.  The natural threshold below avoids subtraction in
`ENat`: it is `max(0, -ord(a))`.
-/

namespace Bong.Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The relative approximation depth required to make the absolute error
integral. -/
noncomputable def absoluteDefectThreshold (a : Kˣ) : Nat :=
  Int.toNat (-ordUnit K a)

/-- Beli's inequality `ord(a) + d(a) ≥ 0`, expressed without subtracting
from an extended natural number. -/
def HasNonnegativeAbsoluteQuadraticDefect (a : Kˣ) : Prop :=
  IsQuadraticApproximation K a (absoluteDefectThreshold a)

theorem absoluteDefectThreshold_eq_zero_of_nonneg
    {a : Kˣ} (ha : 0 ≤ ordUnit K a) :
    absoluteDefectThreshold a = 0 := by
  rw [absoluteDefectThreshold, Int.toNat_eq_zero]
  omega

theorem coe_absoluteDefectThreshold_eq_neg_of_neg
    {a : Kˣ} (ha : ordUnit K a < 0) :
    (absoluteDefectThreshold a : Int) = -ordUnit K a := by
  rw [absoluteDefectThreshold, Int.toNat_of_nonneg]
  omega

private theorem normalizedError_eq_div_sub_sq (a : Kˣ) (x : K) :
    1 - x ^ 2 / (a : K) = ((a : K) - x ^ 2) / (a : K) := by
  field_simp [Units.ne_zero a]

/-- The absolute defect is integral exactly when some square approximation
has integral absolute error. -/
theorem hasNonnegativeAbsoluteQuadraticDefect_iff_exists_sub_sq_mem
    (a : Kˣ) :
    HasNonnegativeAbsoluteQuadraticDefect a ↔
      ∃ x : K, (a : K) - x ^ 2 ∈ IntegerRing K := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, (mem_integerRing_iff K).2 ?_⟩
    change 0 ≤ ord K ((a : K) - x ^ 2)
    rw [normalizedError_eq_div_sub_sq, div_eq_mul_inv,
      ord_mul, AddValuation.map_inv, ← coe_ordUnit] at hx
    have hthreshold :
        0 ≤ (absoluteDefectThreshold a : Int) + ordUnit K a := by
      rw [absoluteDefectThreshold]
      omega
    have hshifted :
        (((absoluteDefectThreshold a : Int) + ordUnit K a : Int) :
            WithTop Int) ≤ ord K ((a : K) - x ^ 2) := by
      calc
        (((absoluteDefectThreshold a : Int) + ordUnit K a : Int) :
            WithTop Int) =
            (absoluteDefectThreshold a : WithTop Int) +
              (ordUnit K a : WithTop Int) := by norm_cast
        _ ≤ (ord K ((a : K) - x ^ 2) +
              -(ordUnit K a : WithTop Int)) +
            (ordUnit K a : WithTop Int) :=
          by simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hx (ordUnit K a : WithTop Int)
        _ = ord K ((a : K) - x ^ 2) := by simp [add_assoc]
    have hthresholdTop :
        (0 : WithTop Int) ≤
          (((absoluteDefectThreshold a : Int) + ordUnit K a : Int) :
            WithTop Int) := by
      exact_mod_cast hthreshold
    exact hthresholdTop.trans hshifted
  · rintro ⟨x, hdiff⟩
    by_cases haNonneg : 0 ≤ ordUnit K a
    · rw [HasNonnegativeAbsoluteQuadraticDefect,
        absoluteDefectThreshold_eq_zero_of_nonneg haNonneg]
      exact isQuadraticApproximation_zero K a
    · have haNeg : ordUnit K a < 0 := lt_of_not_ge haNonneg
      refine ⟨x, ?_⟩
      rw [normalizedError_eq_div_sub_sq, div_eq_mul_inv,
        ord_mul, AddValuation.map_inv, ← coe_ordUnit]
      have hdiffOrd : 0 ≤ ord K ((a : K) - x ^ 2) :=
        (mem_integerRing_iff K).1 hdiff
      have hthreshold :=
        coe_absoluteDefectThreshold_eq_neg_of_neg haNeg
      have hthresholdTop :
          (absoluteDefectThreshold a : WithTop Int) =
            -(ordUnit K a : WithTop Int) := by
        exact_mod_cast hthreshold
      rw [hthresholdTop]
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hdiffOrd
          (-(ordUnit K a : WithTop Int))

/-- Order-theoretic form using the supremal relative defect. -/
theorem hasNonnegativeAbsoluteQuadraticDefect_iff_threshold_le
    (a : Kˣ) :
    HasNonnegativeAbsoluteQuadraticDefect a ↔
      (absoluteDefectThreshold a : ℕ∞) ≤ quadraticDefect K a :=
  isQuadraticApproximation_iff_le_defect K

end Bong.Dyadic
