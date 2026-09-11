/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Proposition37
import Bong.Bong.QuadraticApproximationExact

/-!
# He--Hu (2024), Remark 3.8

This file records the normalization of unit square-class representatives used
in Theorem 1.2 and the two generic binary rows displayed in Remark 3.8.

The relative quadratic defect is transported from `ℕ∞` to the value group
`ℤ ∪ {∞}` so that the square class represented by `1` retains the equality
`d(1) = ord(1 - 1) = ∞`.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The quadratic-defect order embedded in the field's integral value group. -/
noncomputable def quadraticDefectIntOrder (a : Kˣ) : WithTop Int :=
  WithTop.map (fun n : Nat => (n : Int)) (quadraticDefect K a)

/-- A unit representative of the square class of `epsilon`, normalized as in
He--Hu, Remark 3.8. -/
def IsHeHuNormalizedUnitRepresentative (epsilon delta : Kˣ) : Prop :=
  IsValuationUnit K (delta : K) ∧
    IsSquare (epsilon / delta) ∧
      quadraticDefectIntOrder (K := K) delta =
        ord K ((delta : K) - 1)

/-- Every unit square class has a representative satisfying
`d(delta) = ord(delta - 1)`.  This is the existence assertion in Remark 3.8.
-/
theorem exists_heHuNormalizedUnitRepresentative
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    (epsilon : Kˣ) (hepsilon : IsValuationUnit K (epsilon : K)) :
    ∃ delta : Kˣ, IsHeHuNormalizedUnitRepresentative epsilon delta := by
  by_cases hepsilonSquare : IsSquare epsilon
  · refine ⟨1, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · simp [IsValuationUnit]
    · simpa using hepsilonSquare
    · have honeSquare : IsSquare (1 : Kˣ) := ⟨1, by simp⟩
      simp [quadraticDefectIntOrder,
        quadraticDefect_eq_top_of_isSquare (K := K) honeSquare,
        ord_zero]
      exact rfl
  · have hfinite : quadraticDefect K epsilon ≠ ⊤ := by
      exact ((quadraticDefect_eq_top_iff_isSquare
        (K := K) epsilon).not.mpr hepsilonSquare)
    obtain ⟨x, hxExact⟩ :=
      BONG.exists_quadraticApproximation_exact_order epsilon hfinite
    have hdPos : 0 < (quadraticDefect K epsilon).toNat :=
      BONG.quadraticDefect_toNat_pos_of_unit_of_ne_top
        epsilon hepsilon hfinite
    have herrorPos :
        0 < ord K (1 - x ^ 2 / (epsilon : K)) := by
      rw [hxExact]
      exact_mod_cast hdPos
    have hquotOrder : ord K (x ^ 2 / (epsilon : K)) = 0 := by
      have hlt : ord K (1 : K) <
          ord K (1 - x ^ 2 / (epsilon : K)) := by
        simpa only [ord_one] using herrorPos
      have hsub := (ord K).map_sub_eq_of_lt_left hlt
      have heq : 1 - (1 - x ^ 2 / (epsilon : K)) =
          x ^ 2 / (epsilon : K) := by ring
      rw [heq] at hsub
      simpa only [ord_one] using hsub
    have hxNe : x ≠ 0 := by
      intro hzero
      rw [hzero] at hquotOrder
      simp at hquotOrder
    let s : Kˣ := Units.mk0 x hxNe
    have hsOrder : ordUnit K s = 0 := by
      have hquotUnit : ordUnit K (s ^ 2 / epsilon) = 0 := by
        apply WithTop.coe_injective
        rw [coe_ordUnit]
        have hval : ((s ^ 2 / epsilon : Kˣ) : K) =
            x ^ 2 / (epsilon : K) := by simp [s]
        rw [hval, hquotOrder]
        rfl
      rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
        ordUnit_pow,
        (isValuationUnit_iff_ordUnit_eq_zero K epsilon).1 hepsilon]
        at hquotUnit
      omega
    let delta : Kˣ := epsilon / s ^ 2
    refine ⟨delta, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [isValuationUnit_iff_ordUnit_eq_zero]
      dsimp [delta]
      rw [
        div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow,
        (isValuationUnit_iff_ordUnit_eq_zero K epsilon).1 hepsilon,
        hsOrder]
      norm_num
    · refine ⟨s, ?_⟩
      dsimp [delta]
      simp [div_eq_mul_inv, pow_two]
    · have hdeltaFactor : delta = epsilon * (s⁻¹) ^ 2 := by
        simp [delta, div_eq_mul_inv, pow_two]
      have hdeltaDefect : quadraticDefect K delta =
          quadraticDefect K epsilon := by
        rw [hdeltaFactor, quadraticDefect_mul_square]
      have hdeltaOrder : ord K (delta : K) = 0 := by
        rw [← coe_ordUnit]
        change ((ordUnit K delta : Int) : WithTop Int) = 0
        dsimp [delta]
        rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
          ordUnit_pow,
          (isValuationUnit_iff_ordUnit_eq_zero K epsilon).1 hepsilon,
          hsOrder]
        norm_num
      have hfield : (delta : K) - 1 =
          (delta : K) * (1 - (s : K) ^ 2 / (epsilon : K)) := by
        have hcancel : (delta : K) * (s : K) ^ 2 = (epsilon : K) := by
          change ((delta * s ^ 2 : Kˣ) : K) = (epsilon : K)
          apply congrArg Units.val
          simp [delta]
        have hone : (delta : K) *
            ((s : K) ^ 2 / (epsilon : K)) = 1 := by
          calc
            (delta : K) * ((s : K) ^ 2 / (epsilon : K)) =
                ((delta : K) * (s : K) ^ 2) / (epsilon : K) := by ring
            _ = (epsilon : K) / (epsilon : K) := by rw [hcancel]
            _ = 1 := div_self (Units.ne_zero epsilon)
        calc
          (delta : K) - 1 = (delta : K) -
              (delta : K) * ((s : K) ^ 2 / (epsilon : K)) := by rw [hone]
          _ = (delta : K) *
              (1 - (s : K) ^ 2 / (epsilon : K)) := by ring
      rw [quadraticDefectIntOrder, hdeltaDefect,
        ← ENat.coe_toNat hfinite]
      change (((quadraticDefect K epsilon).toNat : Int) : WithTop Int) = _
      rw [hfield, ord_mul, hdeltaOrder, zero_add]
      simpa [s] using hxExact.symm

namespace BONG.GoodBONG

/-- The two coefficient rows in Remark 3.8.  Substituting `a = 1` gives
`<1,-delta*pi^(1-d)>`; substituting the sharp unit gives
`<delta#,-delta#*delta*pi^(1-d)>`. -/
theorem heHu2022Remark38_binaryRows
    (a delta : Kˣ) (d : Int) :
    heHuUnitDefectTailValues (K := K) a delta d 0 = a ∧
      heHuUnitDefectTailValues (K := K) a delta d 1 =
        -(a * delta * uniformizerPowerUnit K (1 - d)) := by
  exact ⟨heHuUnitDefectTailValues_zero a delta d,
    heHuUnitDefectTailValues_one a delta d⟩

end BONG.GoodBONG

end Bong
