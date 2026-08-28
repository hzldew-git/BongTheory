/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.UnitDefectClassification

/-!
# Exact quadratic approximations

These two field-level consequences of the quadratic-defect definition are
used by both the 2003 binary argument and the 2019 residue calculation.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A finite quadratic defect is attained by an approximation whose
normalized error has exactly that order. -/
theorem exists_quadraticApproximation_exact_order
    (q : Kˣ) (hfinite : quadraticDefect K q ≠ ⊤) :
    ∃ x : K,
      ord K (1 - x ^ 2 / (q : K)) =
        (((quadraticDefect K q).toNat : Int) : WithTop Int) := by
  let d := (quadraticDefect K q).toNat
  have happ : IsQuadraticApproximation K q d := by
    apply (isQuadraticApproximation_iff_le_defect K).2
    simpa [d] using (ENat.coe_toNat hfinite).le
  rcases happ with ⟨x, hx⟩
  refine ⟨x, le_antisymm ?_ hx⟩
  by_contra hnotLe
  have hlt : ((d : Int) : WithTop Int) <
      ord K (1 - x ^ 2 / (q : K)) := lt_of_not_ge hnotLe
  have hnext : (((d + 1 : Nat) : Int) : WithTop Int) ≤
      ord K (1 - x ^ 2 / (q : K)) := by
    by_cases htop : ord K (1 - x ^ 2 / (q : K)) = ⊤
    · rw [htop]
      exact le_top
    · obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp htop
      have hdz : (d : Int) < z := by
        apply WithTop.coe_lt_coe.mp
        simpa [hz] using hlt
      rw [← hz]
      apply WithTop.coe_le_coe.mpr
      norm_cast
  have hnextApprox : IsQuadraticApproximation K q (d + 1) :=
    ⟨x, by simpa using hnext⟩
  have hnextDefect :=
    (isQuadraticApproximation_iff_le_defect K).1 hnextApprox
  rw [← ENat.coe_toNat hfinite] at hnextDefect
  have : d + 1 ≤ d := by exact_mod_cast hnextDefect
  omega

/-- A finite quadratic defect of a valuation unit is positive. -/
theorem quadraticDefect_toNat_pos_of_unit_of_ne_top
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    (q : Kˣ) (hq : IsValuationUnit K (q : K))
    (hfinite : quadraticDefect K q ≠ ⊤) :
    0 < (quadraticDefect K q).toNat := by
  have hnonsquare : ¬IsSquare q := by
    intro hsquare
    exact hfinite
      ((quadraticDefect_eq_top_iff_isSquare (K := K) q).2 hsquare)
  have hle := quadraticDefect_le_two_mul_e_of_not_isSquare
    (K := K) hnonsquare
  by_cases hlt : quadraticDefect K q <
      ((2 * ramificationIndex K : Nat) : ℕ∞)
  · rcases quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
        (K := K) q hq hlt with ⟨m, hm⟩
    omega
  · have heq : quadraticDefect K q =
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      le_antisymm hle (not_lt.mp hlt)
    rw [heq]
    simp only [ENat.toNat_coe]
    have hePos := ramificationIndex_pos K
    omega

end BONG

end Bong
