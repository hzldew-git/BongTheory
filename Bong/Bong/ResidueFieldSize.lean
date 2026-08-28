/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.Valuation

/-!
# The residue-field size dichotomy used by Beli

Only the operational lift needed in the later defect calculation is exposed.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The elementary residue-field formulation of `|O/p| > 2`: there is a
valuation unit whose residue is neither zero nor one. -/
def HasResidueFieldMoreThanTwoElements : Prop :=
  ∃ ζ : K,
    IsValuationUnit K ζ ∧
      ¬IsInMaximalIdeal K (ζ - 1)

/-- A residue field with more than two elements contains a lift `ζ` for
which both `ζ` and `ζ+1` are valuation units. -/
theorem HasResidueFieldMoreThanTwoElements.exists_unit_add_one_unit
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    ∃ ζ : K,
      IsValuationUnit K ζ ∧ IsValuationUnit K (ζ + 1) := by
  rcases hres with ⟨ζ, hζ, hζneOne⟩
  change ord K ζ = 0 at hζ
  have hsubNonneg : 0 ≤ ord K (ζ - 1) := by
    have hmin := min_ord_le_ord_add K ζ (-(1 : K))
    simpa [sub_eq_add_neg, hζ] using hmin
  have hsubOrder : ord K (ζ - 1) = 0 := by
    exact le_antisymm (not_lt.mp hζneOne) hsubNonneg
  have hplusOrder : ord K (ζ + 1) = 0 := by
    have heq : ζ + 1 = (ζ - 1) + (2 : K) := by ring
    rw [heq]
    have hlt : ord K (ζ - 1) < ord K (2 : K) := by
      rw [hsubOrder]
      exact ord_two_pos K
    simpa [hsubOrder] using (ord K).map_add_eq_of_lt_left hlt
  exact ⟨ζ, hζ, hplusOrder⟩

end BONG

end Bong
