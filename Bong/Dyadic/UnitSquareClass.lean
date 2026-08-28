/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.QuadraticDefect

/-!
# Square classes modulo valuation-unit squares

Beli's binary invariants naturally take values in
`Kˣ / (𝓞ˣ)²`, rather than in the coarser field square-class group
`Kˣ / (Kˣ)²`.  This file constructs the subgroup of valuation units, its
square subgroup inside `Kˣ`, and the resulting quotient.

## Main definitions

- `valuationUnitSubgroup`: the elements of `Kˣ` of additive valuation zero;
- `valuationUnitSquareSubgroup`: squares of valuation units, viewed in `Kˣ`;
- `UnitSquareClass`: the quotient `Kˣ / (𝓞ˣ)²`;
- `unitSquareClassToSquareClass`: the canonical map to `Kˣ / (Kˣ)²`.
-/

namespace Bong.Dyadic

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K]

/-- The subgroup of nonzero elements having additive valuation zero. -/
noncomputable def valuationUnitSubgroup : Subgroup Kˣ where
  carrier := {a | IsValuationUnit K (a : K)}
  one_mem' := by simp [IsValuationUnit]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, IsValuationUnit] at ha hb ⊢
    simp [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, IsValuationUnit] at ha ⊢
    simp [AddValuation.map_inv, ha]

@[simp]
theorem mem_valuationUnitSubgroup_iff (a : Kˣ) :
    a ∈ valuationUnitSubgroup K ↔ IsValuationUnit K (a : K) :=
  Iff.rfl

/-- Squares of valuation units, embedded back into the full multiplicative group. -/
noncomputable def valuationUnitSquareSubgroup : Subgroup Kˣ :=
  (Subgroup.square (valuationUnitSubgroup K)).map (valuationUnitSubgroup K).subtype

theorem mem_valuationUnitSquareSubgroup_iff (a : Kˣ) :
    a ∈ valuationUnitSquareSubgroup K ↔
      ∃ u : Kˣ, IsValuationUnit K (u : K) ∧ u ^ 2 = a := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    change IsSquare u at hu
    rcases hu with ⟨v, hv⟩
    refine ⟨v, v.property, ?_⟩
    simpa [pow_two] using
      (congrArg ((↑) : valuationUnitSubgroup K → Kˣ) hv).symm
  · rintro ⟨u, hu, rfl⟩
    let v : valuationUnitSubgroup K := ⟨u, hu⟩
    refine ⟨v ^ 2, ?_, ?_⟩
    · exact (Subgroup.mem_square).2 ⟨v, pow_two v⟩
    · rfl

/-- Every valuation-unit square is, in particular, a field square. -/
theorem valuationUnitSquareSubgroup_le_square :
    valuationUnitSquareSubgroup K ≤ Subgroup.square Kˣ := by
  intro a ha
  rw [mem_valuationUnitSquareSubgroup_iff] at ha
  rcases ha with ⟨u, _, rfl⟩
  exact (Subgroup.mem_square).2 ⟨u, pow_two u⟩

/-- Beli's refined square-class group `Kˣ / (𝓞ˣ)²`. -/
abbrev UnitSquareClass := Kˣ ⧸ valuationUnitSquareSubgroup K

/-- The refined square class represented by a nonzero field element. -/
noncomputable def unitSquareClass (a : Kˣ) : UnitSquareClass K :=
  QuotientGroup.mk' (valuationUnitSquareSubgroup K) a

@[simp]
theorem unitSquareClass_one : unitSquareClass K 1 = 1 :=
  rfl

@[simp]
theorem unitSquareClass_mul (a b : Kˣ) :
    unitSquareClass K (a * b) = unitSquareClass K a * unitSquareClass K b :=
  rfl

/-- Multiplication by the square of a valuation unit does not change the refined class. -/
theorem unitSquareClass_mul_unit_square (a u : Kˣ)
    (hu : IsValuationUnit K (u : K)) :
    unitSquareClass K (a * u ^ 2) = unitSquareClass K a := by
  change QuotientGroup.mk' (valuationUnitSquareSubgroup K) (a * u ^ 2) =
    QuotientGroup.mk' (valuationUnitSquareSubgroup K) a
  rw [QuotientGroup.mk'_eq_mk']
  refine ⟨u⁻¹ ^ 2, ?_, ?_⟩
  · rw [mem_valuationUnitSquareSubgroup_iff]
    refine ⟨u⁻¹, ?_, rfl⟩
    simpa [IsValuationUnit, AddValuation.map_inv, hu]
  · simp [mul_assoc]

/-- Equality modulo valuation-unit squares preserves additive valuation. -/
theorem ordUnit_eq_of_unitSquareClass_eq {a b : Kˣ}
    (h : unitSquareClass K a = unitSquareClass K b) :
    ordUnit K a = ordUnit K b := by
  change QuotientGroup.mk' (valuationUnitSquareSubgroup K) a =
    QuotientGroup.mk' (valuationUnitSquareSubgroup K) b at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  rcases h with ⟨z, hz, haz⟩
  rw [mem_valuationUnitSquareSubgroup_iff] at hz
  rcases hz with ⟨u, hu, rfl⟩
  have huOrder : ordUnit K u = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K u).1 hu
  have hord := congrArg (ordUnit K) haz
  simpa [huOrder] using hord

/-- Forgetting the valuation-unit refinement gives the ordinary field square class. -/
noncomputable def unitSquareClassToSquareClass : UnitSquareClass K →* SquareClass K :=
  QuotientGroup.map (valuationUnitSquareSubgroup K) (Subgroup.square Kˣ)
    (MonoidHom.id Kˣ) (valuationUnitSquareSubgroup_le_square K)

@[simp]
theorem unitSquareClassToSquareClass_apply (a : Kˣ) :
    unitSquareClassToSquareClass K (unitSquareClass K a) = squareClass K a :=
  rfl

end Bong.Dyadic
