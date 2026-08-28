/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaPairedHyperbolicCancellation

/-!
# Changing a generator of a scaled hyperbolic plane

Two units with the same valuation generate the same fractional ideal.  The
coordinate map `(x,y) ↦ ((s/t)x,y)` therefore gives an integral isometry
from the standard lattice in `H_s` to the standard lattice in `H_t`.

The final construction applies this map twice at every level of a paired
hyperbolic tower.  It is the scale-generator normalization needed when two
Jordan splittings have equal scale orders but use different chosen units.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Multiply only the first coordinate of a hyperbolic plane. -/
noncomputable def hyperbolicLeftScaleLinearEquiv (c : Kˣ) :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun x := ![(c : K) * x 0, x 1]
  invFun x := ![((c⁻¹ : Kˣ) : K) * x 0, x 1]
  left_inv x := by
    funext i
    fin_cases i <;> simp [Units.ne_zero]
  right_inv x := by
    funext i
    fin_cases i <;> simp [Units.ne_zero]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp <;> ring

@[simp]
theorem hyperbolicLeftScaleLinearEquiv_zero
    (c : Kˣ) (x : Fin 2 → K) :
    hyperbolicLeftScaleLinearEquiv c x 0 = (c : K) * x 0 :=
  rfl

@[simp]
theorem hyperbolicLeftScaleLinearEquiv_one
    (c : Kˣ) (x : Fin 2 → K) :
    hyperbolicLeftScaleLinearEquiv c x 1 = x 1 :=
  rfl

/-- Equal scale orders give an integral isometry between the two standard
scaled hyperbolic lattices. -/
noncomputable def scaledHyperbolicChangeScaleIsometry
    (s t : Kˣ) (hord : ordUnit K s = ordUnit K t) :
    Isometry (QuadraticSpace.hyperbolicPlane s)
      (QuadraticSpace.hyperbolicPlane t)
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
  let c : Kˣ := s / t
  have hcOrder : ordUnit K c = 0 := by
    dsimp only [c]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, hord]
    omega
  have hcUnit : IsValuationUnit K (c : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K c).2 hcOrder
  have hcInvUnit : IsValuationUnit K ((c⁻¹ : Kˣ) : K) := by
    apply (isValuationUnit_iff_ordUnit_eq_zero K c⁻¹).2
    rw [ordUnit_inv, hcOrder]
    simp
  have hcMem : (c : K) ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 hcUnit.ge
  have hcInvMem : ((c⁻¹ : Kˣ) : K) ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 hcInvUnit.ge
  refine
    { toLinearEquiv := hyperbolicLeftScaleLinearEquiv c
      map_bilin := ?_
      map_mem := ?_ }
  · intro x y
    rw [QuadraticSpace.hyperbolicPlane_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply]
    change (t : K) *
        (((c : K) * x 0) * y 1 + x 1 * ((c : K) * y 0)) = _
    have htc : (t : K) * (c : K) = (s : K) := by
      exact congrArg Units.val (by
        simp [c, div_eq_mul_inv, mul_comm] : t * c = s)
    rw [show (t : K) *
        (((c : K) * x 0) * y 1 + x 1 * ((c : K) * y 0)) =
        ((t : K) * (c : K)) * (x 0 * y 1 + x 1 * y 0) by ring,
      htc]
  · intro x
    rw [mem_omearaPlaneLattice_iff,
      mem_omearaPlaneLattice_iff]
    constructor
    · rintro ⟨hx0, hx1⟩
      exact ⟨(IntegerRing K).mul_mem _ _ hcMem hx0, hx1⟩
    · rintro ⟨hcx0, hx1⟩
      have h := (IntegerRing K).mul_mem _ _ hcInvMem hcx0
      change ((c⁻¹ : Kˣ) : K) * ((c : K) * x 0) ∈ IntegerRing K at h
      have hx0 : x 0 ∈ IntegerRing K := by
        simpa [Units.ne_zero] using h
      exact ⟨hx0, hx1⟩

/-- Change every selected generator in a paired hyperbolic tower, provided
the old and new generators have equal valuation at each level. -/
noncomputable def pairedHyperbolicExtensionChangeScale
    {W : Type v} [AddCommGroup W] [Module K W]
    (q : QuadraticSpace K W) (L : Lattice K W) :
    (t : Nat) → (sourceScale targetScale : Fin t → Kˣ) →
      (∀ i, ordUnit K (sourceScale i) = ordUnit K (targetScale i)) →
      Isometry
        (pairedHyperbolicExtensionForm q t sourceScale)
        (pairedHyperbolicExtensionForm q t targetScale)
        (pairedHyperbolicExtensionLattice L t)
        (pairedHyperbolicExtensionLattice L t)
  | 0, sourceScale, targetScale, _ =>
      Isometry.refl
        (pairedHyperbolicExtensionForm q 0 sourceScale)
        (pairedHyperbolicExtensionLattice L 0)
  | t + 1, sourceScale, targetScale, hord =>
      let head := scaledHyperbolicChangeScaleIsometry
        (sourceScale 0) (targetScale 0) (hord 0)
      let tail := pairedHyperbolicExtensionChangeScale q L t
        (Fin.tail sourceScale) (Fin.tail targetScale)
        (fun i ↦ hord i.succ)
      head.orthogonalProductBasic
        (head.orthogonalProductBasic tail)

end Lattice

end Bong
