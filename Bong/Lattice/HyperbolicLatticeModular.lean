/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ModularIsometry
import Bong.Lattice.BasisUnits
import Bong.QuadraticSpace.HyperbolicPlane

namespace Bong

open Dyadic Module

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

theorem hyperbolicPlaneLattice_isModular (s : Kˣ) :
    IsModular (QuadraticSpace.hyperbolicPlane s)
      (hyperbolicPlaneLattice (K := K)) s := by
  rw [IsModular]
  apply Lattice.ext
  apply Submodule.ext
  intro x
  change x ∈ dualLattice (QuadraticSpace.hyperbolicPlane s)
      (hyperbolicPlaneLattice (K := K)) ↔
    x ∈ rescale s⁻¹ (hyperbolicPlaneLattice (K := K))
  rw [mem_dualLattice_iff, mem_rescale_iff]
  constructor
  · intro hx
    let e₀ : Fin 2 → K := Pi.single 0 1
    let e₁ : Fin 2 → K := Pi.single 1 1
    have he₀ : e₀ ∈ hyperbolicPlaneLattice (K := K) := by
      rw [hyperbolicPlaneLattice,
        mem_basisLattice_iff_repr_mem_integerRing]
      simp [e₀]
    have he₁ : e₁ ∈ hyperbolicPlaneLattice (K := K) := by
      rw [hyperbolicPlaneLattice,
        mem_basisLattice_iff_repr_mem_integerRing]
      simp [e₁]
    have hx₀ := hx e₁ he₁
    have hx₁ := hx e₀ he₀
    rw [QuadraticSpace.hyperbolicPlane_bilin_apply] at hx₀ hx₁
    simp [e₀, e₁] at hx₀ hx₁
    refine ⟨(s : K) • x, ?_, ?_⟩
    · rw [hyperbolicPlaneLattice,
        mem_basisLattice_iff_repr_mem_integerRing]
      intro i
      fin_cases i
      · simpa using hx₀
      · simpa using hx₁
    · ext i
      simp
  · rintro ⟨z, hz, hzx⟩
    have hzcoord : ∀ i, z i ∈ IntegerRing K := by
      rw [hyperbolicPlaneLattice,
        mem_basisLattice_iff_repr_mem_integerRing] at hz
      exact hz
    have hxcoord : ∀ i, (s : K) * x i = z i := by
      intro i
      have h := congrFun hzx i
      simp only [Pi.smul_apply, Units.val_inv_eq_inv_val] at h
      calc
        (s : K) * x i = (s : K) * ((s : K)⁻¹ * z i) := by
          exact congrArg (fun t : K ↦ (s : K) * t) h.symm
        _ = z i := by field_simp
    intro y hy
    have hycoord : ∀ i, y i ∈ IntegerRing K := by
      rw [hyperbolicPlaneLattice,
        mem_basisLattice_iff_repr_mem_integerRing] at hy
      exact hy
    rw [QuadraticSpace.hyperbolicPlane_bilin_apply]
    rw [mul_add]
    have hzero : (s : K) * (x 0 * y 1) = z 0 * y 1 := by
      rw [← mul_assoc, hxcoord 0]
    have hone : (s : K) * (x 1 * y 0) = z 1 * y 0 := by
      rw [← mul_assoc, hxcoord 1]
    rw [hzero, hone]
    exact (IntegerRing K).add_mem _ _
      ((IntegerRing K).mul_mem _ _ (hzcoord 0) (hycoord 1))
      ((IntegerRing K).mul_mem _ _ (hzcoord 1) (hycoord 0))

end Lattice

end Bong
