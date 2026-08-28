/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaGeneralPlaneChangeOfComplement
import Bong.Lattice.Omeara9318EvenParity

/-!
# Absorbing a unimodular O'Meara plane into a norm group

If both displayed diagonal coefficients of an integral unimodular plane
belong to the norm group of another positive-rank unimodular lattice, then
all norms of the plane do.  The mixed term and the error ideal are both
contained in `2 O`, hence are already in the target norm group.  This is
the elementary norm calculation used in the determinant correction of
O'Meara 93:28.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The entire norm group of an integral unimodular general plane is
absorbed once its two diagonal coefficients are in the target norm group. -/
theorem normGroupSet_omearaGeneralPlane_subset_of_coefficients_mem
    (alpha beta : K) (hnondegenerate : alpha * beta ≠ 1)
    (halpha : alpha ∈ IntegerRing K)
    (hbeta : beta ∈ IntegerRing K)
    (hdet : IsValuationUnit K (alpha * beta - 1))
    (hL : IsModular q L (1 : Kˣ))
    (hpos : 0 < finrank K V)
    (halphaGroup : alpha ∈ normGroupSet q L)
    (hbetaGroup : beta ∈ normGroupSet q L) :
    normGroupSet
        (QuadraticSpace.omearaGeneralPlane alpha beta hnondegenerate)
        (hyperbolicPlaneLattice (K := K)) ⊆
      normGroupSet q L := by
  let p := QuadraticSpace.omearaGeneralPlane alpha beta hnondegenerate
  have hp : IsModular p (hyperbolicPlaneLattice (K := K)) (1 : Kˣ) :=
    omearaGeneralPlane_isModular_one alpha beta hnondegenerate
      halpha hbeta hdet
  have htwo : twoScaleIdeal p (hyperbolicPlaneLattice (K := K)) =
      twoScaleIdeal q L := by
    rw [twoScaleIdeal_eq_principalIdeal_two_of_unimodular hp (by simp),
      twoScaleIdeal_eq_principalIdeal_two_of_unimodular hL hpos]
  intro z hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  have hxCoordinates := (mem_omearaPlaneLattice_iff x).mp hx
  let x0 : IntegerRing K := ⟨x 0, hxCoordinates.1⟩
  let x1 : IntegerRing K := ⟨x 1, hxCoordinates.2⟩
  have hleft : alpha * x 0 ^ 2 ∈ normGroupSet q L := by
    have h := integralSquare_mul_mem_normGroupSet q L halphaGroup x0
    simpa only [x0, mul_comm] using h
  have hright : beta * x 1 ^ 2 ∈ normGroupSet q L := by
    have h := integralSquare_mul_mem_normGroupSet q L hbetaGroup x1
    simpa only [x1, mul_comm] using h
  have hcrossIdeal : (2 : K) * (x 0 * x 1) ∈ twoScaleIdeal q L := by
    rw [twoScaleIdeal_eq_principalIdeal_two_of_unimodular hL hpos,
      principalIdeal, Submodule.mem_span_singleton]
    refine ⟨x0 * x1, ?_⟩
    change ((x 0 * x 1 : K)) * 2 = 2 * (x 0 * x 1)
    ring
  have hcross : (2 : K) * x 0 * x 1 ∈ normGroupSet q L := by
    apply twoScaleIdeal_subset_normGroupSet q L
    change (2 : K) * x 0 * x 1 ∈ twoScaleIdeal q L
    simpa only [mul_assoc] using hcrossIdeal
  have hyTarget : y ∈ normGroupSet q L := by
    apply twoScaleIdeal_subset_normGroupSet q L
    rw [← htwo]
    exact hy
  have hquadratic : p.quadratic x =
      alpha * x 0 ^ 2 + (2 : K) * x 0 * x 1 + beta * x 1 ^ 2 := by
    change p.bilin x x = _
    rw [QuadraticSpace.omearaGeneralPlane_bilin_apply]
    ring
  rw [hquadratic]
  exact add_mem_normGroupSet q L
    (add_mem_normGroupSet q L
      (add_mem_normGroupSet q L hleft hcross) hright)
    hyTarget

end Lattice

end Bong
