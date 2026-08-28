/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9325FundamentalMonotonicity

/-!
# Norm groups and valuation-unit squares

Multiplication by the square of a valuation unit preserves the scalar norm
group of every lattice.  This elementary fact is the bookkeeping device
needed when two Jordan scale generators have the same valuation but are not
definitionally the same unit.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- A norm-group value remains a norm-group value after multiplication by
the square of a valuation unit. -/
theorem sq_mul_mem_normGroupSet_of_ordUnit_eq_zero
    (c : Kˣ) (hc : ordUnit K c = 0) {z : K}
    (hz : z ∈ normGroupSet q L) :
    ((c ^ 2 : Kˣ) : K) * z ∈ normGroupSet q L := by
  have hcUnit : IsValuationUnit K (c : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K c).2 hc
  have hrescale : rescale c L = L :=
    rescale_eq_self_of_isValuationUnit L c hcUnit
  rw [← hrescale]
  exact sq_mul_mem_normGroupSet_rescale c hz

/-- Multiplication by a valuation-unit square is an automorphism of the
scalar norm group. -/
theorem sq_mul_mem_normGroupSet_iff_of_ordUnit_eq_zero
    (c : Kˣ) (hc : ordUnit K c = 0) (z : K) :
    ((c ^ 2 : Kˣ) : K) * z ∈ normGroupSet q L ↔
      z ∈ normGroupSet q L := by
  constructor
  · intro hz
    have hcInv : ordUnit K c⁻¹ = 0 := by
      rw [ordUnit_inv, hc]
      omega
    have hscaled := sq_mul_mem_normGroupSet_of_ordUnit_eq_zero
      c⁻¹ hcInv hz
    have hcancel :
        (((c⁻¹ ^ 2 : Kˣ) : K) *
          (((c ^ 2 : Kˣ) : K) * z)) = z := by
      simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
      change ((c : K)⁻¹ ^ 2) * ((c : K) ^ 2 * z) = z
      rw [← mul_assoc, ← mul_pow]
      simp
    rwa [hcancel] at hscaled
  · exact sq_mul_mem_normGroupSet_of_ordUnit_eq_zero c hc

/-- Two square rescaling factors of the same valuation act identically on
any fixed norm group. -/
theorem sq_mul_mem_normGroupSet_iff_sq_mul_of_ordUnit_eq
    (c d : Kˣ) (hcd : ordUnit K c = ordUnit K d) (z : K) :
    (((c ^ 2 : Kˣ) : K) * z ∈ normGroupSet q L) ↔
      (((d ^ 2 : Kˣ) : K) * z ∈ normGroupSet q L) := by
  let u : Kˣ := d * c⁻¹
  have hu : ordUnit K u = 0 := by
    dsimp only [u]
    rw [ordUnit_mul, ordUnit_inv, hcd]
    omega
  have hfactor : d ^ 2 = u ^ 2 * c ^ 2 := by
    dsimp only [u]
    rw [mul_pow]
    group
  rw [hfactor]
  simp only [Units.val_mul]
  simpa only [mul_assoc] using
    (sq_mul_mem_normGroupSet_iff_of_ordUnit_eq_zero
      (q := q) (L := L) u hu (((c ^ 2 : Kˣ) : K) * z)).symm

end Lattice

end Bong
