/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.BasisUnits

/-!
# Primitive representatives on one-dimensional subspaces

Every nonzero vector in the ambient space of a full lattice can be rescaled
so that it belongs to the lattice but not to its uniformizer multiple.  This
is the basis-free primitive-vector step used when O'Meara 82:16 is applied to
an isotropic line.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The inverse of a uniformizer is not integral. -/
theorem uniformizer_inv_not_mem_integerRing :
    (uniformizer K)⁻¹ ∉ IntegerRing K := by
  intro hintegral
  have hunitIntegral :
      (((uniformizerUnit K)⁻¹ : Kˣ) : K) ∈ IntegerRing K := by
    simpa using hintegral
  have hnonneg :=
    ordUnit_nonneg_of_mem_integerRing
      ((uniformizerUnit K)⁻¹) hunitIntegral
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    apply WithTop.coe_injective
    simp [ord_uniformizer]
  rw [ordUnit_inv, hpi] at hnonneg
  omega

/-- A nonzero vector can be scaled to a primitive vector of any full
lattice.  Equivalently, every nonzero line meets `L \ uniformizer * L`. -/
theorem exists_unit_smul_mem_not_mem_uniformizer_rescale
    (L : Lattice K V) {z : V} (hz : z ≠ 0) :
    ∃ t : Kˣ, (t : K) • z ∈ L ∧
      (t : K) • z ∉ rescale (uniformizerUnit K) L := by
  classical
  letI := Fintype.ofFinite L.BasisIndex
  let b := L.ambientBasis
  let c := b.repr z
  have hcne : c ≠ 0 := by
    intro hc
    apply hz
    apply b.repr.injective
    simp [c, hc]
  have hsupport : c.support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr hcne
  let S := c.support.attach
  have hS : S.Nonempty := by
    rcases hsupport with ⟨i, hi⟩
    exact ⟨⟨i, hi⟩, by simp [S]⟩
  let coefficientUnit : {i // i ∈ c.support} → Kˣ := fun i =>
    Units.mk0 (c i) (Finsupp.mem_support_iff.mp i.property)
  obtain ⟨j, hjS, hmin⟩ :=
    Finset.exists_min_image S
      (fun i => ordUnit K (coefficientUnit i)) hS
  let t : Kˣ := (coefficientUnit j)⁻¹
  refine ⟨t, ?_, ?_⟩
  · change (t : K) • z ∈ L.toSubmodule
    rw [L.toSubmodule_eq_span_ambientBasis]
    apply (mem_basisLattice_iff_repr_mem_integerRing b ((t : K) • z)).2
    intro i
    by_cases hi : c i = 0
    · simp [b, c, hi]
    · let iS : {i // i ∈ c.support} :=
        ⟨i, Finsupp.mem_support_iff.mpr hi⟩
      have hiS : iS ∈ S := by simp [S, iS]
      have horder : ordUnit K (coefficientUnit j) ≤
          ordUnit K (coefficientUnit iS) := hmin iS hiS
      have hintegralUnit :
          0 ≤ ordUnit K (t * coefficientUnit iS) := by
        simp only [t, ordUnit_mul, ordUnit_inv]
        omega
      rw [show b.repr ((t : K) • z) i = (t : K) * c i by
        simp [c]]
      apply (mem_integerRing_iff K).2
      change (0 : WithTop Int) ≤ ord K ((t : K) * c i)
      have hintegralValue :
          (0 : WithTop Int) ≤ ord K ((t * coefficientUnit iS : Kˣ) : K) := by
        rw [← coe_ordUnit]
        exact_mod_cast hintegralUnit
      simpa [coefficientUnit, iS] using hintegralValue
  · intro hscaled
    rw [mem_rescale_iff] at hscaled
    obtain ⟨y, hy, hyEq⟩ := hscaled
    have hyBasis : y ∈ basisLattice b := by
      change y ∈ L.toSubmodule at hy
      rw [L.toSubmodule_eq_span_ambientBasis] at hy
      exact hy
    have hyIntegral :=
      (mem_basisLattice_iff_repr_mem_integerRing b y).1
        hyBasis j
    have hcoordinate := congrArg (fun w : V => b.repr w j) hyEq
    have hproduct : uniformizer K * b.repr y j = 1 := by
      calc
        uniformizer K * b.repr y j = c j * (c j)⁻¹ := by
          simpa [b, c, t, coefficientUnit, mul_comm] using hcoordinate
        _ = 1 := mul_inv_cancel₀ (Finsupp.mem_support_iff.mp j.property)
    have hcoordinateInv : b.repr y j = (uniformizer K)⁻¹ := by
      apply mul_left_cancel₀ (uniformizer_ne_zero K)
      calc
        uniformizer K * b.repr y j = 1 := hproduct
        _ = uniformizer K * (uniformizer K)⁻¹ := by
          rw [mul_inv_cancel₀ (uniformizer_ne_zero K)]
    rw [hcoordinateInv] at hyIntegral
    exact uniformizer_inv_not_mem_integerRing (K := K) hyIntegral

/-- A scalar carrying a primitive lattice vector back into the lattice is
integral.  This is the basis-free divisibility property needed for the
necessity direction of integral-reflection coefficient criteria. -/
theorem mem_integerRing_of_smul_mem_of_not_mem_uniformizer_rescale
    (L : Lattice K V) {x : V} (hx : x ∈ L)
    (hprimitive : x ∉ rescale (uniformizerUnit K) L)
    (a : K) (hax : a • x ∈ L) :
    a ∈ IntegerRing K := by
  by_cases haZero : a = 0
  · simpa [haZero]
  let au : Kˣ := Units.mk0 a haZero
  by_contra haIntegral
  have haNeg : ordUnit K au < 0 := by
    apply lt_of_not_ge
    intro haNonneg
    apply haIntegral
    apply (mem_integerRing_iff K).2
    change (0 : WithTop Int) ≤ ord K a
    rw [show a = (au : K) by rfl, ← coe_ordUnit]
    exact_mod_cast haNonneg
  let b : Kˣ := (uniformizerUnit K)⁻¹ * au⁻¹
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    apply WithTop.coe_injective
    simp [ord_uniformizer]
  have hbNonneg : 0 ≤ ordUnit K b := by
    dsimp only [b]
    rw [ordUnit_mul, ordUnit_inv, ordUnit_inv, hpi]
    omega
  have hbIntegral : (b : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change (0 : WithTop Int) ≤ ord K (b : K)
    rw [← coe_ordUnit]
    exact_mod_cast hbNonneg
  let bO : IntegerRing K := ⟨(b : K), hbIntegral⟩
  have hscaled := L.smul_mem bO hax
  have hinverse : (((uniformizerUnit K)⁻¹ : Kˣ) : K) • x ∈ L := by
    change (b : K) • (a • x) ∈ L at hscaled
    simpa only [b, au, smul_smul, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0, inv_mul_cancel₀ haZero, mul_assoc,
      mul_one] using hscaled
  apply hprimitive
  have hxScaled := smul_mem_rescale (uniformizerUnit K) L hinverse
  simpa [smul_smul, uniformizer_ne_zero K] using hxScaled

end Lattice

end Bong
