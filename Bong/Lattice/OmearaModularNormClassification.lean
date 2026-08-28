/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaClassificationFoundations

/-!
# O'Meara 93:16 at an arbitrary modular scale

O'Meara states 93:16 for unimodular lattices and uses it at arbitrary Jordan
scales after rescaling the ambient quadratic form.  This file makes that
normalization explicit.  In particular it proves the form-rescaling formulas
for the integral dual, scale ideal, `2sL`, and norm group, and then derives the
modular form of 93:16 without adding a classification interface.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

/-- Rescaling the quadratic form by `c` rescales the integral dual lattice by
`c⁻¹`. -/
theorem dualLattice_rescaleQuadraticUnit (q : QuadraticSpace K V)
    (c : Kˣ) (L : Lattice K V) :
    dualLattice (q.rescaleUnit c) L = rescale c⁻¹ (dualLattice q L) := by
  apply Lattice.ext
  ext x
  change x ∈ dualLattice (q.rescaleUnit c) L ↔
    x ∈ rescale c⁻¹ (dualLattice q L)
  rw [mem_dualLattice_iff, mem_rescale_iff]
  constructor
  · intro hx
    refine ⟨(c : K) • x, ?_, ?_⟩
    · rw [mem_dualLattice_iff]
      intro y hy
      have h := hx y hy
      simpa only [QuadraticSpace.rescaleUnit_bilin_apply,
        LinearMap.BilinForm.smul_left] using h
    · simp [smul_smul]
  · rintro ⟨z, hz, rfl⟩
    intro y hy
    have h := (mem_dualLattice_iff q L z).1 hz y hy
    simp only [QuadraticSpace.rescaleUnit_bilin_apply,
      LinearMap.BilinForm.smul_left, Units.val_inv_eq_inv_val]
    rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero c), one_mul]
    exact h

/-- Form rescaling multiplies the scale ideal by the same scalar. -/
theorem scaleIdeal_rescaleQuadraticUnit (q : QuadraticSpace K V)
    (c : Kˣ) (L : Lattice K V) :
    scaleIdeal (q.rescaleUnit c) L =
      scalarIdeal (c : K) (scaleIdeal q L) := by
  rw [scaleIdeal, scalarIdeal, scaleIdeal, Submodule.map_span]
  congr 1
  ext z
  simp only [scaleGenerators, Set.mem_range, Set.mem_image,
    coefficientMulLinearMap_apply,
    QuadraticSpace.rescaleUnit_bilin_apply]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨q.bilin (p.1 : V) (p.2 : V),
      ⟨p, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, rfl⟩

/-- Form rescaling multiplies the norm ideal by the same scalar. -/
theorem normIdeal_rescaleQuadraticUnit (q : QuadraticSpace K V)
    (c : Kˣ) (L : Lattice K V) :
    normIdeal (q.rescaleUnit c) L =
      scalarIdeal (c : K) (normIdeal q L) := by
  rw [normIdeal, scalarIdeal, normIdeal, Submodule.map_span]
  congr 1
  ext z
  simp only [normGenerators, Set.mem_range, Set.mem_image,
    coefficientMulLinearMap_apply,
    QuadraticSpace.rescaleUnit_quadratic]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨q.quadratic (x : V), ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

/-- Form rescaling multiplies `2sL` by the same scalar. -/
theorem twoScaleIdeal_rescaleQuadraticUnit (q : QuadraticSpace K V)
    (c : Kˣ) (L : Lattice K V) :
    twoScaleIdeal (q.rescaleUnit c) L =
      scalarIdeal (c : K) (twoScaleIdeal q L) := by
  rw [twoScaleIdeal, scaleIdeal_rescaleQuadraticUnit]
  unfold twiceIdeal scalarIdeal
  have htwo : algebraMap (IntegerRing K) K (2 : IntegerRing K) =
      (2 : K) := by
    change ((2 : IntegerRing K) : K) = (2 : K)
    rfl
  ext z
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨2 * x, ⟨x, hx, ?_⟩, ?_⟩
    · simp only [twoMulLinearMap_apply, Algebra.smul_def, htwo]
    · simp only [twoMulLinearMap_apply, coefficientMulLinearMap_apply,
        Algebra.smul_def, htwo]
      ring
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(c : K) * x, ⟨x, hx, ?_⟩, ?_⟩
    · simp only [coefficientMulLinearMap_apply]
    · simp only [twoMulLinearMap_apply, coefficientMulLinearMap_apply,
        Algebra.smul_def, htwo]
      ring

/-- Membership in a norm group after form rescaling is obtained by dividing
the scalar by the rescaling factor. -/
theorem mem_normGroupSet_rescaleQuadraticUnit_iff
    (q : QuadraticSpace K V) (c : Kˣ) (L : Lattice K V) (z : K) :
    z ∈ normGroupSet (q.rescaleUnit c) L ↔
      ((c⁻¹ : Kˣ) : K) * z ∈ normGroupSet q L := by
  constructor
  · rintro ⟨x, hx, y, hy, hvalue⟩
    rw [twoScaleIdeal_rescaleQuadraticUnit] at hy
    rcases hy with ⟨y₀, hy₀, hyEq⟩
    refine ⟨x, hx, y₀, hy₀, ?_⟩
    rw [hvalue, ← hyEq]
    simp only [QuadraticSpace.rescaleUnit_quadratic,
      coefficientMulLinearMap_apply, Units.val_inv_eq_inv_val]
    change ((c : K)⁻¹) * ((c : K) * q.quadratic x + (c : K) * y₀) =
      q.quadratic x + y₀
    rw [← mul_add, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero c), one_mul]
  · intro hz
    rcases hz with ⟨x, hx, y, hy, hvalue⟩
    refine ⟨x, hx, (c : K) * y, ?_, ?_⟩
    · rw [twoScaleIdeal_rescaleQuadraticUnit]
      exact ⟨y, hy, rfl⟩
    · have hscaled := congrArg (fun w : K ↦ (c : K) * w) hvalue
      have hscaled' :
          (c : K) * ((c : K)⁻¹ * z) =
            (c : K) * (q.quadratic x + y) := by
        simpa only [Units.val_inv_eq_inv_val] using hscaled
      simp only [QuadraticSpace.rescaleUnit_quadratic]
      calc
        z = (c : K) * (((c : K)⁻¹) * z) := by
          field_simp [Units.ne_zero c]
        _ = (c : K) * (q.quadratic x + y) := hscaled'
        _ = (c : K) * q.quadratic x + (c : K) * y := by ring

/-- A scalar norm generator rescales by the same factor as the quadratic
form. -/
theorem IsNormGeneratorValue.rescaleQuadraticUnit
    {a : Kˣ} (ha : IsNormGeneratorValue q L a) (c : Kˣ) :
    IsNormGeneratorValue (q.rescaleUnit c) L (c * a) := by
  constructor
  · rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
    have hcancel : ((c⁻¹ : Kˣ) : K) * ((c * a : Kˣ) : K) = (a : K) := by
      simp
    rw [hcancel]
    exact ha.1
  · rw [normIdeal_rescaleQuadraticUnit, ha.2,
      scalarIdeal, principalIdeal, Submodule.map_span]
    change Submodule.span (IntegerRing K)
        (coefficientMulLinearMap (K := K) (c : K) '' {(a : K)}) =
      Submodule.span (IntegerRing K) {((c : K) * (a : K))}
    rw [Set.image_singleton]
    change Submodule.span (IntegerRing K)
      {coefficientMulLinearMap (K := K) (c : K) (a : K)} = _
    rw [coefficientMulLinearMap_apply]

/-- Conversely, dividing a scalar norm generator by the form-rescaling
factor recovers a generator for the original form. -/
theorem IsNormGeneratorValue.unscaleQuadraticUnit
    {c a : Kˣ} (ha : IsNormGeneratorValue (q.rescaleUnit c) L a) :
    IsNormGeneratorValue q L (c⁻¹ * a) := by
  have h := ha.rescaleQuadraticUnit c⁻¹
  simpa [QuadraticSpace.rescaleUnit] using h

/-- Equality of norm groups is preserved when both forms are rescaled by the
same nonzero scalar. -/
theorem normGroupSet_rescaleQuadraticUnit_eq_iff
    (q : QuadraticSpace K V) (c : Kˣ) (L M : Lattice K V) :
    normGroupSet (q.rescaleUnit c) L =
        normGroupSet (q.rescaleUnit c) M ↔
      normGroupSet q L = normGroupSet q M := by
  constructor <;> intro h <;> ext z
  · have hz := Set.ext_iff.mp h ((c : K) * z)
    rw [mem_normGroupSet_rescaleQuadraticUnit_iff,
      mem_normGroupSet_rescaleQuadraticUnit_iff] at hz
    have hcancel : ((c : K)⁻¹) * ((c : K) * z) = z := by
      field_simp [Units.ne_zero c]
    simpa only [Units.val_inv_eq_inv_val, hcancel] using hz
  · rw [mem_normGroupSet_rescaleQuadraticUnit_iff,
      mem_normGroupSet_rescaleQuadraticUnit_iff, h]

/-- An `s`-modular lattice becomes unimodular after multiplying the ambient
form by `s⁻¹`. -/
theorem IsModular.isUnimodular_rescaleQuadraticInverse
    {s : Kˣ} (hL : IsModular q L s) :
    IsUnimodular (q.rescaleUnit s⁻¹) L := by
  rw [isUnimodular_iff_dualLattice_eq,
    dualLattice_rescaleQuadraticUnit, hL, ← rescale_mul]
  convert rescale_one L using 1
  group

/-- Multiplying the ambient quadratic form by `c` multiplies the modular
parameter by `c`.  This is the unnormalized form of the preceding lemma and
is used to transport the conclusions of O'Meara 93:18 back from scale one. -/
theorem IsModular.rescaleQuadraticUnit
    {s : Kˣ} (hL : IsModular q L s) (c : Kˣ) :
    IsModular (q.rescaleUnit c) L (c * s) := by
  rw [IsModular, dualLattice_rescaleQuadraticUnit, hL,
    ← rescale_mul]
  congr 1
  simp only [mul_inv_rev]
  ac_rfl

section ArbitraryUniverse

variable {X : Type v} [AddCommGroup X] [Module K X]
  {p : QuadraticSpace K X} {A B : Lattice K X}

/-- O'Meara 93:16 at an arbitrary common modular scale. -/
noncomputable def omeara9316_of_modular_normGroupSet_eq
    (s : Kˣ) (hA : IsModular p A s) (hB : IsModular p B s)
    (hgroup : normGroupSet p A = normGroupSet p B) :
    Isometry p p A B := by
  have hA' := hA.isUnimodular_rescaleQuadraticInverse
  have hB' := hB.isUnimodular_rescaleQuadraticInverse
  have hgroup' :
      normGroupSet (p.rescaleUnit s⁻¹) A =
        normGroupSet (p.rescaleUnit s⁻¹) B :=
    (normGroupSet_rescaleQuadraticUnit_eq_iff p s⁻¹ A B).2 hgroup
  let g := omeara9316_of_normGroupSet_eq_universe hA' hB' hgroup'
  exact
    { toLinearEquiv := g.toLinearEquiv
      map_bilin := by
        intro x y
        have h := g.map_bilin x y
        simp only [QuadraticSpace.rescaleUnit_bilin_apply] at h
        exact mul_left_cancel₀ (Units.ne_zero (s⁻¹ : Kˣ)) h
      map_mem := g.map_mem }

/-- Equivalence form of modular O'Meara 93:16. -/
theorem omeara9316_modular
    (s : Kˣ) (hA : IsModular p A s) (hB : IsModular p B s) :
    IsIsometric p p A B ↔ normGroupSet p A = normGroupSet p B := by
  constructor
  · rintro ⟨f⟩
    exact (normGroupSet_eq_of_latticeIsometry f).symm
  · intro hgroup
    exact ⟨omeara9316_of_modular_normGroupSet_eq s hA hB hgroup⟩

end ArbitraryUniverse

end Lattice

end Bong
