/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryExactRealization
import Bong.Lattice.FormRescale

/-!
# Exact BONGs for uniformly scaled binary models

An admissible binary parameter `second / first` gives the standard binary
Gram lattice.  Uniformly rescaling its quadratic form by `first` produces a
binary BONG whose two orthogonal values are literally `first` and `second`.

This is a low-level construction: it depends only on binary realization and
uniform form rescaling, so later paper-specific existence criteria can use it
without introducing a circular import through the 2009 or 2019 theories.
-/

namespace Bong

open Dyadic
open Module

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A chosen integral shear for an admissible binary parameter. -/
noncomputable def scaledBinaryShear (a : Kˣ)
    (ha : IsBinaryParameterAdmissible a) : K :=
  Classical.choose ha

theorem two_mul_scaledBinaryShear_mem
    (a : Kˣ) (ha : IsBinaryParameterAdmissible a) :
    (2 : K) * scaledBinaryShear a ha ∈ IntegerRing K :=
  (Classical.choose_spec ha).1

theorem scaledBinaryShear_sq_add_mem
    (a : Kˣ) (ha : IsBinaryParameterAdmissible a) :
    scaledBinaryShear a ha ^ 2 + (a : K) ∈ IntegerRing K :=
  (Classical.choose_spec ha).2

/-- The binary Gram model with its form uniformly rescaled by `first`. -/
noncomputable def scaledBinaryModelSpace
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    QuadraticSpace K (Fin 2 → K) :=
  QuadraticSpace.rescaleUnit first
    (QuadraticSpace.binaryModel (second / first)
      (scaledBinaryShear (second / first) hadmissible))

/-- The standard integral lattice underlying the scaled binary model. -/
noncomputable abbrev scaledBinaryModelLattice : Lattice K (Fin 2 → K) :=
  binaryModelLattice (K := K)

/-- The canonical second vector in the orthogonal complement of the first
standard vector of the scaled model. -/
noncomputable def scaledBinaryOrthogonalSecond
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (scaledBinaryModelSpace first second hadmissible).vectorOrthogonal
      QuadraticSpace.binaryModelFirst :=
  ⟨QuadraticSpace.binaryModelSecond -
      scaledBinaryShear (second / first) hadmissible •
        QuadraticSpace.binaryModelFirst,
    by
      apply (QuadraticSpace.mem_vectorOrthogonal_iff
        (scaledBinaryModelSpace first second hadmissible)
        QuadraticSpace.binaryModelFirst _).2
      simp only [scaledBinaryModelSpace,
        QuadraticSpace.rescaleUnit_bilin_apply,
        QuadraticSpace.binaryModel_bilin_first_second_sub, mul_zero]⟩

@[simp]
theorem coe_scaledBinaryOrthogonalSecond
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (scaledBinaryOrthogonalSecond first second hadmissible : Fin 2 → K) =
      QuadraticSpace.binaryModelSecond -
        scaledBinaryShear (second / first) hadmissible •
          QuadraticSpace.binaryModelFirst :=
  rfl

theorem scaledBinaryModelFirst_isAnisotropic
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (scaledBinaryModelSpace first second hadmissible).IsAnisotropic
      QuadraticSpace.binaryModelFirst :=
  (binaryModelFirst_isAnisotropic
    (second / first)
    (scaledBinaryShear (second / first) hadmissible)).rescaleUnit first

theorem scaledBinaryOrthogonalSecond_ne_zero
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    scaledBinaryOrthogonalSecond first second hadmissible ≠ 0 := by
  intro hzero
  have hcoe : QuadraticSpace.binaryModelSecond (K := K) -
      scaledBinaryShear (second / first) hadmissible •
        QuadraticSpace.binaryModelFirst = (0 : Fin 2 → K) := by
    change (scaledBinaryOrthogonalSecond first second hadmissible :
      Fin 2 → K) = 0
    simpa using congrArg Subtype.val hzero
  have hvalue := QuadraticSpace.binaryModel_quadratic_second_sub
    (second / first) (scaledBinaryShear (second / first) hadmissible)
  rw [hcoe] at hvalue
  have hratioZero : ((second / first : Kˣ) : K) = 0 := by
    simpa using hvalue.symm
  exact Units.ne_zero (second / first) hratioZero

/-- The canonical basis of the one-dimensional projected space. -/
noncomputable def scaledBinaryProjectedBasis
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    Basis (Fin 1) K
      ((scaledBinaryModelSpace first second hadmissible).vectorOrthogonal
        QuadraticSpace.binaryModelFirst) := by
  let q := scaledBinaryModelSpace first second hadmissible
  let x : Fin 2 → K := QuadraticSpace.binaryModelFirst
  let w : q.vectorOrthogonal x :=
    scaledBinaryOrthogonalSecond first second hadmissible
  have hli : LinearIndependent K (fun _ : Fin 1 ↦ w) :=
    linearIndependent_unique_iff.mpr
      (scaledBinaryOrthogonalSecond_ne_zero first second hadmissible)
  have hdim : Module.finrank K (q.vectorOrthogonal x) = 1 := by
    have h : Module.finrank K (q.vectorOrthogonal x) + 1 = 2 := by
      calc
        Module.finrank K (q.vectorOrthogonal x) + 1 =
            Module.finrank K (Fin 2 → K) :=
          q.finrank_vectorOrthogonal
            (scaledBinaryModelFirst_isAnisotropic
              first second hadmissible)
        _ = 2 := by simp
    omega
  exact basisOfLinearIndependentOfCardEqFinrank'
    (fun _ : Fin 1 ↦ w) hli (by simpa [q, x] using hdim.symm)

@[simp]
theorem scaledBinaryProjectedBasis_apply
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first))
    (i : Fin 1) :
    scaledBinaryProjectedBasis first second hadmissible i =
      scaledBinaryOrthogonalSecond first second hadmissible := by
  rw [scaledBinaryProjectedBasis]
  simp

@[simp]
theorem scaledBinaryOrthogonalSecond_quadratic
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    ((scaledBinaryModelSpace first second hadmissible).orthogonalSpace
      QuadraticSpace.binaryModelFirst
      (scaledBinaryModelFirst_isAnisotropic
        first second hadmissible)).quadratic
        (scaledBinaryOrthogonalSecond first second hadmissible) =
      (second : K) := by
  rw [QuadraticSpace.orthogonalSpace_quadratic]
  change (scaledBinaryModelSpace first second hadmissible).quadratic
      (QuadraticSpace.binaryModelSecond -
        scaledBinaryShear (second / first) hadmissible •
          QuadraticSpace.binaryModelFirst) = (second : K)
  rw [scaledBinaryModelSpace, QuadraticSpace.rescaleUnit_quadratic,
    QuadraticSpace.binaryModel_quadratic_second_sub]
  have hunit : first * (second / first) = second := by
    simp [div_eq_mul_inv]
  exact congrArg (fun z : Kˣ ↦ (z : K)) hunit

/-- Projection of the second standard vector is the canonical orthogonal
second vector. -/
theorem scaledBinary_projection_second
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (scaledBinaryModelSpace first second hadmissible).projectionToOrthogonal
        QuadraticSpace.binaryModelFirst
        (scaledBinaryModelFirst_isAnisotropic first second hadmissible)
        QuadraticSpace.binaryModelSecond =
      scaledBinaryOrthogonalSecond first second hadmissible := by
  apply Subtype.ext
  rw [QuadraticSpace.projectionToOrthogonal_coe,
    QuadraticSpace.orthogonalProjection_apply]
  have hbilin :
      (scaledBinaryModelSpace first second hadmissible).bilin
          QuadraticSpace.binaryModelFirst
          QuadraticSpace.binaryModelSecond =
        (first : K) * scaledBinaryShear (second / first) hadmissible := by
    simp only [scaledBinaryModelSpace,
      QuadraticSpace.rescaleUnit_bilin_apply,
      QuadraticSpace.binaryModel_bilin_first_second]
  have hquadratic :
      (scaledBinaryModelSpace first second hadmissible).quadratic
          QuadraticSpace.binaryModelFirst = (first : K) := by
    simp [scaledBinaryModelSpace]
  rw [hbilin, hquadratic, coe_scaledBinaryOrthogonalSecond]
  rw [mul_div_cancel_left₀ _ (Units.ne_zero first)]

/-- The projected scaled model lattice is generated by the canonical second
vector. -/
theorem scaledBinary_projectedLattice
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (scaledBinaryModelLattice (K := K)).projectedLattice
        (scaledBinaryModelSpace first second hadmissible)
        QuadraticSpace.binaryModelFirst
        (scaledBinaryModelFirst_isAnisotropic first second hadmissible) =
      Lattice.basisLattice
        (scaledBinaryProjectedBasis first second hadmissible) := by
  apply Lattice.ext
  change
    (Submodule.span (IntegerRing K)
        (Set.range (binaryModelBasis (K := K)))).map
        ((QuadraticSpace.projectionToOrthogonal
            (scaledBinaryModelSpace first second hadmissible)
            QuadraticSpace.binaryModelFirst
            (scaledBinaryModelFirst_isAnisotropic
              first second hadmissible)).restrictScalars (IntegerRing K)) =
      Submodule.span (IntegerRing K)
        (Set.range (scaledBinaryProjectedBasis first second hadmissible))
  rw [Submodule.map_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change
        (scaledBinaryModelSpace first second hadmissible).projectionToOrthogonal
            QuadraticSpace.binaryModelFirst
            (scaledBinaryModelFirst_isAnisotropic first second hadmissible)
            (binaryModelBasis (K := K) 0) ∈ _
      rw [binaryModelBasis_zero]
      have hzero :
          (scaledBinaryModelSpace first second hadmissible).projectionToOrthogonal
              QuadraticSpace.binaryModelFirst
              (scaledBinaryModelFirst_isAnisotropic first second hadmissible)
              QuadraticSpace.binaryModelFirst = 0 := by
        apply Subtype.ext
        exact (scaledBinaryModelSpace first second hadmissible).orthogonalProjection_self
          (scaledBinaryModelFirst_isAnisotropic first second hadmissible)
      rw [hzero]
      exact Submodule.zero_mem _
    · have hj : j = 0 := Subsingleton.elim j 0
      subst j
      change
        (scaledBinaryModelSpace first second hadmissible).projectionToOrthogonal
            QuadraticSpace.binaryModelFirst
            (scaledBinaryModelFirst_isAnisotropic first second hadmissible)
            (binaryModelBasis (K := K) 1) ∈ _
      rw [binaryModelBasis_one, scaledBinary_projection_second]
      exact Submodule.subset_span
        ⟨0, scaledBinaryProjectedBasis_apply
          first second hadmissible 0⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    apply Submodule.subset_span
    refine ⟨QuadraticSpace.binaryModelSecond,
      ⟨1, binaryModelBasis_one⟩, ?_⟩
    change
      (scaledBinaryModelSpace first second hadmissible).projectionToOrthogonal
          QuadraticSpace.binaryModelFirst
          (scaledBinaryModelFirst_isAnisotropic first second hadmissible)
          QuadraticSpace.binaryModelSecond =
        scaledBinaryProjectedBasis first second hadmissible 0
    rw [scaledBinary_projection_second, scaledBinaryProjectedBasis_apply]

/-- The exact scaled binary model BONG. -/
noncomputable def scaledBinaryExactBONG
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    BONG (Fin 2 → K)
      (scaledBinaryModelSpace first second hadmissible)
      (scaledBinaryModelLattice (K := K)) 2 := by
  let q := scaledBinaryModelSpace first second hadmissible
  let x : Fin 2 → K := QuadraticSpace.binaryModelFirst
  let hx := scaledBinaryModelFirst_isAnisotropic
    first second hadmissible
  let tailQ := q.orthogonalSpace x hx
  let tailBasis := scaledBinaryProjectedBasis first second hadmissible
  have htailOrthogonal : tailQ.bilin.iIsOrtho tailBasis := by
    rw [LinearMap.BilinForm.iIsOrtho_def]
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have htailNe : tailQ.quadratic (tailBasis 0) ≠ 0 := by
    rw [scaledBinaryProjectedBasis_apply,
      scaledBinaryOrthogonalSecond_quadratic]
    exact Units.ne_zero second
  let tailBONG := ofOrthogonalBasisFinOne tailQ tailBasis
    htailOrthogonal htailNe
  have generator : Lattice.IsNormGenerator q
      (scaledBinaryModelLattice (K := K)) x := by
    exact (binaryModelFirst_isNormGenerator
      (second / first)
      (scaledBinaryShear (second / first) hadmissible)
      (two_mul_scaledBinaryShear_mem (second / first) hadmissible)
      (scaledBinaryShear_sq_add_mem (second / first) hadmissible)).rescaleQuadraticUnit
        first
  exact BONG.cons x generator hx
    (tailBONG.castLattice
      (scaledBinary_projectedLattice first second hadmissible).symm)

@[simp]
theorem scaledBinaryExactBONG_ambientVector_zero
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (scaledBinaryExactBONG first second hadmissible).ambientVector 0 =
      QuadraticSpace.binaryModelFirst := by
  rw [scaledBinaryExactBONG, ambientVector_cons_zero]

@[simp]
theorem scaledBinaryExactBONG_ambientVector_one
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (scaledBinaryExactBONG first second hadmissible).ambientVector 1 =
      QuadraticSpace.binaryModelSecond -
        scaledBinaryShear (second / first) hadmissible •
          QuadraticSpace.binaryModelFirst := by
  change (scaledBinaryExactBONG first second hadmissible).ambientVector
      (Fin.succ 0) = _
  rw [scaledBinaryExactBONG, ambientVector_cons_succ,
    ambientVector_castLattice, ambientVector_ofOrthogonalBasisFinOne,
    scaledBinaryProjectedBasis_apply]
  rfl

@[simp]
theorem scaledBinaryExactBONG_value_zero
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (scaledBinaryExactBONG first second hadmissible).value 0 =
      (first : K) := by
  rw [← quadratic_ambientVector,
    scaledBinaryExactBONG_ambientVector_zero]
  simp [scaledBinaryModelSpace]

@[simp]
theorem scaledBinaryExactBONG_value_one
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (scaledBinaryExactBONG first second hadmissible).value 1 =
      (second : K) := by
  rw [← quadratic_ambientVector,
    scaledBinaryExactBONG_ambientVector_one]
  rw [scaledBinaryModelSpace, QuadraticSpace.rescaleUnit_quadratic,
    QuadraticSpace.binaryModel_quadratic_second_sub]
  have hunit : first * (second / first) = second := by
    simp [div_eq_mul_inv]
  exact congrArg (fun z : Kˣ ↦ (z : K)) hunit

end BONG

end Bong
