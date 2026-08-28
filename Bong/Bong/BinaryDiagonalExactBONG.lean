/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryDiagonalModelBONG
import Bong.Bong.BinaryExactRealization

/-!
# An exact BONG for the scaled binary diagonal model

`binaryDiagonalModelBONG` fixes the first vector but deliberately leaves the
one-dimensional projected generator arbitrary.  That is enough to determine
both orders, but not the second value itself.  The comparison in Beli (2019),
Lemma 9.8 needs the stronger model whose two values are literally the displayed
coefficients.  We construct it here using the canonical orthogonal second
vector of the binary Gram model.
-/

namespace Bong

open Dyadic
open Module

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The canonical second vector in the orthogonal complement of the first
vector of the scaled binary diagonal model. -/
noncomputable def binaryDiagonalOrthogonalSecond
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalModelSpace first second hadmissible).vectorOrthogonal
      QuadraticSpace.binaryModelFirst :=
  ⟨QuadraticSpace.binaryModelSecond -
      admissibleBinaryShear (second / first) hadmissible •
        QuadraticSpace.binaryModelFirst,
    by
      apply (QuadraticSpace.mem_vectorOrthogonal_iff
        (binaryDiagonalModelSpace first second hadmissible)
        QuadraticSpace.binaryModelFirst _).2
      simp only [binaryDiagonalModelSpace,
        QuadraticSpace.rescaleUnit_bilin_apply,
        QuadraticSpace.binaryModel_bilin_first_second_sub, mul_zero]⟩

/-- The first standard vector remains anisotropic after scaling the binary
model by its first coefficient. -/
theorem binaryDiagonalModelFirst_isAnisotropic
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalModelSpace first second hadmissible).IsAnisotropic
      QuadraticSpace.binaryModelFirst :=
  QuadraticSpace.IsAnisotropic.rescaleUnit
    (binaryModelFirst_isAnisotropic
      (second / first)
      (admissibleBinaryShear (second / first) hadmissible)) first

@[simp]
theorem coe_binaryDiagonalOrthogonalSecond
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalOrthogonalSecond first second hadmissible : Fin 2 → K) =
      QuadraticSpace.binaryModelSecond -
        admissibleBinaryShear (second / first) hadmissible •
          QuadraticSpace.binaryModelFirst :=
  rfl

theorem binaryDiagonalOrthogonalSecond_ne_zero
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    binaryDiagonalOrthogonalSecond first second hadmissible ≠ 0 := by
  intro hzero
  have hcoe : QuadraticSpace.binaryModelSecond (K := K) -
      admissibleBinaryShear (second / first) hadmissible •
        QuadraticSpace.binaryModelFirst (K := K) =
      (0 : Fin 2 → K) := by
    change (binaryDiagonalOrthogonalSecond first second hadmissible :
      Fin 2 → K) = 0
    simpa using congrArg Subtype.val hzero
  have hvalue := QuadraticSpace.binaryModel_quadratic_second_sub
    (second / first) (admissibleBinaryShear (second / first) hadmissible)
  rw [hcoe] at hvalue
  have hratioZero : ((second / first : Kˣ) : K) = 0 := by
    simpa using hvalue.symm
  exact Units.ne_zero (second / first) hratioZero

/-- The canonical one-dimensional basis of the scaled model orthogonal
complement. -/
noncomputable def binaryDiagonalProjectedBasis
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    Basis (Fin 1) K
      ((binaryDiagonalModelSpace first second hadmissible).vectorOrthogonal
        QuadraticSpace.binaryModelFirst) := by
  let q := binaryDiagonalModelSpace first second hadmissible
  let x : Fin 2 → K := QuadraticSpace.binaryModelFirst
  let w : q.vectorOrthogonal x :=
    binaryDiagonalOrthogonalSecond first second hadmissible
  have hli : LinearIndependent K (fun _ : Fin 1 => w) :=
    linearIndependent_unique_iff.mpr
      (binaryDiagonalOrthogonalSecond_ne_zero first second hadmissible)
  have hdim : Module.finrank K (q.vectorOrthogonal x) = 1 := by
    have h : Module.finrank K (q.vectorOrthogonal x) + 1 = 2 := by
      calc
        Module.finrank K (q.vectorOrthogonal x) + 1 =
            Module.finrank K (Fin 2 → K) :=
          q.finrank_vectorOrthogonal
            (binaryDiagonalModelFirst_isAnisotropic
              first second hadmissible)
        _ = 2 := by simp
    omega
  exact basisOfLinearIndependentOfCardEqFinrank'
    (fun _ : Fin 1 => w) hli (by simpa [q, x] using hdim.symm)

@[simp]
theorem binaryDiagonalProjectedBasis_apply
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first))
    (i : Fin 1) :
    binaryDiagonalProjectedBasis first second hadmissible i =
      binaryDiagonalOrthogonalSecond first second hadmissible := by
  rw [binaryDiagonalProjectedBasis]
  simp

@[simp]
theorem binaryDiagonalOrthogonalSecond_quadratic
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    ((binaryDiagonalModelSpace first second hadmissible).orthogonalSpace
      QuadraticSpace.binaryModelFirst
      (binaryDiagonalModelFirst_isAnisotropic
        first second hadmissible)).quadratic
        (binaryDiagonalOrthogonalSecond first second hadmissible) =
      (second : K) := by
  rw [QuadraticSpace.orthogonalSpace_quadratic]
  change (binaryDiagonalModelSpace first second hadmissible).quadratic
      (QuadraticSpace.binaryModelSecond -
        admissibleBinaryShear (second / first) hadmissible •
          QuadraticSpace.binaryModelFirst) = (second : K)
  rw [binaryDiagonalModelSpace,
    QuadraticSpace.rescaleUnit_quadratic,
    QuadraticSpace.binaryModel_quadratic_second_sub]
  have hunit : first * (second / first) = second := by
    simp [div_eq_mul_inv]
  exact congrArg (fun z : Kˣ => (z : K)) hunit

/-- Projection of the second standard vector is the canonical orthogonal
second vector in the scaled model. -/
theorem binaryDiagonal_projection_second
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalModelSpace first second hadmissible).projectionToOrthogonal
        QuadraticSpace.binaryModelFirst
        (binaryDiagonalModelFirst_isAnisotropic
          first second hadmissible)
        QuadraticSpace.binaryModelSecond =
      binaryDiagonalOrthogonalSecond first second hadmissible := by
  apply Subtype.ext
  rw [QuadraticSpace.projectionToOrthogonal_coe,
    QuadraticSpace.orthogonalProjection_apply]
  have hbilin :
      (binaryDiagonalModelSpace first second hadmissible).bilin
          QuadraticSpace.binaryModelFirst
          QuadraticSpace.binaryModelSecond =
        (first : K) *
          admissibleBinaryShear (second / first) hadmissible := by
    simp only [binaryDiagonalModelSpace,
      QuadraticSpace.rescaleUnit_bilin_apply,
      QuadraticSpace.binaryModel_bilin_first_second]
  rw [hbilin,
    binaryDiagonalModelSpace_quadratic_first,
    coe_binaryDiagonalOrthogonalSecond]
  rw [mul_div_cancel_left₀ _ (Units.ne_zero first)]

/-- The projected scaled binary model lattice is generated by the canonical
orthogonal second vector. -/
theorem binaryDiagonal_projectedLattice
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalModelLattice (K := K)).projectedLattice
        (binaryDiagonalModelSpace first second hadmissible)
        QuadraticSpace.binaryModelFirst
        (binaryDiagonalModelFirst_isAnisotropic
          first second hadmissible) =
      Lattice.basisLattice
        (binaryDiagonalProjectedBasis first second hadmissible) := by
  apply Lattice.ext
  change
    (Submodule.span (IntegerRing K)
        (Set.range (binaryModelBasis (K := K)))).map
        ((QuadraticSpace.projectionToOrthogonal
            (binaryDiagonalModelSpace first second hadmissible)
            QuadraticSpace.binaryModelFirst
            (binaryDiagonalModelFirst_isAnisotropic
              first second hadmissible)).restrictScalars (IntegerRing K)) =
      Submodule.span (IntegerRing K)
        (Set.range
          (binaryDiagonalProjectedBasis first second hadmissible))
  rw [Submodule.map_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · change
        QuadraticSpace.projectionToOrthogonal
            (binaryDiagonalModelSpace first second hadmissible)
            QuadraticSpace.binaryModelFirst
              (binaryDiagonalModelFirst_isAnisotropic
                first second hadmissible)
              (binaryModelBasis (K := K) 0) ∈ _
      rw [binaryModelBasis_zero]
      have hzero :
          QuadraticSpace.projectionToOrthogonal
              (binaryDiagonalModelSpace first second hadmissible)
              QuadraticSpace.binaryModelFirst
                (binaryDiagonalModelFirst_isAnisotropic
                  first second hadmissible)
                QuadraticSpace.binaryModelFirst = 0 := by
        apply Subtype.ext
        exact QuadraticSpace.orthogonalProjection_self
          (binaryDiagonalModelSpace first second hadmissible)
          (binaryDiagonalModelFirst_isAnisotropic
            first second hadmissible)
      rw [hzero]
      exact Submodule.zero_mem _
    · have hj : j = 0 := Subsingleton.elim j 0
      subst j
      change
        QuadraticSpace.projectionToOrthogonal
            (binaryDiagonalModelSpace first second hadmissible)
            QuadraticSpace.binaryModelFirst
              (binaryDiagonalModelFirst_isAnisotropic
                first second hadmissible)
              (binaryModelBasis (K := K) 1) ∈ _
      rw [binaryModelBasis_one,
        binaryDiagonal_projection_second]
      exact Submodule.subset_span
        ⟨0, binaryDiagonalProjectedBasis_apply
          first second hadmissible 0⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    apply Submodule.subset_span
    refine ⟨QuadraticSpace.binaryModelSecond,
      ⟨1, binaryModelBasis_one⟩, ?_⟩
    change
      QuadraticSpace.projectionToOrthogonal
          (binaryDiagonalModelSpace first second hadmissible)
          QuadraticSpace.binaryModelFirst
            (binaryDiagonalModelFirst_isAnisotropic
              first second hadmissible)
            QuadraticSpace.binaryModelSecond =
        binaryDiagonalProjectedBasis first second hadmissible 0
    rw [binaryDiagonal_projection_second,
      binaryDiagonalProjectedBasis_apply]

/-- A BONG of the scaled model whose values are exactly `first` and
`second`. -/
noncomputable def binaryDiagonalExactBONG
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    BONG (Fin 2 → K)
      (binaryDiagonalModelSpace first second hadmissible)
      (binaryDiagonalModelLattice (K := K)) 2 := by
  let q := binaryDiagonalModelSpace first second hadmissible
  let x : Fin 2 → K := QuadraticSpace.binaryModelFirst
  let hx := binaryDiagonalModelFirst_isAnisotropic
    first second hadmissible
  let tailQ := q.orthogonalSpace x hx
  let tailBasis := binaryDiagonalProjectedBasis first second hadmissible
  have htailOrthogonal : tailQ.bilin.iIsOrtho tailBasis := by
    rw [LinearMap.BilinForm.iIsOrtho_def]
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have htailNe : tailQ.quadratic (tailBasis 0) ≠ 0 := by
    rw [binaryDiagonalProjectedBasis_apply,
      binaryDiagonalOrthogonalSecond_quadratic]
    exact Units.ne_zero second
  let tailBONG := ofOrthogonalBasisFinOne tailQ tailBasis
    htailOrthogonal htailNe
  exact BONG.cons x
    ((binaryModelFirst_isNormGenerator
      (second / first)
      (admissibleBinaryShear (second / first) hadmissible)
      (two_mul_admissibleBinaryShear_mem
        (second / first) hadmissible)
      (admissibleBinaryShear_sq_add_mem
        (second / first) hadmissible)).rescaleQuadraticUnit first)
    hx
    (tailBONG.castLattice
      (binaryDiagonal_projectedLattice first second hadmissible).symm)

@[simp]
theorem binaryDiagonalExactBONG_ambientVector_zero
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalExactBONG first second hadmissible).ambientVector 0 =
      QuadraticSpace.binaryModelFirst := by
  rw [binaryDiagonalExactBONG, ambientVector_cons_zero]

@[simp]
theorem binaryDiagonalExactBONG_ambientVector_one
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalExactBONG first second hadmissible).ambientVector 1 =
      QuadraticSpace.binaryModelSecond -
        admissibleBinaryShear (second / first) hadmissible •
          QuadraticSpace.binaryModelFirst := by
  change (binaryDiagonalExactBONG first second hadmissible).ambientVector
      (Fin.succ 0) = _
  rw [binaryDiagonalExactBONG, ambientVector_cons_succ,
    ambientVector_castLattice,
    ambientVector_ofOrthogonalBasisFinOne,
    binaryDiagonalProjectedBasis_apply]
  rfl

@[simp]
theorem binaryDiagonalExactBONG_value_zero
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalExactBONG first second hadmissible).value 0 =
      (first : K) := by
  rw [← quadratic_ambientVector,
    binaryDiagonalExactBONG_ambientVector_zero]
  exact binaryDiagonalModelSpace_quadratic_first
    first second hadmissible

@[simp]
theorem binaryDiagonalExactBONG_value_one
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalExactBONG first second hadmissible).value 1 =
      (second : K) := by
  rw [← quadratic_ambientVector,
    binaryDiagonalExactBONG_ambientVector_one]
  exact binaryDiagonalModelSpace_quadratic_orthogonalSecond
    first second hadmissible

/-- The exact binary model BONG, bundled as a good BONG. -/
noncomputable def binaryDiagonalExactGoodBONG
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    GoodBONG
      (binaryDiagonalModelSpace first second hadmissible)
      (binaryDiagonalModelLattice (K := K)) 2 where
  toBONG := binaryDiagonalExactBONG first second hadmissible
  good := BONG.isGood_binary _

@[simp]
theorem binaryDiagonalExactGoodBONG_valueUnit
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) (i : Fin 2) :
    (binaryDiagonalExactGoodBONG first second hadmissible).valueUnit i =
      ![first, second] i := by
  apply Units.ext
  fin_cases i
  · exact binaryDiagonalExactBONG_value_zero first second hadmissible
  · exact binaryDiagonalExactBONG_value_one first second hadmissible

@[simp]
theorem binaryDiagonalExactGoodBONG_order
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) (i : Fin 2) :
    (binaryDiagonalExactGoodBONG first second hadmissible).order i =
      ![ordUnit K first, ordUnit K second] i := by
  change (binaryDiagonalExactBONG first second hadmissible).order i = _
  rw [BONG.order_eq_ordUnit]
  fin_cases i
  · congr 1
    apply Units.ext
    exact binaryDiagonalExactBONG_value_zero first second hadmissible
  · congr 1
    apply Units.ext
    exact binaryDiagonalExactBONG_value_one first second hadmissible

@[simp]
theorem binaryDiagonalExactGoodBONG_normalizedValue
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) (i : Fin 2) :
    (binaryDiagonalExactGoodBONG first second hadmissible).toBONG.normalizedValue i =
      normalizedUnitPart K (![first, second] i) := by
  unfold normalizedValue normalizedUnitPart
  rw [show
      (binaryDiagonalExactGoodBONG first second hadmissible).toBONG.valueUnit i =
          ![first, second] i by
        exact binaryDiagonalExactGoodBONG_valueUnit
          first second hadmissible i]
  rw [show
      (binaryDiagonalExactGoodBONG first second hadmissible).toBONG.order i =
          ![ordUnit K first, ordUnit K second] i by
        exact binaryDiagonalExactGoodBONG_order
          first second hadmissible i]
  fin_cases i <;> rfl

end BONG

end Bong
