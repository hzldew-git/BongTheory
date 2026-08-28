/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryExactRealization
import Bong.Bong.BinaryShearIsometry
import Bong.Bong.Beli2009QuadraticRepresentation
import Bong.Bong.DiagonalOrthogonalBasis
import Bong.Bong.GoodExistence
import Bong.Bong.Structural
import Bong.Lattice.Product
import Bong.QuadraticSpace.Rescale

/-!
# Explicit unary--binary orthogonal-sum models

The notation `\<c₀\> ⊥ [c₁, c₂]` in Beli's papers denotes more than a
diagonal quadratic space.  The binary lattice is generally not the integral
span of its two orthogonal BONG vectors.  This file therefore packages the
notation as an actual orthogonal sum of

* the standard unary lattice with quadratic value `c₀`, and
* the explicit binary Gram model whose BONG values are `c₁, c₂`.

The shear in the binary Gram model is chosen from the operational
admissibility predicate.  No choice made here changes the mathematical
statement: every chosen shear satisfies the two defining integrality
conditions.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG

/-- The standard rank-one integral lattice in the line `K`. -/
noncomputable def unaryModelLattice : Lattice K K :=
  Lattice.basisLattice (Basis.singleton Unit K)

@[simp]
theorem mem_unaryModelLattice_iff (x : K) :
    x ∈ (unaryModelLattice : Lattice K K) ↔ x ∈ IntegerRing K := by
  change x ∈ Lattice.basisLattice (Basis.singleton Unit K) ↔ _
  rw [Lattice.mem_basisLattice_iff_repr_mem_integerRing]
  simp

/-- A chosen shear witnessing that `a` is an admissible binary parameter. -/
noncomputable def admissibleBinaryShear (a : Kˣ)
    (ha : IsBinaryParameterAdmissible a) : K :=
  Classical.choose ha

theorem two_mul_admissibleBinaryShear_mem
    (a : Kˣ) (ha : IsBinaryParameterAdmissible a) :
    (2 : K) * admissibleBinaryShear a ha ∈ IntegerRing K :=
  (Classical.choose_spec ha).1

theorem admissibleBinaryShear_sq_add_mem
    (a : Kˣ) (ha : IsBinaryParameterAdmissible a) :
    admissibleBinaryShear a ha ^ 2 + (a : K) ∈ IntegerRing K :=
  (Classical.choose_spec ha).2

/-- The concrete binary quadratic space denoted by `[first, second]`.
Its normalized BONG parameter is `second / first`. -/
noncomputable def binaryDiagonalModelSpace
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    QuadraticSpace K (Fin 2 → K) :=
  QuadraticSpace.rescaleUnit first
    (QuadraticSpace.binaryModel (second / first)
      (admissibleBinaryShear (second / first) hadmissible))

/-- The integral lattice underlying `[first, second]`. -/
noncomputable def binaryDiagonalModelLattice : Lattice K (Fin 2 → K) :=
  binaryModelLattice (K := K)

/-- The actual orthogonal-sum quadratic space denoted by
`\<head\> ⊥ [first, second]`. -/
noncomputable def unaryBinaryModelSpace
    (head first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    QuadraticSpace K (K × (Fin 2 → K)) :=
  (QuadraticSpace.rescaleUnit head (QuadraticSpace.line K)).orthogonalSum
    (binaryDiagonalModelSpace first second hadmissible)

/-- The product lattice underlying `\<head\> ⊥ [first, second]`. -/
noncomputable def unaryBinaryModelLattice :
    Lattice K (K × (Fin 2 → K)) :=
  Lattice.product (unaryModelLattice (K := K))
    (binaryDiagonalModelLattice (K := K))

/-- The distinguished vector of the unary summand belongs to the explicit
unary--binary product lattice. -/
theorem unaryBinaryModel_head_mem :
    ((1 : K), (0 : Fin 2 → K)) ∈
      unaryBinaryModelLattice (K := K) := by
  rw [unaryBinaryModelLattice, Lattice.inl_mem_product_iff]
  change (1 : K) ∈ Lattice.basisLattice (Basis.singleton Unit K)
  change (1 : K) ∈ Submodule.span (IntegerRing K)
    (Set.range (Basis.singleton Unit K))
  apply Submodule.subset_span
  refine ⟨Unit.unit, ?_⟩
  simp

@[simp]
theorem binaryDiagonalModelSpace_quadratic_first
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalModelSpace first second hadmissible).quadratic
        QuadraticSpace.binaryModelFirst = (first : K) := by
  simp [binaryDiagonalModelSpace]

@[simp]
theorem binaryDiagonalModelSpace_quadratic_orthogonalSecond
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalModelSpace first second hadmissible).quadratic
        (QuadraticSpace.binaryModelSecond -
          admissibleBinaryShear (second / first) hadmissible •
            QuadraticSpace.binaryModelFirst) = (second : K) := by
  simp only [binaryDiagonalModelSpace,
    QuadraticSpace.rescaleUnit_quadratic,
    QuadraticSpace.binaryModel_quadratic_second_sub]
  rw [Units.val_div_eq_div_val]
  change (first : K) * ((second : K) / (first : K)) = (second : K)
  field_simp [Units.ne_zero first]

@[simp]
theorem unaryBinaryModelSpace_quadratic_head
    (head first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (unaryBinaryModelSpace head first second hadmissible).quadratic
        ((1 : K), (0 : Fin 2 → K)) = (head : K) := by
  simp [QuadraticSpace.quadratic, unaryBinaryModelSpace,
    QuadraticSpace.orthogonalSum]

@[simp]
theorem unaryBinaryModelSpace_quadratic_binaryFirst
    (head first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (unaryBinaryModelSpace head first second hadmissible).quadratic
        ((0 : K), QuadraticSpace.binaryModelFirst) = (first : K) := by
  simpa [QuadraticSpace.quadratic, unaryBinaryModelSpace,
    QuadraticSpace.orthogonalSum] using
      (binaryDiagonalModelSpace_quadratic_first
        first second hadmissible)

@[simp]
theorem unaryBinaryModelSpace_quadratic_binaryOrthogonalSecond
    (head first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (unaryBinaryModelSpace head first second hadmissible).quadratic
        ((0 : K), QuadraticSpace.binaryModelSecond -
          admissibleBinaryShear (second / first) hadmissible •
            QuadraticSpace.binaryModelFirst) = (second : K) := by
  simpa [QuadraticSpace.quadratic, unaryBinaryModelSpace,
    QuadraticSpace.orthogonalSum] using
      (binaryDiagonalModelSpace_quadratic_orthogonalSecond
        first second hadmissible)

/-- The orthogonal basis `e₀, e₁ - c e₀` of the binary Gram model. -/
noncomputable def binaryDiagonalOrthogonalBasis
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    Basis (Fin 2) K (Fin 2 → K) :=
  (binaryModelBasis (K := K)).map
    (binaryShearLinearEquiv
      (-(admissibleBinaryShear (second / first) hadmissible)))

@[simp]
theorem binaryDiagonalOrthogonalBasis_zero
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    binaryDiagonalOrthogonalBasis first second hadmissible 0 =
      QuadraticSpace.binaryModelFirst := by
  ext i
  fin_cases i <;>
    simp [binaryDiagonalOrthogonalBasis,
      binaryShearLinearEquiv_apply_zero,
      binaryShearLinearEquiv_apply_one,
      QuadraticSpace.binaryModelFirst,
      QuadraticSpace.binaryModelSecond]

@[simp]
theorem binaryDiagonalOrthogonalBasis_one
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    binaryDiagonalOrthogonalBasis first second hadmissible 1 =
      QuadraticSpace.binaryModelSecond -
        admissibleBinaryShear (second / first) hadmissible •
          QuadraticSpace.binaryModelFirst := by
  ext i
  fin_cases i <;>
    simp [binaryDiagonalOrthogonalBasis,
      binaryShearLinearEquiv_apply_zero,
      binaryShearLinearEquiv_apply_one,
      QuadraticSpace.binaryModelFirst,
      QuadraticSpace.binaryModelSecond]

/-- The chosen binary basis is orthogonal for the rescaled Gram model. -/
theorem binaryDiagonalOrthogonalBasis_isOrtho
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalModelSpace first second hadmissible).bilin.iIsOrtho
      (binaryDiagonalOrthogonalBasis first second hadmissible) := by
  rw [LinearMap.BilinForm.iIsOrtho_def]
  intro i j hij
  have hfin (k : Fin 2) : k = 0 ∨ k = 1 := by
    rcases (show k.val = 0 ∨ k.val = 1 by omega) with hk | hk
    · left
      exact Fin.ext hk
    · right
      exact Fin.ext hk
  rcases hfin i with rfl | rfl <;> rcases hfin j with rfl | rfl
  · exact (hij rfl).elim
  · rw [binaryDiagonalOrthogonalBasis_zero,
      binaryDiagonalOrthogonalBasis_one]
    simp only [binaryDiagonalModelSpace,
      QuadraticSpace.rescaleUnit_bilin_apply]
    rw [QuadraticSpace.binaryModel_bilin_first_second_sub]
    simp
  · rw [binaryDiagonalOrthogonalBasis_zero,
      binaryDiagonalOrthogonalBasis_one]
    rw [(binaryDiagonalModelSpace first second hadmissible).isSymm.eq]
    simp only [binaryDiagonalModelSpace,
      QuadraticSpace.rescaleUnit_bilin_apply]
    rw [QuadraticSpace.binaryModel_bilin_first_second_sub]
    simp
  · exact (hij rfl).elim

@[simp]
theorem binaryDiagonalOrthogonalBasis_quadratic
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first))
    (i : Fin 2) :
    (binaryDiagonalModelSpace first second hadmissible).quadratic
        (binaryDiagonalOrthogonalBasis first second hadmissible i) =
      ![(first : K), (second : K)] i := by
  have hfin : i = 0 ∨ i = 1 := by
    rcases (show i.val = 0 ∨ i.val = 1 by omega) with hi | hi
    · left
      exact Fin.ext hi
    · right
      exact Fin.ext hi
  rcases hfin with rfl | rfl
  · rw [binaryDiagonalOrthogonalBasis_zero,
      binaryDiagonalModelSpace_quadratic_first]
    rfl
  · rw [binaryDiagonalOrthogonalBasis_one,
      binaryDiagonalModelSpace_quadratic_orthogonalSecond]
    rfl

/-- Indexing `K × K²` by a three-element type in unary--binary order. -/
def unaryBinaryIndexEquiv : Fin 3 ≃ Unit ⊕ Fin 2 :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr finOneEquiv (Equiv.refl (Fin 2)))

@[simp]
theorem unaryBinaryIndexEquiv_zero :
    unaryBinaryIndexEquiv 0 = Sum.inl () := by
  rfl

@[simp]
theorem unaryBinaryIndexEquiv_one :
    unaryBinaryIndexEquiv 1 = Sum.inr 0 := by
  rfl

@[simp]
theorem unaryBinaryIndexEquiv_two :
    unaryBinaryIndexEquiv 2 = Sum.inr 1 := by
  rfl

/-- The full orthogonal basis of `\<head\> ⊥ [first, second]`, ordered as
the coefficient list `![head, first, second]`. -/
noncomputable def unaryBinaryOrthogonalBasis
    (head first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    Basis (Fin 3) K (K × (Fin 2 → K)) :=
  ((Basis.singleton Unit K).prod
      (binaryDiagonalOrthogonalBasis first second hadmissible)).reindex
    unaryBinaryIndexEquiv.symm

@[simp]
theorem unaryBinaryOrthogonalBasis_zero
    (head first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    unaryBinaryOrthogonalBasis head first second hadmissible 0 =
      ((1 : K), (0 : Fin 2 → K)) := by
  simp [unaryBinaryOrthogonalBasis]

@[simp]
theorem unaryBinaryOrthogonalBasis_one
    (head first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    unaryBinaryOrthogonalBasis head first second hadmissible 1 =
      ((0 : K), binaryDiagonalOrthogonalBasis first second hadmissible 0) := by
  simp [unaryBinaryOrthogonalBasis]

@[simp]
theorem unaryBinaryOrthogonalBasis_two
    (head first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    unaryBinaryOrthogonalBasis head first second hadmissible 2 =
      ((0 : K), binaryDiagonalOrthogonalBasis first second hadmissible 1) := by
  simp [unaryBinaryOrthogonalBasis]

/-- The full chosen basis has the three advertised quadratic values. -/
@[simp]
theorem unaryBinaryOrthogonalBasis_quadratic
    (head first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first))
    (i : Fin 3) :
    (unaryBinaryModelSpace head first second hadmissible).quadratic
        (unaryBinaryOrthogonalBasis head first second hadmissible i) =
      ![(head : K), (first : K), (second : K)] i := by
  have hfin : i = 0 ∨ i = 1 ∨ i = 2 := by
    rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 by omega) with
      hi | hi | hi
    · exact Or.inl (Fin.ext hi)
    · exact Or.inr (Or.inl (Fin.ext hi))
    · exact Or.inr (Or.inr (Fin.ext hi))
  rcases hfin with rfl | rfl | rfl
  · rw [unaryBinaryOrthogonalBasis_zero,
      unaryBinaryModelSpace_quadratic_head]
    rfl
  · rw [unaryBinaryOrthogonalBasis_one]
    simpa using binaryDiagonalOrthogonalBasis_quadratic
      first second hadmissible 0
  · rw [unaryBinaryOrthogonalBasis_two]
    simpa using binaryDiagonalOrthogonalBasis_quadratic
      first second hadmissible 1

/-- The full chosen basis is orthogonal. -/
theorem unaryBinaryOrthogonalBasis_isOrtho
    (head first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (unaryBinaryModelSpace head first second hadmissible).bilin.iIsOrtho
      (unaryBinaryOrthogonalBasis head first second hadmissible) := by
  rw [LinearMap.BilinForm.iIsOrtho_def]
  intro i j hij
  have hfin (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
    rcases (show k.val = 0 ∨ k.val = 1 ∨ k.val = 2 by omega) with
      hk | hk | hk
    · exact Or.inl (Fin.ext hk)
    · exact Or.inr (Or.inl (Fin.ext hk))
    · exact Or.inr (Or.inr (Fin.ext hk))
  rcases hfin i with rfl | rfl | rfl <;>
    rcases hfin j with rfl | rfl | rfl
  · exact (hij rfl).elim
  · simp [QuadraticSpace.orthogonalSum, unaryBinaryModelSpace]
  · simp [QuadraticSpace.orthogonalSum, unaryBinaryModelSpace]
  · simp [QuadraticSpace.orthogonalSum, unaryBinaryModelSpace]
  · exact (hij rfl).elim
  · simpa [unaryBinaryModelSpace, QuadraticSpace.orthogonalSum] using
      (LinearMap.BilinForm.iIsOrtho_def.mp
        (binaryDiagonalOrthogonalBasis_isOrtho
          first second hadmissible) (0 : Fin 2) (1 : Fin 2) (by decide))
  · simp [QuadraticSpace.orthogonalSum, unaryBinaryModelSpace]
  · simpa [unaryBinaryModelSpace, QuadraticSpace.orthogonalSum] using
      (LinearMap.BilinForm.iIsOrtho_def.mp
        (binaryDiagonalOrthogonalBasis_isOrtho
          first second hadmissible) (1 : Fin 2) (0 : Fin 2) (by decide))
  · exact (hij rfl).elim

/-- Matching an orthogonal basis with the three advertised coefficients gives
an ambient isometry to the explicit unary--binary model. -/
theorem isIsometric_unaryBinaryModel_of_orthogonalBasisData
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V}
    (X : OrthogonalBasisData q 3)
    (head first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first))
    (hvalues : ∀ i,
      X.valueUnit i = ![head, first, second] i) :
    q.IsIsometric (unaryBinaryModelSpace head first second hadmissible) := by
  have hgram : ∀ i j,
      (unaryBinaryModelSpace head first second hadmissible).bilin
          (unaryBinaryOrthogonalBasis head first second hadmissible i)
          (unaryBinaryOrthogonalBasis head first second hadmissible j) =
        q.bilin (X.basis i) (X.basis j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      change
        (unaryBinaryModelSpace head first second hadmissible).quadratic
            (unaryBinaryOrthogonalBasis head first second hadmissible i) =
          X.value i
      rw [unaryBinaryOrthogonalBasis_quadratic]
      have hv := congrArg Units.val (hvalues i)
      change X.value i = ((![head, first, second] i : Kˣ) : K) at hv
      have hcoe : ((![head, first, second] i : Kˣ) : K) =
          ![(head : K), (first : K), (second : K)] i := by
        fin_cases i <;> rfl
      exact hcoe.symm.trans hv.symm
    · rw [(LinearMap.BilinForm.iIsOrtho_def.mp
          (unaryBinaryOrthogonalBasis_isOrtho
            head first second hadmissible)) i j hij,
        (LinearMap.BilinForm.iIsOrtho_def.mp X.orthogonal) i j hij]
  rcases Lattice.basisLattice_isIsometric_of_gram_eq
      q (unaryBinaryModelSpace head first second hadmissible)
      X.basis
      (unaryBinaryOrthogonalBasis head first second hadmissible)
      hgram with ⟨f⟩
  exact ⟨f.toQuadraticSpaceIsometry⟩

/-- Equal-rank diagonal representation of the three coefficients is the
coordinate-free ambient-space hypothesis for the explicit normal form. -/
theorem GoodBONG.isIsometric_unaryBinaryModel_of_diagonalRepresents
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (a : GoodBONG q L 3)
    (head first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first))
    (hrep : DiagonalRepresents
      (GoodBONG.diagonalUnitCoefficients ![head, first, second])
      a.toBONG.value) :
    q.IsIsometric (unaryBinaryModelSpace head first second hadmissible) := by
  rcases DiagonalRepresents.exists_orthogonalBasisData a
      ![head, first, second] hrep with ⟨X, hvalues⟩
  exact isIsometric_unaryBinaryModel_of_orthogonalBasisData
    X head first second hadmissible hvalues

/-- The ambient dimension of every unary--binary model is three. -/
theorem finrank_unaryBinaryModelAmbient :
    finrank K (K × (Fin 2 → K)) = 3 := by
  simp

/-- A canonical good BONG of the explicit unary--binary lattice.  Its
invariants are computed later from the Jordan decomposition; this definition
only chooses the good BONG whose existence is already part of the structural
theory. -/
noncomputable def unaryBinaryModelGoodBONG
    [BONGGoodExistenceLaws.{u, u} K]
    (head first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    GoodBONG
      (unaryBinaryModelSpace head first second hadmissible)
      (unaryBinaryModelLattice (K := K)) 3 :=
  (Classical.choice
      (exists_good_bong
        (unaryBinaryModelSpace head first second hadmissible)
        (unaryBinaryModelLattice (K := K)))).castLength
    finrank_unaryBinaryModelAmbient

end BONG

end Bong
