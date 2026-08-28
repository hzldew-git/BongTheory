/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryExactRealization
import Bong.Lattice.BasisIsometry
import Bong.QuadraticSpace.Rescale

/-!
# Binary lattices as rescaled explicit models

The integral basis adapted to a binary BONG has the Gram matrix of the
standard binary model, multiplied by the first BONG value.  Consequently the
original binary lattice is explicitly isometric to that rescaled model.  This
is the geometric bridge from BONG invariants to concrete binary lattices.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- Reindex the two standard coordinates by the adapted binary basis index. -/
def binaryModelAdaptedIndexEquiv : Fin 2 ≃ Unit ⊕ Fin 1 :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr finOneEquiv (Equiv.refl (Fin 1)))

@[simp]
theorem binaryModelAdaptedIndexEquiv_zero :
    binaryModelAdaptedIndexEquiv 0 = Sum.inl () := by
  rfl

@[simp]
theorem binaryModelAdaptedIndexEquiv_one :
    binaryModelAdaptedIndexEquiv 1 = Sum.inr 0 := by
  rfl

@[simp]
theorem binaryModelAdaptedIndexEquiv_symm_inl (i : Unit) :
    binaryModelAdaptedIndexEquiv.symm (Sum.inl i) = 0 := by
  cases i
  apply binaryModelAdaptedIndexEquiv.injective
  simp

@[simp]
theorem binaryModelAdaptedIndexEquiv_symm_inr (i : Fin 1) :
    binaryModelAdaptedIndexEquiv.symm (Sum.inr i) = 1 := by
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  apply binaryModelAdaptedIndexEquiv.injective
  simp

/-- The standard model basis indexed like the adapted binary integral basis. -/
noncomputable def binaryModelAdaptedBasis :
    Basis (Unit ⊕ Fin 1) K (Fin 2 → K) :=
  (binaryModelBasis (K := K)).reindex binaryModelAdaptedIndexEquiv

@[simp]
theorem binaryModelAdaptedBasis_inl (i : Unit) :
    binaryModelAdaptedBasis (K := K) (Sum.inl i) =
      QuadraticSpace.binaryModelFirst := by
  cases i
  simp [binaryModelAdaptedBasis]

@[simp]
theorem binaryModelAdaptedBasis_inr (i : Fin 1) :
    binaryModelAdaptedBasis (K := K) (Sum.inr i) =
      QuadraticSpace.binaryModelSecond := by
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  simp [binaryModelAdaptedBasis]

/-- Extend the BONG-adapted integral basis to the ambient field. -/
noncomputable def binaryAdaptedAmbientBasis (b : BONG V q L 2) :
    Basis (Unit ⊕ Fin 1) K V :=
  b.binaryIntegralBasis.extendOfIsLattice K

@[simp]
theorem binaryAdaptedAmbientBasis_inl (b : BONG V q L 2) (i : Unit) :
    b.binaryAdaptedAmbientBasis (Sum.inl i) = b.head := by
  rw [binaryAdaptedAmbientBasis, Basis.extendOfIsLattice_apply]
  exact b.coe_binaryIntegralBasis_inl i

@[simp]
theorem binaryAdaptedAmbientBasis_inr (b : BONG V q L 2) (i : Fin 1) :
    b.binaryAdaptedAmbientBasis (Sum.inr i) = b.binarySecondVector := by
  rw [binaryAdaptedAmbientBasis, Basis.extendOfIsLattice_apply]
  exact b.coe_binaryIntegralBasis_inr i

/-- The mixed coefficient in the normalized binary Gram model. -/
noncomputable def binaryModelCoefficient (b : BONG V q L 2) : K :=
  b.binaryMixedPairing / b.value 0

/-- The coefficient selected by the adapted binary basis satisfies the two
integrality conditions for the binary parameter. -/
theorem binaryModelCoefficient_isAdmissibleWitness (b : BONG V q L 2) :
    (2 : K) * b.binaryModelCoefficient ∈ IntegerRing K ∧
      b.binaryModelCoefficient ^ 2 + (b.binaryParameter : K) ∈
        IntegerRing K := by
  constructor
  · simpa [binaryModelCoefficient, binaryMixedPairing,
      b.value_zero_eq_quadratic_head] using
        (Lattice.two_projectionCoefficient_mem_integerRing
          q L b.head b.binarySecondVector b.head_isNormGenerator
          b.head_isAnisotropic b.binarySecondVector_mem)
  · have hvalueMem :=
      b.quadratic_binarySecondVector_mem_principal_value_zero
    have hquotient :
        q.quadratic b.binarySecondVector / b.value 0 ∈
          IntegerRing K := by
      apply Lattice.mem_integerRing_of_mul_mem_principalIdeal
        (b.value_ne_zero 0)
      convert hvalueMem using 1
      field_simp [b.value_ne_zero 0]
    have hformula :
        b.binaryModelCoefficient ^ 2 + (b.binaryParameter : K) =
          q.quadratic b.binarySecondVector / b.value 0 := by
      rw [b.coe_binaryParameter, b.quadratic_binarySecondVector_eq]
      simp only [binaryModelCoefficient]
      field_simp [b.value_ne_zero 0]
    rw [hformula]
    exact hquotient

/-- The normalized binary model, rescaled by the first BONG value. -/
noncomputable def normalizedBinaryModelSpace (b : BONG V q L 2) :
    QuadraticSpace K (Fin 2 → K) :=
  QuadraticSpace.rescaleUnit (b.valueUnit 0)
    (QuadraticSpace.binaryModel b.binaryParameter b.binaryModelCoefficient)

/-- The explicit coordinate equivalence from the normalized binary model to
the BONG-adapted ambient basis.  Keeping this map visible is useful when a
model vector has to be transported back to a prescribed BONG head. -/
noncomputable def normalizedBinaryModelLinearEquiv (b : BONG V q L 2) :
    (Fin 2 → K) ≃ₗ[K] V :=
  (binaryModelAdaptedBasis (K := K)).equiv b.binaryAdaptedAmbientBasis
    (Equiv.refl (Unit ⊕ Fin 1))

@[simp]
theorem normalizedBinaryModelLinearEquiv_apply_first
    (b : BONG V q L 2) :
    b.normalizedBinaryModelLinearEquiv
        QuadraticSpace.binaryModelFirst = b.head := by
  rw [← binaryModelAdaptedBasis_inl (K := K) ()]
  change
    ((binaryModelAdaptedBasis (K := K)).equiv
      b.binaryAdaptedAmbientBasis (Equiv.refl (Unit ⊕ Fin 1)))
        (binaryModelAdaptedBasis (K := K) (Sum.inl ())) = b.head
  rw [Module.Basis.equiv_apply]
  change b.binaryAdaptedAmbientBasis (Sum.inl ()) = b.head
  exact b.binaryAdaptedAmbientBasis_inl ()

@[simp]
theorem normalizedBinaryModelLinearEquiv_apply_second
    (b : BONG V q L 2) :
    b.normalizedBinaryModelLinearEquiv
        QuadraticSpace.binaryModelSecond = b.binarySecondVector := by
  rw [← binaryModelAdaptedBasis_inr (K := K) (0 : Fin 1)]
  change
    ((binaryModelAdaptedBasis (K := K)).equiv
      b.binaryAdaptedAmbientBasis (Equiv.refl (Unit ⊕ Fin 1)))
        (binaryModelAdaptedBasis (K := K) (Sum.inr (0 : Fin 1))) =
          b.binarySecondVector
  rw [Module.Basis.equiv_apply]
  change b.binaryAdaptedAmbientBasis (Sum.inr (0 : Fin 1)) =
    b.binarySecondVector
  exact b.binaryAdaptedAmbientBasis_inr 0

/-- The chosen lattice isometry behind `normalizedBinaryModel_isIsometric`.
Unlike the proposition-valued wrapper, it records that the first standard
model vector is sent to the prescribed BONG head. -/
noncomputable def normalizedBinaryModelLatticeIsometry
    (b : BONG V q L 2) :
    Lattice.Isometry b.normalizedBinaryModelSpace q
      (binaryModelLattice (K := K)) L := by
  let f : (Fin 2 → K) ≃ₗ[K] V := b.normalizedBinaryModelLinearEquiv
  refine {
    toLinearEquiv := f
    map_bilin := ?_
    map_mem := ?_
  }
  · intro x y
    have hindex (i : Unit ⊕ Fin 1) :
        i = Sum.inl () ∨ i = Sum.inr 0 := by
      rcases i with i | i
      · left
        exact congrArg Sum.inl (Subsingleton.elim i ())
      · right
        exact congrArg Sum.inr (Subsingleton.elim i 0)
    have hgram : ∀ i j,
        q.bilin (b.binaryAdaptedAmbientBasis i)
            (b.binaryAdaptedAmbientBasis j) =
          b.normalizedBinaryModelSpace.bilin
            (binaryModelAdaptedBasis (K := K) i)
            (binaryModelAdaptedBasis (K := K) j) := by
      intro i j
      rcases hindex i with rfl | rfl <;>
        rcases hindex j with rfl | rfl
      · simp only [binaryAdaptedAmbientBasis_inl,
          binaryModelAdaptedBasis_inl, normalizedBinaryModelSpace,
          QuadraticSpace.rescaleUnit_bilin_apply,
          QuadraticSpace.binaryModel_bilin_first_first]
        change q.quadratic b.head = (b.valueUnit 0 : K) * 1
        rw [← b.value_zero_eq_quadratic_head, b.coe_valueUnit, mul_one]
      · simp only [binaryAdaptedAmbientBasis_inl,
          binaryAdaptedAmbientBasis_inr, binaryModelAdaptedBasis_inl,
          binaryModelAdaptedBasis_inr, normalizedBinaryModelSpace,
          QuadraticSpace.rescaleUnit_bilin_apply,
          QuadraticSpace.binaryModel_bilin_first_second]
        change b.binaryMixedPairing =
          (b.valueUnit 0 : K) * b.binaryModelCoefficient
        rw [b.coe_valueUnit]
        simp only [binaryModelCoefficient]
        field_simp [b.value_ne_zero 0]
      · simp only [binaryAdaptedAmbientBasis_inl,
          binaryAdaptedAmbientBasis_inr, binaryModelAdaptedBasis_inl,
          binaryModelAdaptedBasis_inr, normalizedBinaryModelSpace,
          QuadraticSpace.rescaleUnit_bilin_apply]
        rw [(QuadraticSpace.binaryModel b.binaryParameter
          b.binaryModelCoefficient).isSymm.eq]
        rw [QuadraticSpace.binaryModel_bilin_first_second]
        change q.bilin b.binarySecondVector b.head =
          (b.valueUnit 0 : K) * b.binaryModelCoefficient
        rw [q.isSymm.eq]
        change b.binaryMixedPairing = _
        rw [b.coe_valueUnit]
        simp only [binaryModelCoefficient]
        field_simp [b.value_ne_zero 0]
      · simp only [binaryAdaptedAmbientBasis_inr,
          binaryModelAdaptedBasis_inr, normalizedBinaryModelSpace,
          QuadraticSpace.rescaleUnit_bilin_apply,
          QuadraticSpace.binaryModel_bilin_second_second]
        change q.quadratic b.binarySecondVector =
          (b.valueUnit 0 : K) *
            (b.binaryModelCoefficient ^ 2 + (b.binaryParameter : K))
        rw [b.quadratic_binarySecondVector_eq, b.coe_valueUnit,
          b.coe_binaryParameter]
        simp only [binaryModelCoefficient]
        field_simp [b.value_ne_zero 0]
    have hforms : q.bilin.comp f.toLinearMap f.toLinearMap =
        b.normalizedBinaryModelSpace.bilin := by
      apply LinearMap.BilinForm.ext_basis
        (binaryModelAdaptedBasis (K := K))
      intro i j
      rw [LinearMap.BilinForm.comp_apply]
      simpa [f, normalizedBinaryModelLinearEquiv] using hgram i j
    exact DFunLike.congr_fun (DFunLike.congr_fun hforms x) y
  · intro x
    have hmodel :
        Lattice.basisLattice (binaryModelAdaptedBasis (K := K)) =
          binaryModelLattice (K := K) := by
      rw [binaryModelAdaptedBasis, Lattice.basisLattice_reindex]
      rfl
    have hambient :
        Lattice.basisLattice b.binaryAdaptedAmbientBasis = L :=
      Lattice.basisLattice_extendOfIsLattice L b.binaryIntegralBasis
    rw [← hmodel, ← hambient,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing]
    have hrepr :
        b.binaryAdaptedAmbientBasis.repr (f x) =
          (binaryModelAdaptedBasis (K := K)).repr x := by
      simp [f, normalizedBinaryModelLinearEquiv, Basis.equiv]
    exact hrepr ▸ Iff.rfl

@[simp]
theorem normalizedBinaryModelLatticeIsometry_apply_first
    (b : BONG V q L 2) :
    b.normalizedBinaryModelLatticeIsometry.toLinearEquiv
        QuadraticSpace.binaryModelFirst = b.head := by
  change b.normalizedBinaryModelLinearEquiv
      QuadraticSpace.binaryModelFirst = b.head
  exact b.normalizedBinaryModelLinearEquiv_apply_first

@[simp]
theorem normalizedBinaryModelLatticeIsometry_apply_second
    (b : BONG V q L 2) :
    b.normalizedBinaryModelLatticeIsometry.toLinearEquiv
        QuadraticSpace.binaryModelSecond = b.binarySecondVector := by
  change b.normalizedBinaryModelLinearEquiv
      QuadraticSpace.binaryModelSecond = b.binarySecondVector
  exact b.normalizedBinaryModelLinearEquiv_apply_second

theorem basisLattice_binaryModelAdaptedBasis :
    Lattice.basisLattice (binaryModelAdaptedBasis (K := K)) =
      binaryModelLattice (K := K) := by
  rw [binaryModelAdaptedBasis, Lattice.basisLattice_reindex]
  rfl

theorem basisLattice_binaryAdaptedAmbientBasis (b : BONG V q L 2) :
    Lattice.basisLattice b.binaryAdaptedAmbientBasis = L := by
  exact Lattice.basisLattice_extendOfIsLattice L b.binaryIntegralBasis

/-- Every binary BONG lattice is its rescaled explicit Gram model, as an
actual lattice isometry rather than merely an equality of invariants. -/
theorem normalizedBinaryModel_isIsometric (b : BONG V q L 2) :
    Lattice.IsIsometric b.normalizedBinaryModelSpace q
      (binaryModelLattice (K := K)) L := by
  have hindex (i : Unit ⊕ Fin 1) :
      i = Sum.inl () ∨ i = Sum.inr 0 := by
    rcases i with i | i
    · left
      exact congrArg Sum.inl (Subsingleton.elim i ())
    · right
      exact congrArg Sum.inr (Subsingleton.elim i 0)
  have hgram : ∀ i j,
      q.bilin (b.binaryAdaptedAmbientBasis i)
          (b.binaryAdaptedAmbientBasis j) =
        b.normalizedBinaryModelSpace.bilin
          (binaryModelAdaptedBasis (K := K) i)
          (binaryModelAdaptedBasis (K := K) j) := by
    intro i j
    rcases hindex i with rfl | rfl <;>
      rcases hindex j with rfl | rfl
    · simp only [binaryAdaptedAmbientBasis_inl,
        binaryModelAdaptedBasis_inl, normalizedBinaryModelSpace,
        QuadraticSpace.rescaleUnit_bilin_apply,
        QuadraticSpace.binaryModel_bilin_first_first]
      change q.quadratic b.head = (b.valueUnit 0 : K) * 1
      rw [← b.value_zero_eq_quadratic_head, b.coe_valueUnit, mul_one]
    · simp only [binaryAdaptedAmbientBasis_inl,
        binaryAdaptedAmbientBasis_inr, binaryModelAdaptedBasis_inl,
        binaryModelAdaptedBasis_inr, normalizedBinaryModelSpace,
        QuadraticSpace.rescaleUnit_bilin_apply,
        QuadraticSpace.binaryModel_bilin_first_second]
      change b.binaryMixedPairing =
        (b.valueUnit 0 : K) * b.binaryModelCoefficient
      rw [b.coe_valueUnit]
      simp only [binaryModelCoefficient]
      field_simp [b.value_ne_zero 0]
    · simp only [binaryAdaptedAmbientBasis_inl,
        binaryAdaptedAmbientBasis_inr, binaryModelAdaptedBasis_inl,
        binaryModelAdaptedBasis_inr, normalizedBinaryModelSpace,
        QuadraticSpace.rescaleUnit_bilin_apply]
      rw [(QuadraticSpace.binaryModel b.binaryParameter
        b.binaryModelCoefficient).isSymm.eq]
      rw [QuadraticSpace.binaryModel_bilin_first_second]
      change q.bilin b.binarySecondVector b.head =
        (b.valueUnit 0 : K) * b.binaryModelCoefficient
      rw [q.isSymm.eq]
      change b.binaryMixedPairing = _
      rw [b.coe_valueUnit]
      simp only [binaryModelCoefficient]
      field_simp [b.value_ne_zero 0]
    · simp only [binaryAdaptedAmbientBasis_inr,
        binaryModelAdaptedBasis_inr, normalizedBinaryModelSpace,
        QuadraticSpace.rescaleUnit_bilin_apply,
        QuadraticSpace.binaryModel_bilin_second_second]
      change q.quadratic b.binarySecondVector =
        (b.valueUnit 0 : K) *
          (b.binaryModelCoefficient ^ 2 + (b.binaryParameter : K))
      rw [b.quadratic_binarySecondVector_eq, b.coe_valueUnit,
        b.coe_binaryParameter]
      simp only [binaryModelCoefficient]
      field_simp [b.value_ne_zero 0]
  have h := Lattice.basisLattice_isIsometric_of_gram_eq
    b.normalizedBinaryModelSpace q
    (binaryModelAdaptedBasis (K := K)) b.binaryAdaptedAmbientBasis hgram
  rw [basisLattice_binaryModelAdaptedBasis,
    b.basisLattice_binaryAdaptedAmbientBasis] at h
  exact h

/-- Scale only the second standard coordinate of a binary model. -/
def binarySecondScaleFactors (s : Kˣ) : Fin 2 → Kˣ :=
  ![1, s]

/-- The standard basis with its second vector multiplied by `s`. -/
noncomputable def binarySecondScaledBasis (s : Kˣ) :
    Basis (Fin 2) K (Fin 2 → K) :=
  (binaryModelBasis (K := K)).unitsSMul (binarySecondScaleFactors s)

@[simp]
theorem binarySecondScaledBasis_zero (s : Kˣ) :
    binarySecondScaledBasis s 0 = QuadraticSpace.binaryModelFirst := by
  rw [binarySecondScaledBasis, Basis.unitsSMul_apply,
    binaryModelBasis_zero]
  simp [binarySecondScaleFactors]

@[simp]
theorem binarySecondScaledBasis_one (s : Kˣ) :
    binarySecondScaledBasis s 1 =
      (s : K) • QuadraticSpace.binaryModelSecond := by
  rw [binarySecondScaledBasis, Basis.unitsSMul_apply,
    binaryModelBasis_one]
  rfl

/-- A valuation-unit change in the second coordinate preserves the standard
binary model lattice. -/
theorem basisLattice_binarySecondScaledBasis (s : Kˣ)
    (hs : IsValuationUnit K (s : K)) :
    Lattice.basisLattice (binarySecondScaledBasis s) =
      binaryModelLattice (K := K) := by
  rw [binarySecondScaledBasis,
    Lattice.basisLattice_unitsSMul_eq]
  · rfl
  · intro i
    fin_cases i
    · simpa [IsValuationUnit, binarySecondScaleFactors] using
        (Dyadic.ord_one (K := K))
    · simpa [binarySecondScaleFactors] using hs

/-- Multiplying a binary parameter by the square of a valuation unit is an
explicit integral change of the second model coordinate. -/
theorem rescaledBinaryModel_isIsometric_mul_valuationUnit_square
    (u a d s : Kˣ) (c : K) (hs : IsValuationUnit K (s : K))
    (hparameter : d * s ^ 2 = a) :
    Lattice.IsIsometric
      (QuadraticSpace.rescaleUnit u (QuadraticSpace.binaryModel a c))
      (QuadraticSpace.rescaleUnit u
        (QuadraticSpace.binaryModel d (c / (s : K))))
      (binaryModelLattice (K := K)) (binaryModelLattice (K := K)) := by
  have hparameterCoe : (d : K) * (s : K) ^ 2 = (a : K) := by
    exact congrArg Units.val hparameter
  have hindex (i : Fin 2) : i = 0 ∨ i = 1 := by
    by_cases hi : i.val = 0
    · left
      apply Fin.ext
      exact hi
    · right
      apply Fin.ext
      omega
  have hgram : ∀ i j,
      (QuadraticSpace.rescaleUnit u
          (QuadraticSpace.binaryModel d (c / (s : K)))).bilin
          (binarySecondScaledBasis s i) (binarySecondScaledBasis s j) =
        (QuadraticSpace.rescaleUnit u
          (QuadraticSpace.binaryModel a c)).bilin
          (binaryModelBasis (K := K) i) (binaryModelBasis (K := K) j) := by
    intro i j
    rcases hindex i with rfl | rfl <;>
      rcases hindex j with rfl | rfl
    · simp only [binarySecondScaledBasis_zero,
        binaryModelBasis_zero, QuadraticSpace.rescaleUnit_bilin_apply,
        QuadraticSpace.binaryModel_bilin_first_first]
    · simp only [binarySecondScaledBasis_zero,
        binarySecondScaledBasis_one, binaryModelBasis_zero,
        binaryModelBasis_one, QuadraticSpace.rescaleUnit_bilin_apply,
        LinearMap.BilinForm.smul_right,
        QuadraticSpace.binaryModel_bilin_first_second]
      field_simp [Units.ne_zero s]
    · simp only [binarySecondScaledBasis_zero,
        binarySecondScaledBasis_one, binaryModelBasis_zero,
        binaryModelBasis_one, QuadraticSpace.rescaleUnit_bilin_apply]
      rw [(QuadraticSpace.binaryModel d (c / (s : K))).isSymm.eq,
        (QuadraticSpace.binaryModel a c).isSymm.eq]
      simp only [LinearMap.BilinForm.smul_right,
        QuadraticSpace.binaryModel_bilin_first_second]
      field_simp [Units.ne_zero s]
    · simp only [binarySecondScaledBasis_one,
        binaryModelBasis_one, QuadraticSpace.rescaleUnit_bilin_apply,
        LinearMap.BilinForm.smul_left,
        LinearMap.BilinForm.smul_right,
        QuadraticSpace.binaryModel_bilin_second_second]
      rw [← hparameterCoe]
      field_simp [Units.ne_zero s]
  have h := Lattice.basisLattice_isIsometric_of_gram_eq
    (QuadraticSpace.rescaleUnit u (QuadraticSpace.binaryModel a c))
    (QuadraticSpace.rescaleUnit u
      (QuadraticSpace.binaryModel d (c / (s : K))))
    (binaryModelBasis (K := K)) (binarySecondScaledBasis s) hgram
  rw [show Lattice.basisLattice (binaryModelBasis (K := K)) =
      binaryModelLattice (K := K) by rfl,
    basisLattice_binarySecondScaledBasis s hs] at h
  exact h

end BONG

end Bong
