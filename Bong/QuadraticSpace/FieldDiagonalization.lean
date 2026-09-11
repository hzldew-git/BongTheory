/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalTailCancellation
import Bong.QuadraticSpace.OrthogonalSum
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Diagonalization and Witt cancellation over an arbitrary characteristic-zero field

The original project diagonalization first chose a lattice and then a BONG,
so it was restricted to the dyadic local-field context.  This file instead
uses the ordinary orthogonal-basis theorem for a nondegenerate symmetric
bilinear form.  It provides the field-generic diagonalization and Witt
cancellation needed before scalar-extension arguments can formalize He
(2025), Lemma 2.2.
-/

namespace Bong

namespace QuadraticSpace

universe u v w z z'

variable {K : Type u} [Field K] [CharZero K]
  {U : Type z} [AddCommGroup U] [Module K U]
  {U' : Type z'} [AddCommGroup U'] [Module K U']
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

/-- A chosen orthogonal basis over an arbitrary characteristic-zero field. -/
noncomputable def fieldOrthogonalFinBasis
    [FiniteDimensional K V] (q : QuadraticSpace K V) :
    Module.Basis (Fin (Module.finrank K V)) K V := by
  letI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  exact Classical.choose
    (LinearMap.BilinForm.exists_orthogonal_basis
      (B := q.bilin) (LinearMap.BilinForm.isSymm_iff.mp q.isSymm))

/-- The chosen field-generic basis is orthogonal. -/
theorem fieldOrthogonalFinBasis_isOrtho
    [FiniteDimensional K V] (q : QuadraticSpace K V) :
    q.bilin.iIsOrtho
      (q.fieldOrthogonalFinBasis : Fin (Module.finrank K V) → V) := by
  letI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  exact Classical.choose_spec
    (LinearMap.BilinForm.exists_orthogonal_basis
      (B := q.bilin) (LinearMap.BilinForm.isSymm_iff.mp q.isSymm))

/-- Diagonal coefficients of the chosen field-generic orthogonal basis. -/
noncomputable def fieldDiagonalCoefficients
    [FiniteDimensional K V] (q : QuadraticSpace K V) :
    Fin (Module.finrank K V) → K :=
  fun i ↦ q.quadratic (q.fieldOrthogonalFinBasis i)

/-- Nondegeneracy makes every chosen diagonal coefficient nonzero. -/
theorem fieldDiagonalCoefficients_ne_zero
    [FiniteDimensional K V] (q : QuadraticSpace K V)
    (i : Fin (Module.finrank K V)) :
    q.fieldDiagonalCoefficients i ≠ 0 := by
  change q.bilin (q.fieldOrthogonalFinBasis i)
      (q.fieldOrthogonalFinBasis i) ≠ 0
  exact q.fieldOrthogonalFinBasis_isOrtho
    |>.not_isOrtho_basis_self_of_nondegenerate q.nondegenerate i

/-- The finite diagonal model over an arbitrary characteristic-zero field. -/
noncomputable def fieldDiagonalModel
    [FiniteDimensional K V] (q : QuadraticSpace K V) :
    QuadraticSpace K (Fin (Module.finrank K V) → K) :=
  finiteDiagonal q.fieldDiagonalCoefficients
    q.fieldDiagonalCoefficients_ne_zero

/-- The Gram matrix in the field-generic orthogonal basis is diagonal. -/
theorem toMatrix_fieldOrthogonalFinBasis
    [FiniteDimensional K V] (q : QuadraticSpace K V) :
    LinearMap.BilinForm.toMatrix q.fieldOrthogonalFinBasis q.bilin =
      Matrix.diagonal q.fieldDiagonalCoefficients := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp [fieldDiagonalCoefficients, quadratic]
  · rw [if_neg hij]
    exact q.fieldOrthogonalFinBasis_isOrtho hij

/-- The coordinate equivalence is an isometry to the field-generic diagonal
model. -/
noncomputable def fieldDiagonalizationIsometry
    [FiniteDimensional K V] (q : QuadraticSpace K V) :
    Isometry q q.fieldDiagonalModel where
  toLinearEquiv := q.fieldOrthogonalFinBasis.equivFun
  map_bilin := by
    intro x y
    rw [fieldDiagonalModel, finiteDiagonal_bilin_apply]
    have hmatrix :=
      LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec
        q.fieldOrthogonalFinBasis q.bilin x y
    rw [q.toMatrix_fieldOrthogonalFinBasis] at hmatrix
    rw [hmatrix]
    change (∑ i, q.fieldDiagonalCoefficients i *
        q.fieldOrthogonalFinBasis.equivFun x i *
        q.fieldOrthogonalFinBasis.equivFun y i) =
      q.fieldOrthogonalFinBasis.equivFun x ⬝ᵥ
        (Matrix.diagonal q.fieldDiagonalCoefficients).mulVec
          (q.fieldOrthogonalFinBasis.equivFun y)
    simp only [dotProduct, Matrix.mulVec, Matrix.diagonal_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp [ite_mul, mul_comm, mul_left_comm]

/-- Componentwise product of field-generic quadratic-space isometries. -/
noncomputable def Isometry.fieldOrthogonalSum
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {q' : QuadraticSpace K U} {r' : QuadraticSpace K U'}
    (f : Isometry q q') (g : Isometry r r') :
    Isometry (q.orthogonalSum r) (q'.orthogonalSum r') where
  toLinearEquiv := f.toLinearEquiv.prodCongr g.toLinearEquiv
  map_bilin := by
    intro x y
    simp only [orthogonalSum_bilin_apply, LinearEquiv.prodCongr_apply]
    rw [f.map_bilin, g.map_bilin]

/-- Split and append coordinate functions without any local-field
structure. -/
noncomputable def fieldFinAddArrowEquiv (m n : Nat) :
    ((Fin m → K) × (Fin n → K)) ≃ₗ[K] (Fin (m + n) → K) where
  toFun := fun x ↦ Fin.append x.1 x.2
  invFun := fun x ↦
    (fun i ↦ x (Fin.castAdd n i), fun j ↦ x (Fin.natAdd m j))
  left_inv := by
    intro x
    apply Prod.ext <;> funext i
    · simp
    · simp
  right_inv := by
    intro x
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp
    · simp
  map_add' := by
    intro x y
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp
    · simp
  map_smul' := by
    intro c x
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp
    · simp

omit [CharZero K] in
@[simp]
theorem fieldFinAddArrowEquiv_apply_castAdd (m n : Nat)
    (x : (Fin m → K) × (Fin n → K)) (i : Fin m) :
    fieldFinAddArrowEquiv (K := K) m n x (Fin.castAdd n i) =
      x.1 i := by
  simp [fieldFinAddArrowEquiv]

omit [CharZero K] in
@[simp]
theorem fieldFinAddArrowEquiv_apply_natAdd (m n : Nat)
    (x : (Fin m → K) × (Fin n → K)) (i : Fin n) :
    fieldFinAddArrowEquiv (K := K) m n x (Fin.natAdd m i) =
      x.2 i := by
  simp [fieldFinAddArrowEquiv]

/-- Appending coefficient lists models the orthogonal sum of two finite
diagonal spaces over an arbitrary field. -/
noncomputable def fieldFiniteDiagonalOrthogonalSumIsometry
    {m n : Nat} (a : Fin m → K) (b : Fin n → K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    Isometry
      ((finiteDiagonal a ha).orthogonalSum (finiteDiagonal b hb))
      (finiteDiagonal (Fin.append a b) (by
        intro i
        refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
        · simpa using ha j
        · simpa using hb j)) where
  toLinearEquiv :=
    fieldFinAddArrowEquiv m n
  map_bilin := by
    intro x y
    rw [finiteDiagonal_bilin_apply, orthogonalSum_bilin_apply,
      finiteDiagonal_bilin_apply, finiteDiagonal_bilin_apply]
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    simp only [fieldFinAddArrowEquiv_apply_castAdd,
      fieldFinAddArrowEquiv_apply_natAdd]

/-- A scalar coordinate identifies a scaled line with its one-entry finite
diagonal model over an arbitrary field. -/
noncomputable def fieldScaledLineDiagonalizationIsometry (a : Kˣ) :
    Isometry (scaledLine a)
      (finiteDiagonal (fun _ : Fin 1 ↦ (a : K))
        (fun _ ↦ Units.ne_zero a)) where
  toLinearEquiv :=
    { toFun := fun x _ ↦ x
      invFun := fun x ↦ x 0
      left_inv := by intro x; rfl
      right_inv := by intro x; funext i; exact Fin.eq_zero i ▸ rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_bilin := by
    intro x y
    rw [finiteDiagonal_bilin_apply, scaledLine_bilin_apply]
    simp

/-- Multiplying the coordinate by a unit identifies two scaled lines whose
coefficients differ by the corresponding square. -/
def fieldScaledLineIsometryOfEqMulSquare
    (a b c : Kˣ) (h : (a : K) = (b : K) * (c : K) ^ 2) :
    Isometry (scaledLine a) (scaledLine b) where
  toLinearEquiv :=
    { toFun := fun x ↦ (c : K) * x
      invFun := fun x ↦ (c⁻¹ : Kˣ) * x
      left_inv := by
        intro x
        simp only [Units.val_inv_eq_inv_val]
        field_simp
      right_inv := by
        intro x
        simp only [Units.val_inv_eq_inv_val]
        field_simp
      map_add' := by intros; ring
      map_smul' := by intros; simp only [smul_eq_mul, RingHom.id_apply]; ring }
  map_bilin := by
    intro x y
    simp only [scaledLine_bilin_apply]
    change (b : K) * ((c : K) * x) * ((c : K) * y) =
      (a : K) * x * y
    rw [h]
    ring

/-- A nonzero value of a finite diagonal polynomial gives a representation
of the corresponding scaled line. -/
theorem fieldFiniteDiagonalRepresentsScaledLineOfValue
    {n : Nat} (b : Fin n → K) (hb : ∀ i, b i ≠ 0)
    (a : Kˣ) (x : Fin n → K)
    (hvalue : diagonalQuadratic b x = (a : K)) :
    (finiteDiagonal b hb).Represents (scaledLine a) := by
  classical
  have hx : x ≠ 0 := by
    intro hzero
    rw [hzero] at hvalue
    have ha : (a : K) = 0 := by
      simpa [diagonalQuadratic] using hvalue.symm
    exact Units.ne_zero a ha
  obtain ⟨j, hxj⟩ : ∃ j : Fin n, x j ≠ 0 := by
    by_contra hnot
    push Not at hnot
    apply hx
    funext i
    exact hnot i
  let f : (Fin 1 → K) →ₗ[K] (Fin n → K) :=
    { toFun := fun y i ↦ y 0 * x i
      map_add' := by intros; funext i; simp only [Pi.add_apply]; ring
      map_smul' := by
        intros
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have hinjective : Function.Injective f := by
    intro y z hyz
    apply funext
    intro i
    fin_cases i
    have hj := congrFun hyz j
    change y 0 * x j = z 0 * x j at hj
    exact mul_right_cancel₀ hxj hj
  have hdiag : DiagonalRepresents (fun _ : Fin 1 ↦ (a : K)) b := by
    refine ⟨f, hinjective, ?_⟩
    intro y
    change diagonalQuadratic b (fun i ↦ y 0 * x i) =
      diagonalQuadratic (fun _ : Fin 1 ↦ (a : K)) y
    calc
      diagonalQuadratic b (fun i ↦ y 0 * x i) =
          y 0 ^ 2 * diagonalQuadratic b x := by
            unfold diagonalQuadratic
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = y 0 ^ 2 * (a : K) := by rw [hvalue]
      _ = diagonalQuadratic (fun _ : Fin 1 ↦ (a : K)) y := by
        simp [diagonalQuadratic]
        ring
  have hfinite := DiagonalRepresents.toQuadraticSpaceRepresents
    (fun _ : Fin 1 ↦ Units.ne_zero a) hb hdiag
  exact hfinite.trans
    ⟨(fieldScaledLineDiagonalizationIsometry a).toRepresentation⟩

/-- Appending a scaled line to a finite diagonal space appends its
coefficient to the diagonal list. -/
noncomputable def fieldFiniteDiagonalScaledLineSnocIsometry
    {n : Nat} (b : Fin n → K) (hb : ∀ i, b i ≠ 0) (a : Kˣ) :
    Isometry
      ((finiteDiagonal b hb).orthogonalSum (scaledLine a))
      (finiteDiagonal (Fin.snoc b (a : K)) (by
        intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · rw [Fin.snoc_last]
          exact Units.ne_zero a
        · rw [Fin.snoc_castSucc]
          exact hb j)) := by
  let line := fieldScaledLineDiagonalizationIsometry a
  let tail := Isometry.refl (finiteDiagonal b hb)
  let append := fieldFiniteDiagonalOrthogonalSumIsometry
    b (fun _ : Fin 1 ↦ (a : K)) hb (fun _ ↦ Units.ne_zero a)
  simpa only [Fin.append_right_eq_snoc] using
    (tail.fieldOrthogonalSum line).trans append

/-- Exchange two factors of an orthogonal sum over an arbitrary field. -/
noncomputable def fieldOrthogonalSumSwap
    (q : QuadraticSpace K V) (r : QuadraticSpace K W) :
    Isometry (q.orthogonalSum r) (r.orthogonalSum q) where
  toLinearEquiv := LinearEquiv.prodComm K V W
  map_bilin := by
    intro x y
    simp only [orthogonalSum_bilin_apply, LinearEquiv.prodComm_apply]
    exact add_comm _ _

/-- A field-generic diagonal presentation of an orthogonal sum. -/
noncomputable def fieldOrthogonalSumDiagonalizationIsometry
    [FiniteDimensional K V] [FiniteDimensional K W]
    (q : QuadraticSpace K V) (r : QuadraticSpace K W) :
    Isometry (q.orthogonalSum r)
      (finiteDiagonal
        (Fin.append q.fieldDiagonalCoefficients
          r.fieldDiagonalCoefficients)
        (by
          intro i
          refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
          · simpa using q.fieldDiagonalCoefficients_ne_zero j
          · simpa using r.fieldDiagonalCoefficients_ne_zero j)) :=
  (q.fieldDiagonalizationIsometry.fieldOrthogonalSum
      r.fieldDiagonalizationIsometry).trans
    (fieldFiniteDiagonalOrthogonalSumIsometry
      q.fieldDiagonalCoefficients r.fieldDiagonalCoefficients
      q.fieldDiagonalCoefficients_ne_zero
      r.fieldDiagonalCoefficients_ne_zero)

/-- Cancel a literally common finite nondegenerate orthogonal summand from
a representation over an arbitrary characteristic-zero field. -/
theorem fieldOrthogonalSumLeftCancelRepresents
    [FiniteDimensional K U] [FiniteDimensional K V]
    [FiniteDimensional K W]
    (p : QuadraticSpace K U) (q : QuadraticSpace K V)
    (r : QuadraticSpace K W)
    (h : (p.orthogonalSum r).Represents (p.orthogonalSum q)) :
    r.Represents q := by
  rcases h with ⟨f⟩
  let sourceDiagonal := p.fieldOrthogonalSumDiagonalizationIsometry q
  let targetDiagonal := p.fieldOrthogonalSumDiagonalizationIsometry r
  let diagonalRepresentation := targetDiagonal.toRepresentation.trans <|
    f.trans sourceDiagonal.symm.toRepresentation
  have hfull : DiagonalRepresents
      (Fin.append p.fieldDiagonalCoefficients q.fieldDiagonalCoefficients)
      (Fin.append p.fieldDiagonalCoefficients r.fieldDiagonalCoefficients) := by
    refine ⟨diagonalRepresentation.toLinearMap,
      diagonalRepresentation.injective, ?_⟩
    intro x
    simpa only [finiteDiagonal_quadratic_apply] using
      diagonalRepresentation.map_quadratic x
  have htail : DiagonalRepresents q.fieldDiagonalCoefficients
      r.fieldDiagonalCoefficients := by
    exact DiagonalRepresents.cancel_common_prefix
      p.fieldDiagonalCoefficients q.fieldDiagonalCoefficients
      r.fieldDiagonalCoefficients
      p.fieldDiagonalCoefficients_ne_zero
      q.fieldDiagonalCoefficients_ne_zero
      r.fieldDiagonalCoefficients_ne_zero hfull
  rcases DiagonalRepresents.toQuadraticSpaceRepresents
      q.fieldDiagonalCoefficients_ne_zero
      r.fieldDiagonalCoefficients_ne_zero htail with ⟨tail⟩
  exact ⟨r.fieldDiagonalizationIsometry.symm.toRepresentation.trans <|
    tail.trans q.fieldDiagonalizationIsometry.toRepresentation⟩

/-- Cancel isometric finite head summands from a representation over an
arbitrary characteristic-zero field. -/
theorem fieldOrthogonalSumCancelRepresents
    [FiniteDimensional K U] [FiniteDimensional K U']
    [FiniteDimensional K V] [FiniteDimensional K W]
    (p : QuadraticSpace K U) (p' : QuadraticSpace K U')
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (head : Isometry p p')
    (total : (p'.orthogonalSum r).Represents (p.orthogonalSum q)) :
    r.Represents q := by
  rcases total with ⟨f⟩
  apply fieldOrthogonalSumLeftCancelRepresents p q r
  exact ⟨(head.symm.fieldOrthogonalSum (Isometry.refl r)).toRepresentation.trans f⟩

/-- Cancel a literally common finite nondegenerate orthogonal summand over
an arbitrary characteristic-zero field. -/
noncomputable def fieldOrthogonalSumLeftCancel
    [FiniteDimensional K U] [FiniteDimensional K V]
    [FiniteDimensional K W]
    (p : QuadraticSpace K U) (q : QuadraticSpace K V)
    (r : QuadraticSpace K W)
    (f : Isometry (p.orthogonalSum q) (p.orthogonalSum r)) :
    Isometry q r := by
  have hsum := f.toLinearEquiv.finrank_eq
  have hfinrank : Module.finrank K V = Module.finrank K W := by
    rw [Module.finrank_prod, Module.finrank_prod] at hsum
    exact Nat.add_left_cancel hsum
  let sourceDiagonal := p.fieldOrthogonalSumDiagonalizationIsometry q
  let targetDiagonal := p.fieldOrthogonalSumDiagonalizationIsometry r
  let diagonalIsometry :=
    sourceDiagonal.symm.trans (f.trans targetDiagonal)
  let diagonalRepresentation := diagonalIsometry.toRepresentation
  have hfull : DiagonalRepresents
      (Fin.append p.fieldDiagonalCoefficients q.fieldDiagonalCoefficients)
      (Fin.append p.fieldDiagonalCoefficients r.fieldDiagonalCoefficients) := by
    refine ⟨diagonalRepresentation.toLinearMap,
      diagonalRepresentation.injective, ?_⟩
    intro x
    simpa only [finiteDiagonal_quadratic_apply] using
      diagonalRepresentation.map_quadratic x
  have htail : DiagonalRepresents q.fieldDiagonalCoefficients
      r.fieldDiagonalCoefficients := by
    exact DiagonalRepresents.cancel_common_prefix
      p.fieldDiagonalCoefficients q.fieldDiagonalCoefficients
      r.fieldDiagonalCoefficients
      p.fieldDiagonalCoefficients_ne_zero
      q.fieldDiagonalCoefficients_ne_zero
      r.fieldDiagonalCoefficients_ne_zero hfull
  have hrep : r.fieldDiagonalModel.Represents q.fieldDiagonalModel :=
    DiagonalRepresents.toQuadraticSpaceRepresents
      q.fieldDiagonalCoefficients_ne_zero
      r.fieldDiagonalCoefficients_ne_zero htail
  let diagonalTail :=
    (Classical.choice hrep).toIsometryOfFinrankEq (by
      simpa only [Module.finrank_fin_fun] using hfinrank)
  exact q.fieldDiagonalizationIsometry.trans <|
    diagonalTail.trans r.fieldDiagonalizationIsometry.symm

/-- Cancel isometric finite head summands over an arbitrary
characteristic-zero field. -/
noncomputable def fieldOrthogonalSumCancel
    [FiniteDimensional K U] [FiniteDimensional K U']
    [FiniteDimensional K V] [FiniteDimensional K W]
    (p : QuadraticSpace K U) (p' : QuadraticSpace K U')
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (head : Isometry p p')
    (total : Isometry (p.orthogonalSum q) (p'.orthogonalSum r)) :
    Isometry q r :=
  fieldOrthogonalSumLeftCancel p q r <|
    total.trans (head.symm.fieldOrthogonalSum (Isometry.refl r))

end QuadraticSpace

end Bong
