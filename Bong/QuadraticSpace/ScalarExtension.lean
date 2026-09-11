/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.FieldDiagonalization
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Scalar extension of finite-dimensional quadratic spaces

This file constructs scalar extension in the project's bilinear-form
convention.  It proves that nondegeneracy survives a field extension and
that isometries and finite orthogonal sums commute with extension.  These
facts are the algebraic infrastructure used in the induction in He (2025),
Lemma 2.2.
-/

namespace Bong

open scoped TensorProduct

namespace QuadraticSpace

universe u v w x

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
  {V : Type w} [AddCommGroup V] [Module F V]
  {W : Type x} [AddCommGroup W] [Module F W]

/-- The Gram matrix of a base-changed form is obtained by applying the
coefficient embedding to the original Gram matrix. -/
theorem toMatrix_baseChange [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V)
    (b : Module.Basis (Fin (Module.finrank F V)) F V) :
    LinearMap.BilinForm.toMatrix (b.baseChange E) (B.baseChange E) =
      (algebraMap F E).mapMatrix
        (LinearMap.BilinForm.toMatrix b B) := by
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply,
    Module.Basis.baseChange_apply,
    LinearMap.BilinForm.baseChange_tmul,
    RingHom.mapMatrix_apply]
  simp [Algebra.smul_def]

/-- A nondegenerate bilinear form remains nondegenerate after a field
extension. -/
theorem _root_.LinearMap.BilinForm.Nondegenerate.baseChangeField
    [FiniteDimensional F V]
    {B : LinearMap.BilinForm F V} (hB : B.Nondegenerate) :
    (B.baseChange E).Nondegenerate := by
  let b := Module.finBasis F V
  apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero
    (B₃ := B.baseChange E) (b.baseChange E)
  rw [toMatrix_baseChange B b, ← RingHom.map_det]
  exact (map_ne_zero (algebraMap F E)).mpr <|
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB

/-- Scalar extension of a finite-dimensional quadratic space. -/
noncomputable def scalarExtension [FiniteDimensional F V]
    (q : QuadraticSpace F V) :
    QuadraticSpace E (E ⊗[F] V) where
  bilin := q.bilin.baseChange E
  isSymm := LinearMap.BilinForm.isSymm_iff.mpr <|
    LinearMap.BilinForm.IsSymm.baseChange E <|
      LinearMap.BilinForm.isSymm_iff.mp q.isSymm
  nondegenerate := q.nondegenerate.baseChangeField

@[simp]
theorem scalarExtension_bilin_tmul [FiniteDimensional F V]
    (q : QuadraticSpace F V) (a b : E) (x y : V) :
    (q.scalarExtension (E := E)).bilin (a ⊗ₜ x) (b ⊗ₜ y) =
      q.bilin x y • (a * b) :=
  rfl

@[simp]
theorem scalarExtension_quadratic_tmul [FiniteDimensional F V]
    (q : QuadraticSpace F V) (a : E) (x : V) :
    (q.scalarExtension (E := E)).quadratic (a ⊗ₜ x) =
      q.quadratic x • a ^ 2 := by
  rw [quadratic, scalarExtension_bilin_tmul, pow_two]
  rfl

/-- A quadratic-space isometry extends along a field embedding. -/
noncomputable def Isometry.scalarExtension
    [FiniteDimensional F V] [FiniteDimensional F W]
    {q : QuadraticSpace F V} {r : QuadraticSpace F W}
    (f : Isometry q r) :
    Isometry (q.scalarExtension (E := E))
      (r.scalarExtension (E := E)) where
  toLinearEquiv := f.toLinearEquiv.baseChange F E V W
  map_bilin := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul b w =>
            simp [f.map_bilin]
        | add y z hy hz =>
            simp only [map_add, hy, hz]
    | add x y hx hy =>
        simp only [map_add, LinearMap.add_apply, hx, hy]

/-- An injective quadratic-space representation extends along a field
embedding. -/
noncomputable def Representation.scalarExtension
    [FiniteDimensional F V] [FiniteDimensional F W]
    {q : QuadraticSpace F V} {r : QuadraticSpace F W}
    (f : Representation q r) :
    Representation (q.scalarExtension (E := E))
      (r.scalarExtension (E := E)) where
  toLinearMap := f.toLinearMap.baseChange E
  injective := by
    have hker : LinearMap.ker f.toLinearMap = ⊥ :=
      LinearMap.ker_eq_bot.mpr f.injective
    obtain ⟨g, hg⟩ :=
      f.toLinearMap.exists_leftInverse_of_injective hker
    apply Function.LeftInverse.injective (g := g.baseChange E)
    intro x
    have hmap := congrArg (fun h ↦ h.baseChange E) hg
    have happ := DFunLike.congr_fun hmap x
    simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply,
      LinearMap.baseChange_id, LinearMap.id_apply] using happ
  map_bilin := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul b w =>
            simp [f.map_bilin]
        | add y z hy hz =>
            simp only [map_add, hy, hz]
    | add x y hx hy =>
        simp only [map_add, LinearMap.add_apply, hx, hy]

/-- Scalar extension carries a finite diagonal space to the diagonal space
obtained by applying the coefficient embedding. -/
noncomputable def scalarExtensionFiniteDiagonalIsometry
    {n : Nat} (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    Isometry ((finiteDiagonal a ha).scalarExtension (E := E))
      (finiteDiagonal (fun i ↦ algebraMap F E (a i))
        (fun i ↦ (map_ne_zero (algebraMap F E)).mpr (ha i))) where
  toLinearEquiv := TensorProduct.piScalarRight F E E (Fin n)
  map_bilin := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul d y =>
            simp only [TensorProduct.piScalarRight_apply,
              TensorProduct.piScalarRightHom_tmul,
              finiteDiagonal_bilin_apply,
              scalarExtension_bilin_tmul]
            simp only [Algebra.smul_def]
            rw [map_sum]
            simp_rw [map_mul]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring
        | add y z hy hz =>
            simp only [map_add, hy, hz]
    | add x y hx hy =>
        simp only [map_add, LinearMap.add_apply, hx, hy]

/-- Scalar extension of a scaled line is the line whose coefficient is the
image of the original unit. -/
noncomputable def scalarExtensionScaledLineIsometry (a : Fˣ) :
    Isometry ((scaledLine a).scalarExtension (E := E))
      (scaledLine (Units.map (algebraMap F E).toMonoidHom a)) := by
  let first :=
    (fieldScaledLineDiagonalizationIsometry a).scalarExtension (E := E)
  let second := scalarExtensionFiniteDiagonalIsometry
    (E := E) (fun _ : Fin 1 ↦ (a : F))
      (fun _ ↦ Units.ne_zero a)
  let third :=
    (fieldScaledLineDiagonalizationIsometry
      (Units.map (algebraMap F E).toMonoidHom a)).symm
  exact first.trans <| second.trans third

/-- Scalar extension commutes with an orthogonal sum. -/
noncomputable def scalarExtensionOrthogonalSumIsometry
    [FiniteDimensional F V] [FiniteDimensional F W]
    (q : QuadraticSpace F V) (r : QuadraticSpace F W) :
    Isometry ((q.orthogonalSum r).scalarExtension (E := E))
      ((q.scalarExtension (E := E)).orthogonalSum
        (r.scalarExtension (E := E))) where
  toLinearEquiv := TensorProduct.prodRight F E E V W
  map_bilin := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul b y =>
            rcases x with ⟨xV, xW⟩
            rcases y with ⟨yV, yW⟩
            simp [orthogonalSum_bilin_apply, add_smul]
        | add y z hy hz =>
            simp only [map_add, hy, hz]
    | add x y hx hy =>
        simp only [map_add, LinearMap.add_apply, hx, hy]

end QuadraticSpace

end Bong
