/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.OrthogonalExtension
import Bong.QuadraticSpace.SpinorNorm

/-!
# Spinor norm under orthogonal extension

An isometry of `x^perp` and its extension fixing `K x` have naturally
isometric residual Wall spaces.  Consequently their spinor norms agree.
-/

namespace Bong

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {x : V}
  {anisotropic : q.IsAnisotropic x}

omit [CharZero K] in
/-- Residual endomorphisms commute with extension from `x^perp`. -/
theorem residualLinearMap_orthogonalExtension
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) (y : V) :
    residualLinearMap (orthogonalExtensionIsometry f) y =
      (residualLinearMap f
        (q.projectionToOrthogonal x anisotropic y) :
          q.vectorOrthogonal x) := by
  rw [residualLinearMap_apply, residualLinearMap_apply]
  change y - orthogonalExtensionLinearMap f y =
    ((q.projectionToOrthogonal x anisotropic y -
      f.toLinearEquiv (q.projectionToOrthogonal x anisotropic y) :
        q.vectorOrthogonal x) : V)
  rw [orthogonalExtensionLinearMap_apply]
  rw [← q.lineProjection_apply x y]
  simp only [Submodule.coe_sub]
  have hdecompose := q.lineProjection_add_orthogonalProjection x y
  change q.lineProjection x y +
      (q.projectionToOrthogonal x anisotropic y : V) = y at hdecompose
  calc
    y - (q.lineProjection x y +
        (f.toLinearEquiv
          (q.projectionToOrthogonal x anisotropic y) : V)) =
      (q.lineProjection x y +
          (q.projectionToOrthogonal x anisotropic y : V)) -
        (q.lineProjection x y +
          (f.toLinearEquiv
            (q.projectionToOrthogonal x anisotropic y) : V)) :=
      congrArg (fun z : V => z -
        (q.lineProjection x y +
          (f.toLinearEquiv
            (q.projectionToOrthogonal x anisotropic y) : V)))
        hdecompose.symm
    _ = (q.projectionToOrthogonal x anisotropic y : V) -
        (f.toLinearEquiv
          (q.projectionToOrthogonal x anisotropic y) : V) := by
      abel

/-- Inclusion identifies the tail residual space with the ambient one. -/
noncomputable def orthogonalExtensionResidualLinearMap
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) :
    residualSpace f →ₗ[K]
      residualSpace (orthogonalExtensionIsometry f) where
  toFun y := ⟨(y : q.vectorOrthogonal x), by
    rcases y.property with ⟨z, hz⟩
    refine ⟨(z : V), ?_⟩
    rw [residualLinearMap_orthogonalExtension]
    have hprojection :
        q.projectionToOrthogonal x anisotropic (z : V) = z := by
      apply Subtype.ext
      exact q.orthogonalProjection_eq_self z.property
    rw [hprojection]
    exact congrArg Subtype.val hz⟩
  map_add' y z := by
    apply Subtype.ext
    rfl
  map_smul' a y := by
    apply Subtype.ext
    rfl

omit [CharZero K] in
@[simp]
theorem orthogonalExtensionResidualLinearMap_coe
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) (y : residualSpace f) :
    ((orthogonalExtensionResidualLinearMap f y :
        residualSpace (orthogonalExtensionIsometry f)) : V) =
      (y : q.vectorOrthogonal x) :=
  rfl

omit [CharZero K] in
/-- The residual-space inclusion is injective. -/
theorem orthogonalExtensionResidualLinearMap_injective
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) :
    Function.Injective (orthogonalExtensionResidualLinearMap f) := by
  intro y z hyz
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun w : residualSpace (orthogonalExtensionIsometry f) => (w : V)) hyz

omit [CharZero K] in
/-- The residual-space inclusion is surjective. -/
theorem orthogonalExtensionResidualLinearMap_surjective
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) :
    Function.Surjective (orthogonalExtensionResidualLinearMap f) := by
  intro y
  rcases y.property with ⟨z, hz⟩
  refine ⟨residualMap f (q.projectionToOrthogonal x anisotropic z), ?_⟩
  apply Subtype.ext
  change (residualLinearMap f
      (q.projectionToOrthogonal x anisotropic z) :
        q.vectorOrthogonal x) = (y : V)
  rw [← residualLinearMap_orthogonalExtension f z]
  exact hz

/-- The canonical equivalence of the two residual spaces. -/
noncomputable def orthogonalExtensionResidualEquiv
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) :
    residualSpace f ≃ₗ[K]
      residualSpace (orthogonalExtensionIsometry f) :=
  LinearEquiv.ofBijective (orthogonalExtensionResidualLinearMap f)
    ⟨orthogonalExtensionResidualLinearMap_injective f,
      orthogonalExtensionResidualLinearMap_surjective f⟩

omit [CharZero K] in
@[simp]
theorem orthogonalExtensionResidualEquiv_coe
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) (y : residualSpace f) :
    ((orthogonalExtensionResidualEquiv f y :
        residualSpace (orthogonalExtensionIsometry f)) : V) =
      (y : q.vectorOrthogonal x) :=
  rfl

/-- Explicit residual vectors are carried to their ambient counterparts. -/
theorem orthogonalExtensionResidualEquiv_residualMap
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic))
    (y : q.vectorOrthogonal x) :
    orthogonalExtensionResidualEquiv f (residualMap f y) =
      residualMap (orthogonalExtensionIsometry f) (y : V) := by
  apply Subtype.ext
  rw [orthogonalExtensionResidualEquiv_coe]
  change (residualLinearMap f y : q.vectorOrthogonal x) =
    residualLinearMap (orthogonalExtensionIsometry f) (y : V)
  have hprojection :
      q.projectionToOrthogonal x anisotropic (y : V) = y := by
    apply Subtype.ext
    exact q.orthogonalProjection_eq_self y.property
  have h := residualLinearMap_orthogonalExtension f (y : V)
  rw [hprojection] at h
  exact h.symm

/-- The residual equivalence is an isometry of Wall forms. -/
theorem wallForm_orthogonalExtensionResidualEquiv
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) (y z : residualSpace f) :
    wallForm (orthogonalExtensionIsometry f)
        (orthogonalExtensionResidualEquiv f y)
        (orthogonalExtensionResidualEquiv f z) =
      wallForm f y z := by
  rcases residualMap_surjective f y with ⟨w, rfl⟩
  rw [orthogonalExtensionResidualEquiv_residualMap,
    wallForm_residualMap_left, wallForm_residualMap_left]
  rw [orthogonalExtensionResidualEquiv_coe]
  rfl

/-- Orthogonal extension by a fixed anisotropic line preserves spinor norm. -/
theorem spinorNorm_orthogonalExtension [FiniteDimensional K V]
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) :
    spinorNorm (orthogonalExtensionIsometry f) = spinorNorm f := by
  let F := orthogonalExtensionIsometry f
  let e := orthogonalExtensionResidualEquiv f
  have hfin : Module.finrank K (residualSpace F) =
      Module.finrank K (residualSpace f) := e.finrank_eq.symm
  let b := (wallBasis f).map e
  have hmatrix :
      LinearMap.BilinForm.toMatrix b (wallForm F) =
        LinearMap.BilinForm.toMatrix (wallBasis f) (wallForm f) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply,
      LinearMap.BilinForm.toMatrix_apply]
    exact wallForm_orthogonalExtensionResidualEquiv f
      (wallBasis f i) (wallBasis f j)
  have hdet :
      Matrix.det (LinearMap.BilinForm.toMatrix b (wallForm F)) =
        wallDeterminant f := by
    rw [wallDeterminant, hmatrix]
  have hu :
      Units.mk0
          (Matrix.det (LinearMap.BilinForm.toMatrix b (wallForm F)))
          ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1
            (wallForm_nondegenerate F)) =
        Units.mk0 (wallDeterminant f) (wallDeterminant_ne_zero f) := by
    apply Units.ext
    exact hdet
  rw [spinorNorm_eq_basisDeterminantOfFinrankEq F hfin b, hu]
  exact (spinorNorm_eq_wallDeterminant f).symm

end QuadraticSpace

end Bong
