/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.MixedPairing
import Bong.QuadraticSpace.Isometry
import Mathlib.LinearAlgebra.Determinant

/-!
# Extending an isometry of an orthogonal complement

An isometry of `x^⊥` extends to the whole quadratic space by fixing the line
`K x`.  This is the linear-algebraic construction used in Beli (2003),
Sections 2.3--2.5.
-/

namespace Bong

namespace QuadraticSpace

universe u v w

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Projection onto the anisotropic line through `x`. -/
def lineProjection (q : QuadraticSpace K V) (x : V) : V →ₗ[K] V :=
  (q.quadratic x)⁻¹ • (q.bilin x).smulRight x

@[simp]
theorem lineProjection_apply (q : QuadraticSpace K V) (x y : V) :
    q.lineProjection x y = (q.bilin x y / q.quadratic x) • x := by
  simp [lineProjection, div_eq_mul_inv, mul_comm, smul_smul]

/-- Line and orthogonal projections reconstruct the original vector. -/
theorem lineProjection_add_orthogonalProjection (q : QuadraticSpace K V)
    (x y : V) :
    q.lineProjection x y + q.orthogonalProjection x y = y := by
  rw [lineProjection_apply, orthogonalProjection_apply]
  abel

/-- The bilinear form splits into its line and orthogonal-complement parts. -/
theorem bilin_projection_decomposition (q : QuadraticSpace K V)
    (x : V) (anisotropic : q.IsAnisotropic x) (y z : V) :
    q.bilin y z =
      (q.bilin x y / q.quadratic x) *
          (q.bilin x z / q.quadratic x) * q.quadratic x +
        q.bilin (q.orthogonalProjection x y)
          (q.orthogonalProjection x z) := by
  rw [q.orthogonalProjection_apply, q.orthogonalProjection_apply]
  simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  rw [q.isSymm.eq y x]
  rw [show q.bilin x x = q.quadratic x from rfl]
  simp only [div_eq_mul_inv]
  have hcancel :
      q.bilin x y * q.bilin x z * q.quadratic x *
          (q.quadratic x)⁻¹ ^ 2 =
        q.bilin x y * q.bilin x z * (q.quadratic x)⁻¹ := by
    calc
      _ = q.bilin x y * q.bilin x z *
          (q.quadratic x * (q.quadratic x)⁻¹) *
            (q.quadratic x)⁻¹ := by ring
      _ = _ := by rw [mul_inv_cancel₀ anisotropic]; ring
  ring_nf
  linear_combination -2 * hcancel

variable {q : QuadraticSpace K V} {x : V}
  {anisotropic : q.IsAnisotropic x}

/-- Coordinates for the orthogonal decomposition `V = K x ⊥ x^⊥`. -/
noncomputable def lineOrthogonalLinearEquiv :
    V ≃ₗ[K] K × q.vectorOrthogonal x where
  toFun y :=
    (q.bilin x y / q.quadratic x,
      q.projectionToOrthogonal x anisotropic y)
  invFun p := p.1 • x + (p.2 : V)
  left_inv y := by
    change (q.bilin x y / q.quadratic x) • x +
        (q.projectionToOrthogonal x anisotropic y : V) = y
    simpa only [q.lineProjection_apply,
      q.projectionToOrthogonal_coe] using
        q.lineProjection_add_orthogonalProjection x y
  right_inv p := by
    rcases p with ⟨a, z⟩
    apply Prod.ext
    · change q.bilin x (a • x + (z : V)) / q.quadratic x = a
      rw [map_add, LinearMap.BilinForm.smul_right]
      have hz : q.bilin x (z : V) = 0 :=
        (q.mem_vectorOrthogonal_iff x z).1 z.property
      rw [hz, add_zero]
      change (a * q.quadratic x) / q.quadratic x = a
      rw [mul_div_cancel_right₀ a anisotropic]
    · apply Subtype.ext
      change q.orthogonalProjection x (a • x + (z : V)) = z
      rw [q.orthogonalProjection_apply,
        map_add, LinearMap.BilinForm.smul_right]
      have hz : q.bilin x (z : V) = 0 :=
        (q.mem_vectorOrthogonal_iff x z).1 z.property
      rw [hz, add_zero]
      change a • x + (z : V) -
          ((a * q.quadratic x) / q.quadratic x) • x = z
      rw [mul_div_cancel_right₀ a anisotropic]
      abel
  map_add' y z := by
    apply Prod.ext
    · change q.bilin x (y + z) / q.quadratic x =
        q.bilin x y / q.quadratic x +
          q.bilin x z / q.quadratic x
      rw [map_add]
      ring
    · apply Subtype.ext
      simpa using congrArg Subtype.val
        (map_add (q.projectionToOrthogonal x anisotropic) y z)
  map_smul' a y := by
    apply Prod.ext
    · change q.bilin x (a • y) / q.quadratic x =
        a * (q.bilin x y / q.quadratic x)
      rw [LinearMap.BilinForm.smul_right]
      ring
    · apply Subtype.ext
      simpa using congrArg Subtype.val
        (map_smul (q.projectionToOrthogonal x anisotropic) a y)

/-- The linear extension which fixes `K x` and acts by `f` on `x^⊥`. -/
noncomputable def orthogonalExtensionLinearMap
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) : V →ₗ[K] V :=
  q.lineProjection x +
    (Submodule.subtype (q.vectorOrthogonal x)).comp
      (f.toLinearEquiv.toLinearMap.comp
        (q.projectionToOrthogonal x anisotropic))

@[simp]
theorem orthogonalExtensionLinearMap_apply
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) (y : V) :
    orthogonalExtensionLinearMap f y =
      (q.bilin x y / q.quadratic x) • x +
        (f.toLinearEquiv (q.projectionToOrthogonal x anisotropic y) : V) := by
  simp [orthogonalExtensionLinearMap]

/-- The extension preserves pairing with the distinguished vector. -/
theorem bilin_orthogonalExtensionLinearMap
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) (y : V) :
    q.bilin x (orthogonalExtensionLinearMap f y) = q.bilin x y := by
  rw [orthogonalExtensionLinearMap_apply]
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right]
  have horth :
      q.bilin x
        (f.toLinearEquiv (q.projectionToOrthogonal x anisotropic y) : V) = 0 :=
    (q.mem_vectorOrthogonal_iff x _).1
      (f.toLinearEquiv (q.projectionToOrthogonal x anisotropic y)).property
  rw [horth, add_zero]
  change (q.bilin x y / q.quadratic x) * q.quadratic x = q.bilin x y
  exact div_mul_cancel₀ _ anisotropic

/-- Orthogonal projection intertwines the extension and the tail isometry. -/
theorem orthogonalProjection_orthogonalExtensionLinearMap
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) (y : V) :
    q.orthogonalProjection x (orthogonalExtensionLinearMap f y) =
      (f.toLinearEquiv (q.projectionToOrthogonal x anisotropic y) : V) := by
  rw [q.orthogonalProjection_apply, bilin_orthogonalExtensionLinearMap,
    orthogonalExtensionLinearMap_apply]
  abel

/-- Extending the inverse tail map gives an inverse linear map. -/
theorem orthogonalExtensionLinearMap_symm_apply_apply
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) (y : V) :
    orthogonalExtensionLinearMap f.symm
        (orthogonalExtensionLinearMap f y) = y := by
  rw [orthogonalExtensionLinearMap_apply,
    bilin_orthogonalExtensionLinearMap]
  have hprojection :
      q.projectionToOrthogonal x anisotropic
          (orthogonalExtensionLinearMap f y) =
        f.toLinearEquiv (q.projectionToOrthogonal x anisotropic y) := by
    apply Subtype.ext
    exact orthogonalProjection_orthogonalExtensionLinearMap f y
  rw [hprojection]
  simp only [Isometry.symm, LinearEquiv.symm_apply_apply]
  simpa only [lineProjection_apply, projectionToOrthogonal_coe] using
    q.lineProjection_add_orthogonalProjection x y

/-- The linear equivalence obtained by fixing `K x` and extending `f`. -/
noncomputable def orthogonalExtensionLinearEquiv
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinear (orthogonalExtensionLinearMap f)
    (orthogonalExtensionLinearMap f.symm)
    (by
      ext y
      exact orthogonalExtensionLinearMap_symm_apply_apply f.symm y)
    (by
      ext y
      exact orthogonalExtensionLinearMap_symm_apply_apply f y)

@[simp]
theorem orthogonalExtensionLinearEquiv_apply
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) (y : V) :
    orthogonalExtensionLinearEquiv f y = orthogonalExtensionLinearMap f y :=
  rfl

/-- Extending an isometry from `x^⊥` while fixing `x` preserves its
determinant. -/
theorem det_orthogonalExtensionLinearEquiv [FiniteDimensional K V]
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) :
    LinearEquiv.det (orthogonalExtensionLinearEquiv f) =
      LinearEquiv.det f.toLinearEquiv := by
  let e := lineOrthogonalLinearEquiv
    (q := q) (x := x) (anisotropic := anisotropic)
  let g := LinearEquiv.prodCongr (LinearEquiv.refl K K) f.toLinearEquiv
  have hconj :
      (e.symm.trans (orthogonalExtensionLinearEquiv f)).trans e = g := by
    apply LinearEquiv.ext
    intro p
    rcases p with ⟨a, z⟩
    have hz : q.bilin x (z : V) = 0 :=
      (q.mem_vectorOrthogonal_iff x z).1 z.property
    have hcoeff :
        q.bilin x (a • x + (z : V)) / q.quadratic x = a := by
      rw [map_add, LinearMap.BilinForm.smul_right, hz, add_zero]
      change (a * q.quadratic x) / q.quadratic x = a
      rw [mul_div_cancel_right₀ a anisotropic]
    have hproj :
        q.projectionToOrthogonal x anisotropic (a • x + (z : V)) = z := by
      apply Subtype.ext
      change q.orthogonalProjection x (a • x + (z : V)) = z
      rw [q.orthogonalProjection_apply,
        map_add, LinearMap.BilinForm.smul_right, hz, add_zero]
      change a • x + (z : V) -
          ((a * q.quadratic x) / q.quadratic x) • x = z
      rw [mul_div_cancel_right₀ a anisotropic]
      abel
    apply Prod.ext
    · change q.bilin x
          (orthogonalExtensionLinearEquiv f (a • x + (z : V))) /
            q.quadratic x = a
      rw [orthogonalExtensionLinearEquiv_apply,
        bilin_orthogonalExtensionLinearMap]
      exact hcoeff
    · apply Subtype.ext
      change q.orthogonalProjection x
          (orthogonalExtensionLinearEquiv f (a • x + (z : V))) =
        (f.toLinearEquiv z : V)
      rw [orthogonalExtensionLinearEquiv_apply]
      have htail := orthogonalProjection_orthogonalExtensionLinearMap f
        (a • x + (z : V))
      rw [hproj] at htail
      exact htail
  calc
    LinearEquiv.det (orthogonalExtensionLinearEquiv f) =
        LinearEquiv.det
          ((e.symm.trans (orthogonalExtensionLinearEquiv f)).trans e) :=
      (LinearEquiv.det_conj (orthogonalExtensionLinearEquiv f) e).symm
    _ = LinearEquiv.det g := congrArg LinearEquiv.det hconj
    _ = LinearEquiv.det f.toLinearEquiv := by
      apply Units.ext
      simp [g, LinearEquiv.coe_det, LinearMap.det_prodMap]

/-- The restricted projection intertwines the extension and its tail map. -/
theorem projectionToOrthogonal_orthogonalExtensionLinearEquiv
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) (y : V) :
    q.projectionToOrthogonal x anisotropic
        (orthogonalExtensionLinearEquiv f y) =
      f.toLinearEquiv (q.projectionToOrthogonal x anisotropic y) := by
  apply Subtype.ext
  exact orthogonalProjection_orthogonalExtensionLinearMap f y

@[simp]
theorem orthogonalExtensionLinearEquiv_apply_distinguished
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) :
    orthogonalExtensionLinearEquiv f x = x := by
  rw [orthogonalExtensionLinearEquiv_apply,
    orthogonalExtensionLinearMap_apply]
  have hprojection : q.projectionToOrthogonal x anisotropic x = 0 := by
    apply Subtype.ext
    exact q.orthogonalProjection_self anisotropic
  rw [hprojection]
  simp only [map_zero, Submodule.coe_zero, add_zero]
  change (q.quadratic x / q.quadratic x) • x = x
  rw [div_self anisotropic, one_smul]

/-- Extending a tail isometry gives an isometry of the ambient space. -/
noncomputable def orthogonalExtensionIsometry
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) : Isometry q q where
  toLinearEquiv := orthogonalExtensionLinearEquiv f
  map_bilin y z := by
    rw [orthogonalExtensionLinearEquiv_apply,
      orthogonalExtensionLinearEquiv_apply]
    rw [q.bilin_projection_decomposition x anisotropic
      (orthogonalExtensionLinearMap f y)
      (orthogonalExtensionLinearMap f z)]
    rw [bilin_orthogonalExtensionLinearMap,
      bilin_orthogonalExtensionLinearMap,
      orthogonalProjection_orthogonalExtensionLinearMap,
      orthogonalProjection_orthogonalExtensionLinearMap]
    have htail := f.map_bilin
      (q.projectionToOrthogonal x anisotropic y)
      (q.projectionToOrthogonal x anisotropic z)
    change q.bilin
        (f.toLinearEquiv (q.projectionToOrthogonal x anisotropic y) : V)
        (f.toLinearEquiv (q.projectionToOrthogonal x anisotropic z) : V) =
      q.bilin (q.orthogonalProjection x y)
        (q.orthogonalProjection x z) at htail
    rw [htail]
    exact (q.bilin_projection_decomposition x anisotropic y z).symm

section TwoSpaces

variable {W : Type w} [AddCommGroup W] [Module K W]
  {r : QuadraticSpace K W} {y : W}
  {anisotropicSource : r.IsAnisotropic y}

/-- The linear extension of an isometry between two orthogonal complements.
The distinguished source line `K y` is sent to the distinguished target line
`K x`; equality of their quadratic values supplies the line isometry. -/
noncomputable def headExtensionLinearMap
    (_hvalue : q.quadratic x = r.quadratic y)
    (f : Isometry (r.orthogonalSpace y anisotropicSource)
      (q.orthogonalSpace x anisotropic)) : W →ₗ[K] V :=
  (r.quadratic y)⁻¹ • (r.bilin y).smulRight x +
    (Submodule.subtype (q.vectorOrthogonal x)).comp
      (f.toLinearEquiv.toLinearMap.comp
        (r.projectionToOrthogonal y anisotropicSource))

@[simp]
theorem headExtensionLinearMap_apply
    (hvalue : q.quadratic x = r.quadratic y)
    (f : Isometry (r.orthogonalSpace y anisotropicSource)
      (q.orthogonalSpace x anisotropic)) (z : W) :
    headExtensionLinearMap hvalue f z =
      (r.bilin y z / r.quadratic y) • x +
        (f.toLinearEquiv
          (r.projectionToOrthogonal y anisotropicSource z) : V) := by
  simp [headExtensionLinearMap, div_eq_mul_inv, mul_comm, smul_smul]

/-- The extension preserves pairing with the distinguished source and target
vectors. -/
theorem bilin_headExtensionLinearMap
    (hvalue : q.quadratic x = r.quadratic y)
    (f : Isometry (r.orthogonalSpace y anisotropicSource)
      (q.orthogonalSpace x anisotropic)) (z : W) :
    q.bilin x (headExtensionLinearMap hvalue f z) = r.bilin y z := by
  rw [headExtensionLinearMap_apply]
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right]
  have horth :
      q.bilin x
        (f.toLinearEquiv
          (r.projectionToOrthogonal y anisotropicSource z) : V) = 0 :=
    (q.mem_vectorOrthogonal_iff x _).1
      (f.toLinearEquiv
        (r.projectionToOrthogonal y anisotropicSource z)).property
  rw [horth, add_zero]
  change (r.bilin y z / r.quadratic y) * q.quadratic x = r.bilin y z
  rw [hvalue]
  exact div_mul_cancel₀ _ anisotropicSource

/-- Orthogonal projection intertwines the cross-space extension and the tail
isometry. -/
theorem orthogonalProjection_headExtensionLinearMap
    (hvalue : q.quadratic x = r.quadratic y)
    (f : Isometry (r.orthogonalSpace y anisotropicSource)
      (q.orthogonalSpace x anisotropic)) (z : W) :
    q.orthogonalProjection x (headExtensionLinearMap hvalue f z) =
      (f.toLinearEquiv
        (r.projectionToOrthogonal y anisotropicSource z) : V) := by
  rw [q.orthogonalProjection_apply,
    bilin_headExtensionLinearMap hvalue f,
    headExtensionLinearMap_apply, hvalue]
  abel

/-- Applying the extension of the inverse tail isometry after the extension
recovers the source vector. -/
theorem headExtensionLinearMap_symm_apply_apply
    (hvalue : q.quadratic x = r.quadratic y)
    (f : Isometry (r.orthogonalSpace y anisotropicSource)
      (q.orthogonalSpace x anisotropic)) (z : W) :
    headExtensionLinearMap (q := r) (r := q) (x := y) (y := x)
        hvalue.symm f.symm (headExtensionLinearMap hvalue f z) = z := by
  rw [headExtensionLinearMap_apply,
    bilin_headExtensionLinearMap hvalue f, hvalue]
  have hprojection :
      q.projectionToOrthogonal x anisotropic
          (headExtensionLinearMap hvalue f z) =
        f.toLinearEquiv
          (r.projectionToOrthogonal y anisotropicSource z) := by
    apply Subtype.ext
    exact orthogonalProjection_headExtensionLinearMap hvalue f z
  rw [hprojection]
  simp only [Isometry.symm, LinearEquiv.symm_apply_apply]
  simpa only [lineProjection_apply, projectionToOrthogonal_coe] using
    r.lineProjection_add_orthogonalProjection y z

/-- The linear equivalence obtained by adjoining equal anisotropic head
lines to an isometry of their orthogonal complements. -/
noncomputable def headExtensionLinearEquiv
    (hvalue : q.quadratic x = r.quadratic y)
    (f : Isometry (r.orthogonalSpace y anisotropicSource)
      (q.orthogonalSpace x anisotropic)) : W ≃ₗ[K] V :=
  LinearEquiv.ofLinear (headExtensionLinearMap hvalue f)
    (headExtensionLinearMap (q := r) (r := q) (x := y) (y := x)
      hvalue.symm f.symm)
    (by
      ext z
      exact headExtensionLinearMap_symm_apply_apply hvalue.symm f.symm z)
    (by
      ext z
      exact headExtensionLinearMap_symm_apply_apply hvalue f z)

@[simp]
theorem headExtensionLinearEquiv_apply
    (hvalue : q.quadratic x = r.quadratic y)
    (f : Isometry (r.orthogonalSpace y anisotropicSource)
      (q.orthogonalSpace x anisotropic)) (z : W) :
    headExtensionLinearEquiv hvalue f z = headExtensionLinearMap hvalue f z :=
  rfl

/-- The restricted projection of the extended map is literally the supplied
tail isometry. -/
theorem projectionToOrthogonal_headExtensionLinearEquiv
    (hvalue : q.quadratic x = r.quadratic y)
    (f : Isometry (r.orthogonalSpace y anisotropicSource)
      (q.orthogonalSpace x anisotropic)) (z : W) :
    q.projectionToOrthogonal x anisotropic
        (headExtensionLinearEquiv hvalue f z) =
      f.toLinearEquiv
        (r.projectionToOrthogonal y anisotropicSource z) := by
  apply Subtype.ext
  exact orthogonalProjection_headExtensionLinearMap hvalue f z

@[simp]
theorem headExtensionLinearEquiv_apply_sourceHead
    (hvalue : q.quadratic x = r.quadratic y)
    (f : Isometry (r.orthogonalSpace y anisotropicSource)
      (q.orthogonalSpace x anisotropic)) :
    headExtensionLinearEquiv hvalue f y = x := by
  rw [headExtensionLinearEquiv_apply, headExtensionLinearMap_apply]
  have hprojection :
      r.projectionToOrthogonal y anisotropicSource y = 0 := by
    apply Subtype.ext
    exact r.orthogonalProjection_self anisotropicSource
  rw [hprojection]
  simp only [map_zero, Submodule.coe_zero, add_zero]
  change (r.quadratic y / r.quadratic y) • x = x
  rw [div_self anisotropicSource, one_smul]

/-- An equal-valued head line and an isometry of the two orthogonal
complements assemble to an isometry of the ambient quadratic spaces. -/
noncomputable def headExtensionIsometry
    (hvalue : q.quadratic x = r.quadratic y)
    (f : Isometry (r.orthogonalSpace y anisotropicSource)
      (q.orthogonalSpace x anisotropic)) : Isometry r q where
  toLinearEquiv := headExtensionLinearEquiv hvalue f
  map_bilin z t := by
    rw [headExtensionLinearEquiv_apply, headExtensionLinearEquiv_apply]
    rw [q.bilin_projection_decomposition x anisotropic
      (headExtensionLinearMap hvalue f z)
      (headExtensionLinearMap hvalue f t)]
    rw [bilin_headExtensionLinearMap hvalue f,
      bilin_headExtensionLinearMap hvalue f,
      orthogonalProjection_headExtensionLinearMap hvalue f,
      orthogonalProjection_headExtensionLinearMap hvalue f,
      hvalue]
    have htail := f.map_bilin
      (r.projectionToOrthogonal y anisotropicSource z)
      (r.projectionToOrthogonal y anisotropicSource t)
    change q.bilin
        (f.toLinearEquiv
          (r.projectionToOrthogonal y anisotropicSource z) : V)
        (f.toLinearEquiv
          (r.projectionToOrthogonal y anisotropicSource t) : V) =
      r.bilin (r.orthogonalProjection y z)
        (r.orthogonalProjection y t) at htail
    rw [htail]
    exact (r.bilin_projection_decomposition y anisotropicSource z t).symm

@[simp]
theorem headExtensionIsometry_apply_sourceHead
    (hvalue : q.quadratic x = r.quadratic y)
    (f : Isometry (r.orthogonalSpace y anisotropicSource)
      (q.orthogonalSpace x anisotropic)) :
    (headExtensionIsometry hvalue f).toLinearEquiv y = x :=
  headExtensionLinearEquiv_apply_sourceHead hvalue f

end TwoSpaces

end QuadraticSpace

end Bong
