/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.Isometry
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Residual spaces and the Wall form

For an isometry `f`, its residual space is `range (1 - f)`.  The Wall form on
this space is

`χ_f((1-f)w, v) = 2 B(w,v)`.

We construct it using a linear section of `1-f` and prove that the result is
independent of the chosen section.  Its determinant square class will define
the spinor norm without choosing a reflection decomposition.
-/

namespace Bong

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}

/-- The endomorphism `1 - f` attached to an isometry. -/
def residualLinearMap (f : Isometry q q) : V →ₗ[K] V :=
  LinearMap.id - f.toLinearEquiv.toLinearMap

@[simp]
theorem residualLinearMap_apply (f : Isometry q q) (y : V) :
    residualLinearMap f y = y - f.toLinearEquiv y :=
  rfl

/-- The residual space `range (1 - f)`. -/
def residualSpace (f : Isometry q q) : Submodule K V :=
  LinearMap.range (residualLinearMap f)

/-- The residual map with codomain restricted to its range. -/
def residualMap (f : Isometry q q) : V →ₗ[K] residualSpace f :=
  (residualLinearMap f).rangeRestrict

@[simp]
theorem residualMap_coe (f : Isometry q q) (y : V) :
    (residualMap f y : V) = y - f.toLinearEquiv y :=
  rfl

/-- The range-restricted residual map has full range. -/
theorem residualMap_range_eq_top (f : Isometry q q) :
    LinearMap.range (residualMap f) = ⊤ :=
  LinearMap.range_rangeRestrict (residualLinearMap f)

/-- The residual map is surjective by construction. -/
theorem residualMap_surjective (f : Isometry q q) :
    Function.Surjective (residualMap f) :=
  LinearMap.range_eq_top.mp (residualMap_range_eq_top f)

/-- A chosen linear section of the residual map. -/
noncomputable def residualSection (f : Isometry q q) :
    residualSpace f →ₗ[K] V :=
  Classical.choose
    ((residualMap f).exists_rightInverse_of_surjective
      (residualMap_range_eq_top f))

/-- The chosen section is a right inverse of the residual map. -/
@[simp]
theorem residualMap_residualSection (f : Isometry q q)
    (y : residualSpace f) :
    residualMap f (residualSection f y) = y := by
  have h := Classical.choose_spec
    ((residualMap f).exists_rightInverse_of_surjective
      (residualMap_range_eq_top f))
  exact LinearMap.congr_fun h y

/-- Fixed vectors are exactly the kernel of `1 - f`. -/
theorem residualLinearMap_eq_zero_iff (f : Isometry q q) (y : V) :
    residualLinearMap f y = 0 ↔ f.toLinearEquiv y = y := by
  rw [residualLinearMap_apply, sub_eq_zero, eq_comm]

/-- Every fixed vector is orthogonal to the residual space. -/
theorem bilin_fixed_residual_eq_zero (f : Isometry q q) {w : V}
    (hw : f.toLinearEquiv w = w) (y : residualSpace f) :
    q.bilin w (y : V) = 0 := by
  rcases y.property with ⟨z, hz⟩
  rw [← hz, residualLinearMap_apply]
  simp only [LinearMap.BilinForm.sub_right]
  have hmap := f.map_bilin w z
  rw [hw] at hmap
  rw [hmap]
  exact sub_self _

/-- The right orthogonal complement of the residual space is exactly the
fixed space. -/
theorem mem_orthogonal_residualSpace_iff (f : Isometry q q) (z : V) :
    z ∈ q.bilin.orthogonal (residualSpace f) ↔
      f.toLinearEquiv z = z := by
  constructor
  · intro hz
    apply sub_eq_zero.mp
    apply q.nondegenerate.1
    intro y
    have hresidual :
        residualLinearMap f (f.toLinearEquiv.symm y) ∈ residualSpace f :=
      LinearMap.mem_range_self _ _
    have hzpair := hz _ hresidual
    rw [residualLinearMap_apply,
      f.toLinearEquiv.apply_symm_apply] at hzpair
    change q.bilin
        (f.toLinearEquiv.symm y - y) z = 0 at hzpair
    rw [q.isSymm.eq] at hzpair
    have hmap := f.map_bilin z (f.toLinearEquiv.symm y)
    rw [f.toLinearEquiv.apply_symm_apply] at hmap
    simp only [LinearMap.BilinForm.sub_left]
    rw [hmap]
    simpa only [LinearMap.BilinForm.sub_right] using hzpair
  · intro hz y hy
    rw [q.isSymm.eq]
    exact bilin_fixed_residual_eq_zero f hz ⟨y, hy⟩

/--
Two right inverses of the residual map give the same pairing against residual
vectors.
-/
theorem bilin_section_independent (f : Isometry q q)
    (s t : residualSpace f →ₗ[K] V)
    (hs : (residualMap f).comp s = LinearMap.id)
    (ht : (residualMap f).comp t = LinearMap.id)
    (y z : residualSpace f) :
    q.bilin (s y) (z : V) = q.bilin (t y) (z : V) := by
  have hkernel : residualLinearMap f (s y - t y) = 0 := by
    have hresidual : residualMap f (s y - t y) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hs, LinearMap.id_apply,
        ← LinearMap.comp_apply, ht, LinearMap.id_apply, sub_self]
    exact congrArg Subtype.val hresidual
  have hfixed : f.toLinearEquiv (s y - t y) = s y - t y :=
    (residualLinearMap_eq_zero_iff f _).1 hkernel
  have horth := bilin_fixed_residual_eq_zero f hfixed z
  simp only [LinearMap.BilinForm.sub_left, sub_eq_zero] at horth
  exact horth

/-- The Wall bilinear form on the residual space. -/
noncomputable def wallForm (f : Isometry q q) :
    LinearMap.BilinForm K (residualSpace f) :=
  (2 : K) • q.bilin.comp (residualSection f)
    (Submodule.subtype (residualSpace f))

@[simp]
theorem wallForm_apply (f : Isometry q q)
    (y z : residualSpace f) :
    wallForm f y z = 2 * q.bilin (residualSection f y) (z : V) := by
  simp [wallForm]

/-- The Wall form satisfies its defining identity on explicit residuals. -/
theorem wallForm_residualMap_left (f : Isometry q q) (w : V)
    (z : residualSpace f) :
    wallForm f (residualMap f w) z = 2 * q.bilin w (z : V) := by
  rw [wallForm_apply]
  have hsection : residualLinearMap f
      (residualSection f (residualMap f w) - w) = 0 := by
    have hresidual : residualMap f
        (residualSection f (residualMap f w) - w) = 0 := by
      rw [map_sub, residualMap_residualSection, sub_self]
    exact congrArg Subtype.val hresidual
  have hfixed : f.toLinearEquiv
      (residualSection f (residualMap f w) - w) =
        residualSection f (residualMap f w) - w :=
    (residualLinearMap_eq_zero_iff f _).1 hsection
  have horth := bilin_fixed_residual_eq_zero f hfixed z
  simp only [LinearMap.BilinForm.sub_left, sub_eq_zero] at horth
  rw [horth]

/-- The quadratic form associated with the Wall form is the restriction of
the ambient quadratic form to the residual space.  This is the identity
`chi_f(y,y) = Q(y)` used in Wall's reflection-reduction argument. -/
theorem wallForm_self_eq_quadratic (f : Isometry q q)
    (y : residualSpace f) :
    wallForm f y y = q.quadratic (y : V) := by
  let w : V := residualSection f y
  have hw : residualMap f w = y := residualMap_residualSection f y
  have hy : (y : V) = w - f.toLinearEquiv w := by
    have hcoe := congrArg Subtype.val hw
    change w - f.toLinearEquiv w = (y : V) at hcoe
    exact hcoe.symm
  calc
    wallForm f y y = wallForm f (residualMap f w) y := by rw [hw]
    _ = 2 * q.bilin w (y : V) := wallForm_residualMap_left f w y
    _ = q.quadratic (y : V) := by
      rw [hy]
      simp only [quadratic, LinearMap.BilinForm.sub_right,
        LinearMap.BilinForm.sub_left]
      have hmap := f.map_bilin w w
      rw [hmap]
      have hsymm : q.bilin (f.toLinearEquiv w) w =
          q.bilin w (f.toLinearEquiv w) := q.isSymm.eq _ _
      rw [hsymm]
      ring

/-- The Wall form separates vectors in its left argument. -/
theorem wallForm_separatingLeft [CharZero K] [FiniteDimensional K V]
    (f : Isometry q q) : (wallForm f).SeparatingLeft := by
  intro y hy
  let w : V := residualSection f y
  have horthogonal : ∀ z : V,
      q.bilin (w - f.toLinearEquiv.symm w) z = 0 := by
    intro z
    have hwall := hy (residualMap f z)
    rw [wallForm_apply] at hwall
    change 2 * q.bilin w (z - f.toLinearEquiv z) = 0 at hwall
    have htwo : (2 : K) ≠ 0 := by norm_num
    have hpair : q.bilin w (z - f.toLinearEquiv z) = 0 :=
      (mul_eq_zero.mp hwall).resolve_left htwo
    simp only [LinearMap.BilinForm.sub_right] at hpair
    have hmap := f.map_bilin (f.toLinearEquiv.symm w) z
    rw [f.toLinearEquiv.apply_symm_apply] at hmap
    simp only [LinearMap.BilinForm.sub_left]
    rw [← hmap]
    exact hpair
  have hw : w = f.toLinearEquiv.symm w := by
    exact sub_eq_zero.mp (q.nondegenerate.1 _ horthogonal)
  have hfixed : f.toLinearEquiv w = w := by
    calc
      f.toLinearEquiv w =
          f.toLinearEquiv (f.toLinearEquiv.symm w) := congrArg _ hw
      _ = w := f.toLinearEquiv.apply_symm_apply w
  rw [← residualMap_residualSection f y]
  apply Subtype.ext
  change w - f.toLinearEquiv w = 0
  rw [hfixed, sub_self]

/-- The Wall form is nondegenerate in finite dimension. -/
theorem wallForm_nondegenerate [CharZero K] [FiniteDimensional K V]
    (f : Isometry q q) : (wallForm f).Nondegenerate :=
  LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    (wallForm_separatingLeft f)

/-- A chosen finite basis of the residual space. -/
noncomputable def wallBasis [FiniteDimensional K V] (f : Isometry q q) :
    Module.Basis (Fin (Module.finrank K (residualSpace f))) K
      (residualSpace f) :=
  Module.finBasis K (residualSpace f)

/-- The determinant of the Wall form in the chosen residual basis. -/
noncomputable def wallDeterminant [FiniteDimensional K V]
    (f : Isometry q q) : K :=
  Matrix.det (LinearMap.BilinForm.toMatrix (wallBasis f) (wallForm f))

/-- The Wall determinant is nonzero. -/
theorem wallDeterminant_ne_zero [CharZero K] [FiniteDimensional K V]
    (f : Isometry q q) : wallDeterminant f ≠ 0 := by
  rw [wallDeterminant]
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (wallBasis f)).1
    (wallForm_nondegenerate f)

end QuadraticSpace

end Bong
