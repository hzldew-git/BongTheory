/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.OrthogonalExtension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Reflection

/-!
# Reflections of quadratic spaces

For an anisotropic vector `x`, reflection in the hyperplane `x^⊥` is

`y ↦ y - (2 B(x,y) / Q(x)) x`.

The construction is the basic generator used by the spinor norm.
-/

namespace Bong

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The covector defining reflection in the hyperplane perpendicular to `x`. -/
noncomputable def reflectionFunctional (q : QuadraticSpace K V) (x : V) :
    Module.Dual K V :=
  (2 / q.quadratic x) • q.bilin x

@[simp]
theorem reflectionFunctional_apply (q : QuadraticSpace K V) (x y : V) :
    q.reflectionFunctional x y = 2 * q.bilin x y / q.quadratic x := by
  simp [reflectionFunctional]
  ring

/-- The reflection covector takes the value two on its anisotropic vector. -/
theorem reflectionFunctional_self (q : QuadraticSpace K V) {x : V}
    (anisotropic : q.IsAnisotropic x) : q.reflectionFunctional x x = 2 := by
  rw [reflectionFunctional_apply]
  change 2 * q.quadratic x / q.quadratic x = 2
  rw [mul_div_cancel_right₀ _ anisotropic]

/-- The linear reflection in the hyperplane `x^⊥`. -/
noncomputable def reflectionLinearEquiv (q : QuadraticSpace K V) (x : V)
    (anisotropic : q.IsAnisotropic x) : V ≃ₗ[K] V :=
  Module.reflection (q.reflectionFunctional_self anisotropic)

@[simp]
theorem reflectionLinearEquiv_apply (q : QuadraticSpace K V) (x : V)
    (anisotropic : q.IsAnisotropic x) (y : V) :
    q.reflectionLinearEquiv x anisotropic y =
      y - (2 * q.bilin x y / q.quadratic x) • x := by
  rw [reflectionLinearEquiv, Module.reflection_apply,
    reflectionFunctional_apply]

/-- Reflection is involutive. -/
theorem reflectionLinearEquiv_involutive (q : QuadraticSpace K V) (x : V)
    (anisotropic : q.IsAnisotropic x) :
    Function.Involutive (q.reflectionLinearEquiv x anisotropic) :=
  Module.involutive_reflection (q.reflectionFunctional_self anisotropic)

/-- A quadratic reflection has determinant `-1`. -/
theorem det_reflectionLinearEquiv [FiniteDimensional K V]
    (q : QuadraticSpace K V) {x : V} (anisotropic : q.IsAnisotropic x) :
    LinearEquiv.det (q.reflectionLinearEquiv x anisotropic) = (-1 : Kˣ) := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  let b := Module.finBasis K V
  rw [← LinearMap.det_toMatrix b]
  change Matrix.det
      (LinearMap.toMatrix b b
        (Module.preReflection x (q.reflectionFunctional x))) = -1
  rw [Module.preReflection]
  change Matrix.det
      (LinearMap.toMatrix b b
        (LinearMap.id - (q.reflectionFunctional x).smulRight x)) = -1
  simp only [map_sub, LinearMap.toMatrix_id,
    LinearMap.toMatrix_smulRight]
  let u : Fin (Module.finrank K V) → K := b.repr x
  let w : Fin (Module.finrank K V) → K :=
    (q.reflectionFunctional x) ∘ b
  change Matrix.det (1 - Matrix.vecMulVec u w) = -1
  have hmatrix :
      (1 - Matrix.vecMulVec u w : Matrix _ _ K) =
        1 + Matrix.replicateCol Unit (-u) * Matrix.replicateRow Unit w := by
    ext i j
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply]
    ring
  rw [hmatrix, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hdot : w ⬝ᵥ u = 2 := by
    change ∑ i, q.reflectionFunctional x (b i) * (b.repr x) i = 2
    calc
      ∑ i, q.reflectionFunctional x (b i) * (b.repr x) i =
          q.reflectionFunctional x
            (∑ i, (b.repr x) i • b i) := by
        simp only [map_sum, map_smul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = q.reflectionFunctional x x := by rw [b.sum_repr]
      _ = 2 := q.reflectionFunctional_self anisotropic
  change 1 + w ⬝ᵥ (-u) = -1
  rw [dotProduct_neg, hdot]
  ring

/-- Reflection negates its defining anisotropic vector. -/
@[simp]
theorem reflectionLinearEquiv_apply_self (q : QuadraticSpace K V) (x : V)
    (anisotropic : q.IsAnisotropic x) :
    q.reflectionLinearEquiv x anisotropic x = -x :=
  Module.reflection_apply_self (q.reflectionFunctional_self anisotropic)

/-- Reflection fixes every vector perpendicular to its defining vector. -/
@[simp]
theorem reflectionLinearEquiv_apply_of_mem_vectorOrthogonal
    (q : QuadraticSpace K V) (x : V) (anisotropic : q.IsAnisotropic x)
    (y : q.vectorOrthogonal x) :
    q.reflectionLinearEquiv x anisotropic (y : V) = y := by
  rw [reflectionLinearEquiv_apply]
  have hxy : q.bilin x (y : V) = 0 :=
    (q.mem_vectorOrthogonal_iff x y).1 y.property
  rw [hxy]
  simp

/-- Reflection in an anisotropic vector is a quadratic-space isometry. -/
noncomputable def reflectionIsometry (q : QuadraticSpace K V) (x : V)
    (anisotropic : q.IsAnisotropic x) : Isometry q q where
  toLinearEquiv := q.reflectionLinearEquiv x anisotropic
  map_bilin y z := by
    rw [reflectionLinearEquiv_apply, reflectionLinearEquiv_apply]
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    rw [q.isSymm.eq y x]
    rw [show q.bilin x x = q.quadratic x from rfl]
    field_simp [anisotropic]
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
    rw [hcancel]
    ring

/-- Reflection in `x - y` sends `x` to `y` when the two vectors have equal
quadratic value and their difference is anisotropic. -/
theorem reflectionLinearEquiv_sub_apply_left_of_equalValue
    (q : QuadraticSpace K V) (x y : V)
    (hsub : q.IsAnisotropic (x - y))
    (heq : q.quadratic x = q.quadratic y) :
    q.reflectionLinearEquiv (x - y) hsub x = y := by
  have hnumerator :
      2 * q.bilin (x - y) x = q.quadratic (x - y) := by
    simp only [quadratic, LinearMap.BilinForm.sub_left,
      LinearMap.BilinForm.sub_right]
    have heq' : q.bilin x x = q.bilin y y := heq
    rw [q.isSymm.eq y x]
    linear_combination heq'
  have hcoefficient :
      2 * q.bilin (x - y) x / q.quadratic (x - y) = 1 := by
    rw [hnumerator, div_self hsub]
  rw [q.reflectionLinearEquiv_apply, hcoefficient, one_smul]
  abel

/-- If equal-valued anisotropic vectors have isotropic difference, their sum
is anisotropic. -/
theorem isAnisotropic_add_of_not_isAnisotropic_sub
    (q : QuadraticSpace K V) (x y : V) (hx : q.IsAnisotropic x)
    (heq : q.quadratic x = q.quadratic y)
    (hsub : ¬q.IsAnisotropic (x - y)) :
    q.IsAnisotropic (x + y) := by
  intro hsum
  have hsubzero : q.quadratic (x - y) = 0 := by
    simpa [IsAnisotropic] using hsub
  have hfour : (4 : K) * q.quadratic x = 0 := by
    calc
      (4 : K) * q.quadratic x =
          q.quadratic (x + y) + q.quadratic (x - y) := by
        rw [q.quadratic_add x y]
        rw [show x - y = x + (-y) by abel, q.quadratic_add x (-y)]
        simp only [quadratic_neg, LinearMap.BilinForm.neg_right]
        rw [← heq]
        ring
      _ = 0 := by rw [hsum, hsubzero, add_zero]
  exact hx ((mul_eq_zero.mp hfour).resolve_left (by norm_num))

/-- Reflection in `x + y` sends `x` to `-y` for equal-valued vectors. -/
theorem reflectionLinearEquiv_add_apply_left_of_quadratic_eq
    (q : QuadraticSpace K V) (x y : V)
    (hsum : q.IsAnisotropic (x + y))
    (heq : q.quadratic x = q.quadratic y) :
    q.reflectionLinearEquiv (x + y) hsum x = -y := by
  have hnumerator :
      2 * q.bilin (x + y) x = q.quadratic (x + y) := by
    simp only [quadratic, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.add_right]
    have heq' : q.bilin x x = q.bilin y y := heq
    rw [q.isSymm.eq y x]
    linear_combination heq'
  have hcoefficient :
      2 * q.bilin (x + y) x / q.quadratic (x + y) = 1 := by
    rw [hnumerator, div_self hsum]
  rw [q.reflectionLinearEquiv_apply, hcoefficient, one_smul]
  abel

/-- An explicit one-vector Witt transporter.  One reflection suffices when
`x - y` is anisotropic; otherwise a reflection in `x + y`, followed by a
reflection in `y`, sends `x` to `y`. -/
noncomputable def equalValueTransportIsometry
    (q : QuadraticSpace K V) (x y : V)
    (hx : q.IsAnisotropic x) (hy : q.IsAnisotropic y)
    (heq : q.quadratic x = q.quadratic y) : Isometry q q := by
  classical
  exact if hsub : q.IsAnisotropic (x - y) then
      q.reflectionIsometry (x - y) hsub
    else
      (q.reflectionIsometry (x + y)
        (q.isAnisotropic_add_of_not_isAnisotropic_sub x y hx heq hsub)).trans
        (q.reflectionIsometry y hy)

@[simp]
theorem equalValueTransportIsometry_apply_left
    (q : QuadraticSpace K V) (x y : V)
    (hx : q.IsAnisotropic x) (hy : q.IsAnisotropic y)
    (heq : q.quadratic x = q.quadratic y) :
    (q.equalValueTransportIsometry x y hx hy heq).toLinearEquiv x = y := by
  classical
  rw [equalValueTransportIsometry]
  split
  · exact q.reflectionLinearEquiv_sub_apply_left_of_equalValue x y ‹_› heq
  · have hsum :=
      q.isAnisotropic_add_of_not_isAnisotropic_sub x y hx heq ‹_›
    change q.reflectionLinearEquiv y hy
      (q.reflectionLinearEquiv (x + y) hsum x) = y
    rw [q.reflectionLinearEquiv_add_apply_left_of_quadratic_eq x y hsum heq]
    calc
      q.reflectionLinearEquiv y hy (-y) =
          -q.reflectionLinearEquiv y hy y :=
        (q.reflectionLinearEquiv y hy).map_neg y
      _ = -(-y) := by rw [q.reflectionLinearEquiv_apply_self y hy]
      _ = y := neg_neg y

/-- Extending a reflection from `x^⊥` is reflection in the same tail vector. -/
theorem orthogonalExtensionIsometry_reflection
    (q : QuadraticSpace K V) (x : V) (anisotropic : q.IsAnisotropic x)
    (y : q.vectorOrthogonal x)
    (hy : (q.orthogonalSpace x anisotropic).IsAnisotropic y) :
    orthogonalExtensionIsometry
        ((q.orthogonalSpace x anisotropic).reflectionIsometry y hy) =
      q.reflectionIsometry (y : V) hy := by
  apply Isometry.ext
  intro z
  change orthogonalExtensionLinearEquiv
      ((q.orthogonalSpace x anisotropic).reflectionIsometry y hy) z =
    q.reflectionLinearEquiv (y : V) hy z
  rw [orthogonalExtensionLinearEquiv_apply,
    orthogonalExtensionLinearMap_apply]
  rw [reflectionIsometry, reflectionLinearEquiv_apply,
    reflectionLinearEquiv_apply]
  have hyx : q.bilin (y : V) x = 0 := by
    rw [q.isSymm.eq]
    exact (q.mem_vectorOrthogonal_iff x y).1 y.property
  have hpair : q.bilin (y : V) (q.orthogonalProjection x z) =
      q.bilin (y : V) z := by
    rw [q.orthogonalProjection_apply]
    simp only [LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_right, hyx, mul_zero, sub_zero]
  change (q.bilin x z / q.quadratic x) • x +
      (q.orthogonalProjection x z -
        (2 * q.bilin (y : V) (q.orthogonalProjection x z) /
          q.quadratic (y : V)) • (y : V)) =
    z - (2 * q.bilin (y : V) z / q.quadratic (y : V)) • (y : V)
  rw [hpair]
  have hdecompose := q.lineProjection_add_orthogonalProjection x z
  rw [q.lineProjection_apply] at hdecompose
  let t : V :=
    (2 * q.bilin (y : V) z / q.quadratic (y : V)) • (y : V)
  change (q.bilin x z / q.quadratic x) • x +
      (q.orthogonalProjection x z - t) = z - t
  calc
    _ = ((q.bilin x z / q.quadratic x) • x +
        q.orthogonalProjection x z) - t := by abel
    _ = z - t := by rw [hdecompose]

end QuadraticSpace

end Bong
