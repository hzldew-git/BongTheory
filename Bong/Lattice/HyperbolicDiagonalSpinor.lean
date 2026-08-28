/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.HyperbolicDiagonal
import Bong.Lattice.SpinorNormMultiplicative

/-!
# Spinor norm of a hyperbolic diagonal automorphism

The integral isometry `(x,y) ↦ (t x,t⁻¹ y)` is the product of the
reflections in `(1,1)` and `(t,1)`.  Consequently its spinor norm is the
square class of `t`.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The spinor norm of the integral hyperbolic diagonal automorphism is its
diagonal multiplier modulo squares. -/
theorem integralSpinorNorm_scaledHyperbolicDiagonalLatticeIsometry
    (s t : Kˣ) (ht : IsValuationUnit K (t : K)) :
    integralSpinorNorm
        (scaledHyperbolicDiagonalLatticeIsometry s t ht) =
      squareClass K t := by
  let q := QuadraticSpace.hyperbolicPlane s
  let x : Fin 2 → K := ![1, 1]
  let y : Fin 2 → K := ![(t : K), 1]
  have hx : q.IsAnisotropic x := by
    rw [QuadraticSpace.IsAnisotropic,
      QuadraticSpace.hyperbolicPlane_quadratic_apply]
    change 2 * (s : K) * (1 * 1) ≠ 0
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Units.ne_zero s)) (by norm_num)
  have hy : q.IsAnisotropic y := by
    rw [QuadraticSpace.IsAnisotropic,
      QuadraticSpace.hyperbolicPlane_quadratic_apply]
    change 2 * (s : K) * ((t : K) * 1) ≠ 0
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Units.ne_zero s))
      (mul_ne_zero (Units.ne_zero t) (by norm_num))
  have hfactor :
      (scaledHyperbolicDiagonalLatticeIsometry s t ht).toQuadraticSpaceIsometry =
        (q.reflectionIsometry x hx).trans (q.reflectionIsometry y hy) := by
    apply QuadraticSpace.Isometry.ext
    intro z
    funext i
    fin_cases i
    · change (t : K) * z 0 =
        (q.reflectionLinearEquiv y hy)
          ((q.reflectionLinearEquiv x hx) z) 0
      rw [
        QuadraticSpace.reflectionLinearEquiv_apply,
        QuadraticSpace.reflectionLinearEquiv_apply]
      simp only [q, x, y, QuadraticSpace.hyperbolicPlane_bilin_apply,
        QuadraticSpace.hyperbolicPlane_quadratic_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        one_mul, mul_one]
      field_simp [Units.ne_zero s, Units.ne_zero t]
      ring
    · change ((t⁻¹ : Kˣ) : K) * z 1 =
        (q.reflectionLinearEquiv y hy)
          ((q.reflectionLinearEquiv x hx) z) 1
      rw [
        QuadraticSpace.reflectionLinearEquiv_apply,
        QuadraticSpace.reflectionLinearEquiv_apply]
      simp only [q, x, y, QuadraticSpace.hyperbolicPlane_bilin_apply,
        QuadraticSpace.hyperbolicPlane_quadratic_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        one_mul, mul_one]
      simp only [Units.val_inv_eq_inv_val]
      field_simp [Units.ne_zero s, Units.ne_zero t]
      ring
  change QuadraticSpace.spinorNorm
      (scaledHyperbolicDiagonalLatticeIsometry s t ht).toQuadraticSpaceIsometry = _
  rw [hfactor, QuadraticSpace.spinorNorm_trans,
    QuadraticSpace.spinorNorm_reflection,
    QuadraticSpace.spinorNorm_reflection]
  have hqx : Units.mk0 (q.quadratic x) hx =
      Units.mk0 (2 * (s : K))
        (mul_ne_zero (by norm_num) (Units.ne_zero s)) := by
    apply Units.ext
    simp [q, x, QuadraticSpace.hyperbolicPlane_quadratic_apply]
  have hqy : Units.mk0 (q.quadratic y) hy =
      Units.mk0 (2 * (s : K) * (t : K))
        (mul_ne_zero (mul_ne_zero (by norm_num) (Units.ne_zero s))
          (Units.ne_zero t)) := by
    apply Units.ext
    simp [q, y, QuadraticSpace.hyperbolicPlane_quadratic_apply]
  rw [hqx, hqy]
  let twoS : Kˣ := Units.mk0 (2 * (s : K))
    (mul_ne_zero (by norm_num) (Units.ne_zero s))
  have hprod :
      Units.mk0 (2 * (s : K))
          (mul_ne_zero (by norm_num) (Units.ne_zero s)) *
        Units.mk0 (2 * (s : K) * (t : K))
          (mul_ne_zero (mul_ne_zero (by norm_num) (Units.ne_zero s))
            (Units.ne_zero t)) = t * twoS ^ 2 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0, Units.val_pow_eq_pow_val]
    dsimp [twoS]
    ring
  change squareClass K
      (Units.mk0 (2 * (s : K))
          (mul_ne_zero (by norm_num) (Units.ne_zero s)) *
        Units.mk0 (2 * (s : K) * (t : K))
          (mul_ne_zero (mul_ne_zero (by norm_num) (Units.ne_zero s))
            (Units.ne_zero t))) = squareClass K t
  rw [hprod]
  exact squareClass_mul_square K t twoS

end Lattice

end Bong
