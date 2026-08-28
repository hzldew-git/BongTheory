/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalHeadCancellation

/-!
# Coordinate-square isometries of finite diagonal spaces

Multiplying each diagonal coefficient by an independently chosen nonzero
square does not change the isometry class.  This elementary construction is
used by Beli (2019), Lemma 7.19 in its type-III branch.
-/

namespace Bong

universe u

namespace QuadraticSpace

variable {K : Type u} [Field K]

/-- Divide coordinate `i` by the unit `u i`. -/
noncomputable def diagonalSquareLinearEquiv {n : Nat}
    (u : Fin n → Kˣ) : (Fin n → K) ≃ₗ[K] (Fin n → K) where
  toFun x i := (((u i)⁻¹ : Kˣ) : K) * x i
  invFun x i := (u i : K) * x i
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem diagonalSquareLinearEquiv_apply {n : Nat}
    (u : Fin n → Kˣ) (x : Fin n → K) (i : Fin n) :
    diagonalSquareLinearEquiv u x i = (((u i)⁻¹ : Kˣ) : K) * x i :=
  rfl

/-- Finite diagonal forms whose coefficients differ coordinatewise by
nonzero squares are explicitly isometric. -/
theorem finiteDiagonal_isIsometric_of_eq_square_mul {n : Nat}
    (a b : Fin n → K) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (u : Fin n → Kˣ) (hcoeff : ∀ i, b i = (u i : K) ^ 2 * a i) :
    (finiteDiagonal a ha).IsIsometric (finiteDiagonal b hb) := by
  refine ⟨{
    toLinearEquiv := diagonalSquareLinearEquiv u
    map_bilin := ?_ }⟩
  intro x y
  rw [finiteDiagonal_bilin_apply, finiteDiagonal_bilin_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcoeff i]
  simp only [diagonalSquareLinearEquiv_apply, Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero]

end QuadraticSpace

end Bong
