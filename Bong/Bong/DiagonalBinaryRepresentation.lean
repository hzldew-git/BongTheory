/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Classification
import Bong.Dyadic.HilbertSymbol

/-!
# Unary representation by a binary diagonal form

This file identifies representation of a nonzero unary diagonal form by a
nondegenerate binary diagonal form with the corresponding quadratic norm
equation.  It is the elementary bridge between the representation language
used in Beli's conditions and the Hilbert-symbol language used in Section 8.
-/

namespace Bong

open Dyadic

universe u

namespace DiagonalRepresents

variable {K : Type u} [Field K] [CharZero K]

/-- The linear embedding determined by a vector `(x,y)` in a binary
coordinate space. -/
noncomputable def unaryToBinaryLinearMap (x y : K) :
    (Fin 1 → K) →ₗ[K] (Fin 2 → K) where
  toFun z := Fin.cons (x * z 0) (fun _ ↦ y * z 0)
  map_add' z w := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
      simp [mul_add]
  map_smul' c z := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
      simp [mul_left_comm]

@[simp]
theorem unaryToBinaryLinearMap_zero (x y : K) (z : Fin 1 → K) :
    unaryToBinaryLinearMap x y z 0 = x * z 0 := by
  rfl

@[simp]
theorem unaryToBinaryLinearMap_one (x y : K) (z : Fin 1 → K) :
    unaryToBinaryLinearMap x y z 1 = y * z 0 := by
  rfl

theorem unaryToBinaryLinearMap_injective
    {x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    Function.Injective (unaryToBinaryLinearMap x y) := by
  intro z w hzw
  funext i
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  rcases hxy with hx | hy
  · have hzero := congrFun hzw (0 : Fin 2)
    simpa only [unaryToBinaryLinearMap_zero] using
      (mul_left_cancel₀ hx hzero)
  · have hone := congrFun hzw (1 : Fin 2)
    simpa only [unaryToBinaryLinearMap_one] using
      (mul_left_cancel₀ hy hone)

/-- A nonzero unary coefficient `b` is represented by `[a₁,a₂]` exactly
when `b/a₁` is a norm from the quadratic algebra of discriminant
`-a₁a₂`. -/
theorem unary_binary_iff_isQuadraticNorm
    (a₁ a₂ b : Kˣ) :
    DiagonalRepresents (fun _ : Fin 1 ↦ (b : K))
        (Fin.cons (a₁ : K) (fun _ : Fin 1 ↦ (a₂ : K))) ↔
      IsQuadraticNorm K (-(a₁ * a₂)) (b * a₁⁻¹) := by
  constructor
  · rintro ⟨f, _, hquadratic⟩
    let e : Fin 1 → K := fun _ ↦ 1
    let x : K := f e 0
    let z : K := f e 1
    have hvalue :
        (a₁ : K) * x ^ 2 + (a₂ : K) * z ^ 2 = (b : K) := by
      simpa [diagonalQuadratic, e, x, z] using hquadratic e
    refine ⟨x, z / (a₁ : K), ?_⟩
    rw [Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val]
    change x ^ 2 - (-((a₁ : K) * (a₂ : K))) *
        (z / (a₁ : K)) ^ 2 = (b : K) * (a₁ : K)⁻¹
    calc
      x ^ 2 - (-((a₁ : K) * (a₂ : K))) *
          (z / (a₁ : K)) ^ 2 =
          ((a₁ : K) * x ^ 2 + (a₂ : K) * z ^ 2) / (a₁ : K) := by
            field_simp [Units.ne_zero a₁]
            ring
      _ = (b : K) / (a₁ : K) := by rw [hvalue]
      _ = (b : K) * (a₁ : K)⁻¹ := div_eq_mul_inv _ _
  · rintro ⟨x, y, hnorm⟩
    rw [Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val] at hnorm
    change x ^ 2 - (-((a₁ : K) * (a₂ : K))) * y ^ 2 =
      (b : K) * (a₁ : K)⁻¹ at hnorm
    have hvalue :
        (a₁ : K) * x ^ 2 + (a₂ : K) * ((a₁ : K) * y) ^ 2 =
          (b : K) := by
      calc
        (a₁ : K) * x ^ 2 + (a₂ : K) * ((a₁ : K) * y) ^ 2 =
            (a₁ : K) *
              (x ^ 2 - (-((a₁ : K) * (a₂ : K))) * y ^ 2) := by
                ring
        _ = (a₁ : K) * ((b : K) * (a₁ : K)⁻¹) := by rw [hnorm]
        _ = (b : K) := by field_simp [Units.ne_zero a₁]
    have hxy : x ≠ 0 ∨ (a₁ : K) * y ≠ 0 := by
      by_contra hnot
      push Not at hnot
      rw [hnot.1, hnot.2] at hvalue
      have hzero : (0 : K) = (b : K) := by simpa using hvalue
      exact Units.ne_zero b hzero.symm
    refine ⟨unaryToBinaryLinearMap x ((a₁ : K) * y),
      unaryToBinaryLinearMap_injective hxy, ?_⟩
    intro t
    have ht : ∀ i : Fin 1, t i = t 0 := by
      intro i
      rw [Fin.eq_zero i]
    simp only [diagonalQuadratic, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_zero,
      unaryToBinaryLinearMap_zero, unaryToBinaryLinearMap_one,
      Finset.sum_empty, add_zero]
    change
      (a₁ : K) * (x * t 0) ^ 2 +
          (a₂ : K) * (((a₁ : K) * y) * t 0) ^ 2 =
        (b : K) * (t 0) ^ 2
    rw [← hvalue]
    ring

/-- Hilbert-symbol form of `unary_binary_iff_isQuadraticNorm`. -/
theorem unary_binary_iff_hilbertSymbol_one
    (a₁ a₂ b : Kˣ) :
    DiagonalRepresents (fun _ : Fin 1 ↦ (b : K))
        (Fin.cons (a₁ : K) (fun _ : Fin 1 ↦ (a₂ : K))) ↔
      hilbertSymbol K (b * a₁⁻¹) (-(a₁ * a₂)) = 1 := by
  rw [hilbertSymbol_comm K, hilbertSymbol_eq_one_iff,
    unary_binary_iff_isQuadraticNorm]

end DiagonalRepresents

end Bong
