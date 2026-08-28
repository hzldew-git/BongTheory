/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaFundamentalIdeals

/-!
# Product-defect sums under square rescaling

Absolute quadratic defects are covariant under multiplication by squares.
This file packages the corresponding monotonicity and exact rescaling laws
for O'Meara's product-defect sums.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Product-defect sums are monotone in both scalar sets. -/
theorem productDefectSum_mono {A B C D : Set K}
    (hAC : A ⊆ C) (hBD : B ⊆ D) :
    productDefectSum A B ≤ productDefectSum C D := by
  unfold productDefectSum
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  let c : C := ⟨a.1, hAC a.2⟩
  let d : D := ⟨b.1, hBD b.2⟩
  exact (le_iSup (fun y : D ↦
    scalarQuadraticDefectIdeal (c.1 * y.1)) d).trans
      (le_iSup (fun x : C ↦
        ⨆ y : D, scalarQuadraticDefectIdeal (x.1 * y.1)) c)

/-- Absolute quadratic-defect ideals transform exactly under a square
factor. -/
theorem quadraticDefectIdeal_mul_square_eq
    (a c : Kˣ) :
    quadraticDefectIdeal (a * c ^ 2) =
      scalarIdeal ((c ^ 2 : Kˣ) : K) (quadraticDefectIdeal a) := by
  unfold quadraticDefectIdeal
  rw [quadraticDefect_mul_square]
  by_cases htop : quadraticDefect K a = ⊤
  · simp [htop, scalarIdeal]
  · rw [if_neg htop, if_neg htop, scalarIdeal_powerIdeal_units,
      ordUnit_mul, ordUnit_pow]
    congr 1
    ring

/-- Scalar extension of square covariance, including the zero scalar. -/
theorem scalarQuadraticDefectIdeal_mul_square_eq
    (c : Kˣ) (x : K) :
    scalarQuadraticDefectIdeal (((c ^ 2 : Kˣ) : K) * x) =
      scalarIdeal ((c ^ 2 : Kˣ) : K)
        (scalarQuadraticDefectIdeal x) := by
  by_cases hx : x = 0
  · subst x
    simp [scalarIdeal]
  · let a : Kˣ := Units.mk0 x hx
    have hcx : (((c ^ 2 : Kˣ) : K) * x) =
        ((a * c ^ 2 : Kˣ) : K) := by
      change ((c ^ 2 : Kˣ) : K) * (a : K) =
        ((a * c ^ 2 : Kˣ) : K)
      simp only [Units.val_mul, mul_comm]
    have hxIdeal : scalarQuadraticDefectIdeal x = quadraticDefectIdeal a := by
      change scalarQuadraticDefectIdeal (a : K) = quadraticDefectIdeal a
      exact scalarQuadraticDefectIdeal_eq_quadraticDefectIdeal a
    rw [hcx, scalarQuadraticDefectIdeal_eq_quadraticDefectIdeal,
      hxIdeal, quadraticDefectIdeal_mul_square_eq]

/-- Multiplication of the first norm group by `c²` multiplies the entire
product-defect sum by the same ideal factor. -/
theorem scalarIdeal_productDefectSum_le_of_sq_mul_subset
    (c : Kˣ) {A B C : Set K}
    (hAC : ∀ x ∈ A, (((c ^ 2 : Kˣ) : K) * x) ∈ C) :
    scalarIdeal ((c ^ 2 : Kˣ) : K) (productDefectSum A B) ≤
      productDefectSum C B := by
  unfold productDefectSum scalarIdeal
  rw [Submodule.map_iSup]
  apply iSup_le
  intro a
  rw [Submodule.map_iSup]
  apply iSup_le
  intro b
  change scalarIdeal ((c ^ 2 : Kˣ) : K)
      (scalarQuadraticDefectIdeal (a.1 * b.1)) ≤
    ⨆ a : C, ⨆ b : B, scalarQuadraticDefectIdeal (a.1 * b.1)
  rw [← scalarQuadraticDefectIdeal_mul_square_eq]
  let cA : C := ⟨((c ^ 2 : Kˣ) : K) * a.1, hAC a.1 a.2⟩
  have hterm := (le_iSup (fun y : B ↦
      scalarQuadraticDefectIdeal (cA.1 * y.1)) b).trans
        (le_iSup (fun x : C ↦
          ⨆ y : B, scalarQuadraticDefectIdeal (x.1 * y.1)) cA)
  simpa only [cA, mul_assoc] using hterm

/-- Composition rule for scalar multiplication of coefficient ideals. -/
theorem scalarIdeal_scalarIdeal_eq
    (a b : K) (I : CoefficientIdeal (K := K)) :
    scalarIdeal a (scalarIdeal b I) = scalarIdeal (a * b) I := by
  ext z
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by simp only [coefficientMulLinearMap_apply, mul_assoc]⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨b * y, ⟨y, hy, rfl⟩, ?_⟩
    simp only [coefficientMulLinearMap_apply, mul_assoc]

@[simp]
theorem scalarIdeal_one (I : CoefficientIdeal (K := K)) :
    scalarIdeal (1 : K) I = I := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ∈ I at hx
    simpa only [coefficientMulLinearMap_apply, one_mul] using hx
  · intro hz
    exact ⟨z, hz, by simp only [coefficientMulLinearMap_apply, one_mul]⟩

/-- Scalar multiplication distributes over the supremum of two ideals. -/
theorem scalarIdeal_sup (c : K)
    (I P : CoefficientIdeal (K := K)) :
    scalarIdeal c (I ⊔ P) = scalarIdeal c I ⊔ scalarIdeal c P := by
  unfold scalarIdeal
  exact Submodule.map_sup _ _ _

/-- A common upper bound for two scalar images bounds the scalar image of
their supremum. -/
theorem scalarIdeal_sup_le (c : K)
    (I P Q : CoefficientIdeal (K := K))
    (hI : scalarIdeal c I ≤ Q) (hP : scalarIdeal c P ≤ Q) :
    scalarIdeal c (I ⊔ P) ≤ Q := by
  unfold scalarIdeal
  rintro x ⟨y, hy, rfl⟩
  rcases (Submodule.mem_sup).1 hy with ⟨yI, hyI, yP, hyP, rfl⟩
  rw [map_add]
  apply Q.add_mem
  · apply hI
    exact ⟨yI, hyI, rfl⟩
  · apply hP
    exact ⟨yP, hyP, rfl⟩

/-- Square rescaling in both arguments gives the corresponding one-sided
containment for product-defect sums. -/
theorem scalarIdeal_productDefectSum_le_of_two_sq_mul_subsets
    (c d : Kˣ) {A B C D : Set K}
    (hAC : ∀ x ∈ A, (((c ^ 2 : Kˣ) : K) * x) ∈ C)
    (hBD : ∀ x ∈ B, (((d ^ 2 : Kˣ) : K) * x) ∈ D) :
    scalarIdeal ((((c * d) ^ 2 : Kˣ) : K))
        (productDefectSum A B) ≤
      productDefectSum C D := by
  have hfirst := scalarIdeal_productDefectSum_le_of_sq_mul_subset
    (B := B) c hAC
  have hsecond : scalarIdeal ((d ^ 2 : Kˣ) : K)
      (productDefectSum C B) ≤ productDefectSum C D := by
    calc
      scalarIdeal ((d ^ 2 : Kˣ) : K) (productDefectSum C B) =
          scalarIdeal ((d ^ 2 : Kˣ) : K) (productDefectSum B C) := by
        rw [productDefectSum_comm C B]
      _ ≤ productDefectSum D C :=
        scalarIdeal_productDefectSum_le_of_sq_mul_subset d hBD
      _ = productDefectSum C D := productDefectSum_comm D C
  calc
    scalarIdeal ((((c * d) ^ 2 : Kˣ) : K))
        (productDefectSum A B) =
      scalarIdeal ((d ^ 2 : Kˣ) : K)
        (scalarIdeal ((c ^ 2 : Kˣ) : K)
          (productDefectSum A B)) := by
        rw [scalarIdeal_scalarIdeal_eq]
        congr 1
        norm_cast
        simp [mul_pow, mul_comm]
    _ ≤ scalarIdeal ((d ^ 2 : Kˣ) : K) (productDefectSum C B) :=
      Submodule.map_mono hfirst
    _ ≤ productDefectSum C D := hsecond

/-- Exact covariance of product-defect sums under independently chosen
square rescalings of the two scalar sets. -/
theorem productDefectSum_eq_scalarIdeal_of_sq_scaled
    (c d : Kˣ) {A B C D : Set K}
    (hC : ∀ z : K, z ∈ C ↔ (((c ^ 2)⁻¹ : Kˣ) : K) * z ∈ A)
    (hD : ∀ z : K, z ∈ D ↔ (((d ^ 2)⁻¹ : Kˣ) : K) * z ∈ B) :
    productDefectSum C D =
      scalarIdeal ((((c * d) ^ 2 : Kˣ) : K))
        (productDefectSum A B) := by
  apply le_antisymm
  · have hreverse :=
      scalarIdeal_productDefectSum_le_of_two_sq_mul_subsets
        c⁻¹ d⁻¹
        (A := C) (B := D) (C := A) (D := B)
        (fun z hz ↦ (hC z).1 hz)
        (fun z hz ↦ (hD z).1 hz)
    have hmapped := Submodule.map_mono hreverse
      (f := coefficientMulLinearMap (K := K) (((c * d) ^ 2 : Kˣ) : K))
    change scalarIdeal (((c * d) ^ 2 : Kˣ) : K)
        (scalarIdeal ((((c⁻¹ * d⁻¹) ^ 2 : Kˣ) : K))
          (productDefectSum C D)) ≤
      scalarIdeal (((c * d) ^ 2 : Kˣ) : K)
        (productDefectSum A B) at hmapped
    calc
      productDefectSum C D =
          scalarIdeal (((c * d) ^ 2 : Kˣ) : K)
            (scalarIdeal ((((c⁻¹ * d⁻¹) ^ 2 : Kˣ) : K))
              (productDefectSum C D)) := by
        rw [scalarIdeal_scalarIdeal_eq]
        have hfactor : (((c * d) ^ 2 : Kˣ) : K) *
            (((c⁻¹ * d⁻¹) ^ 2 : Kˣ) : K) = 1 := by
          have hu : (c * d) ^ 2 * (c⁻¹ * d⁻¹) ^ 2 = (1 : Kˣ) := by
            calc
              (c * d) ^ 2 * (c⁻¹ * d⁻¹) ^ 2 =
                  (c ^ 2 * (c ^ 2)⁻¹) * (d ^ 2 * (d ^ 2)⁻¹) := by
                simp only [mul_pow, inv_pow]
                ac_rfl
              _ = 1 := by simp
          simpa only [Units.val_mul, Units.val_one] using congrArg Units.val hu
        rw [hfactor, scalarIdeal_one]
      _ ≤ scalarIdeal (((c * d) ^ 2 : Kˣ) : K)
          (productDefectSum A B) := hmapped
  · apply scalarIdeal_productDefectSum_le_of_two_sq_mul_subsets c d
    · intro x hx
      apply (hC (((c ^ 2 : Kˣ) : K) * x)).2
      have hcancel : (((c ^ 2)⁻¹ : Kˣ) : K) *
          (((c ^ 2 : Kˣ) : K) * x) = x := by
        simp only [Units.val_inv_eq_inv_val]
        rw [← mul_assoc]
        rw [inv_mul_cancel₀ (Units.ne_zero (c ^ 2)), one_mul]
      rwa [hcancel]
    · intro x hx
      apply (hD (((d ^ 2 : Kˣ) : K) * x)).2
      have hcancel : (((d ^ 2)⁻¹ : Kˣ) : K) *
          (((d ^ 2 : Kˣ) : K) * x) = x := by
        simp only [Units.val_inv_eq_inv_val]
        rw [← mul_assoc]
        rw [inv_mul_cancel₀ (Units.ne_zero (d ^ 2)), one_mul]
      rwa [hcancel]

end Lattice

end Bong
