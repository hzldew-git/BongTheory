/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalHyperbolicBlocks
import Bong.Lattice.CodimensionOneDeterminantCancellation

/-!
# Binary spaces with hyperbolic determinant class

This file supplies the field-space cancellation used in the even branch of
O'Meara 93:28.  A binary quadratic space whose determinant class is the class
of `-1` is explicitly diagonalized and identified with the standard
hyperbolic plane.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K]

/-- Reindexing all coordinates of a finite diagonal quadratic space gives an
isometric finite diagonal space. -/
noncomputable def finiteDiagonalReindexIsometry
    {m n : Nat} (a : Fin m → K) (ha : ∀ i, a i ≠ 0)
    (e : Fin n ≃ Fin m) :
    Isometry (finiteDiagonal a ha)
      (finiteDiagonal (fun i ↦ a (e i)) (fun i ↦ ha (e i))) where
  toLinearEquiv :=
    (LinearEquiv.piCongrLeft K (fun _ : Fin m ↦ K) e).symm
  map_bilin := by
    intro x y
    rw [finiteDiagonal_bilin_apply, finiteDiagonal_bilin_apply]
    let E := LinearEquiv.piCongrLeft K (fun _ : Fin m ↦ K) e
    have hx (i : Fin n) : E.symm x i = x (e i) := by
      have hfun : E.symm x = fun j ↦ x (e j) := by
        apply E.injective
        change E (E.symm x) = E (fun j ↦ x (e j))
        rw [E.apply_symm_apply]
        funext j
        change x j =
          (Equiv.piCongrLeft (fun _ : Fin m ↦ K) e)
            (fun k ↦ x (e k)) j
        simpa using (Equiv.piCongrLeft_apply_apply
          (fun _ : Fin m ↦ K) e (fun k ↦ x (e k)) (e.symm j)).symm
      exact congrFun hfun i
    have hy (i : Fin n) : E.symm y i = y (e i) := by
      have hfun : E.symm y = fun j ↦ y (e j) := by
        apply E.injective
        change E (E.symm y) = E (fun j ↦ y (e j))
        rw [E.apply_symm_apply]
        funext j
        change y j =
          (Equiv.piCongrLeft (fun _ : Fin m ↦ K) e)
            (fun k ↦ y (e k)) j
        simpa using (Equiv.piCongrLeft_apply_apply
          (fun _ : Fin m ↦ K) e (fun k ↦ y (e k)) (e.symm j)).symm
      exact congrFun hfun i
    calc
      (∑ i, a (e i) * E.symm x i * E.symm y i) =
          ∑ i, a (e i) * x (e i) * y (e i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hx i, hy i]
      _ = ∑ i, a i * x i * y i :=
        Equiv.sum_comp e (fun i ↦ a i * x i * y i)

variable [ValuativeRel K] [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- If the product of two diagonal coefficients has square class `-1`,
their signed ratio is a square. -/
theorem isSquare_neg_div_of_squareClass_mul_eq_neg_one
    (first second : Kˣ)
    (hclasses : squareClass K (first * second) =
      squareClass K (-1 : Kˣ)) :
    IsSquare (-(first / second)) := by
  have hsquareProduct : IsSquare ((first * second) * (-1 : Kˣ)) :=
    isSquare_mul_of_squareClass_eq _ _ hclasses
  rcases hsquareProduct with ⟨t, ht⟩
  refine ⟨t / second, ?_⟩
  calc
    -(first / second) =
        ((first * second) * (-1 : Kˣ)) / (second * second) := by
      apply Units.ext
      simp only [div_eq_mul_inv, Units.val_neg, Units.val_mul,
        Units.val_inv_eq_inv_val, Units.val_one]
      field_simp [Units.ne_zero]
    _ = (t * t) / (second * second) := by rw [ht]
    _ = (t / second) * (t / second) := by
      apply Units.ext
      simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp [Units.ne_zero]

/-- A binary quadratic space with determinant class `-1` is hyperbolic. -/
theorem rankTwo_isIsometric_hyperbolicPlane_one_of_determinantClass_eq
    [FiniteDimensional K V]
    (q : QuadraticSpace K V) (L : Lattice K V)
    (hfinrank : finrank K V = 2)
    (hdet : Lattice.determinantClass q L = unitSquareClass K (-1 : Kˣ)) :
    q.IsIsometric (hyperbolicPlane (1 : Kˣ)) := by
  let e : Fin 2 ≃ Fin (finrank K V) := finCongr hfinrank.symm
  let c : Fin 2 → Kˣ := fun i ↦ q.diagonalUnits (e i)
  have hproduct : c 0 * c 1 =
      diagonalUnitDeterminant q.diagonalUnits := by
    unfold diagonalUnitDeterminant c
    simpa only [Fin.prod_univ_two] using e.prod_comp q.diagonalUnits
  have hclasses : squareClass K (c 0 * c 1) = squareClass K (-1 : Kˣ) := by
    rw [hproduct]
    calc
      squareClass K (diagonalUnitDeterminant q.diagonalUnits) =
          unitSquareClassToSquareClass K
            (Lattice.determinantClass q L) :=
        Lattice.squareClass_diagonalUnitDeterminant_eq_determinantClass_toSquareClass
          q L
      _ = unitSquareClassToSquareClass K (unitSquareClass K (-1 : Kˣ)) := by
        rw [hdet]
      _ = squareClass K (-1 : Kˣ) :=
        unitSquareClassToSquareClass_apply K (-1 : Kˣ)
  have hsignedRatio : IsSquare (-(c 0 / c 1)) :=
    isSquare_neg_div_of_squareClass_mul_eq_neg_one (c 0) (c 1) hclasses
  rcases finiteDiagonal_fin_two_isIsometric_hyperbolicPlane_one
      (c 0) (c 1) hsignedRatio with ⟨toHyperbolic⟩
  let reindex := finiteDiagonalReindexIsometry
    (fun i ↦ (q.diagonalUnits i : K))
    (fun i ↦ Units.ne_zero (q.diagonalUnits i)) e
  have hcoeff : (fun i : Fin 2 ↦ (q.diagonalUnits (e i) : K)) =
      ![(c 0 : K), (c 1 : K)] := by
    funext i
    fin_cases i <;> rfl
  let toHyperbolic' : Isometry
      (finiteDiagonal (fun i : Fin 2 ↦ (q.diagonalUnits (e i) : K))
        (fun i ↦ Units.ne_zero (q.diagonalUnits (e i))))
      (hyperbolicPlane (1 : Kˣ)) := by
    simpa only [hcoeff] using toHyperbolic
  exact ⟨q.diagonalizationIsometry.trans (reindex.trans toHyperbolic')⟩

end QuadraticSpace

end Bong
