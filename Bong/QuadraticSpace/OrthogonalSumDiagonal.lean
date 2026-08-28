/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.Diagonalization
import Bong.QuadraticSpace.OrthogonalSum
import Bong.QuadraticSpace.HyperbolicPlane
import Bong.Bong.DiagonalHasseSymbol

/-!
# Diagonal coordinates for orthogonal sums

This file identifies a product of two finite diagonal spaces with the
diagonal space obtained by appending their coefficient lists.  It then
combines this elementary map with the canonical BONG diagonalization of an
arbitrary quadratic space.  In particular, adjoining the line `[a]` really
appends the coefficient `a`; no independently chosen determinant is hidden
in that operation.
-/

namespace Bong

open Dyadic
open BONG.GoodBONG

namespace QuadraticSpace

universe u v w v' w'

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {V' : Type v'} [AddCommGroup V'] [Module K V']
  {W' : Type w'} [AddCommGroup W'] [Module K W']

/-- Coercing a field-unit coefficient never produces zero. -/
theorem diagonalUnitCoefficients_ne_zero {n : Nat}
    (c : Fin n → Kˣ) (i : Fin n) :
    diagonalUnitCoefficients c i ≠ 0 := by
  exact Units.ne_zero (c i)

/-- Split and append finite coordinate tuples. -/
noncomputable def finAddArrowEquiv (m n : Nat) :
    ((Fin m → K) × (Fin n → K)) ≃ₗ[K] (Fin (m + n) → K) where
  toFun x := Fin.append x.1 x.2
  invFun x :=
    (fun i ↦ x (Fin.castAdd n i), fun j ↦ x (Fin.natAdd m j))
  left_inv x := by
    apply Prod.ext <;> funext i
    · simp
    · simp
  right_inv x := by
    funext i
    refine Fin.addCases (m := m) (n := n) (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp
    · simp
  map_add' x y := by
    funext i
    refine Fin.addCases (m := m) (n := n) (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp
    · simp
  map_smul' c x := by
    funext i
    refine Fin.addCases (m := m) (n := n) (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp
    · simp

@[simp]
theorem finAddArrowEquiv_apply_castAdd (m n : Nat)
    (x : (Fin m → K) × (Fin n → K)) (i : Fin m) :
    finAddArrowEquiv (K := K) m n x (Fin.castAdd n i) = x.1 i := by
  simp [finAddArrowEquiv]

@[simp]
theorem finAddArrowEquiv_apply_natAdd (m n : Nat)
    (x : (Fin m → K) × (Fin n → K)) (i : Fin n) :
    finAddArrowEquiv (K := K) m n x (Fin.natAdd m i) = x.2 i := by
  simp [finAddArrowEquiv]

/-- Componentwise product of quadratic-space isometries. -/
noncomputable def Isometry.orthogonalSum
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {q' : QuadraticSpace K V'} {r' : QuadraticSpace K W'}
    (f : Isometry q q') (g : Isometry r r') :
    Isometry (q.orthogonalSum r) (q'.orthogonalSum r') where
  toLinearEquiv := f.toLinearEquiv.prodCongr g.toLinearEquiv
  map_bilin := by
    intro x y
    simp only [orthogonalSum_bilin_apply, LinearEquiv.prodCongr_apply]
    rw [f.map_bilin, g.map_bilin]

/-- The orthogonal sum of two finite diagonal spaces is the finite diagonal
space obtained by appending their unit coefficient lists. -/
noncomputable def finiteDiagonalOrthogonalSumIsometry
    {m n : Nat} (a : Fin m → Kˣ) (b : Fin n → Kˣ) :
    Isometry
      ((finiteDiagonal (diagonalUnitCoefficients a)
          (fun i ↦ Units.ne_zero (a i))).orthogonalSum
        (finiteDiagonal (diagonalUnitCoefficients b)
          (fun i ↦ Units.ne_zero (b i))))
      (finiteDiagonal (diagonalUnitCoefficients (Fin.append a b))
        (fun i ↦ Units.ne_zero (Fin.append a b i))) where
  toLinearEquiv := finAddArrowEquiv m n
  map_bilin := by
    intro x y
    rw [finiteDiagonal_bilin_apply, orthogonalSum_bilin_apply,
      finiteDiagonal_bilin_apply, finiteDiagonal_bilin_apply]
    simp only [Fin.sum_univ_add, diagonalUnitCoefficients,
      Fin.append_left, Fin.append_right,
      finAddArrowEquiv_apply_castAdd, finAddArrowEquiv_apply_natAdd]

/-- The canonical diagonal presentation of an orthogonal sum is the append
of the chosen diagonal presentations of its factors. -/
noncomputable def orthogonalSumDiagonalizationIsometry
    [FiniteDimensional K V] [FiniteDimensional K W]
    (q : QuadraticSpace K V) (r : QuadraticSpace K W) :
    Isometry (q.orthogonalSum r)
      (finiteDiagonal
        (diagonalUnitCoefficients (Fin.append q.diagonalUnits r.diagonalUnits))
        (fun i ↦ Units.ne_zero
          (Fin.append q.diagonalUnits r.diagonalUnits i))) :=
  (q.diagonalizationIsometry.orthogonalSum r.diagonalizationIsometry).trans
    (finiteDiagonalOrthogonalSumIsometry q.diagonalUnits r.diagonalUnits)

/-- The scalar coordinate identifies `[a]` with the one-entry diagonal
space whose coefficient is exactly `a`. -/
noncomputable def scaledLineDiagonalizationIsometry (a : Kˣ) :
    Isometry (scaledLine a)
      (finiteDiagonal (diagonalUnitCoefficients (fun _ : Fin 1 ↦ a))
        (fun _ ↦ Units.ne_zero a)) where
  toLinearEquiv :=
    { toFun := fun x _ ↦ x
      invFun := fun x ↦ x 0
      left_inv := by intro x; rfl
      right_inv := by intro x; funext i; exact Fin.eq_zero i ▸ rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_bilin := by
    intro x y
    rw [finiteDiagonal_bilin_apply, scaledLine_bilin_apply]
    simp [diagonalUnitCoefficients]

/-- Adjoining `[a]` appends precisely the coefficient `a` to the chosen
diagonal presentation of `q`. -/
noncomputable def orthogonalSumScaledLineDiagonalizationIsometry
    [FiniteDimensional K V] (q : QuadraticSpace K V) (a : Kˣ) :
    Isometry (q.orthogonalSum (scaledLine a))
      (finiteDiagonal
        (diagonalUnitCoefficients (Fin.snoc q.diagonalUnits a))
        (diagonalUnitCoefficients_ne_zero
          (Fin.snoc q.diagonalUnits a))) := by
  have f :=
    (q.diagonalizationIsometry.orthogonalSum
      (scaledLineDiagonalizationIsometry a)).trans
      (finiteDiagonalOrthogonalSumIsometry
        q.diagonalUnits (fun _ : Fin 1 ↦ a))
  simpa only [Fin.append_right_eq_snoc] using f

/-- Representation by an orthogonal one-line extension is equivalent to the
corresponding codimension-one diagonal representation. -/
theorem orthogonalSum_scaledLine_represents_iff_diagonalRepresents
    [FiniteDimensional K V] [FiniteDimensional K W]
    (q : QuadraticSpace K V) (r : QuadraticSpace K W) (a : Kˣ) :
    (q.orthogonalSum (scaledLine a)).Represents r ↔
      DiagonalRepresents
        (diagonalUnitCoefficients r.diagonalUnits)
        (diagonalUnitCoefficients (Fin.snoc q.diagonalUnits a)) := by
  exact (represents_iff_of_isometries r.diagonalizationIsometry
      (orthogonalSumScaledLineDiagonalizationIsometry q a)).trans
    (finiteDiagonal_represents_iff_diagonalRepresents
      r.diagonalUnits (Fin.snoc q.diagonalUnits a))

/-- The field unit represented by `2`. -/
noncomputable def fieldTwoUnit : Kˣ :=
  Units.mk0 (2 : K) (by norm_num)

@[simp]
theorem coe_fieldTwoUnit : (fieldTwoUnit (K := K) : K) = 2 :=
  rfl

/-- Hyperbolic coordinates `(x+y)/2,(x-y)/2`. -/
noncomputable def hyperbolicDiagonalLinearEquiv :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun x := ![(x 0 + x 1) / 2, (x 0 - x 1) / 2]
  invFun x := ![x 0 + x 1, x 0 - x 1]
  left_inv x := by
    funext i
    fin_cases i <;> simp <;> ring
  right_inv x := by
    funext i
    fin_cases i <;> simp <;> ring
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp <;> ring

/-- The standard hyperbolic plane is diagonal with coefficients `2,-2`. -/
noncomputable def hyperbolicPlaneDiagonalizationIsometry :
    Isometry (hyperbolicPlane (1 : Kˣ))
      (finiteDiagonal
        (diagonalUnitCoefficients
          ![fieldTwoUnit (K := K), -fieldTwoUnit (K := K)])
        (diagonalUnitCoefficients_ne_zero
          ![fieldTwoUnit (K := K), -fieldTwoUnit (K := K)])) where
  toLinearEquiv := hyperbolicDiagonalLinearEquiv
  map_bilin := by
    intro x y
    rw [finiteDiagonal_bilin_apply, hyperbolicPlane_bilin_apply]
    simp only [Fin.sum_univ_two, diagonalUnitCoefficients,
      Matrix.cons_val_zero, Matrix.cons_val_one, coe_fieldTwoUnit,
      Units.val_neg, Units.val_one, one_mul]
    change
      2 * ((x 0 + x 1) / 2) * ((y 0 + y 1) / 2) +
          (-2) * ((x 0 - x 1) / 2) * ((y 0 - y 1) / 2) =
        x 0 * y 1 + x 1 * y 0
    ring

/-- Appending a two-tuple is the same as applying `snoc` twice. -/
theorem append_finTwo_eq_snoc_snoc {n : Nat}
    (c : Fin n → Kˣ) (a b : Kˣ) :
    Fin.append c ![a, b] = Fin.snoc (Fin.snoc c a) b := by
  have htwo : ![a, b] = Fin.snoc (fun _ : Fin 1 ↦ a) b := by
    funext i
    fin_cases i <;> rfl
  rw [htwo, Fin.append_snoc, Fin.append_right_eq_snoc]

/-- The orthogonal sum with a hyperbolic plane appends the exact diagonal
pair `2,-2`. -/
noncomputable def orthogonalSumHyperbolicDiagonalizationIsometry
    [FiniteDimensional K V] (q : QuadraticSpace K V) :
    Isometry (q.orthogonalSum (hyperbolicPlane (1 : Kˣ)))
      (finiteDiagonal
        (diagonalUnitCoefficients
          (Fin.snoc (Fin.snoc q.diagonalUnits (fieldTwoUnit (K := K)))
            (-fieldTwoUnit (K := K))))
        (diagonalUnitCoefficients_ne_zero
          (Fin.snoc (Fin.snoc q.diagonalUnits (fieldTwoUnit (K := K)))
            (-fieldTwoUnit (K := K))))) := by
  have f :=
    (q.diagonalizationIsometry.orthogonalSum
      (hyperbolicPlaneDiagonalizationIsometry (K := K))).trans
      (finiteDiagonalOrthogonalSumIsometry q.diagonalUnits
        ![fieldTwoUnit (K := K), -fieldTwoUnit (K := K)])
  rw [append_finTwo_eq_snoc_snoc] at f
  exact f

/-- Representation by a hyperbolic extension is the corresponding
codimension-one diagonal representation. -/
theorem orthogonalSum_hyperbolic_represents_iff_diagonalRepresents
    [FiniteDimensional K V] [FiniteDimensional K W]
    (q : QuadraticSpace K V) (r : QuadraticSpace K W) :
    (r.orthogonalSum (hyperbolicPlane (1 : Kˣ))).Represents q ↔
      DiagonalRepresents
        (diagonalUnitCoefficients q.diagonalUnits)
        (diagonalUnitCoefficients
          (Fin.snoc (Fin.snoc r.diagonalUnits (fieldTwoUnit (K := K)))
            (-fieldTwoUnit (K := K)))) := by
  exact (represents_iff_of_isometries q.diagonalizationIsometry
      (orthogonalSumHyperbolicDiagonalizationIsometry r)).trans
    (finiteDiagonal_represents_iff_diagonalRepresents q.diagonalUnits
      (Fin.snoc (Fin.snoc r.diagonalUnits (fieldTwoUnit (K := K)))
        (-fieldTwoUnit (K := K))))

end QuadraticSpace

end Bong
