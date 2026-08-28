/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.Valuation
import Bong.Lattice.Ideals
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Matrix congruences over a dyadic valuation field

Determinants are polynomial expressions with integral coefficients.  Thus
entrywise congruence modulo the maximal ideal, for integral matrices, passes
to their determinants.  This elementary lemma is used in the projection
calculation in the necessity proof of O'Meara 93:28.
-/

namespace Bong

open Dyadic
open scoped BigOperators

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A finite product of integral elements is integral. -/
theorem isIntegral_finset_prod {ι : Type v} (s : Finset ι) (a : ι → K)
    (ha : ∀ i ∈ s, Dyadic.IsIntegral K (a i)) :
    Dyadic.IsIntegral K (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Dyadic.IsIntegral]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact isIntegral_mul K (ha i (by simp))
        (ih (fun j hj ↦ ha j (by simp [hj])))

/-- A finite sum of elements of the maximal ideal remains in that ideal. -/
theorem isInMaximalIdeal_finset_sum {ι : Type v} (s : Finset ι)
    (a : ι → K) (ha : ∀ i ∈ s, IsInMaximalIdeal K (a i)) :
    IsInMaximalIdeal K (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [IsInMaximalIdeal]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact isInMaximalIdeal_add K (ha i (by simp))
        (ih (fun j hj ↦ ha j (by simp [hj])))

/-- Products of pairwise congruent integral families are congruent modulo
the maximal ideal. -/
theorem isInMaximalIdeal_finset_prod_sub_prod {ι : Type v}
    (s : Finset ι) (a b : ι → K)
    (ha : ∀ i ∈ s, Dyadic.IsIntegral K (a i))
    (hb : ∀ i ∈ s, Dyadic.IsIntegral K (b i))
    (hab : ∀ i ∈ s, IsInMaximalIdeal K (a i - b i)) :
    IsInMaximalIdeal K ((∏ i ∈ s, a i) - ∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [IsInMaximalIdeal]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      have htail := ih
        (fun j hj ↦ ha j (by simp [hj]))
        (fun j hj ↦ hb j (by simp [hj]))
        (fun j hj ↦ hab j (by simp [hj]))
      have hleft : IsInMaximalIdeal K
          ((a i - b i) * ∏ j ∈ s, a j) :=
        isInMaximalIdeal_mul_isIntegral K (hab i (by simp))
          (isIntegral_finset_prod s a
            (fun j hj ↦ ha j (by simp [hj])))
      have hright : IsInMaximalIdeal K
          (b i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j)) :=
        isIntegral_mul_isInMaximalIdeal K (hb i (by simp)) htail
      convert isInMaximalIdeal_add K hleft hright using 1 <;> ring

/-- Products of pairwise congruent integral families remain congruent
modulo an arbitrary coefficient ideal. -/
theorem mem_coefficientIdeal_finset_prod_sub_prod {ι : Type v}
    (I : Lattice.CoefficientIdeal (K := K))
    (s : Finset ι) (a b : ι → K)
    (ha : ∀ i ∈ s, Dyadic.IsIntegral K (a i))
    (hb : ∀ i ∈ s, Dyadic.IsIntegral K (b i))
    (hab : ∀ i ∈ s, a i - b i ∈ I) :
    (∏ i ∈ s, a i) - ∏ i ∈ s, b i ∈ I := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using I.zero_mem
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      have htail := ih
        (fun j hj ↦ ha j (by simp [hj]))
        (fun j hj ↦ hb j (by simp [hj]))
        (fun j hj ↦ hab j (by simp [hj]))
      have hprodA : Dyadic.IsIntegral K (∏ j ∈ s, a j) :=
        isIntegral_finset_prod s a (fun j hj ↦ ha j (by simp [hj]))
      let cA : IntegerRing K :=
        ⟨∏ j ∈ s, a j, (mem_integerRing_iff K).2 hprodA⟩
      have hleftRaw := I.smul_mem cA (hab i (by simp))
      have hleft : (a i - b i) * ∏ j ∈ s, a j ∈ I := by
        change (cA : K) * (a i - b i) ∈ I at hleftRaw
        simpa only [cA, mul_comm] using hleftRaw
      let cB : IntegerRing K :=
        ⟨b i, (mem_integerRing_iff K).2 (hb i (by simp))⟩
      have hrightRaw := I.smul_mem cB htail
      have hright : b i *
          ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) ∈ I := by
        change (cB : K) *
          ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) ∈ I at hrightRaw
        simpa only [cB] using hrightRaw
      convert I.add_mem hleft hright using 1 <;> ring

/-- Entrywise congruent integral square matrices have congruent
determinants modulo the maximal ideal. -/
theorem isInMaximalIdeal_det_sub_det {ι : Type v}
    [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι K)
    (hA : ∀ i j, Dyadic.IsIntegral K (A i j))
    (hB : ∀ i j, Dyadic.IsIntegral K (B i j))
    (hAB : ∀ i j, IsInMaximalIdeal K (A i j - B i j)) :
    IsInMaximalIdeal K (A.det - B.det) := by
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  apply isInMaximalIdeal_finset_sum
  intro sigma _
  have hprod : IsInMaximalIdeal K
      ((∏ i, A (sigma i) i) - ∏ i, B (sigma i) i) :=
    isInMaximalIdeal_finset_prod_sub_prod Finset.univ
      (fun i ↦ A (sigma i) i) (fun i ↦ B (sigma i) i)
      (by intro i _; exact hA _ _)
      (by intro i _; exact hB _ _)
      (by intro i _; exact hAB _ _)
  rcases Int.units_eq_one_or sigma.sign with hsign | hsign
  · simp [hsign]
    exact hprod
  · simp [hsign]
    have hneg : IsInMaximalIdeal K
        (-((∏ i, A (sigma i) i) - ∏ i, B (sigma i) i)) := by
      unfold IsInMaximalIdeal
      rw [ord_neg]
      exact hprod
    convert hneg using 1 <;> ring

/-- Entrywise congruent integral square matrices have congruent
determinants modulo any coefficient ideal. -/
theorem mem_coefficientIdeal_det_sub_det {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (I : Lattice.CoefficientIdeal (K := K))
    (A B : Matrix ι ι K)
    (hA : ∀ i j, Dyadic.IsIntegral K (A i j))
    (hB : ∀ i j, Dyadic.IsIntegral K (B i j))
    (hAB : ∀ i j, A i j - B i j ∈ I) :
    A.det - B.det ∈ I := by
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro sigma _
  have hprod : (∏ i, A (sigma i) i) - ∏ i, B (sigma i) i ∈ I :=
    mem_coefficientIdeal_finset_prod_sub_prod I Finset.univ
      (fun i ↦ A (sigma i) i) (fun i ↦ B (sigma i) i)
      (by intro i _; exact hA _ _)
      (by intro i _; exact hB _ _)
      (by intro i _; exact hAB _ _)
  rcases Int.units_eq_one_or sigma.sign with hsign | hsign
  · simp [hsign]
    exact hprod
  · simp [hsign]
    have hneg := I.neg_mem hprod
    convert hneg using 1 <;> ring

/-- A maximal-ideal perturbation of a valuation unit is again a valuation
unit. -/
theorem isValuationUnit_of_sub_isInMaximalIdeal {a b : K}
    (hb : IsValuationUnit K b)
    (hab : IsInMaximalIdeal K (a - b)) :
    IsValuationUnit K a := by
  have hlt : ord K b < ord K (a - b) := by
    rw [hb]
    exact hab
  have hadd := (ord K).map_add_eq_of_lt_left hlt
  have hrewrite : b + (a - b) = a := by ring
  rw [hrewrite, hb] at hadd
  exact hadd

/-- If the Gram matrix of a finite family for a bilinear form has nonzero
determinant, then the family is linearly independent.  No nondegeneracy
hypothesis on the ambient form is needed. -/
theorem linearIndependent_of_bilinMatrix_det_ne_zero
    {X : Type v} [AddCommGroup X] [Module K X]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K X) (x : ι → X)
    (hdet : Matrix.det (fun i j ↦ B (x i) (x j)) ≠ 0) :
    LinearIndependent K x := by
  have hrows : LinearIndependent K
      (fun i ↦ (fun j ↦ B (x i) (x j))) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  rw [Fintype.linearIndependent_iff] at hrows ⊢
  intro c hc i
  apply hrows c
  · ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc
      ∑ k, c k * B (x k) (x j) =
          B (∑ k, c k • x k) (x j) := by simp
      _ = 0 := by rw [hc]; simp

end Bong
