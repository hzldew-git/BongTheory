/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006SectionTwo
import Bong.Bong.Beli2019Lemma83
import Bong.Bong.DiagonalOrthogonalBasis

/-!
# Exact realization of a ternary coefficient list

This file packages the realization argument repeatedly used in Beli (2019).
An equal-rank diagonal representation supplies an orthogonal basis with a
prescribed coefficient list.  The 2006 good-BONG criterion realizes that
basis integrally, while the three explicit candidates for the first alpha
invariant determine its value.

Unlike the specialized realization in Lemma 9.9, the result below retains
all three coefficient equalities.  This is needed for the block replacement
in Lemma 7.12 and Lemma 7.14.
-/

namespace Bong

open Dyadic

universe u v

open BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The diagonal polynomial of the values of an arbitrary orthogonal basis is
the ambient quadratic form in its basis coordinates. -/
theorem BONG.OrthogonalBasisData.diagonalQuadratic_value_eq
    {n : Nat} (X : BONG.OrthogonalBasisData q n) (x : Fin n → K) :
    diagonalQuadratic X.value x =
      q.quadratic (X.basis.equivFun.symm x) := by
  have hdiag : LinearMap.BilinForm.toMatrix X.basis q.bilin =
      Matrix.diagonal X.value := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [LinearMap.BilinForm.toMatrix_apply, Matrix.diagonal_apply_eq]
      rfl
    · rw [LinearMap.BilinForm.toMatrix_apply,
        (LinearMap.BilinForm.iIsOrtho_def.mp X.orthogonal) i j hij]
      simp [hij]
  have h := q.bilin.dotProduct_toMatrix_mulVec X.basis x x
  change dotProduct x
      ((LinearMap.BilinForm.toMatrix X.basis q.bilin).mulVec x) =
    q.quadratic (X.basis.equivFun.symm x) at h
  rw [hdiag] at h
  simpa [diagonalQuadratic, dotProduct, Matrix.mulVec,
    Matrix.diagonal_apply, pow_two, mul_assoc, mul_left_comm, mul_comm]
    using h

/-- Coordinate change from an arbitrary orthogonal basis to a BONG basis of
the same quadratic space gives an equal-rank diagonal representation. -/
theorem BONG.OrthogonalBasisData.diagonalRepresents_bong
    {M : Lattice K V} {n : Nat}
    (X : BONG.OrthogonalBasisData q n) (b : BONG V q M n) :
    DiagonalRepresents
      (diagonalUnitCoefficients X.valueUnit)
      (diagonalUnitCoefficients b.valueUnit) := by
  let coordinateChange : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    X.basis.equivFun.symm.trans b.basis.equivFun
  refine ⟨coordinateChange.toLinearMap, coordinateChange.injective, ?_⟩
  intro x
  change diagonalQuadratic b.value (coordinateChange x) =
    diagonalQuadratic X.value x
  rw [b.diagonalQuadratic_value_eq, X.diagonalQuadratic_value_eq]
  simp [coordinateChange]

/-- Composition of equal-rank diagonal representations. -/
theorem DiagonalRepresents.trans_exact
    {n : Nat} {a b c : Fin n → K}
    (hab : DiagonalRepresents a b) (hbc : DiagonalRepresents b c) :
    DiagonalRepresents a c := by
  rcases hab with ⟨f, hf, hqf⟩
  rcases hbc with ⟨g, hg, hqg⟩
  refine ⟨g.comp f, hg.comp hf, ?_⟩
  intro x
  change diagonalQuadratic c (g (f x)) = diagonalQuadratic a x
  rw [hqg, hqf]

namespace BONG.GoodBONG

/-- In rank three, the first alpha is the minimum of the half-gap and the
two relevant adjacent-defect candidates.  This small local form avoids a
dependency on the later Lemma 9.9 realization module. -/
theorem ternary_firstAlpha_eq_min_candidates_exact
    (b : GoodBONG q L 3) :
    (b.alphaValue (0 : Fin 2) : WithTop ℚ) =
      min (b.halfGapCandidate (0 : Fin 2))
        (min (b.leftDefectCandidate (0 : Fin 2) (0 : Fin 2))
          (b.rightDefectCandidate (0 : Fin 2) (1 : Fin 2))) := by
  classical
  rw [b.coe_alphaValue]
  apply le_antisymm
  · exact le_min (b.alpha_le_halfGapCandidate 0)
      (le_min (b.alpha_le_leftDefectCandidate le_rfl)
        (b.alpha_le_rightDefectCandidate (by decide)))
  · unfold alpha
    apply Finset.le_min'
    intro y hy
    have hleft :
        (Finset.univ.filter fun j : Fin 2 ↦ j ≤ (0 : Fin 2)) = {0} := by
      decide
    have hright :
        (Finset.univ.filter fun j : Fin 2 ↦ (0 : Fin 2) ≤ j) =
          {0, 1} := by
      decide
    unfold alphaCandidates at hy
    rw [hleft, hright] at hy
    simp only [Finset.image_singleton, Finset.image_insert,
      Finset.union_insert, Finset.union_singleton,
      Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _)

/-- A ternary good BONG with a prescribed coefficient list, order profile,
and first alpha invariant. -/
structure ExactTernaryRealization
    (q : QuadraticSpace K V) (values : Fin 3 → Kˣ)
    (R S A : Int) where
  lattice : Lattice K V
  bong : GoodBONG q lattice 3
  valueUnits : ∀ i, bong.valueUnit i = values i
  orders : ∀ i, bong.order i = ![R, S, R] i
  firstAlpha : bong.alphaValue (0 : Fin 2) = (A : ℚ)

/-- Realize an exact ternary coefficient list once its ambient form, binary
admissibility, and the three candidates for `alphaValue 0` are known.

The order profile has equal outer terms, so the weak two-step condition is
automatic. -/
theorem exists_exactTernaryRealization
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    (reference : GoodBONG q L 3) (values : Fin 3 → Kˣ)
    (R S A : Int)
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients values)
      (diagonalUnitCoefficients reference.valueUnit))
    (horders : ∀ i, ordUnit K (values i) = ![R, S, R] i)
    (hadmissible :
      ∀ (i : Fin 3) (hi : i.1 + 1 < 3),
        IsBinaryParameterAdmissible
          (values ⟨i.1 + 1, hi⟩ / values i))
    (hhalf :
      (((((S - R : Int) : ℚ) / 2 + ramificationIndex K : ℚ)) :
          WithTop ℚ) = ((A : ℚ) : WithTop ℚ))
    (hleft :
      ((((S - R : Int) : ℚ) : WithTop ℚ) +
          defectOrder (K := K) (-(values 0 * values 1))) =
        ((A : ℚ) : WithTop ℚ))
    (hright :
      defectOrder (K := K) (-(values 1 * values 2)) =
        ((A : ℚ) : WithTop ℚ)) :
    Nonempty (ExactTernaryRealization q values R S A) := by
  rcases DiagonalRepresents.exists_orthogonalBasisData
      reference values hrep with ⟨X, hvalues⟩
  have hordersX : ∀ i, X.order i = ![R, S, R] i := by
    intro i
    unfold BONG.OrthogonalBasisData.order
    rw [hvalues i]
    exact horders i
  have hweak : X.HasWeakTwoStepOrder := by
    intro i hi
    have hiZero : i = (0 : Fin 3) := by
      apply Fin.ext
      omega
    subst i
    have hnext : (⟨(0 : Fin 3).1 + 2, hi⟩ : Fin 3) = (2 : Fin 3) := by
      apply Fin.ext
      rfl
    rw [hnext, hordersX (0 : Fin 3), hordersX (2 : Fin 3)]
    exact le_rfl
  have hadmissibleX :
      ∀ (i : Fin 3) (hi : i.1 + 1 < 3),
        IsBinaryParameterAdmissible (X.adjacentParameter i hi) := by
    intro i hi
    unfold BONG.OrthogonalBasisData.adjacentParameter
    rw [hvalues ⟨i.1 + 1, hi⟩, hvalues i]
    exact hadmissible i hi
  have hcriteria : X.SatisfiesGoodBONGCriteria :=
    ⟨hweak, hadmissibleX⟩
  rcases (X.hasGoodRealization_iff_beli2006Criteria).2 hcriteria with
    ⟨M, b, hreal, hgood⟩
  let c : GoodBONG q M 3 := ⟨b, hgood⟩
  have hvaluesC : ∀ i, c.valueUnit i = values i := by
    intro i
    apply Units.ext
    change b.value i = ((values i : Kˣ) : K)
    calc
      b.value i = X.value i := (X.value_eq_of_isRealizedBy hreal i).symm
      _ = ((X.valueUnit i : Kˣ) : K) := rfl
      _ = ((values i : Kˣ) : K) := congrArg Units.val (hvalues i)
  have hordersC : ∀ i, c.order i = ![R, S, R] i := by
    intro i
    calc
      c.order i = X.order i := (X.order_eq_of_isRealizedBy hreal i).symm
      _ = ![R, S, R] i := hordersX i
  have hfirstDefectC : c.adjacentDefect (0 : Fin 2) =
      defectOrder (K := K) (-(values 0 * values 1)) := by
    unfold adjacentDefect adjacentProduct
    change defectOrder (K := K)
      (-(c.valueUnit (0 : Fin 3) * c.valueUnit (1 : Fin 3))) = _
    rw [hvaluesC (0 : Fin 3), hvaluesC (1 : Fin 3)]
  have hsecondDefectC : c.adjacentDefect (1 : Fin 2) =
      defectOrder (K := K) (-(values 1 * values 2)) := by
    unfold adjacentDefect adjacentProduct
    change defectOrder (K := K)
      (-(c.valueUnit (1 : Fin 3) * c.valueUnit (2 : Fin 3))) = _
    rw [hvaluesC (1 : Fin 3), hvaluesC (2 : Fin 3)]
  have hhalfC : c.halfGapCandidate (0 : Fin 2) =
      (((((S - R : Int) : ℚ) / 2 + ramificationIndex K : ℚ)) :
        WithTop ℚ) := by
    unfold halfGapCandidate
    rw [hordersC (0 : Fin 2).succ, hordersC (0 : Fin 2).castSucc]
    rfl
  have hleftC : c.leftDefectCandidate (0 : Fin 2) (0 : Fin 2) =
      ((((S - R : Int) : ℚ) : WithTop ℚ) +
        defectOrder (K := K) (-(values 0 * values 1))) := by
    unfold leftDefectCandidate
    rw [hordersC (0 : Fin 2).succ,
      hordersC (0 : Fin 2).castSucc, hfirstDefectC]
    rfl
  have hrightC : c.rightDefectCandidate (0 : Fin 2) (1 : Fin 2) =
      defectOrder (K := K) (-(values 1 * values 2)) := by
    unfold rightDefectCandidate
    rw [hordersC (1 : Fin 2).succ,
      hordersC (0 : Fin 2).castSucc, hsecondDefectC]
    simp
  have hfirstAlphaTop :
      (c.alphaValue (0 : Fin 2) : WithTop ℚ) =
        ((A : ℚ) : WithTop ℚ) := by
    rw [c.ternary_firstAlpha_eq_min_candidates_exact,
      hhalfC, hleftC, hrightC, hhalf, hleft, hright]
    simp
  have hfirstAlpha : c.alphaValue (0 : Fin 2) = (A : ℚ) :=
    WithTop.coe_eq_coe.mp hfirstAlphaTop
  exact ⟨{
    lattice := M
    bong := c
    valueUnits := hvaluesC
    orders := hordersC
    firstAlpha := hfirstAlpha
  }⟩

/-- Variant of `exists_exactTernaryRealization` in which the half-gap
candidate realizes the prescribed first alpha and the two defect candidates
are only required to be no smaller.  This is the form needed when an adjacent
signed product is a square and hence has infinite defect. -/
theorem exists_exactTernaryRealization_of_halfGap
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    (reference : GoodBONG q L 3) (values : Fin 3 → Kˣ)
    (R S A : Int)
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients values)
      (diagonalUnitCoefficients reference.valueUnit))
    (horders : ∀ i, ordUnit K (values i) = ![R, S, R] i)
    (hadmissible :
      ∀ (i : Fin 3) (hi : i.1 + 1 < 3),
        IsBinaryParameterAdmissible
          (values ⟨i.1 + 1, hi⟩ / values i))
    (hhalf :
      (((((S - R : Int) : ℚ) / 2 + ramificationIndex K : ℚ)) :
          WithTop ℚ) = ((A : ℚ) : WithTop ℚ))
    (hleftLower :
      ((A : ℚ) : WithTop ℚ) ≤
        ((((S - R : Int) : ℚ) : WithTop ℚ) +
          defectOrder (K := K) (-(values 0 * values 1))))
    (hrightLower :
      ((A : ℚ) : WithTop ℚ) ≤
        defectOrder (K := K) (-(values 1 * values 2))) :
    Nonempty (ExactTernaryRealization q values R S A) := by
  rcases DiagonalRepresents.exists_orthogonalBasisData
      reference values hrep with ⟨X, hvalues⟩
  have hordersX : ∀ i, X.order i = ![R, S, R] i := by
    intro i
    unfold BONG.OrthogonalBasisData.order
    rw [hvalues i]
    exact horders i
  have hweak : X.HasWeakTwoStepOrder := by
    intro i hi
    have hiZero : i = (0 : Fin 3) := by
      apply Fin.ext
      omega
    subst i
    have hnext : (⟨(0 : Fin 3).1 + 2, hi⟩ : Fin 3) = (2 : Fin 3) := by
      apply Fin.ext
      rfl
    rw [hnext, hordersX (0 : Fin 3), hordersX (2 : Fin 3)]
    exact le_rfl
  have hadmissibleX :
      ∀ (i : Fin 3) (hi : i.1 + 1 < 3),
        IsBinaryParameterAdmissible (X.adjacentParameter i hi) := by
    intro i hi
    unfold BONG.OrthogonalBasisData.adjacentParameter
    rw [hvalues ⟨i.1 + 1, hi⟩, hvalues i]
    exact hadmissible i hi
  have hcriteria : X.SatisfiesGoodBONGCriteria :=
    ⟨hweak, hadmissibleX⟩
  rcases (X.hasGoodRealization_iff_beli2006Criteria).2 hcriteria with
    ⟨M, b, hreal, hgood⟩
  let c : GoodBONG q M 3 := ⟨b, hgood⟩
  have hvaluesC : ∀ i, c.valueUnit i = values i := by
    intro i
    apply Units.ext
    change b.value i = ((values i : Kˣ) : K)
    calc
      b.value i = X.value i := (X.value_eq_of_isRealizedBy hreal i).symm
      _ = ((X.valueUnit i : Kˣ) : K) := rfl
      _ = ((values i : Kˣ) : K) := congrArg Units.val (hvalues i)
  have hordersC : ∀ i, c.order i = ![R, S, R] i := by
    intro i
    calc
      c.order i = X.order i := (X.order_eq_of_isRealizedBy hreal i).symm
      _ = ![R, S, R] i := hordersX i
  have hfirstDefectC : c.adjacentDefect (0 : Fin 2) =
      defectOrder (K := K) (-(values 0 * values 1)) := by
    unfold adjacentDefect adjacentProduct
    change defectOrder (K := K)
      (-(c.valueUnit (0 : Fin 3) * c.valueUnit (1 : Fin 3))) = _
    rw [hvaluesC (0 : Fin 3), hvaluesC (1 : Fin 3)]
  have hsecondDefectC : c.adjacentDefect (1 : Fin 2) =
      defectOrder (K := K) (-(values 1 * values 2)) := by
    unfold adjacentDefect adjacentProduct
    change defectOrder (K := K)
      (-(c.valueUnit (1 : Fin 3) * c.valueUnit (2 : Fin 3))) = _
    rw [hvaluesC (1 : Fin 3), hvaluesC (2 : Fin 3)]
  have hhalfC : c.halfGapCandidate (0 : Fin 2) =
      (((((S - R : Int) : ℚ) / 2 + ramificationIndex K : ℚ)) :
        WithTop ℚ) := by
    unfold halfGapCandidate
    rw [hordersC (0 : Fin 2).succ, hordersC (0 : Fin 2).castSucc]
    rfl
  have hleftC : c.leftDefectCandidate (0 : Fin 2) (0 : Fin 2) =
      ((((S - R : Int) : ℚ) : WithTop ℚ) +
        defectOrder (K := K) (-(values 0 * values 1))) := by
    unfold leftDefectCandidate
    rw [hordersC (0 : Fin 2).succ,
      hordersC (0 : Fin 2).castSucc, hfirstDefectC]
    rfl
  have hrightC : c.rightDefectCandidate (0 : Fin 2) (1 : Fin 2) =
      defectOrder (K := K) (-(values 1 * values 2)) := by
    unfold rightDefectCandidate
    rw [hordersC (1 : Fin 2).succ,
      hordersC (0 : Fin 2).castSucc, hsecondDefectC]
    simp
  have hfirstAlphaTop :
      (c.alphaValue (0 : Fin 2) : WithTop ℚ) =
        ((A : ℚ) : WithTop ℚ) := by
    rw [c.ternary_firstAlpha_eq_min_candidates_exact,
      hhalfC, hleftC, hrightC, hhalf]
    exact min_eq_left (le_min hleftLower hrightLower)
  have hfirstAlpha : c.alphaValue (0 : Fin 2) = (A : ℚ) :=
    WithTop.coe_eq_coe.mp hfirstAlphaTop
  exact ⟨{
    lattice := M
    bong := c
    valueUnits := hvaluesC
    orders := hordersC
    firstAlpha := hfirstAlpha
  }⟩

end BONG.GoodBONG

end Bong
