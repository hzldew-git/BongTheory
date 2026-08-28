/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma99Coefficients

/-!
# Beli (2019), Lemma 9.9: realization of the explicit coefficients

This file turns the coefficient lists from `Beli2019Lemma99Coefficients`
into good BONGs and computes their first alpha invariant.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- In rank three, the first alpha is the minimum of exactly the three
terms displayed in the proof of Lemma 9.9. -/
theorem ternary_firstAlpha_eq_min_candidates
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
        (Finset.univ.filter fun j : Fin 2 => j ≤ (0 : Fin 2)) = {0} := by
      decide
    have hright :
        (Finset.univ.filter fun j : Fin 2 => (0 : Fin 2) ≤ j) =
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

/-- The unified coefficient list gives a good BONG once its two adjacent
binary parameters satisfy the explicit order-and-defect bounds.  The three
remaining hypotheses say that all alpha candidates are at least `A` and one
of them is exactly `A`. -/
theorem exists_beli2019Lemma99Realization_of_coefficients
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    (reference : GoodBONG q L 3) (R S A : Int) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hparity : Int.ModEq 2 R S)
    (hdeterminant : Int.ModEq 2
      (ordUnit K reference.toBONG.valueProduct) R)
    (hmatch : reference.Lemma814FirstThreeIsotropic ↔
      hilbertSymbol K η ε = 1)
    (hANonnegative : 0 ≤ A)
    (hgapLower : S - R ≤ A)
    (hforwardOrder : 0 ≤ S - R + 2 * (ramificationIndex K : Int))
    (hbackwardOrder : 0 ≤ R - S + 2 * (ramificationIndex K : Int))
    (hhalfLower : ((A : ℚ) : WithTop ℚ) ≤
      (((((S - R : Int) : ℚ) / 2 + ramificationIndex K : ℚ)) :
        WithTop ℚ))
    (hfirstLower : ((A : ℚ) : WithTop ℚ) ≤
      ((((S - R : Int) : ℚ) : WithTop ℚ) +
        defectOrder (K := K) η))
    (hsecondLower : ((A : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) ε)
    (hattained :
      ((((((S - R : Int) : ℚ) / 2 + ramificationIndex K : ℚ)) :
          WithTop ℚ) = ((A : ℚ) : WithTop ℚ)) ∨
      (((((S - R : Int) : ℚ) : WithTop ℚ) +
          defectOrder (K := K) η) = ((A : ℚ) : WithTop ℚ)) ∨
      defectOrder (K := K) ε = ((A : ℚ) : WithTop ℚ)) :
    ∃ D : Beli2019Lemma99Realization (q := q) R S R A,
      D.bong.adjacentDefect (1 : Fin 2) = defectOrder (K := K) ε := by
  let values := reference.beli2019Lemma99Values R S ε η
  have hrep : DiagonalRepresents
      (diagonalUnitCoefficients values)
      (diagonalUnitCoefficients reference.valueUnit) := by
    exact reference.beli2019Lemma99Values_diagonalRepresents
      R S ε η hparity hdeterminant hmatch
  rcases DiagonalRepresents.exists_orthogonalBasisData
      reference values hrep with ⟨X, hvalues⟩
  have hvalueOrders := reference.beli2019Lemma99Values_orders
    R S ε η hεUnit hηUnit
  have hordersX : ∀ i, X.order i = ![R, S, R] i := by
    intro i
    unfold BONG.OrthogonalBasisData.order
    rw [hvalues i]
    exact hvalueOrders i
  have hfirstDefectX : X.adjacentDefect (0 : Fin 2) =
      defectOrder (K := K) η := by
    unfold BONG.OrthogonalBasisData.adjacentDefect
      BONG.OrthogonalBasisData.adjacentProduct
    change defectOrder (K := K)
      (-(X.valueUnit (0 : Fin 3) * X.valueUnit (1 : Fin 3))) = _
    rw [hvalues (0 : Fin 3), hvalues (1 : Fin 3)]
    exact reference.beli2019Lemma99Values_firstAdjacentDefect
      R S ε η hparity
  have hsecondDefectX : X.adjacentDefect (1 : Fin 2) =
      defectOrder (K := K) ε := by
    unfold BONG.OrthogonalBasisData.adjacentDefect
      BONG.OrthogonalBasisData.adjacentProduct
    change defectOrder (K := K)
      (-(X.valueUnit (1 : Fin 3) * X.valueUnit (2 : Fin 3))) = _
    rw [hvalues (1 : Fin 3), hvalues (2 : Fin 3)]
    exact reference.beli2019Lemma99Values_secondAdjacentDefect
      R S ε η hparity
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
    change R ≤ R
    exact le_rfl
  have hANonnegativeTop : (0 : WithTop ℚ) ≤ ((A : ℚ) : WithTop ℚ) := by
    exact_mod_cast hANonnegative
  have hadmissible :
      ∀ (i : Fin 3) (hi : i.1 + 1 < 3),
        IsBinaryParameterAdmissible (X.adjacentParameter i hi) := by
    intro i hi
    have hiCases : i = (0 : Fin 3) ∨ i = (1 : Fin 3) := by
      have hiVal : i.1 = 0 ∨ i.1 = 1 := by omega
      rcases hiVal with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hiCases with rfl | rfl
    · have hnext : (⟨(0 : Fin 3).1 + 1, hi⟩ : Fin 3) =
          (1 : Fin 3) := by
        apply Fin.ext
        rfl
      have hord : ordUnit K (X.adjacentParameter (0 : Fin 3) hi) =
          S - R := by
        rw [X.ordUnit_adjacentParameter (0 : Fin 3) hi, hnext,
          hordersX (0 : Fin 3), hordersX (1 : Fin 3)]
        change S - R = S - R
        rfl
      have hdefect : defectOrder (K := K)
          (-X.adjacentParameter (0 : Fin 3) hi) =
          defectOrder (K := K) η := by
        calc
          defectOrder (K := K) (-X.adjacentParameter (0 : Fin 3) hi) =
              X.adjacentDefect (0 : Fin 2) := by
            simpa using X.defectOrder_neg_adjacentParameter
              (0 : Fin 3) hi
          _ = defectOrder (K := K) η := hfirstDefectX
      apply (isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
        (X.adjacentParameter (0 : Fin 3) hi)).2
      constructor
      · rw [hord]
        exact hforwardOrder
      · apply
          Dyadic.hasNonnegativeAbsoluteQuadraticDefect_of_nonneg_add_defectOrder
        have hneg : ordUnit K (-X.adjacentParameter (0 : Fin 3) hi) =
            ordUnit K (X.adjacentParameter (0 : Fin 3) hi) := by
          apply WithTop.coe_injective
          simp only [coe_ordUnit, Units.val_neg, ord_neg]
        rw [hneg, hord, hdefect]
        exact hANonnegativeTop.trans hfirstLower
    · have hnext : (⟨(1 : Fin 3).1 + 1, hi⟩ : Fin 3) =
          (2 : Fin 3) := by
        apply Fin.ext
        rfl
      have hord : ordUnit K (X.adjacentParameter (1 : Fin 3) hi) =
          R - S := by
        rw [X.ordUnit_adjacentParameter (1 : Fin 3) hi, hnext,
          hordersX (1 : Fin 3), hordersX (2 : Fin 3)]
        change R - S = R - S
        rfl
      have hdefect : defectOrder (K := K)
          (-X.adjacentParameter (1 : Fin 3) hi) =
          defectOrder (K := K) ε := by
        calc
          defectOrder (K := K) (-X.adjacentParameter (1 : Fin 3) hi) =
              X.adjacentDefect (1 : Fin 2) := by
            simpa using X.defectOrder_neg_adjacentParameter
              (1 : Fin 3) hi
          _ = defectOrder (K := K) ε := hsecondDefectX
      apply (isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
        (X.adjacentParameter (1 : Fin 3) hi)).2
      constructor
      · rw [hord]
        exact hbackwardOrder
      · apply
          Dyadic.hasNonnegativeAbsoluteQuadraticDefect_of_nonneg_add_defectOrder
        have hneg : ordUnit K (-X.adjacentParameter (1 : Fin 3) hi) =
            ordUnit K (X.adjacentParameter (1 : Fin 3) hi) := by
          apply WithTop.coe_injective
          simp only [coe_ordUnit, Units.val_neg, ord_neg]
        rw [hneg, hord, hdefect]
        have hbackward : (0 : ℚ) ≤ (R - S : Int) + A := by
          exact_mod_cast (show 0 ≤ R - S + A by omega)
        have hbackwardTop : (0 : WithTop ℚ) ≤
            ((((R - S : Int) : ℚ) : WithTop ℚ) +
              ((A : ℚ) : WithTop ℚ)) := by
          exact_mod_cast hbackward
        exact hbackwardTop.trans (by
          simpa [add_comm] using add_le_add_left hsecondLower
            ((((R - S : Int) : ℚ) : WithTop ℚ)))
  have hcriteria : X.SatisfiesGoodBONGCriteria := ⟨hweak, hadmissible⟩
  rcases (X.hasGoodRealization_iff_beli2006Criteria).2 hcriteria with
    ⟨M, b, hreal, hgood⟩
  let c : GoodBONG q M 3 := ⟨b, hgood⟩
  have hordersC : ∀ i, c.order i = ![R, S, R] i := by
    intro i
    calc
      c.order i = X.order i := (X.order_eq_of_isRealizedBy hreal i).symm
      _ = ![R, S, R] i := hordersX i
  have hfirstDefectC : c.adjacentDefect (0 : Fin 2) =
      defectOrder (K := K) η := by
    calc
      c.adjacentDefect (0 : Fin 2) = X.adjacentDefect (0 : Fin 2) :=
        (X.adjacentDefect_eq_of_isRealizedBy hreal 0).symm
      _ = defectOrder (K := K) η := hfirstDefectX
  have hsecondDefectC : c.adjacentDefect (1 : Fin 2) =
      defectOrder (K := K) ε := by
    calc
      c.adjacentDefect (1 : Fin 2) = X.adjacentDefect (1 : Fin 2) :=
        (X.adjacentDefect_eq_of_isRealizedBy hreal 1).symm
      _ = defectOrder (K := K) ε := hsecondDefectX
  have hhalfC : c.halfGapCandidate (0 : Fin 2) =
      (((((S - R : Int) : ℚ) / 2 + ramificationIndex K : ℚ)) :
        WithTop ℚ) := by
    unfold halfGapCandidate
    rw [hordersC (0 : Fin 2).succ, hordersC (0 : Fin 2).castSucc]
    rfl
  have hleftC : c.leftDefectCandidate (0 : Fin 2) (0 : Fin 2) =
      ((((S - R : Int) : ℚ) : WithTop ℚ) +
        defectOrder (K := K) η) := by
    unfold leftDefectCandidate
    rw [hordersC (0 : Fin 2).succ,
      hordersC (0 : Fin 2).castSucc, hfirstDefectC]
    rfl
  have hrightC : c.rightDefectCandidate (0 : Fin 2) (1 : Fin 2) =
      defectOrder (K := K) ε := by
    unfold rightDefectCandidate
    rw [hordersC (1 : Fin 2).succ,
      hordersC (0 : Fin 2).castSucc, hsecondDefectC]
    simp
  have hfirstAlphaTop : (c.alphaValue (0 : Fin 2) : WithTop ℚ) =
      ((A : ℚ) : WithTop ℚ) := by
    rw [c.ternary_firstAlpha_eq_min_candidates, hhalfC, hleftC, hrightC]
    apply le_antisymm
    · rcases hattained with hhalf | hfirst | hsecond
      · exact (min_le_left _ _).trans_eq hhalf
      · exact ((min_le_right _ _).trans (min_le_left _ _)).trans_eq hfirst
      · exact ((min_le_right _ _).trans (min_le_right _ _)).trans_eq hsecond
    · exact le_min hhalfLower (le_min hfirstLower hsecondLower)
  have hfirstAlpha : c.alphaValue (0 : Fin 2) = (A : ℚ) :=
    WithTop.coe_eq_coe.mp hfirstAlphaTop
  let D : Beli2019Lemma99Realization (q := q) R S R A := {
    lattice := M
    bong := c
    orders := hordersC
    firstAlpha := hfirstAlpha
  }
  refine ⟨D, ?_⟩
  exact hsecondDefectC

end BONG.GoodBONG

end Bong
