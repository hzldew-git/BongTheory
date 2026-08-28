/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma99Realization

/-!
# Beli (2019), Lemma 9.9: constructive sufficiency

The proof follows the three coefficient choices in the paper.  Field-level
unit defects are supplied by the dyadic unit-defect spectrum and the
complementary Hilbert-choice theorem; the preceding realization theorem then
constructs the lattice and computes its first alpha.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Beli2019Lemma99Conditions

variable {reference : GoodBONG q L 3} {R S A : Int}

theorem alpha_nonnegative
    (C : Beli2019Lemma99Conditions reference R S A) : 0 ≤ A := by
  exact (le_max_left 0 (S - R)).trans C.lower

theorem gap_le_alpha
    (C : Beli2019Lemma99Conditions reference R S A) : S - R ≤ A := by
  exact (le_max_right 0 (S - R)).trans C.lower

/-- The interval in Lemma 9.9 forces both adjacent order gaps to be at least
`-2e`, exactly as observed at the start of the paper's sufficiency proof. -/
theorem gap_bounds
    (C : Beli2019Lemma99Conditions reference R S A) :
    -(2 * (ramificationIndex K : Int)) ≤ S - R ∧
      S - R ≤ 2 * (ramificationIndex K : Int) := by
  have hA0Q : (0 : ℚ) ≤ (A : ℚ) := by
    exact_mod_cast C.alpha_nonnegative
  have hgapQ : ((S - R : Int) : ℚ) ≤ (A : ℚ) := by
    exact_mod_cast C.gap_le_alpha
  have hlowerQ : (-(2 * (ramificationIndex K : Int)) : Int) ≤ S - R := by
    have h : (-(2 * (ramificationIndex K : ℚ)) : ℚ) ≤
        ((S - R : Int) : ℚ) := by
      linarith [C.upper]
    exact_mod_cast h
  have hupperQ : S - R ≤ 2 * (ramificationIndex K : Int) := by
    have h : ((S - R : Int) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) := by
      linarith [C.upper]
    exact_mod_cast h
  exact ⟨hlowerQ, hupperQ⟩

theorem forward_order_nonnegative
    (C : Beli2019Lemma99Conditions reference R S A) :
    0 ≤ S - R + 2 * (ramificationIndex K : Int) := by
  have h := C.gap_bounds.1
  omega

theorem backward_order_nonnegative
    (C : Beli2019Lemma99Conditions reference R S A) :
    0 ≤ R - S + 2 * (ramificationIndex K : Int) := by
  have h := C.gap_bounds.2
  omega

theorem halfCandidate_lower
    (C : Beli2019Lemma99Conditions reference R S A) :
    ((A : ℚ) : WithTop ℚ) ≤
      (((((S - R : Int) : ℚ) / 2 + ramificationIndex K : ℚ)) :
        WithTop ℚ) := by
  exact_mod_cast C.upper

theorem alpha_le_twoE
    (C : Beli2019Lemma99Conditions reference R S A) :
    A ≤ 2 * (ramificationIndex K : Int) := by
  have hgapQ : ((S - R : Int) : ℚ) ≤ (A : ℚ) := by
    exact_mod_cast C.gap_le_alpha
  have hAQ : (A : ℚ) ≤ 2 * (ramificationIndex K : ℚ) := by
    linarith [C.upper]
  exact_mod_cast hAQ

theorem alpha_lt_twoE_of_odd
    (C : Beli2019Lemma99Conditions reference R S A) (hodd : Odd A) :
    (A : ℚ) < 2 * (ramificationIndex K : ℚ) := by
  have hne : A ≠ 2 * (ramificationIndex K : Int) := by
    intro heq
    rcases hodd with ⟨k, hk⟩
    omega
  have hlt : A < 2 * (ramificationIndex K : Int) :=
    lt_of_le_of_ne C.alpha_le_twoE hne
  exact_mod_cast hlt

end Beli2019Lemma99Conditions

/-- The even-alpha branch of the constructive converse.  Both twists are
one, so the two adjacent defects are infinite and the half-gap candidate
realizes `A`. -/
theorem beli2019Lemma99_even_sufficiency
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    (reference : GoodBONG q L 3) (R S A : Int)
    (C : Beli2019Lemma99Conditions reference R S A)
    (hEven : Even A) :
    Nonempty (Beli2019Lemma99Realization (q := q) R S R A) := by
  rcases C.evenBoundary hEven with ⟨hAhalf, hisotropic⟩
  have honeUnit : IsValuationUnit K ((1 : Kˣ) : K) := by
    apply (isValuationUnit_iff_ordUnit_eq_zero K (1 : Kˣ)).2
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hmatch : reference.Lemma814FirstThreeIsotropic ↔
      hilbertSymbol K (1 : Kˣ) (1 : Kˣ) = 1 := by
    constructor
    · intro _
      exact hilbertSymbol_one_left (K := K) (1 : Kˣ)
    · intro _
      exact hisotropic
  have hfirstLower : ((A : ℚ) : WithTop ℚ) ≤
      ((((S - R : Int) : ℚ) : WithTop ℚ) +
        defectOrder (K := K) (1 : Kˣ)) := by
    rw [defectOrder_one]
    exact le_top
  have hsecondLower : ((A : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) (1 : Kˣ) := by
    rw [defectOrder_one]
    exact le_top
  have hattained :
      ((((((S - R : Int) : ℚ) / 2 + ramificationIndex K : ℚ)) :
          WithTop ℚ) = ((A : ℚ) : WithTop ℚ)) ∨
      (((((S - R : Int) : ℚ) : WithTop ℚ) +
          defectOrder (K := K) (1 : Kˣ)) = ((A : ℚ) : WithTop ℚ)) ∨
      defectOrder (K := K) (1 : Kˣ) = ((A : ℚ) : WithTop ℚ) := by
    left
    exact_mod_cast hAhalf.symm
  rcases exists_beli2019Lemma99Realization_of_coefficients
      reference R S A (1 : Kˣ) (1 : Kˣ)
      honeUnit honeUnit C.orderParity C.determinantOrder hmatch
      C.alpha_nonnegative C.gap_le_alpha
      C.forward_order_nonnegative C.backward_order_nonnegative
      C.halfCandidate_lower hfirstLower hsecondLower hattained with
    ⟨D, _⟩
  exact ⟨D⟩

/-- The odd-alpha branch, including the `moreover` clause
`d(-a₂a₃) = A`. -/
theorem beli2019Lemma99_odd_sufficiency
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    (reference : GoodBONG q L 3) (R S A : Int)
    (C : Beli2019Lemma99Conditions reference R S A)
    (hOdd : Odd A) :
    Beli2019Lemma99OddRealization (q := q) R S R A := by
  have hOddRational : IsOddRationalInteger (A : ℚ) :=
    ⟨A, hOdd, rfl⟩
  have hANonnegativeQ : (0 : ℚ) ≤ (A : ℚ) := by
    exact_mod_cast C.alpha_nonnegative
  have hALt : (A : ℚ) < 2 * (ramificationIndex K : ℚ) :=
    C.alpha_lt_twoE_of_odd hOdd
  rcases DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      (A : ℚ) hOddRational hANonnegativeQ hALt with
    ⟨ε, hεUnit, hεDefect⟩
  have realize (η : Kˣ)
      (hηUnit : IsValuationUnit K (η : K))
      (hmatch : reference.Lemma814FirstThreeIsotropic ↔
        hilbertSymbol K η ε = 1)
      (hfirstLower : ((A : ℚ) : WithTop ℚ) ≤
        ((((S - R : Int) : ℚ) : WithTop ℚ) +
          defectOrder (K := K) η)) :
      Beli2019Lemma99OddRealization (q := q) R S R A := by
    have hsecondLower : ((A : ℚ) : WithTop ℚ) ≤
        defectOrder (K := K) ε := by
      rw [hεDefect]
    have hattained :
        ((((((S - R : Int) : ℚ) / 2 + ramificationIndex K : ℚ)) :
            WithTop ℚ) = ((A : ℚ) : WithTop ℚ)) ∨
        (((((S - R : Int) : ℚ) : WithTop ℚ) +
            defectOrder (K := K) η) = ((A : ℚ) : WithTop ℚ)) ∨
        defectOrder (K := K) ε = ((A : ℚ) : WithTop ℚ) := by
      right
      right
      exact hεDefect
    rcases exists_beli2019Lemma99Realization_of_coefficients
        reference R S A ε η hεUnit hηUnit C.orderParity
        C.determinantOrder hmatch C.alpha_nonnegative C.gap_le_alpha
        C.forward_order_nonnegative C.backward_order_nonnegative
        C.halfCandidate_lower hfirstLower hsecondLower hattained with
      ⟨D, hDDefect⟩
    refine ⟨D, ?_⟩
    exact hDDefect.trans hεDefect
  by_cases hisotropic : reference.Lemma814FirstThreeIsotropic
  · have honeUnit : IsValuationUnit K ((1 : Kˣ) : K) := by
      apply (isValuationUnit_iff_ordUnit_eq_zero K (1 : Kˣ)).2
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    have hmatch : reference.Lemma814FirstThreeIsotropic ↔
        hilbertSymbol K (1 : Kˣ) ε = 1 := by
      constructor
      · intro _
        exact hilbertSymbol_one_left (K := K) ε
      · intro _
        exact hisotropic
    have hfirstLower : ((A : ℚ) : WithTop ℚ) ≤
        ((((S - R : Int) : ℚ) : WithTop ℚ) +
          defectOrder (K := K) (1 : Kˣ)) := by
      rw [defectOrder_one]
      exact le_top
    exact realize (1 : Kˣ) honeUnit hmatch hfirstLower
  · have hAPosQ : (0 : ℚ) < (A : ℚ) := by
      have hAPos : 0 < A := by
        rcases hOdd with ⟨k, hk⟩
        have hA0 := C.alpha_nonnegative
        omega
      exact_mod_cast hAPos
    rcases exists_complementaryDefect_hilbert_neg
        (K := K) ε (A : ℚ) hεDefect hAPosQ hALt with
      ⟨η, hηUnit, hηDefect, hηHilbert⟩
    have hmatch : reference.Lemma814FirstThreeIsotropic ↔
        hilbertSymbol K η ε = 1 := by
      constructor
      · intro h
        exact (hisotropic h).elim
      · intro hone
        rw [hηHilbert] at hone
        norm_num at hone
    have hfirstQ : (A : ℚ) ≤
        ((S - R : Int) : ℚ) +
          (2 * (ramificationIndex K : ℚ) - (A : ℚ)) := by
      linarith [C.upper]
    have hfirstLower : ((A : ℚ) : WithTop ℚ) ≤
        ((((S - R : Int) : ℚ) : WithTop ℚ) +
          defectOrder (K := K) η) := by
      rw [hηDefect]
      exact_mod_cast hfirstQ
    exact realize η hηUnit hmatch hfirstLower

/-- Constructive sufficiency in Beli (2019), Lemma 9.9. -/
theorem beli2019Lemma99_sufficiency
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    (reference : GoodBONG q L 3) (R S A : Int)
    (C : Beli2019Lemma99Conditions reference R S A) :
    Nonempty (Beli2019Lemma99Realization (q := q) R S R A) := by
  by_cases hEven : Even A
  · exact beli2019Lemma99_even_sufficiency reference R S A C hEven
  · have hOdd : Odd A := Int.not_even_iff_odd.mp hEven
    rcases beli2019Lemma99_odd_sufficiency reference R S A C hOdd with
      ⟨D, _⟩
    exact ⟨D⟩

/-- Full iff statement of Beli (2019), Lemma 9.9. -/
theorem beli2019Lemma99
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (reference : GoodBONG q L 3)
    (R₁ R₂ R₃ A₁ : Int) (houter : R₁ = R₃) :
    Nonempty (Beli2019Lemma99Realization (q := q) R₁ R₂ R₃ A₁) ↔
      Beli2019Lemma99Conditions reference R₁ R₂ A₁ := by
  subst R₃
  constructor
  · rintro ⟨D⟩
    exact beli2019Lemma99_necessity reference R₁ R₂ R₁ A₁ rfl D
  · intro C
    exact beli2019Lemma99_sufficiency reference R₁ R₂ A₁ C

/-- The final assertion of Lemma 9.9, stated separately for direct reuse. -/
theorem beli2019Lemma99_moreover
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    (reference : GoodBONG q L 3)
    (R₁ R₂ R₃ A₁ : Int) (houter : R₁ = R₃)
    (hOdd : Odd A₁)
    (C : Beli2019Lemma99Conditions reference R₁ R₂ A₁) :
    Beli2019Lemma99OddRealization (q := q) R₁ R₂ R₃ A₁ := by
  subst R₃
  exact beli2019Lemma99_odd_sufficiency reference R₁ R₂ A₁ C hOdd

end BONG.GoodBONG

end Bong
