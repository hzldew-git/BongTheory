/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma92UnitChoice

/-!
# Beli (2019), Lemma 9.2: completed low-rank branches

This file assembles the common unit-choice certificate with the rank-four and
rank-five realizations.  The hypotheses are the explicit numerical facts
established in the reduction paragraphs of the printed proof.  Keeping them
in named structures makes the remaining task precise: derive these facts from
the failure of the corresponding identity branch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Numerical data common to both quaternary branches in the reduction of
Lemma 9.2.  The field names use zero-based Lean indices; `secondAlpha` and
`thirdAlpha` refer to the paper's `α₂` and `α₃`. -/
structure Lemma92RankFourCommonData (a : GoodBONG q L 4) : Prop where
  secondAlpha_odd : IsOddRationalInteger (a.alphaValue (1 : Fin 3))
  secondAlpha_nonnegative : 0 ≤ a.alphaValue (1 : Fin 3)
  secondAlpha_lt_twoE :
    a.alphaValue (1 : Fin 3) < 2 * (ramificationIndex K : ℚ)
  thirdAlpha_odd : IsOddRationalInteger (a.alphaValue (2 : Fin 3))
  thirdAlpha_nonnegative : 0 ≤ a.alphaValue (2 : Fin 3)
  thirdAlpha_lt_twoE :
    a.alphaValue (2 : Fin 3) < 2 * (ramificationIndex K : ℚ)
  lastAdjacent_gt_secondAlpha :
    (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.tail.adjacentDefect (1 : Fin 2)
  secondThird_sum_lt_twoE :
    a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) <
      2 * (ramificationIndex K : ℚ)
  thirdAlpha_recursion :
    a.alphaValue (2 : Fin 3) =
      (a.orderGap (2 : Fin 3) : ℚ) + a.alphaValue (1 : Fin 3)

/-- Extra data used in the printed `R₁ < R₃` quaternary branch. -/
structure Lemma92RankFourFirstData
    (a : GoodBONG q L 4) : Prop extends Lemma92RankFourCommonData a where
  firstAdjacent_lt_secondAlpha :
    a.adjacentDefect (0 : Fin 3) <
      (a.alphaValue (1 : Fin 3) : WithTop ℚ)
  firstAlpha_candidate :
    (((a.orderGap (0 : Fin 3) : Int) : ℚ) : WithTop ℚ) +
        a.adjacentDefect (0 : Fin 3) =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ)
  commonRightEndpoint : ∀ i : Fin 3,
    a.alphaRightEndpoint i = a.alphaRightEndpoint (0 : Fin 3)

/-- Extra data used in the alternating-order quaternary branch
`R₁ = R₃`, `R₂ = R₄`. -/
structure Lemma92RankFourAlternatingData
    (a : GoodBONG q L 4) : Prop extends Lemma92RankFourCommonData a where
  alternating : a.HasQuaternaryAlternatingOrders
  firstAlpha_candidate :
    (((a.orderGap (0 : Fin 3) : Int) : ℚ) : WithTop ℚ) +
        a.adjacentDefect (0 : Fin 3) =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ)
  commonRightEndpoint : ∀ i : Fin 3,
    a.alphaRightEndpoint i = a.alphaRightEndpoint (0 : Fin 3)

/-- Numerical data in the rank-five reduction used after all three early
alternatives have been excluded. -/
structure Lemma92RankFiveData (a : GoodBONG q L 5) : Prop where
  thirdAlpha_odd : IsOddRationalInteger (a.alphaValue (2 : Fin 4))
  thirdAlpha_nonnegative : 0 ≤ a.alphaValue (2 : Fin 4)
  thirdAlpha_lt_twoE :
    a.alphaValue (2 : Fin 4) < 2 * (ramificationIndex K : ℚ)
  fourthAlpha_odd : IsOddRationalInteger (a.alphaValue (3 : Fin 4))
  fourthAlpha_nonnegative : 0 ≤ a.alphaValue (3 : Fin 4)
  fourthAlpha_lt_twoE :
    a.alphaValue (3 : Fin 4) < 2 * (ramificationIndex K : ℚ)
  lastAdjacent_gt_thirdAlpha :
    (a.alphaValue (2 : Fin 4) : WithTop ℚ) <
      a.tail.tail.adjacentDefect (1 : Fin 2)
  thirdFourth_sum_lt_twoE :
    a.alphaValue (2 : Fin 4) + a.alphaValue (3 : Fin 4) <
      2 * (ramificationIndex K : ℚ)
  fourthAlpha_recursion :
    a.alphaValue (3 : Fin 4) =
      (a.orderGap (3 : Fin 4) : ℚ) + a.alphaValue (2 : Fin 4)
  firstBinary_normalized :
    a.adjacentBinaryAlpha (0 : Fin 4) =
      (a.alphaValue (0 : Fin 4) : WithTop ℚ)
  commonRightEndpoint : ∀ i : Fin 4,
    a.alphaRightEndpoint i = a.alphaRightEndpoint (0 : Fin 4)
  notEarly : ¬a.Lemma92EarlyAlternative

namespace Lemma92RankFourCommonData

/-- Lemma 8.2 supplies the two units used in either rank-four branch. -/
theorem exists_unitChoice
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    {a : GoodBONG q L 4} (D : Lemma92RankFourCommonData a) :
    Nonempty (Lemma92TernaryUnitChoiceData a.tail
      (a.alphaValue (1 : Fin 3)) (a.alphaValue (2 : Fin 3))) :=
  a.tail.exists_lemma92TernaryUnitChoiceData
    (a.alphaValue (1 : Fin 3)) (a.alphaValue (2 : Fin 3))
    D.secondAlpha_odd D.secondAlpha_nonnegative D.secondAlpha_lt_twoE
    D.thirdAlpha_odd D.thirdAlpha_nonnegative D.thirdAlpha_lt_twoE
    D.lastAdjacent_gt_secondAlpha D.secondThird_sum_lt_twoE

/-- The unit-choice certificate gives exactly the scaled final adjacent defect
appearing in the quaternary base equality. -/
theorem scaledLastAdjacent_defect
    [QuadraticDefectLaws K]
    {a : GoodBONG q L 4} (_D : Lemma92RankFourCommonData a)
    (U : Lemma92TernaryUnitChoiceData a.tail
      (a.alphaValue (1 : Fin 3)) (a.alphaValue (2 : Fin 3))) :
    defectOrder (K := K)
        (-(U.epsilon * a.valueUnit (2 : Fin 4) *
          a.valueUnit (3 : Fin 4))) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
  have hproduct :
      -(U.epsilon * a.valueUnit (2 : Fin 4) *
          a.valueUnit (3 : Fin 4)) =
        U.epsilon * a.tail.adjacentProduct (1 : Fin 2) := by
    unfold adjacentProduct
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    have hcast : Fin.castSucc (1 : Fin 2) = (1 : Fin 3) := Fin.ext rfl
    have hsucc : Fin.succ (1 : Fin 2) = (2 : Fin 3) := Fin.ext rfl
    rw [hcast, hsucc, a.valueUnit_goodTail (1 : Fin 3),
      a.valueUnit_goodTail (2 : Fin 3)]
    simp
    ring
  rw [hproduct]
  exact U.scaledLastAdjacent_defect

/-- The final recursion identity turns the preceding scaled defect into the
last alpha candidate used in both quaternary branches. -/
theorem lastCandidate
    [QuadraticDefectLaws K]
    {a : GoodBONG q L 4} (D : Lemma92RankFourCommonData a)
    (U : Lemma92TernaryUnitChoiceData a.tail
      (a.alphaValue (1 : Fin 3)) (a.alphaValue (2 : Fin 3))) :
    (((a.orderGap (2 : Fin 3) : Int) : ℚ) : WithTop ℚ) +
        defectOrder (K := K)
          (-(U.epsilon * a.valueUnit (2 : Fin 4) *
            a.valueUnit (3 : Fin 4))) =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
  rw [D.scaledLastAdjacent_defect U, ← WithTop.coe_add]
  exact_mod_cast D.thirdAlpha_recursion.symm

end Lemma92RankFourCommonData

namespace Lemma92RankFourFirstData

/-- Because the first adjacent defect is strictly smaller than `d(ε)`, the
first alpha candidate is unchanged by multiplication by `ε`. -/
theorem firstCandidate
    [QuadraticDefectLaws K]
    {a : GoodBONG q L 4} (D : Lemma92RankFourFirstData a)
    (U : Lemma92TernaryUnitChoiceData a.tail
      (a.alphaValue (1 : Fin 3)) (a.alphaValue (2 : Fin 3))) :
    (((a.orderGap (0 : Fin 3) : Int) : ℚ) : WithTop ℚ) +
        defectOrder (K := K)
          (-(U.epsilon * a.valueUnit (0 : Fin 4) *
            a.valueUnit (1 : Fin 4))) =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
  have hlt : a.adjacentDefect (0 : Fin 3) <
      defectOrder (K := K) U.epsilon := by
    rw [U.epsilon_defect]
    exact D.firstAdjacent_lt_secondAlpha
  have hdefect :
      defectOrder (K := K)
          (U.epsilon * a.adjacentProduct (0 : Fin 3)) =
        a.adjacentDefect (0 : Fin 3) := by
    exact defectOrder_mul_eq_right_of_lt_left hlt
  have hproduct :
      -(U.epsilon * a.valueUnit (0 : Fin 4) *
          a.valueUnit (1 : Fin 4)) =
        U.epsilon * a.adjacentProduct (0 : Fin 3) := by
    unfold adjacentProduct
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    simp
    ring
  rw [hproduct, hdefect]
  exact D.firstAlpha_candidate

/-- Completed rank-four `R₁ < R₃` branch, including construction on the same
lattice and the required head-deletion alpha equality. -/
theorem exists_transform
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    {a : GoodBONG q L 4} (D : Lemma92RankFourFirstData a) :
    Nonempty (Beli2019Lemma92Transform a) := by
  rcases D.toLemma92RankFourCommonData.exists_unitChoice with ⟨U⟩
  rcases a.exists_lemma92EarlyScalingData_of_firstCandidate
      U.epsilon U.eta U.epsilon_isValuationUnit U.eta_isValuationUnit
      U.epsilon_defect U.eta_defect U.adjacent_hilbert
      (D.firstCandidate U) D.commonRightEndpoint
      (le_of_lt D.secondThird_sum_lt_twoE) with ⟨S⟩
  exact S.exists_lemma92Transform D.thirdAlpha_recursion
    (D.toLemma92RankFourCommonData.scaledLastAdjacent_defect U)

end Lemma92RankFourFirstData

namespace Lemma92RankFourAlternatingData

/-- Completed alternating-order quaternary branch. -/
theorem exists_transform
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    {a : GoodBONG q L 4} (D : Lemma92RankFourAlternatingData a) :
    Nonempty (Beli2019Lemma92Transform a) := by
  rcases D.toLemma92RankFourCommonData.exists_unitChoice with ⟨U⟩
  rcases a.exists_lemma92EarlyScalingData_of_lastCandidate
      U.epsilon U.eta U.epsilon_isValuationUnit U.eta_isValuationUnit
      U.epsilon_defect U.eta_defect U.adjacent_hilbert D.alternating
      (D.toLemma92RankFourCommonData.lastCandidate U) with ⟨S⟩
  exact S.exists_lemma92Transform D.thirdAlpha_recursion
    (D.toLemma92RankFourCommonData.scaledLastAdjacent_defect U)

end Lemma92RankFourAlternatingData

namespace Lemma92RankFiveData

/-- Lemma 8.2 supplies the two units in the rank-five branch. -/
theorem exists_unitChoice
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    {a : GoodBONG q L 5} (D : Lemma92RankFiveData a) :
    Nonempty (Lemma92TernaryUnitChoiceData a.tail.tail
      (a.alphaValue (2 : Fin 4)) (a.alphaValue (3 : Fin 4))) :=
  a.tail.tail.exists_lemma92TernaryUnitChoiceData
    (a.alphaValue (2 : Fin 4)) (a.alphaValue (3 : Fin 4))
    D.thirdAlpha_odd D.thirdAlpha_nonnegative D.thirdAlpha_lt_twoE
    D.fourthAlpha_odd D.fourthAlpha_nonnegative D.fourthAlpha_lt_twoE
    D.lastAdjacent_gt_thirdAlpha D.thirdFourth_sum_lt_twoE

/-- The rank-five unit certificate gives the scaled last adjacent defect. -/
theorem scaledLastAdjacent_defect
    [QuadraticDefectLaws K]
    {a : GoodBONG q L 5} (_D : Lemma92RankFiveData a)
    (U : Lemma92TernaryUnitChoiceData a.tail.tail
      (a.alphaValue (2 : Fin 4)) (a.alphaValue (3 : Fin 4))) :
    defectOrder (K := K)
        (-(U.epsilon * a.valueUnit (3 : Fin 5) *
          a.valueUnit (4 : Fin 5))) =
      (a.alphaValue (2 : Fin 4) : WithTop ℚ) := by
  have hproduct :
      -(U.epsilon * a.valueUnit (3 : Fin 5) *
          a.valueUnit (4 : Fin 5)) =
        U.epsilon * a.tail.tail.adjacentProduct (1 : Fin 2) := by
    unfold adjacentProduct
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    have hcast : Fin.castSucc (1 : Fin 2) = (1 : Fin 3) := Fin.ext rfl
    have hsucc : Fin.succ (1 : Fin 2) = (2 : Fin 3) := Fin.ext rfl
    have htailSuccOne : Fin.succ (1 : Fin 3) = (2 : Fin 4) := Fin.ext rfl
    have htailSuccTwo : Fin.succ (2 : Fin 3) = (3 : Fin 4) := Fin.ext rfl
    rw [hcast, hsucc, a.tail.valueUnit_goodTail (1 : Fin 3),
      a.tail.valueUnit_goodTail (2 : Fin 3), htailSuccOne, htailSuccTwo,
      a.valueUnit_goodTail (2 : Fin 4),
      a.valueUnit_goodTail (3 : Fin 4)]
    simp
    ring
  rw [hproduct]
  exact U.scaledLastAdjacent_defect

/-- Completed rank-five branch of Lemma 9.2. -/
theorem exists_transform
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    {a : GoodBONG q L 5} (D : Lemma92RankFiveData a) :
    Nonempty (Beli2019Lemma92Transform a) := by
  rcases D.exists_unitChoice with ⟨U⟩
  rcases a.exists_lemma92LaterScalingData
      U.epsilon U.eta U.epsilon_isValuationUnit U.eta_isValuationUnit
      U.epsilon_defect U.eta_defect U.adjacent_hilbert
      D.firstBinary_normalized D.commonRightEndpoint
      (le_of_lt D.thirdFourth_sum_lt_twoE) with ⟨S⟩
  exact S.exists_lemma92Transform D.notEarly D.fourthAlpha_recursion
    (D.scaledLastAdjacent_defect U)

end Lemma92RankFiveData

/-- Exhaustion form of the quaternary proof: either the original BONG already
has the required head-deletion equality, or one of the two explicit scaling
branches applies. -/
theorem exists_lemma92Transform_rankFour_of_reduction
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 4)
    (hcases :
      a.alphaValue (2 : Fin 3) = a.tail.alphaValue (1 : Fin 2) ∨
        Lemma92RankFourFirstData a ∨
          Lemma92RankFourAlternatingData a) :
    Nonempty (Beli2019Lemma92Transform a) := by
  rcases hcases with heq | hfirst | halternating
  · apply exists_lemma92Transform_identity a
    · intro i hi
      omega
    · intro _
      exact heq
  · exact hfirst.exists_transform
  · exact halternating.exists_transform

/-- Exhaustion form of the rank-five proof in the complement of the early
alternative. -/
theorem exists_lemma92Transform_rankFive_of_reduction
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 5) (hnotEarly : ¬a.Lemma92EarlyAlternative)
    (hcases :
      a.alphaValue (3 : Fin 4) = a.tail.alphaValue (2 : Fin 3) ∨
        Lemma92RankFiveData a) :
    Nonempty (Beli2019Lemma92Transform a) := by
  rcases hcases with heq | D
  · apply exists_lemma92Transform_identity a
    · intro i hi
      have hiTwo : i = (2 : Fin 3) := by
        apply Fin.ext
        change i.1 = 2
        omega
      subst i
      exact heq
    · intro hearly
      exact (hnotEarly hearly).elim
  · exact D.exists_transform

end BONG.GoodBONG

end Bong
