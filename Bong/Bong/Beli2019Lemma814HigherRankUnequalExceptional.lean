/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814HigherRankUnequalBoundary
import Bong.Bong.Beli2019Lemma73

/-!
# Beli (2019), Lemma 8.14: the unequal-outer exceptional boundary

This file closes the final higher-rank branch of Lemma 8.14.  On the
third-alpha half-gap boundary it derives the right-endpoint plateau and the
odd unit-defect spectrum, reduces the third binary exception to case (b),
reinstates reduction (II), and applies Corollary 8.9 to the initial ternary
segment.  Lemma 8.1(ii) then raises the third adjacent defect strictly and
eliminates the remaining binary exception.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

theorem lemma814UnequalBoundary_rightEndpoint_eq
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (E : a.Beli2019Lemma814UnequalBoundaryExceptionalData b) :
    let c := E.hardData.normalForm.transformed
    c.alphaRightEndpoint (0 : Fin (N + 3)) =
      c.alphaRightEndpoint (2 : Fin (N + 3)) := by
  let c := E.hardData.normalForm.transformed
  have hcapped : c.truncatedPrefixDefect b (-1) 3 1 =
      (c.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) := by
    rw [c.lemma814FirstThirdCappedDefect_eq_min_raw b,
      min_eq_right E.hardData.thirdAlpha_lt_rawDefect.le]
  have hboundTop := E.hardData.unequalOuterBound.2
  rw [hcapped] at hboundTop
  dsimp only [c] at hboundTop
  have hboundTop' :
      (E.hardData.normalForm.transformed.alphaValue
          (0 : Fin (N + 3)) : WithTop ℚ) +
          (((E.hardData.normalForm.transformed.order
            (2 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) +
          (E.hardData.normalForm.transformed.alphaValue
            (2 : Fin (N + 3)) : WithTop ℚ) ≤
        ((2 * (ramificationIndex K : ℚ) +
          (E.hardData.normalForm.transformed.order
            (1 : Fin (N + 4)) : ℚ) : ℚ) : WithTop ℚ) := by
    simpa only [add_assoc] using hboundTop
  have hbound :
      c.alphaValue (0 : Fin (N + 3)) +
          (c.order (2 : Fin (N + 4)) : ℚ) +
          c.alphaValue (2 : Fin (N + 3)) ≤
        2 * (ramificationIndex K : ℚ) +
          (c.order (1 : Fin (N + 4)) : ℚ) := by
    dsimp only [c]
    exact_mod_cast hboundTop'
  have hboundary := E.thirdAlpha_eq_halfGap
  unfold halfGapValue orderGap at hboundary
  change c.alphaValue (2 : Fin (N + 3)) =
      (((c.order (3 : Fin (N + 4)) - c.order (2 : Fin (N + 4)) : Int) : ℚ) /
        2 + (ramificationIndex K : ℚ)) at hboundary
  push_cast at hboundary
  have hforward : c.alphaRightEndpoint (0 : Fin (N + 3)) ≤
      c.alphaRightEndpoint (2 : Fin (N + 3)) := by
    unfold alphaRightEndpoint
    change -(c.order (1 : Fin (N + 4)) : ℚ) +
        c.alphaValue (0 : Fin (N + 3)) ≤
      -(c.order (3 : Fin (N + 4)) : ℚ) +
        c.alphaValue (2 : Fin (N + 3))
    linarith
  have hreverse : c.alphaRightEndpoint (2 : Fin (N + 3)) ≤
      c.alphaRightEndpoint (0 : Fin (N + 3)) :=
    c.alphaRightEndpoint_antitone (by norm_num)
  exact le_antisymm hforward hreverse

theorem lemma814UnequalBoundary_middleRightEndpoint_eq
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (E : a.Beli2019Lemma814UnequalBoundaryExceptionalData b) :
    let c := E.hardData.normalForm.transformed
    c.alphaRightEndpoint (1 : Fin (N + 3)) =
      c.alphaRightEndpoint (2 : Fin (N + 3)) := by
  let c := E.hardData.normalForm.transformed
  have houter := lemma814UnequalBoundary_rightEndpoint_eq a b E
  have hmiddle := c.beli2019Lemma84_i_right
    (0 : Fin (N + 3)) (2 : Fin (N + 3)) (by norm_num) houter
    (1 : Fin (N + 3))
      (by change (0 : Nat) ≤ 1; omega) (by change (1 : Nat) ≤ 2; omega)
  exact hmiddle.trans houter

theorem lemma814UnequalBoundary_secondAlpha_eq_complementary
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (E : a.Beli2019Lemma814UnequalBoundaryExceptionalData b) :
    let c := E.hardData.normalForm.transformed
    c.alphaValue (1 : Fin (N + 3)) =
      (ramificationIndex K : ℚ) -
        ((c.order (3 : Fin (N + 4)) - c.order (2 : Fin (N + 4)) : Int) : ℚ) / 2 := by
  let c := E.hardData.normalForm.transformed
  have hendpoint := lemma814UnequalBoundary_middleRightEndpoint_eq a b E
  unfold alphaRightEndpoint at hendpoint
  change -(c.order (2 : Fin (N + 4)) : ℚ) +
      c.alphaValue (1 : Fin (N + 3)) =
    -(c.order (3 : Fin (N + 4)) : ℚ) +
      c.alphaValue (2 : Fin (N + 3)) at hendpoint
  have hboundary := E.thirdAlpha_eq_halfGap
  unfold halfGapValue orderGap at hboundary
  change c.alphaValue (2 : Fin (N + 3)) =
      (((c.order (3 : Fin (N + 4)) - c.order (2 : Fin (N + 4)) : Int) : ℚ) /
        2 + (ramificationIndex K : ℚ)) at hboundary
  push_cast at hboundary ⊢
  linarith

theorem lemma814UnequalBoundary_secondThirdAlpha_sum
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (E : a.Beli2019Lemma814UnequalBoundaryExceptionalData b) :
    let c := E.hardData.normalForm.transformed
    c.alphaValue (1 : Fin (N + 3)) +
        c.alphaValue (2 : Fin (N + 3)) =
      2 * (ramificationIndex K : ℚ) := by
  let c := E.hardData.normalForm.transformed
  have hsecond := lemma814UnequalBoundary_secondAlpha_eq_complementary a b E
  have hboundary := E.thirdAlpha_eq_halfGap
  unfold halfGapValue orderGap at hboundary
  change c.alphaValue (2 : Fin (N + 3)) =
      (((c.order (3 : Fin (N + 4)) - c.order (2 : Fin (N + 4)) : Int) : ℚ) /
        2 + (ramificationIndex K : ℚ)) at hboundary
  linarith

theorem lemma814UnequalBoundary_firstAlpha_lt_halfGap
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (E : a.Beli2019Lemma814UnequalBoundaryExceptionalData b) :
    let c := E.hardData.normalForm.transformed
    c.alphaValue (0 : Fin (N + 3)) <
      c.halfGapValue (0 : Fin (N + 3)) := by
  let c := E.hardData.normalForm.transformed
  have hendpoint := lemma814UnequalBoundary_rightEndpoint_eq a b E
  unfold alphaRightEndpoint at hendpoint
  change -(c.order (1 : Fin (N + 4)) : ℚ) +
      c.alphaValue (0 : Fin (N + 3)) =
    -(c.order (3 : Fin (N + 4)) : ℚ) +
      c.alphaValue (2 : Fin (N + 3)) at hendpoint
  have hboundary := E.thirdAlpha_eq_halfGap
  unfold halfGapValue orderGap at hboundary
  change c.alphaValue (2 : Fin (N + 3)) =
      (((c.order (3 : Fin (N + 4)) - c.order (2 : Fin (N + 4)) : Int) : ℚ) /
        2 + (ramificationIndex K : ℚ)) at hboundary
  have houterQ : (c.order (0 : Fin (N + 4)) : ℚ) <
      c.order (2 : Fin (N + 4)) := by
    exact_mod_cast E.hardData.normalForm.outer_lt
  have hgoodQ : (c.order (1 : Fin (N + 4)) : ℚ) ≤
      c.order (3 : Fin (N + 4)) := by
    have hgood := c.good (⟨1, by omega⟩ : Fin (N + 4))
      (by change 1 + 2 < N + 4; omega)
    change c.order (1 : Fin (N + 4)) ≤ c.order (3 : Fin (N + 4)) at hgood
    exact_mod_cast hgood
  unfold halfGapValue orderGap
  change c.alphaValue (0 : Fin (N + 3)) <
    (((c.order (1 : Fin (N + 4)) - c.order (0 : Fin (N + 4)) : Int) : ℚ) /
      2 + (ramificationIndex K : ℚ))
  push_cast at hboundary ⊢
  linarith

private theorem oddRationalInteger_of_modEqTwo
    {x y : ℚ} (hxy : RationalModEqTwo x y)
    (hy : IsOddRationalInteger y) : IsOddRationalInteger x := by
  rcases hxy with ⟨a, b, hxa, hyb, hab⟩
  rcases hy with ⟨z, hzOdd, hyz⟩
  have hbz : b = z := by
    exact_mod_cast hyb.symm.trans hyz
  subst z
  refine ⟨a, ?_, hxa⟩
  rw [Int.modEq_iff_dvd] at hab
  rcases hab with ⟨k, hk⟩
  rcases hzOdd with ⟨d, hd⟩
  exact ⟨d - k, by omega⟩

private theorem oddRationalInteger_lt_two_mul_of_le
    {x : ℚ} {e : Nat} (hodd : IsOddRationalInteger x)
    (hle : x ≤ 2 * (e : ℚ)) : x < 2 * (e : ℚ) := by
  apply lt_of_le_of_ne hle
  intro heq
  rcases hodd with ⟨z, ⟨d, hd⟩, hz⟩
  have hze : z = 2 * (e : Int) := by
    exact_mod_cast hz.symm.trans heq
  omega

structure Beli2019Lemma814UnequalBoundaryAlphaData (c : GoodBONG q L (N + 4)) : Prop where
  rightEndpoint_eq : c.alphaRightEndpoint (0 : Fin (N + 3)) =
    c.alphaRightEndpoint (2 : Fin (N + 3))
  secondAlpha_eq_complement : c.alphaValue (1 : Fin (N + 3)) =
    (ramificationIndex K : ℚ) -
      ((c.order (3 : Fin (N + 4)) - c.order (2 : Fin (N + 4)) : Int) : ℚ) / 2
  secondThirdAlpha_sum : c.alphaValue (1 : Fin (N + 3)) +
    c.alphaValue (2 : Fin (N + 3)) = 2 * (ramificationIndex K : ℚ)
  first_odd : IsOddRationalInteger (c.alphaValue (0 : Fin (N + 3)))
  second_odd : IsOddRationalInteger (c.alphaValue (1 : Fin (N + 3)))
  third_odd : IsOddRationalInteger (c.alphaValue (2 : Fin (N + 3)))
  first_lt_twoE : c.alphaValue (0 : Fin (N + 3)) < 2 * (ramificationIndex K : ℚ)
  second_lt_twoE : c.alphaValue (1 : Fin (N + 3)) < 2 * (ramificationIndex K : ℚ)
  third_lt_twoE : c.alphaValue (2 : Fin (N + 3)) < 2 * (ramificationIndex K : ℚ)

theorem lemma814UnequalBoundary_alphaData
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (E : a.Beli2019Lemma814UnequalBoundaryExceptionalData b) :
    let c := E.hardData.normalForm.transformed
    Beli2019Lemma814UnequalBoundaryAlphaData c := by
  let c := E.hardData.normalForm.transformed
  have hendpoint := lemma814UnequalBoundary_rightEndpoint_eq a b E
  have hfirstOdd := c.beli2009Lemma27_iv (0 : Fin (N + 3))
    (ne_of_lt (lemma814UnequalBoundary_firstAlpha_lt_halfGap a b E))
  have h73 := c.beli2019Lemma73_ii
    (0 : Fin (N + 3)) (2 : Fin (N + 3))
      (by change (0 : Nat) < 2; omega) hendpoint
  have hsecondOdd := oddRationalInteger_of_modEqTwo
    (h73.alpha_modEq (1 : Fin (N + 3))
      (by change (0 : Nat) ≤ 1; omega)
      (by change (1 : Nat) ≤ 2; omega)) hfirstOdd
  have hthirdOdd := oddRationalInteger_of_modEqTwo
    (h73.alpha_modEq (2 : Fin (N + 3))
      (by change (0 : Nat) ≤ 2; omega) le_rfl) hfirstOdd
  have hfirstLe := h73.alpha_le (0 : Fin (N + 3)) le_rfl
    (by change (0 : Nat) ≤ 2; omega)
  have hsecondLe := h73.alpha_le (1 : Fin (N + 3))
    (by change (0 : Nat) ≤ 1; omega) (by change (1 : Nat) ≤ 2; omega)
  have hthirdLe := h73.alpha_le (2 : Fin (N + 3))
    (by change (0 : Nat) ≤ 2; omega) le_rfl
  exact {
    rightEndpoint_eq := hendpoint
    secondAlpha_eq_complement := lemma814UnequalBoundary_secondAlpha_eq_complementary a b E
    secondThirdAlpha_sum := lemma814UnequalBoundary_secondThirdAlpha_sum a b E
    first_odd := hfirstOdd
    second_odd := hsecondOdd
    third_odd := hthirdOdd
    first_lt_twoE := oddRationalInteger_lt_two_mul_of_le hfirstOdd hfirstLe
    second_lt_twoE := oddRationalInteger_lt_two_mul_of_le hsecondOdd hsecondLe
    third_lt_twoE := oddRationalInteger_lt_two_mul_of_le hthirdOdd hthirdLe
  }

theorem lemma814UnequalBoundary_unitDefects
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [DyadicUnitDefectSpectrumLaws K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (E : a.Beli2019Lemma814UnequalBoundaryExceptionalData b) :
    let c := E.hardData.normalForm.transformed
    IsValuationUnitDefect (K := K) (c.alphaValue (0 : Fin (N + 3))) ∧
      IsValuationUnitDefect (K := K) (c.alphaValue (1 : Fin (N + 3))) ∧
        IsValuationUnitDefect (K := K) (c.alphaValue (2 : Fin (N + 3))) := by
  let c := E.hardData.normalForm.transformed
  have D := lemma814UnequalBoundary_alphaData a b E
  have hfirstNonnegative := (c.beli2009Lemma27_i (0 : Fin (N + 3))).1
  have hsecondNonnegative := (c.beli2009Lemma27_i (1 : Fin (N + 3))).1
  have hthirdNonnegative := (c.beli2009Lemma27_i (2 : Fin (N + 3))).1
  exact ⟨
    DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      _ D.first_odd hfirstNonnegative D.first_lt_twoE,
    DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      _ D.second_odd hsecondNonnegative D.second_lt_twoE,
    DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      _ D.third_odd hthirdNonnegative D.third_lt_twoE
  ⟩

theorem lemma814UnequalThirdPair_adjacentDefect_eq
    (c : GoodBONG q L (N + 4)) :
    c.lemma814UnequalThirdPair.adjacentDefect (0 : Fin 1) =
      c.adjacentDefect (2 : Fin (N + 3)) := by
  let s := c.lemma814UnequalThirdPair
  let w := c.lemma814UnequalThirdPairSegment
  unfold adjacentDefect adjacentProduct GoodBONG.valueUnit
  change defectOrder (K := K)
      (-(w.bong.valueUnit 0 * w.bong.valueUnit 1)) =
    defectOrder (K := K)
      (-(c.toBONG.valueUnit 2 * c.toBONG.valueUnit 3))
  rw [w.valueUnit_eq, w.valueUnit_eq]
  congr 3

structure Beli2019Lemma814UnequalPairExceptionData (c : GoodBONG q L (N + 4)) : Prop where
  residueTwo : ¬HasResidueFieldMoreThanTwoElements (K := K)
  thirdAdjacentDefect_eq_secondAlpha :
    c.adjacentDefect (2 : Fin (N + 3)) =
      (c.alphaValue (1 : Fin (N + 3)) : WithTop ℚ)

theorem lemma814UnequalBoundary_pairExceptionData
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [DyadicUnitDefectSpectrumLaws K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (E : a.Beli2019Lemma814UnequalBoundaryExceptionalData b) :
    let c := E.hardData.normalForm.transformed
    Beli2019Lemma814UnequalPairExceptionData c := by
  let c := E.hardData.normalForm.transformed
  let s := c.lemma814UnequalThirdPair
  have D := lemma814UnequalBoundary_alphaData a b E
  have hthirdUnit := (lemma814UnequalBoundary_unitDefects a b E).2.2
  have halpha : s.alphaValue (0 : Fin 1) =
      c.alphaValue (2 : Fin (N + 3)) :=
    c.lemma814UnequalThirdPair_alpha_eq_thirdAlpha
      E.hardData.normalForm.thirdBinaryAlpha_eq
  have hlocalUnit : IsValuationUnitDefect (K := K)
      (s.alphaValue (0 : Fin 1)) := by
    rw [halpha]
    exact hthirdUnit
  have hE : s.Beli2019Lemma88Exceptional := by
    simpa only [c, s] using E.thirdPairExceptional
  rcases hE with ⟨hhalf, hA | hB | hC⟩
  · exact (hA hlocalUnit).elim
  · rcases hB with ⟨B⟩
    have hadjacentLocal :=
      s.adjacentDefect_zero_eq_complementary_of_lemma88ExceptionB B
    have hcomplement : s.lemma88ComplementaryDefect =
        c.alphaValue (1 : Fin (N + 3)) := by
      have hboundary := s.halfGap_add_lemma88ComplementaryDefect
      unfold AttainsHalfGap at hhalf
      rw [← hhalf, halpha] at hboundary
      linarith [D.secondThirdAlpha_sum]
    have hadjacent : c.adjacentDefect (2 : Fin (N + 3)) =
        (c.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) := by
      rw [← lemma814UnequalThirdPair_adjacentDefect_eq c, hadjacentLocal]
      exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hcomplement
    exact {
      residueTwo := B.residueTwo
      thirdAdjacentDefect_eq_secondAlpha := hadjacent
    }
  · rcases hC with ⟨C⟩
    exact ((by omega : ¬3 ≤ 2) C.rank_three).elim

structure Beli2019Lemma814UnequalReducedExceptionalData
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1) where
  hardData : a.Beli2019Lemma814UnequalHardData b
  thirdAlpha_eq_halfGap :
    hardData.normalForm.transformed.alphaValue (2 : Fin (N + 3)) =
      hardData.normalForm.transformed.halfGapValue (2 : Fin (N + 3))
  thirdPairExceptional :
    hardData.normalForm.transformed.lemma814UnequalThirdPair.Beli2019Lemma88Exceptional
  initialThreeSecondAlpha_eq :
    hardData.normalForm.transformed.lemma814InitialThree.alphaValue (1 : Fin 2) =
      hardData.normalForm.transformed.alphaValue (1 : Fin (N + 3))

theorem lemma814UnequalBoundary_reduceII_dispatch
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a original : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (E : a.Beli2019Lemma814UnequalBoundaryExceptionalData b) :
    let c := E.hardData.normalForm.transformed
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) ∨
      Nonempty (c.Beli2019Lemma814UnequalReducedExceptionalData b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  let c := E.hardData.normalForm.transformed
  rcases c.exists_lemma814SecondNormalForm
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW) b
      E.hardData.normalForm.firstOrder_eq
      E.hardData.normalForm.conditions
      E.hardData.normalForm.firstBinaryAlpha_eq
      E.hardData.normalForm.notExceptional with ⟨S⟩
  let d := S.transformed
  have horders := c.order_invariant d
  have halphas := c.alpha_invariant d
  have hhalf : d.AttainsHalfGap (2 : Fin (N + 3)) := by
    unfold AttainsHalfGap
    rw [← halphas (2 : Fin (N + 3)),
      ← c.halfGapValue_invariant (classificationV := classificationV)
        d (2 : Fin (N + 3))]
    exact E.thirdAlpha_eq_halfGap
  have hthirdBinary : d.adjacentBinaryAlpha (2 : Fin (N + 3)) =
      (d.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) :=
    d.adjacentBinaryAlpha_eq_alpha_of_attainsHalfGap
      (2 : Fin (N + 3)) hhalf
  have houter : d.order (0 : Fin (N + 4)) <
      d.order (2 : Fin (N + 4)) := by
    rw [← horders (0 : Fin (N + 4)), ← horders (2 : Fin (N + 4))]
    exact E.hardData.normalForm.outer_lt
  have hstrict :
      (d.order (0 : Fin (N + 4)) : ℚ) +
          d.alphaValue (0 : Fin (N + 3)) <
        (d.order (1 : Fin (N + 4)) : ℚ) +
          d.alphaValue (1 : Fin (N + 3)) := by
    rw [← horders (0 : Fin (N + 4)),
      ← halphas (0 : Fin (N + 3)),
      ← horders (1 : Fin (N + 4)),
      ← halphas (1 : Fin (N + 3))]
    exact E.hardData.normalForm.firstEndpoint_strict
  let T : c.Beli2019Lemma814ThirdAdjacentNormalForm b := {
    transformed := d
    firstOrder_eq := S.firstOrder_eq
    firstBinaryAlpha_eq := S.firstBinaryAlpha_eq
    thirdBinaryAlpha_eq := hthirdBinary
    outer_lt := houter
    firstEndpoint_strict := hstrict
    conditions := S.conditions
    notExceptional := S.notExceptional
  }
  by_cases hone : hilbertSymbol K (d.lemma814Epsilon b)
      (d.adjacentProduct (0 : Fin (N + 3))) = 1
  · left
    rcases d.beli2019Lemma814_binaryBranch b S.firstOrder_eq S.conditions
        S.firstBinaryAlpha_eq hone with ⟨U⟩
    exact ⟨{
      transformed := U.transformed
      firstValue_eq := U.firstValue_eq
    }⟩
  · have hneg : hilbertSymbol K (d.lemma814Epsilon b)
        (d.adjacentProduct (0 : Fin (N + 3))) = -1 := by
      apply (hilbertSymbol_eq_neg_one_iff K _ _).2
      intro hnorm
      exact hone ((hilbertSymbol_eq_one_iff K _ _).2 hnorm)
    rcases d.lemma814_outerCases_of_hilbert_neg_one b S.conditions hneg with
      houterEq | hbound
    · exact (ne_of_lt houter houterEq).elim
    · by_cases hraw : defectOrder (K := K)
          ((-1) * d.prefixProduct 3 * b.prefixProduct 1) ≤
        (d.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)
      · left
        exact d.beli2019Lemma814_higherRankUnequal_of_raw_le_thirdAlpha
          (classificationV := classificationV)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV)
          (prefixChangeW := prefixChangeW)
          original b S.firstOrder_eq S.conditions S.firstBinaryAlpha_eq
            hbound hraw
      · let H : c.Beli2019Lemma814UnequalHardData b := {
          normalForm := T
          hilbert_neg_one := hneg
          unequalOuterBound := hbound
          thirdAlpha_lt_rawDefect := lt_of_not_ge hraw
        }
        by_cases hpair :
          d.lemma814UnequalThirdPair.Beli2019Lemma88Exceptional
        · right
          exact ⟨{
            hardData := H
            thirdAlpha_eq_halfGap := by
              dsimp only [H, T]
              exact hhalf
            thirdPairExceptional := by
              dsimp only [H, T]
              exact hpair
            initialThreeSecondAlpha_eq := by
              dsimp only [H, T]
              exact S.initialThreeSecondAlpha_eq
          }⟩
        · left
          exact
            beli2019Lemma814_higherRankUnequal_boundary_of_thirdPair_notExceptional
              (classificationV := classificationV)
              (classificationW := classificationW)
              (prefixChangeV := prefixChangeV)
              (prefixChangeW := prefixChangeW)
              c original b H (by simpa only [H, T] using hpair)

theorem lemma814UnequalInitialThree_not_corollary89Exceptional
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [DyadicUnitDefectSpectrumLaws K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (R : a.Beli2019Lemma814UnequalReducedExceptionalData b) :
    ¬R.hardData.normalForm.transformed.lemma814InitialThree.Beli2019Corollary89Exceptional := by
  let d := R.hardData.normalForm.transformed
  let E : a.Beli2019Lemma814UnequalBoundaryExceptionalData b := {
    hardData := R.hardData
    thirdAlpha_eq_halfGap := R.thirdAlpha_eq_halfGap
    thirdPairExceptional := R.thirdPairExceptional
  }
  let s := d.lemma814InitialThree
  have A : Beli2019Lemma814UnequalBoundaryAlphaData d := by
    simpa only [E, d] using lemma814UnequalBoundary_alphaData a b E
  have hsecondUnit : IsValuationUnitDefect (K := K)
      (d.alphaValue (1 : Fin (N + 3))) := by
    simpa only [E, d] using (lemma814UnequalBoundary_unitDefects a b E).2.1
  have hfirstLocal : s.alphaValue (0 : Fin 2) =
      d.alphaValue (0 : Fin (N + 3)) :=
    d.lemma814InitialThree_firstAlpha_eq
      R.hardData.normalForm.firstBinaryAlpha_eq
  have hsecondLocal : s.alphaValue (1 : Fin 2) =
      d.alphaValue (1 : Fin (N + 3)) :=
    R.initialThreeSecondAlpha_eq
  intro hExceptional
  rcases hExceptional with ⟨hhalf, hA | hB | hC⟩
  · apply hA
    change IsValuationUnitDefect (K := K) (s.alphaValue (1 : Fin 2))
    rw [hsecondLocal]
    exact hsecondUnit
  · rcases hB with ⟨B⟩
    have hlocalHalf := hhalf
    unfold AttainsHalfGap at hlocalHalf
    change s.alphaValue (1 : Fin 2) =
      s.halfGapValue (1 : Fin 2) at hlocalHalf
    have hsecondHalf : d.alphaValue (1 : Fin (N + 3)) =
        d.halfGapValue (1 : Fin (N + 3)) := by
      unfold halfGapValue orderGap at hlocalHalf ⊢
      change s.alphaValue (1 : Fin 2) =
        (((s.order (2 : Fin 3) - s.order (1 : Fin 3) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ)) at hlocalHalf
      change d.alphaValue (1 : Fin (N + 3)) =
        (((d.order (2 : Fin (N + 4)) - d.order (1 : Fin (N + 4)) : Int) : ℚ) /
          2 + (ramificationIndex K : ℚ))
      rw [hsecondLocal] at hlocalHalf
      rw [d.lemma814InitialThree_order_eq,
        d.lemma814InitialThree_order_eq] at hlocalHalf
      exact hlocalHalf
    have horderOneThreeQ : (d.order (1 : Fin (N + 4)) : ℚ) =
        d.order (3 : Fin (N + 4)) := by
      unfold halfGapValue orderGap at hsecondHalf
      change d.alphaValue (1 : Fin (N + 3)) =
        (((d.order (2 : Fin (N + 4)) - d.order (1 : Fin (N + 4)) : Int) : ℚ) /
          2 + (ramificationIndex K : ℚ)) at hsecondHalf
      have hcomplementFormula := A.secondAlpha_eq_complement
      push_cast at hsecondHalf hcomplementFormula
      linarith
    have horderOneThree : d.order (1 : Fin (N + 4)) =
        d.order (3 : Fin (N + 4)) := by
      exact_mod_cast horderOneThreeQ
    have hfirstThirdAlpha : d.alphaValue (0 : Fin (N + 3)) =
        d.alphaValue (2 : Fin (N + 3)) := by
      have hendpoint := A.rightEndpoint_eq
      unfold alphaRightEndpoint at hendpoint
      change -(d.order (1 : Fin (N + 4)) : ℚ) +
          d.alphaValue (0 : Fin (N + 3)) =
        -(d.order (3 : Fin (N + 4)) : ℚ) +
          d.alphaValue (2 : Fin (N + 3)) at hendpoint
      rw [horderOneThree] at hendpoint
      linarith
    have hcomplement : s.lemma89ComplementaryDefect =
        d.alphaValue (2 : Fin (N + 3)) := by
      unfold lemma89ComplementaryDefect orderGap
      change (ramificationIndex K : ℚ) -
          (((s.order (2 : Fin 3) - s.order (1 : Fin 3) : Int) : ℚ) / 2) =
        d.alphaValue (2 : Fin (N + 3))
      rw [d.lemma814InitialThree_order_eq,
        d.lemma814InitialThree_order_eq]
      have hthird := R.thirdAlpha_eq_halfGap
      unfold halfGapValue orderGap at hthird
      change d.alphaValue (2 : Fin (N + 3)) =
        (((d.order (3 : Fin (N + 4)) - d.order (2 : Fin (N + 4)) : Int) : ℚ) /
          2 + (ramificationIndex K : ℚ)) at hthird
      push_cast at hthird ⊢
      change (ramificationIndex K : ℚ) -
          ((d.order (2 : Fin (N + 4)) : ℚ) - d.order (1 : Fin (N + 4))) / 2 =
        d.alphaValue (2 : Fin (N + 3))
      rw [horderOneThree]
      linarith
    have hstrict := B.previousAlpha_strict (by omega : 3 ≤ 3)
    change s.lemma89ComplementaryDefect < s.alphaValue (0 : Fin 2) at hstrict
    rw [hcomplement, hfirstLocal, hfirstThirdAlpha] at hstrict
    exact (lt_irrefl _ hstrict).elim
  · rcases hC with ⟨C⟩
    have houterLocal := C.outerOrders_eq
    have houter : d.order (0 : Fin (N + 4)) =
        d.order (2 : Fin (N + 4)) := by
      change s.order (0 : Fin 3) = s.order (2 : Fin 3) at houterLocal
      rw [d.lemma814InitialThree_order_eq,
        d.lemma814InitialThree_order_eq] at houterLocal
      exact houterLocal
    exact (ne_of_lt R.hardData.normalForm.outer_lt houter).elim

structure Beli2019Lemma814UnequalCorollary89ScalingData
    (d : GoodBONG q L (N + 4)) where
  epsilon : Kˣ
  epsilon_isValuationUnit : IsValuationUnit K (epsilon : K)
  epsilon_defect : defectOrder (K := K) epsilon =
    (d.alphaValue (1 : Fin (N + 3)) : WithTop ℚ)
  transformed : GoodBONG q L (N + 4)
  thirdValue_eq : transformed.valueUnit (2 : Fin (N + 4)) =
    epsilon * d.valueUnit (2 : Fin (N + 4))
  fourthValue_eq : transformed.valueUnit (3 : Fin (N + 4)) =
    d.valueUnit (3 : Fin (N + 4))

theorem exists_lemma814UnequalCorollary89ScalingData
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (R : a.Beli2019Lemma814UnequalReducedExceptionalData b) :
    Nonempty (Beli2019Lemma814UnequalCorollary89ScalingData R.hardData.normalForm.transformed) := by
  let d := R.hardData.normalForm.transformed
  let s := d.lemma814InitialThree
  have hnot := lemma814UnequalInitialThree_not_corollary89Exceptional a b R
  rcases s.beli2019Corollary89 hnot with ⟨T⟩
  rcases d.toBONG.beliLemma49_ii d.good d.lemma814InitialThreeSegment
      T.transformed.toBONG T.transformed.good with ⟨replacement⟩
  let transformed : GoodBONG q L (N + 4) :=
    ⟨replacement.bong, replacement.good⟩
  have hthirdLocal : transformed.valueUnit (2 : Fin (N + 4)) =
      T.transformed.valueUnit (2 : Fin 3) := by
    apply Units.ext
    change replacement.bong.value 2 = T.transformed.toBONG.value 2
    rw [← replacement.bong.quadratic_ambientVector,
      ← T.transformed.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector 2) =
      q.quadratic (T.transformed.toBONG.ambientVector 2 : V)
    exact congrArg q.quadratic (replacement.inside_eq (2 : Fin 3))
  have hfourth : transformed.valueUnit (3 : Fin (N + 4)) =
      d.valueUnit (3 : Fin (N + 4)) := by
    apply Units.ext
    change replacement.bong.value 3 = d.toBONG.value 3
    rw [← replacement.bong.quadratic_ambientVector,
      ← d.toBONG.quadratic_ambientVector]
    exact congrArg q.quadratic
      (replacement.after_eq (3 : Fin (N + 4)) (by
        change 3 ≤ 3 % (N + 4)
        rw [Nat.mod_eq_of_lt (by omega : 3 < N + 4)]))
  have hlast : T.transformed.valueUnit (2 : Fin 3) =
      T.epsilon * s.valueUnit (2 : Fin 3) := by
    convert T.lastValue_eq using 1 <;> congr 1
  have hsegmentThird : s.valueUnit (2 : Fin 3) =
      d.valueUnit (2 : Fin (N + 4)) := by
    exact d.lemma814InitialThree_valueUnit_eq (2 : Fin 3)
  exact ⟨{
    epsilon := T.epsilon
    epsilon_isValuationUnit := T.epsilon_isValuationUnit
    epsilon_defect := T.epsilon_defect.trans <|
      congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) R.initialThreeSecondAlpha_eq
    transformed := transformed
    thirdValue_eq := hthirdLocal.trans <| hlast.trans <|
      congrArg (T.epsilon * ·) hsegmentThird
    fourthValue_eq := hfourth
  }⟩

namespace Beli2019Lemma814UnequalCorollary89ScalingData

variable {d : GoodBONG q L (N + 4)}

theorem thirdAdjacentProduct_eq
    (D : Beli2019Lemma814UnequalCorollary89ScalingData d) :
    D.transformed.adjacentProduct (2 : Fin (N + 3)) =
      D.epsilon * d.adjacentProduct (2 : Fin (N + 3)) := by
  unfold adjacentProduct
  change -(D.transformed.valueUnit (2 : Fin (N + 4)) *
        D.transformed.valueUnit (3 : Fin (N + 4))) =
    D.epsilon *
      (-(d.valueUnit (2 : Fin (N + 4)) * d.valueUnit (3 : Fin (N + 4))))
  have hthird := D.thirdValue_eq
  have hfourth := D.fourthValue_eq
  change D.transformed.valueUnit (2 : Fin (N + 4)) =
    D.epsilon * d.valueUnit (2 : Fin (N + 4)) at hthird
  change D.transformed.valueUnit (3 : Fin (N + 4)) =
    d.valueUnit (3 : Fin (N + 4)) at hfourth
  rw [hthird, hfourth]
  apply Units.ext
  simp only [Units.val_neg, Units.val_mul]
  ring

theorem secondAlpha_lt_thirdAdjacentDefect
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    (D : Beli2019Lemma814UnequalCorollary89ScalingData d)
    (hresidueTwo : ¬HasResidueFieldMoreThanTwoElements (K := K))
    (hold : d.adjacentDefect (2 : Fin (N + 3)) =
      (d.alphaValue (1 : Fin (N + 3)) : WithTop ℚ)) :
    (d.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) <
      D.transformed.adjacentDefect (2 : Fin (N + 3)) := by
  let x := d.adjacentProduct (2 : Fin (N + 3))
  have hx : defectOrder (K := K) x =
      (d.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) := by
    exact hold
  have heq : quadraticDefect K D.epsilon = quadraticDefect K x :=
    quadraticDefect_eq_of_defectOrder_eq D.epsilon x
      (D.epsilon_defect.trans hx.symm)
  have hfinite : quadraticDefect K D.epsilon ≠ ⊤ :=
    quadraticDefect_ne_top_of_defectOrder_eq_coe D.epsilon
      (d.alphaValue (1 : Fin (N + 3))) D.epsilon_defect
  have hstrictRaw := beli2019Lemma81_ii_strict hresidueTwo D.epsilon
    x heq hfinite
  have hstrict := defectOrder_lt_of_quadraticDefect_lt
    D.epsilon (D.epsilon * x) hstrictRaw
  unfold adjacentDefect
  rw [D.thirdAdjacentProduct_eq]
  exact D.epsilon_defect ▸ hstrict

end Beli2019Lemma814UnequalCorollary89ScalingData

theorem beli2019Lemma814_higherRankUnequal_of_reducedExceptional
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a original : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (R : a.Beli2019Lemma814UnequalReducedExceptionalData b) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  let d := R.hardData.normalForm.transformed
  let E : a.Beli2019Lemma814UnequalBoundaryExceptionalData b := {
    hardData := R.hardData
    thirdAlpha_eq_halfGap := R.thirdAlpha_eq_halfGap
    thirdPairExceptional := R.thirdPairExceptional
  }
  have P : Beli2019Lemma814UnequalPairExceptionData d := by
    simpa only [E, d] using lemma814UnequalBoundary_pairExceptionData a b E
  rcases exists_lemma814UnequalCorollary89ScalingData a b R with ⟨D⟩
  let changed := D.transformed
  have hstrictAdjacent :
      (d.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) <
        changed.adjacentDefect (2 : Fin (N + 3)) :=
    D.secondAlpha_lt_thirdAdjacentDefect P.residueTwo
      P.thirdAdjacentDefect_eq_secondAlpha
  have horders := d.order_invariant changed
  have halphas := d.alpha_invariant changed
  have horder : changed.order (0 : Fin (N + 4)) =
      b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin (N + 4))]
    exact R.hardData.normalForm.firstOrder_eq
  have hstrictEndpoint :
      (changed.order (0 : Fin (N + 4)) : ℚ) +
          changed.alphaValue (0 : Fin (N + 3)) <
        (changed.order (1 : Fin (N + 4)) : ℚ) +
          changed.alphaValue (1 : Fin (N + 3)) := by
    rw [← horders (0 : Fin (N + 4)),
      ← halphas (0 : Fin (N + 3)),
      ← horders (1 : Fin (N + 4)),
      ← halphas (1 : Fin (N + 3))]
    exact R.hardData.normalForm.firstEndpoint_strict
  have hfirstBinary :=
    changed.firstBinaryAlpha_eq_alpha_of_firstEndpoint_strict hstrictEndpoint
  have hhalf : changed.AttainsHalfGap (2 : Fin (N + 3)) := by
    unfold AttainsHalfGap
    rw [← halphas (2 : Fin (N + 3)),
      ← d.halfGapValue_invariant (classificationV := classificationV)
        changed (2 : Fin (N + 3))]
    exact R.thirdAlpha_eq_halfGap
  have hthirdBinary : changed.adjacentBinaryAlpha (2 : Fin (N + 3)) =
      (changed.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) :=
    changed.adjacentBinaryAlpha_eq_alpha_of_attainsHalfGap
      (2 : Fin (N + 3)) hhalf
  have houter : changed.order (0 : Fin (N + 4)) <
      changed.order (2 : Fin (N + 4)) := by
    rw [← horders (0 : Fin (N + 4)),
      ← horders (2 : Fin (N + 4))]
    exact R.hardData.normalForm.outer_lt
  have hconditions := d.lemma813Conditions_changeTargetBONG
    (classificationV := classificationV)
    (classificationW := classificationW) changed b
      R.hardData.normalForm.firstOrder_eq R.hardData.normalForm.conditions
  have hinvariant := d.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) changed b
  have hnotExceptional : ¬changed.Beli2019Lemma814Exceptional b :=
    fun X ↦ R.hardData.normalForm.notExceptional (hinvariant.mpr X)
  let T : d.Beli2019Lemma814ThirdAdjacentNormalForm b := {
    transformed := changed
    firstOrder_eq := horder
    firstBinaryAlpha_eq := hfirstBinary
    thirdBinaryAlpha_eq := hthirdBinary
    outer_lt := houter
    firstEndpoint_strict := hstrictEndpoint
    conditions := hconditions
    notExceptional := hnotExceptional
  }
  by_cases hone : hilbertSymbol K (changed.lemma814Epsilon b)
      (changed.adjacentProduct (0 : Fin (N + 3))) = 1
  · rcases changed.beli2019Lemma814_binaryBranch b horder hconditions
        hfirstBinary hone with ⟨U⟩
    exact ⟨{
      transformed := U.transformed
      firstValue_eq := U.firstValue_eq
    }⟩
  · have hneg : hilbertSymbol K (changed.lemma814Epsilon b)
        (changed.adjacentProduct (0 : Fin (N + 3))) = -1 := by
      apply (hilbertSymbol_eq_neg_one_iff K _ _).2
      intro hnorm
      exact hone ((hilbertSymbol_eq_one_iff K _ _).2 hnorm)
    rcases changed.lemma814_outerCases_of_hilbert_neg_one b hconditions hneg with
      houterEq | hbound
    · exact (ne_of_lt houter houterEq).elim
    · by_cases hraw : defectOrder (K := K)
          ((-1) * changed.prefixProduct 3 * b.prefixProduct 1) ≤
        (changed.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)
      · exact changed.beli2019Lemma814_higherRankUnequal_of_raw_le_thirdAlpha
          (classificationV := classificationV)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV)
          (prefixChangeW := prefixChangeW)
          original b horder hconditions hfirstBinary hbound hraw
      · let H : d.Beli2019Lemma814UnequalHardData b := {
          normalForm := T
          hilbert_neg_one := hneg
          unequalOuterBound := hbound
          thirdAlpha_lt_rawDefect := lt_of_not_ge hraw
        }
        by_cases hpair :
          changed.lemma814UnequalThirdPair.Beli2019Lemma88Exceptional
        · let Echanged : d.Beli2019Lemma814UnequalBoundaryExceptionalData b := {
            hardData := H
            thirdAlpha_eq_halfGap := by
              dsimp only [H, T]
              exact hhalf
            thirdPairExceptional := by
              dsimp only [H, T]
              exact hpair
          }
          have Pchanged : Beli2019Lemma814UnequalPairExceptionData changed := by
            simpa only [Echanged, H, T] using
              lemma814UnequalBoundary_pairExceptionData d b Echanged
          have hadjacent := Pchanged.thirdAdjacentDefect_eq_secondAlpha
          rw [← halphas (1 : Fin (N + 3))] at hadjacent
          rw [hadjacent] at hstrictAdjacent
          exact (lt_irrefl _ hstrictAdjacent).elim
        · exact
            beli2019Lemma814_higherRankUnequal_boundary_of_thirdPair_notExceptional
              (classificationV := classificationV)
              (classificationW := classificationW)
              (prefixChangeV := prefixChangeV)
              (prefixChangeW := prefixChangeW)
              d original b H (by simpa only [H, T] using hpair)

theorem beli2019Lemma814_higherRankUnequal_of_boundaryExceptional
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a original : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (E : a.Beli2019Lemma814UnequalBoundaryExceptionalData b) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  rcases lemma814UnequalBoundary_reduceII_dispatch
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      a original b E with hdone | hreduced
  · exact hdone
  · rcases hreduced with ⟨R⟩
    exact beli2019Lemma814_higherRankUnequal_of_reducedExceptional
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      E.hardData.normalForm.transformed original b R

theorem beli2019Lemma814_higherRankUnequal_of_hardData
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a original : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (H : a.Beli2019Lemma814UnequalHardData b) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  rcases lemma814UnequalHardData_dispatch
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      a original b H with hdone | hexceptional
  · exact hdone
  · rcases hexceptional with ⟨E⟩
    exact beli2019Lemma814_higherRankUnequal_of_boundaryExceptional
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      a original b E

/-- The complete `R₁ < R₃` branch of the higher-rank converse in Lemma
8.14.  Corollary 8.11 first normalizes the first adjacent pair and Corollary
8.10 restores reduction (II).  Positive Hilbert symbol and small raw-defect
subcases terminate immediately; the remaining normal form is discharged by
the exceptional-boundary argument above. -/
theorem beli2019Lemma814_higherRankUnequal
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a original : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 4)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (houter : a.order (0 : Fin (N + 4)) <
      a.order (2 : Fin (N + 4))) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases a.beli2019Corollary811 (0 : Fin (N + 3)) with ⟨C⟩
  let c := C.transformed
  have hordersAC := a.order_invariant c
  have hbinaryC : c.firstBinaryAlpha =
      (c.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := by
    simpa only [c, adjacentBinaryAlpha_zero] using C.adjacentBinaryAlpha_eq
  have horderC : c.order (0 : Fin (N + 4)) = b.order (0 : Fin 1) := by
    rw [← hordersAC (0 : Fin (N + 4))]
    exact horder
  have hconditionsC := a.lemma813Conditions_changeTargetBONG
    (classificationV := classificationV)
    (classificationW := classificationW) c b horder conditions
  have hinvariantAC := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) c b
  have hnotC : ¬c.Beli2019Lemma814Exceptional b :=
    fun X ↦ hnotExceptional (hinvariantAC.mpr X)
  have houterC : c.order (0 : Fin (N + 4)) <
      c.order (2 : Fin (N + 4)) := by
    rw [← hordersAC (0 : Fin (N + 4)),
      ← hordersAC (2 : Fin (N + 4))]
    exact houter
  rcases c.exists_lemma814SecondNormalForm
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      b horderC hconditionsC hbinaryC hnotC with ⟨S⟩
  let d := S.transformed
  have hordersCD := c.order_invariant d
  have houterD : d.order (0 : Fin (N + 4)) <
      d.order (2 : Fin (N + 4)) := by
    rw [← hordersCD (0 : Fin (N + 4)),
      ← hordersCD (2 : Fin (N + 4))]
    exact houterC
  by_cases hone : hilbertSymbol K (d.lemma814Epsilon b)
      (d.adjacentProduct (0 : Fin (N + 3))) = 1
  · rcases d.beli2019Lemma814_binaryBranch b S.firstOrder_eq S.conditions
        S.firstBinaryAlpha_eq hone with ⟨T⟩
    exact ⟨{
      transformed := T.transformed
      firstValue_eq := T.firstValue_eq
    }⟩
  · have hneg : hilbertSymbol K (d.lemma814Epsilon b)
        (d.adjacentProduct (0 : Fin (N + 3))) = -1 := by
      apply (hilbertSymbol_eq_neg_one_iff K _ _).2
      intro hnorm
      exact hone ((hilbertSymbol_eq_one_iff K _ _).2 hnorm)
    rcases d.lemma814_outerCases_of_hilbert_neg_one b S.conditions hneg with
      houterEq | hbound
    · exact (ne_of_lt houterD houterEq).elim
    · by_cases hraw : defectOrder (K := K)
          ((-1) * d.prefixProduct 3 * b.prefixProduct 1) ≤
        (d.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)
      · exact d.beli2019Lemma814_higherRankUnequal_of_raw_le_thirdAlpha
          (classificationV := classificationV)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV)
          (prefixChangeW := prefixChangeW)
          original b S.firstOrder_eq S.conditions S.firstBinaryAlpha_eq
            hbound hraw
      · have hrawStrict :
            (d.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) <
              defectOrder (K := K)
                ((-1) * d.prefixProduct 3 * b.prefixProduct 1) :=
          lt_of_not_ge hraw
        rcases d.exists_lemma814ThirdAdjacentNormalForm
            (classificationV := classificationV)
            (classificationW := classificationW)
            (prefixChangeV := prefixChangeV)
            (prefixChangeW := prefixChangeW)
            b S.firstOrder_eq S.conditions S.notExceptional
              S.initialThreeFirstAlpha_eq S.initialThreeSecondAlpha_eq
              houterD hrawStrict with ⟨U⟩
        rcases lemma814ThirdAdjacentNormalForm_dispatch
            (classificationV := classificationV)
            (classificationW := classificationW)
            (prefixChangeV := prefixChangeV)
            (prefixChangeW := prefixChangeW)
            d original b U with hdone | hhard
        · exact hdone
        · rcases hhard with ⟨H⟩
          exact beli2019Lemma814_higherRankUnequal_of_hardData
            (classificationV := classificationV)
            (classificationW := classificationW)
            (prefixChangeV := prefixChangeV)
            (prefixChangeW := prefixChangeW)
            d original b H

end BONG.GoodBONG
end Bong
