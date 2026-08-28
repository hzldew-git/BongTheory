/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814Sufficiency

/-!
# Beli (2019), Lemma 8.14: reduction from higher rank to rank three

The rank-four and higher-rank parts of the proof repeatedly choose a good
BONG whose first ternary segment satisfies the rank-three hypotheses.  The
rank-three transformation is then inserted back into the ambient BONG by
Beli (2003), Lemma 4.9(ii).  This file isolates that common lifting step.
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

/-- A prescribed-first-value transformation of the first ternary segment
lifts to a prescribed-first-value transformation of the entire ambient
good BONG.  The output may be viewed as a transformation of any other good
BONG of the same lattice, because the conclusion only prescribes the first
value of the new BONG. -/
theorem prescribedFirstValueTransform_of_firstThreeSegment
    [BeliLemma49Laws.{u, v} K]
    (a original : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (T : (segment.toGoodBONG a.good).Beli2019PrescribedFirstValueTransform b) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  rcases a.toBONG.beliLemma49_ii a.good segment
      T.transformed.toBONG T.transformed.good with ⟨replacement⟩
  let transformed : GoodBONG q L (N + 3) :=
    ⟨replacement.bong, replacement.good⟩
  have hinside := replacement.inside_eq (0 : Fin 3)
  have hfirst : transformed.valueUnit (0 : Fin (N + 3)) =
      T.transformed.valueUnit (0 : Fin 3) := by
    apply Units.ext
    change replacement.bong.value 0 = T.transformed.toBONG.value 0
    rw [← replacement.bong.quadratic_ambientVector,
      ← T.transformed.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector 0) =
      q.quadratic (T.transformed.toBONG.ambientVector 0 : V)
    exact congrArg q.quadratic hinside
  exact ⟨{
    transformed := transformed
    firstValue_eq := hfirst.trans T.firstValue_eq
  }⟩

/-- The analogous lifting step for a quaternary initial segment.  After the
rank-four case is solved, this is the final embedding step for every target
of rank at least five. -/
theorem prescribedFirstValueTransform_of_firstFourSegment
    [BeliLemma49Laws.{u, v} K]
    (a original : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfour : 4 ≤ N + 3)
    (segment : BONG.SegmentWitness a.toBONG 0 4 hfour)
    (T : (segment.toGoodBONG a.good).Beli2019PrescribedFirstValueTransform b) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  rcases a.toBONG.beliLemma49_ii a.good segment
      T.transformed.toBONG T.transformed.good with ⟨replacement⟩
  let transformed : GoodBONG q L (N + 3) :=
    ⟨replacement.bong, replacement.good⟩
  have hinside := replacement.inside_eq (0 : Fin 4)
  have hfirst : transformed.valueUnit (0 : Fin (N + 3)) =
      T.transformed.valueUnit (0 : Fin 4) := by
    apply Units.ext
    change replacement.bong.value 0 = T.transformed.toBONG.value 0
    rw [← replacement.bong.quadratic_ambientVector,
      ← T.transformed.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector 0) =
      q.quadratic (T.transformed.toBONG.ambientVector 0 : V)
    exact congrArg q.quadratic hinside
  exact ⟨{
    transformed := transformed
    firstValue_eq := hfirst.trans T.firstValue_eq
  }⟩

/-- Once a chosen first ternary segment satisfies the explicit hypotheses
of Lemma 8.14 and avoids its ternary exceptional cases, the completed
rank-three theorem solves the ambient problem.  This is the common terminal
step in both the quaternary and the rank-at-least-five arguments. -/
theorem beli2019Lemma814_of_safeFirstThreeSegment
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
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a original : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (horder : (segment.toGoodBONG a.good).order (0 : Fin 3) =
      b.order (0 : Fin 1))
    (conditions : (segment.toGoodBONG a.good).Lemma813Conditions b)
    (hnotExceptional :
      ¬(segment.toGoodBONG a.good).Beli2019Lemma814Exceptional b) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  rcases (segment.toGoodBONG a.good).beli2019Lemma814_rankThree
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      b horder conditions hnotExceptional with ⟨T⟩
  exact a.prescribedFirstValueTransform_of_firstThreeSegment
    original b segment T

/-- Version of the preceding reduction in which the first-order equality is
transported automatically from the ambient BONG to its initial segment. -/
theorem beli2019Lemma814_of_safeFirstThreeSegment_of_ambientOrder
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
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a original : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (horder : a.order (0 : Fin (N + 3)) = b.order (0 : Fin 1))
    (conditions : (segment.toGoodBONG a.good).Lemma813Conditions b)
    (hnotExceptional :
      ¬(segment.toGoodBONG a.good).Beli2019Lemma814Exceptional b) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  have hsegmentOrder :
      (segment.toGoodBONG a.good).order (0 : Fin 3) =
        a.order (0 : Fin (N + 3)) := by
    change segment.bong.order 0 = a.toBONG.order 0
    simpa [BONG.SegmentWitness.sourceIndex] using
      segment.order_eq (0 : Fin 3)
  exact a.beli2019Lemma814_of_safeFirstThreeSegment
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW)
    original b segment (hsegmentOrder.trans horder)
      conditions hnotExceptional

/-- If the third alpha is its half-gap value, P1 gives the lower bound on
the fourth alpha used in the rank-at-least-five part of the proof:
`e - (R₄ - R₃) / 2 ≤ α₄`. -/
theorem lemma814ThirdComplementaryDefect_le_fourthAlpha
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3)
    (hthird : a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) =
      a.halfGapValue (⟨2, by omega⟩ : Fin (N + 2))) :
    a.lemma814ThirdComplementaryDefect (by omega) ≤
      a.alphaValue (⟨3, by omega⟩ : Fin (N + 2)) := by
  let third : Fin (N + 2) := ⟨2, by omega⟩
  let fourth : Fin (N + 2) := ⟨3, by omega⟩
  have hmono := a.alphaLeftEndpoint_monotone
    (show third ≤ fourth by
      change 2 ≤ 3
      omega)
  change a.alphaLeftEndpoint third ≤ a.alphaLeftEndpoint fourth at hmono
  unfold alphaLeftEndpoint at hmono
  have hthird' : a.alphaValue third = a.halfGapValue third := by
    simpa only [third] using hthird
  unfold halfGapValue orderGap at hthird'
  unfold lemma814ThirdComplementaryDefect
  change (ramificationIndex K : ℚ) -
      ((a.order third.succ - a.order third.castSucc : Int) : ℚ) / 2 ≤
    a.alphaValue fourth
  rw [hthird'] at hmono
  push_cast at hmono ⊢
  have hboundary : third.succ = fourth.castSucc := by
    apply Fin.ext
    rfl
  rw [hboundary] at hmono ⊢
  linarith

/-- Therefore, when the strict later-alpha inequality fails, the fourth
alpha is exactly the complementary third-gap value.  This is the equality
derived in the paper immediately after excluding ambient exception (c). -/
theorem fourthAlpha_eq_lemma814ThirdComplementaryDefect_of_not_strict
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (hfive : 5 ≤ N + 3)
    (hthird : a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) =
      a.halfGapValue (⟨2, by omega⟩ : Fin (N + 2)))
    (hnotStrict : ¬a.lemma814ThirdComplementaryDefect (by omega) <
      a.alphaValue (⟨3, by omega⟩ : Fin (N + 2))) :
    a.alphaValue (⟨3, by omega⟩ : Fin (N + 2)) =
      a.lemma814ThirdComplementaryDefect (by omega) := by
  apply le_antisymm (le_of_not_gt hnotStrict)
  exact a.lemma814ThirdComplementaryDefect_le_fourthAlpha hfive hthird

/-- In the quaternary boundary case of the proof, `R₁ = R₃`, `R₂ < R₄`,
and `α₂ + α₃ = 2e` force all three displayed alphas to be odd rational
integers.  If the last two were even, Lemma 2.7(iv) would put both at their
half-gap values, whose sum is strictly larger than `2e`. -/
theorem rankFour_firstThreeAlphas_odd_of_boundary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ)) :
    IsOddRationalInteger (a.alphaValue (0 : Fin 3)) ∧
      IsOddRationalInteger (a.alphaValue (1 : Fin 3)) ∧
        IsOddRationalInteger (a.alphaValue (2 : Fin 3)) := by
  have hremark := a.beli2019Remark87 (0 : Fin 2) houter
  have hgapOneEven : Even (a.orderGap (1 : Fin 3)) := by
    have hmod := hremark.middle_next_modEq
    rw [Int.modEq_iff_dvd] at hmod
    rcases hmod with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    change a.order (2 : Fin 4) - a.order (1 : Fin 4) = 2 * k at hk
    change a.order (2 : Fin 4) - a.order (1 : Fin 4) = k + k
    omega
  have hsecondInteger : IsRationalInteger (a.alphaValue (1 : Fin 3)) := by
    by_cases hhalf : a.alphaValue (1 : Fin 3) =
        a.halfGapValue (1 : Fin 3)
    · rw [hhalf]
      exact a.halfGapValue_isRationalInteger_of_even (1 : Fin 3) hgapOneEven
    · exact (a.beli2009Lemma27_iv (1 : Fin 3) hhalf).isRationalInteger
  rcases hsecondInteger with ⟨z, hz⟩
  have hthirdInteger : IsRationalInteger (a.alphaValue (2 : Fin 3)) := by
    refine ⟨2 * (ramificationIndex K : Int) - z, ?_⟩
    rw [hz] at hsum
    push_cast at hsum ⊢
    linarith
  rcases hthirdInteger with ⟨w, hw⟩
  have hzwSum : z + w = 2 * (ramificationIndex K : Int) := by
    rw [hz, hw] at hsum
    exact_mod_cast hsum
  have hzwMod : Int.ModEq 2 z w := by
    rw [Int.modEq_iff_dvd]
    refine ⟨(ramificationIndex K : Int) - z, ?_⟩
    omega
  have hsecondOdd : IsOddRationalInteger
      (a.alphaValue (1 : Fin 3)) := by
    by_contra hnotOdd
    have hzNotOdd : ¬Odd z := by
      intro hzOdd
      exact hnotOdd ⟨z, hzOdd, hz⟩
    have hzEven : Even z := Int.not_odd_iff_even.mp hzNotOdd
    have hwEven : Even w := by
      rw [Int.modEq_iff_dvd] at hzwMod
      rcases hzwMod with ⟨k, hk⟩
      rcases hzEven with ⟨d, hd⟩
      refine ⟨d + k, ?_⟩
      omega
    have hthirdNotOdd : ¬IsOddRationalInteger
        (a.alphaValue (2 : Fin 3)) := by
      rintro ⟨w', hw'Odd, hw'⟩
      have hww' : w = w' := by
        exact_mod_cast hw.symm.trans hw'
      subst w'
      exact (Int.not_odd_iff_even.mpr hwEven) hw'Odd
    have hsecondHalf : a.alphaValue (1 : Fin 3) =
        a.halfGapValue (1 : Fin 3) := by
      by_contra hne
      exact hnotOdd (a.beli2009Lemma27_iv (1 : Fin 3) hne)
    have hthirdHalf : a.alphaValue (2 : Fin 3) =
        a.halfGapValue (2 : Fin 3) := by
      by_contra hne
      exact hthirdNotOdd (a.beli2009Lemma27_iv (2 : Fin 3) hne)
    rw [hsecondHalf, hthirdHalf] at hsum
    unfold halfGapValue orderGap at hsum
    push_cast at hsum
    have hsecondFourthQ :
        (a.order (1 : Fin 4) : ℚ) < a.order (3 : Fin 4) := by
      exact_mod_cast hsecondFourth
    linarith
  have hthirdOdd : IsOddRationalInteger
      (a.alphaValue (2 : Fin 3)) := by
    rcases hsecondOdd with ⟨z', hz'Odd, hz'⟩
    have hzz' : z = z' := by
      exact_mod_cast hz.symm.trans hz'
    subst z'
    refine ⟨w, ?_, hw⟩
    rw [Int.modEq_iff_dvd] at hzwMod
    rcases hzwMod with ⟨k, hk⟩
    rcases hz'Odd with ⟨d, hd⟩
    exact ⟨d + k, by omega⟩
  have hfirstOdd : IsOddRationalInteger
      (a.alphaValue (0 : Fin 3)) := by
    rcases hsecondOdd with ⟨z', hz'Odd, hz'⟩
    have horderMod := hremark.previous_middle_modEq
    rw [Int.modEq_iff_dvd] at horderMod
    rcases horderMod with ⟨k, hk⟩
    have hk' : a.order (1 : Fin 4) - a.order (0 : Fin 4) = 2 * k := by
      change a.order (1 : Fin 4) - a.order (0 : Fin 4) = 2 * k at hk
      exact hk
    refine ⟨z' + 2 * k, ?_, ?_⟩
    · rcases hz'Odd with ⟨d, hd⟩
      exact ⟨d + k, by omega⟩
    · have hrelation := hremark.currentAlpha_eq
      change a.alphaValue (1 : Fin 3) =
          ((a.order (0 : Fin 4) - a.order (1 : Fin 4) : Int) : ℚ) +
            a.alphaValue (0 : Fin 3) at hrelation
      rw [hz'] at hrelation
      have hkQ : (a.order (1 : Fin 4) : ℚ) - a.order (0 : Fin 4) =
          2 * (k : ℚ) := by
        exact_mod_cast hk'
      push_cast at hrelation ⊢
      linarith
  exact ⟨hfirstOdd, hsecondOdd, hthirdOdd⟩

/-- The oddness conclusion in the boundary case, together with the strict
`2e` bounds stated in the paper. -/
structure Beli2019Lemma814RankFourBoundaryAlphaData
    (a : GoodBONG q L 4) : Prop where
  first_odd : IsOddRationalInteger (a.alphaValue (0 : Fin 3))
  second_odd : IsOddRationalInteger (a.alphaValue (1 : Fin 3))
  third_odd : IsOddRationalInteger (a.alphaValue (2 : Fin 3))
  first_lt_twoE : a.alphaValue (0 : Fin 3) <
    2 * (ramificationIndex K : ℚ)
  second_lt_twoE : a.alphaValue (1 : Fin 3) <
    2 * (ramificationIndex K : ℚ)
  third_lt_twoE : a.alphaValue (2 : Fin 3) <
    2 * (ramificationIndex K : ℚ)

private theorem oddRationalInteger_pos_of_nonneg {x : ℚ}
    (hodd : IsOddRationalInteger x) (hnonnegative : 0 ≤ x) : 0 < x := by
  rcases hodd with ⟨z, ⟨d, hd⟩, hz⟩
  rw [hz] at hnonnegative ⊢
  have hzNonnegative : 0 ≤ z := by exact_mod_cast hnonnegative
  have hzPositive : 0 < z := by omega
  exact_mod_cast hzPositive

/-- Full alpha-arithmetic package for the quaternary equality branch. -/
theorem rankFour_boundaryAlphaData
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ)) :
    a.Beli2019Lemma814RankFourBoundaryAlphaData := by
  rcases a.rankFour_firstThreeAlphas_odd_of_boundary
      houter hsecondFourth hsum with ⟨hfirstOdd, hsecondOdd, hthirdOdd⟩
  have hfirstNonnegative := (a.beli2009Lemma27_i (0 : Fin 3)).1
  have hsecondNonnegative := (a.beli2009Lemma27_i (1 : Fin 3)).1
  have hthirdNonnegative := (a.beli2009Lemma27_i (2 : Fin 3)).1
  have hfirstPositive := oddRationalInteger_pos_of_nonneg
    hfirstOdd hfirstNonnegative
  have hsecondPositive := oddRationalInteger_pos_of_nonneg
    hsecondOdd hsecondNonnegative
  have hthirdPositive := oddRationalInteger_pos_of_nonneg
    hthirdOdd hthirdNonnegative
  have hremark := a.beli2019Remark87 (0 : Fin 2) houter
  have hfirstSecond : a.alphaValue (0 : Fin 3) +
      a.alphaValue (1 : Fin 3) ≤ 2 * (ramificationIndex K : ℚ) := by
    have h := hremark.alphaSum_le_twoE
    change a.alphaValue (0 : Fin 3) + a.alphaValue (1 : Fin 3) ≤
      2 * (ramificationIndex K : ℚ) at h
    exact h
  exact {
    first_odd := hfirstOdd
    second_odd := hsecondOdd
    third_odd := hthirdOdd
    first_lt_twoE := by linarith
    second_lt_twoE := by linarith
    third_lt_twoE := by linarith
  }

/-- Consequently the three boundary alphas all occur as defects of
valuation units, exactly the assertion `α₁, α₂, α₃ ∈ d(𝒪ˣ)` used in the
next choices of the quaternary proof. -/
theorem rankFour_boundaryAlphas_areValuationUnitDefects
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [DyadicUnitDefectSpectrumLaws K]
    (a : GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ)) :
    IsValuationUnitDefect (K := K) (a.alphaValue (0 : Fin 3)) ∧
      IsValuationUnitDefect (K := K) (a.alphaValue (1 : Fin 3)) ∧
        IsValuationUnitDefect (K := K) (a.alphaValue (2 : Fin 3)) := by
  have D := a.rankFour_boundaryAlphaData houter hsecondFourth hsum
  have hfirstNonnegative := (a.beli2009Lemma27_i (0 : Fin 3)).1
  have hsecondNonnegative := (a.beli2009Lemma27_i (1 : Fin 3)).1
  have hthirdNonnegative := (a.beli2009Lemma27_i (2 : Fin 3)).1
  exact ⟨
    DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      _ D.first_odd hfirstNonnegative D.first_lt_twoE,
    DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      _ D.second_odd hsecondNonnegative D.second_lt_twoE,
    DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      _ D.third_odd hthirdNonnegative D.third_lt_twoE
  ⟩

end BONG.GoodBONG

end Bong
