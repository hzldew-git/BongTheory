/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814HigherRankUnequalExceptional

/-!
# Beli (2019), Lemma 8.14

This file assembles the rank-three, rank-four, and higher-rank proofs into
the complete explicit form of Lemma 8.14.  In rank four, the missing doubly
alternating order case is a direct application of Lemma 8.3.  In rank at
least five, good-BONG two-step monotonicity splits the proof into the
completed equal- and unequal-outer branches.
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

/-- In rank four, equality of both two-step order pairs gives the alternating
order pattern required by Lemma 8.3, which directly installs the prescribed
first value. -/
theorem beli2019Lemma814_rankFour_alternating
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    (a original : GoodBONG q L 4) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) = a.order (3 : Fin 4)) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  have halternating : a.HasQuaternaryAlternatingOrders :=
    ⟨houter, hsecondFourth⟩
  let epsilon := a.lemma814Epsilon b
  have hepsilonUnit : IsValuationUnit K (epsilon : K) :=
    a.lemma814Epsilon_isValuationUnit b horder
  have hepsilonDefect : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) epsilon :=
    a.alpha_le_lemma814EpsilonDefect b conditions
  rcases a.beli2019Lemma83 halternating epsilon hepsilonUnit
      hepsilonDefect with ⟨c, hc⟩
  have hfirst : c.valueUnit (0 : Fin 4) = b.valueUnit (0 : Fin 1) := by
    calc
      c.valueUnit (0 : Fin 4) = epsilon * a.valueUnit (0 : Fin 4) := hc
      _ = b.valueUnit (0 : Fin 1) := a.lemma814Epsilon_mul_firstValue b
  exact ⟨{
    transformed := c
    firstValue_eq := hfirst
  }⟩

/-- Complete rank-four sufficiency, including the unequal outer branch, the
strict second-fourth branch, and the doubly alternating endpoint. -/
theorem beli2019Lemma814_rankFour_complete
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
    [DyadicTernaryRepresentationObstructionLaws K]
    (a original : GoodBONG q L 4) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  have houterLe : a.order (0 : Fin 4) ≤ a.order (2 : Fin 4) :=
    a.good (0 : Fin 4) (by omega)
  rcases lt_or_eq_of_le houterLe with houter | houter
  · exact a.beli2019Lemma814_higherRankUnequal
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b horder conditions hnotExceptional houter
  · have hsecondLe : a.order (1 : Fin 4) ≤ a.order (3 : Fin 4) :=
      a.good (1 : Fin 4) (by omega)
    rcases lt_or_eq_of_le hsecondLe with hsecond | hsecond
    · exact a.beli2019Lemma814_rankFour
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV)
        (prefixChangeW := prefixChangeW)
        original b horder conditions hnotExceptional houter hsecond
    · exact beli2019Lemma814_rankFour_alternating a original b horder conditions
        houter hsecond

/-- Complete sufficiency in every rank at least five. -/
theorem beli2019Lemma814_higherRank_complete
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
    [DyadicTernaryRepresentationObstructionLaws K]
    (a original : GoodBONG q L (N + 5)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 5)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  have houterLe : a.order (0 : Fin (N + 5)) ≤
      a.order (2 : Fin (N + 5)) := by
    have hgood := a.good (⟨0, by omega⟩ : Fin (N + 5))
      (by change 0 + 2 < N + 5; omega)
    change a.order (0 : Fin (N + 5)) ≤ a.order (2 : Fin (N + 5)) at hgood
    exact hgood
  rcases lt_or_eq_of_le houterLe with houter | houter
  · exact a.beli2019Lemma814_higherRankUnequal
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b horder conditions hnotExceptional houter
  · exact a.beli2019Lemma814_higherRank_equalOuter
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b horder conditions hnotExceptional houter

/-- Beli (2019), Lemma 8.14 in its noncircular explicit form, for every
target rank at least three. -/
theorem beli2019Lemma814Explicit
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
    [DyadicTernaryRepresentationObstructionLaws K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) :
    a.Beli2019Lemma814ExplicitStatement b := by
  intro horder conditions
  constructor
  · exact a.beli2019Lemma814_necessity
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW) b
  · intro hnotExceptional
    cases N with
    | zero =>
        exact a.beli2019Lemma814_rankThree
          (classificationV := classificationV)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV)
          (prefixChangeW := prefixChangeW)
          b horder conditions hnotExceptional
    | succ N =>
        cases N with
        | zero =>
            exact beli2019Lemma814_rankFour_complete
              (classificationV := classificationV)
              (classificationW := classificationW)
              (prefixChangeV := prefixChangeV)
              (prefixChangeW := prefixChangeW)
              a a b horder conditions hnotExceptional
        | succ N =>
            exact beli2019Lemma814_higherRank_complete
              (classificationV := classificationV)
              (classificationW := classificationW)
              (prefixChangeV := prefixChangeV)
              (prefixChangeW := prefixChangeW)
              a a b horder conditions hnotExceptional
end BONG.GoodBONG
end Bong
