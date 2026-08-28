/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma92RankFiveReduction
import Bong.Bong.Beli2019Lemma92LocalToGlobal

/-!
# Beli (2019), Lemma 9.2

This file assembles the two low-rank constructions and the propagation
argument into the complete statement of Lemma 9.2.  In ranks at least five,
the paper's early alternative is solved on the initial quaternary segment;
its complement is solved on the initial rank-five segment.  The segment is
then inserted back into the original good BONG and the base alpha equality
is propagated through the remaining coefficients.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- Lemma 9.2 for every rank at least five.  The first four coefficients
handle the early branch and the first five coefficients handle its
complement. -/
theorem beli2019Lemma92_rankAtLeastFive
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
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L (N + 5)) :
    Nonempty (Beli2019Lemma92Transform a) := by
  by_cases hearly : a.Lemma92EarlyAlternative
  · rcases a.lemma92InitialFour.beli2019Lemma92_rankFour with ⟨T⟩
    exact a.exists_lemma92Transform_of_initialFourTransform T
      (a.lemma92InitialFour_earlyAlternative_iff.mpr hearly)
  · have hlocalNotEarly :
        ¬a.lemma92InitialFive.Lemma92EarlyAlternative := by
      intro hlocal
      exact hearly (a.lemma92InitialFive_earlyAlternative_iff.mp hlocal)
    rcases a.lemma92InitialFive.beli2019Lemma92_rankFive_of_notEarly
        hlocalNotEarly with ⟨T⟩
    exact a.exists_lemma92Transform_of_initialFiveTransform T hearly

/-- Beli (2019), Lemma 9.2, for every rank `n ≥ 4` represented as
`n = N + 4`. -/
theorem beli2019Lemma92
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
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L (N + 4)) :
    Nonempty (Beli2019Lemma92Transform a) := by
  cases N with
  | zero =>
      exact a.beli2019Lemma92_rankFour
  | succ N =>
      exact a.beli2019Lemma92_rankAtLeastFive

end BONG.GoodBONG

end Bong
