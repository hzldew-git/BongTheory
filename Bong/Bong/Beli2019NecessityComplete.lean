/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019RankCompletion
import Bong.Bong.GoodBONGSameRankIntegralImage

/-!
# Beli (2019), necessity after rank completion

Sections 4--6 and Lemmas 2.20--2.21 prove the necessity direction of
Theorem 2.1.  It lives below the final sufficiency theorem so that later
Section 9 arguments may use necessity for a represented prefix without
depending circularly on the theorem they are helping to prove.
-/

namespace Bong

open Dyadic

universe u v w

/-- Sections 4--6 and the rank-completion lemmas prove necessity. -/
theorem beli2019_necessity
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [BONGStructuralLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [HilbertSymbolLaws K] [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [Beli2019SectionFiveLaws.{u, v} K]
    [Beli2019SectionFourLaws.{u, v} K]
    [GoodBONGDeepIntegralExtensionLaws.{u, v, w} K]
    (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (hRank : n ≤ m) (representation : Lattice.Represents q r L M) :
    RepresentationConditions a b hRank := by
  rcases representation with ⟨f⟩
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  by_cases hEqual : n = m
  · subst m
    rcases exists_goodBONGSameRankIntegralImageData a b f with ⟨D⟩
    have himage := a.representationConditions_of_lattice_le
      D.imageBONG D.image_le
    have himagePrime := RepresentationConditions.toPrime
      (sourceLaws := sourceLaws) (targetLaws := sourceLaws) himage
    have hprime := a.representationConditionsPrime_of_scalarAgreement
      D.scalarAgreement himagePrime
    have htrigger := a.beli2019Lemma216
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b hRank hprime.orderCondition hprime.defectCondition
    exact (representationConditions_iff_prime a b hRank htrigger).mpr hprime
  · have hStrict : n < m := hRank.lt_of_ne hEqual
    rcases GoodBONGDeepIntegralExtensionLaws.extension a b hStrict f
      (a.rankCompletionOrderBound (n := n))
      (a.rankCompletionAlphaBound b) with ⟨D⟩
    have hcompleted := a.representationConditions_of_lattice_le
      D.completedBONG D.completed_le
    have hcompletedPrime := RepresentationConditions.toPrime
      (sourceLaws := sourceLaws) (targetLaws := sourceLaws) hcompleted
    have hprime := a.representationConditionsPrime_of_prefixAgreement
      (alphaV := sourceLaws) (alphaW := targetLaws)
      D.prefixAgreement hStrict D.boundaryOrder D.boundaryAlpha
      hcompletedPrime
    have htrigger := a.beli2019Lemma216
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b hRank hprime.orderCondition hprime.defectCondition
    exact (representationConditions_iff_prime a b hRank htrigger).mpr hprime

end Bong
