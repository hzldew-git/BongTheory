/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Corollary311
import Bong.Bong.Beli2019Lemma91Transitivity
import Bong.Bong.Beli2019Lemma93Monotonicity
import Bong.Bong.Beli2019Lemma93TailOrder

/-!
# Beli (2019), Lemma 9.3: normalization of the two selected BONGs

In the ordinary branch, Lemma 9.1 first prescribes the target head.  Lemma
9.2 is then applied independently on both lattices.  This file packages that
composition and transports the four representation conditions to the selected
BONGs by Corollary 3.11.
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

/-- The early alternative of Lemma 9.2 depends only on the invariant order
sequence, hence is unchanged by replacing a good BONG on the same lattice. -/
theorem lemma92EarlyAlternative_iff
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    (a c : GoodBONG q L (N + 4)) :
    a.Lemma92EarlyAlternative ↔ c.Lemma92EarlyAlternative := by
  have horders := a.order_invariant c
  unfold Lemma92EarlyAlternative orderGap
  rw [horders (0 : Fin (N + 4)), horders (1 : Fin (N + 4)),
    horders (2 : Fin (N + 4)), horders (3 : Fin (N + 4)),
    horders ((0 : Fin (N + 3)).succ),
    horders ((0 : Fin (N + 3)).castSucc)]

/-- The normalized pair used by the ordinary branch of Lemma 9.3. -/
structure Beli2019Lemma93NormalizedPair
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4)) where
  sourceBeforeLemma92 : GoodBONG r M (N + 4)
  targetBeforeLemma92 : GoodBONG q L (N + 4)
  targetFirstValue_eq :
    targetBeforeLemma92.valueUnit (0 : Fin (N + 4)) =
      sourceBeforeLemma92.valueUnit (0 : Fin (N + 4))
  targetTransform : Beli2019Lemma92Transform targetBeforeLemma92
  sourceTransform : Beli2019Lemma92Transform sourceBeforeLemma92
  selectedConditions :
    RepresentationConditions targetTransform.transformed
      sourceTransform.transformed (Nat.le_refl (N + 3))
  headValue_eq :
    targetTransform.transformed.value 0 = sourceTransform.transformed.value 0
  secondOrder_le :
    targetTransform.transformed.order ⟨1, by omega⟩ ≤
      sourceTransform.transformed.order ⟨1, by omega⟩

/-- Assemble the normalized pair from the two explicit Lemma 9.2 transforms.
The new second-order inequality is derived from condition (i), not stored as
an additional arithmetic assumption. -/
noncomputable def Beli2019Lemma93NormalizedPair.ofTransforms
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (c : GoodBONG q L (N + 4))
    (d : GoodBONG r M (N + 4))
    (hcFirst : c.valueUnit (0 : Fin (N + 4)) =
      d.valueUnit (0 : Fin (N + 4)))
    (Ta : Beli2019Lemma92Transform c)
    (Tb : Beli2019Lemma92Transform d) :
    Beli2019Lemma93NormalizedPair a b := by
  have selectedConditions :
      RepresentationConditions Ta.transformed Tb.transformed
        (Nat.le_refl (N + 3)) :=
    (a.representationConditions_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      Ta.transformed b Tb.transformed (Nat.le_refl (N + 3))).mp conditions
  have hheadUnit : Ta.transformed.valueUnit (0 : Fin (N + 4)) =
      Tb.transformed.valueUnit (0 : Fin (N + 4)) :=
    Ta.firstValue_eq.trans (hcFirst.trans Tb.firstValue_eq.symm)
  have hhead : Ta.transformed.value 0 = Tb.transformed.value 0 := by
    simpa only [coe_valueUnit] using congrArg Units.val hheadUnit
  have hfirstOrder : Ta.transformed.order (0 : Fin (N + 4)) =
      Tb.transformed.order (0 : Fin (N + 4)) := by
    unfold GoodBONG.order
    rw [Ta.transformed.toBONG.order_eq_ordUnit,
      Tb.transformed.toBONG.order_eq_ordUnit]
    simpa only [GoodBONG.valueUnit] using
      congrArg (ordUnit K) hheadUnit
  exact
    { sourceBeforeLemma92 := d
      targetBeforeLemma92 := c
      targetFirstValue_eq := hcFirst
      targetTransform := Ta
      sourceTransform := Tb
      selectedConditions := selectedConditions
      headValue_eq := hhead
      secondOrder_le :=
        Ta.transformed.secondOrder_le_of_firstOrder_eq Tb.transformed
          selectedConditions.orderCondition hfirstOrder }

/-- Assemble the ordinary normalization after the source BONG has already
been selected.  This ordering is needed in Case 1 of Lemma 9.3: Corollary
8.11 first changes the source, and only then Lemma 9.1 prescribes the target
head to equal the newly selected source head. -/
theorem exists_beli2019Lemma93NormalizedPair_of_selectedSource
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [targetParity : Beli2009AlphaParityLaws.{u, v} K]
    [targetLocalization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [targetConstruction : BeliLemma43ConstructionLaws.{u, v} K]
    [targetSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [targetBinaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [targetQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [targetLemma49 : BeliLemma49Laws.{u, v} K]
    [targetLemma47 : BeliLemma47Laws.{u, v} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFiveW : Beli2019SectionFiveLaws.{u, w} K]
    [sectionFourW : Beli2019SectionFourLaws.{u, w} K]
    [sectionFourV : Beli2019SectionFourLaws.{u, v} K]
    [deepWW : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K]
    (a : GoodBONG q L (N + 4)) (b d : GoodBONG r M (N + 4))
    (hfirst : a.order (0 : Fin (N + 4)) =
      d.order (0 : Fin (N + 4)))
    (ambient : q.Represents r)
    (rootConditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (selectedConditions :
      RepresentationConditions a d (Nat.le_refl (N + 3)))
    (hcase : a.Lemma91Alternative d)
    (Tb : Beli2019Lemma92Transform d) :
    Nonempty (Beli2019Lemma93NormalizedPair a b) := by
  rcases a.beli2019Lemma91_sameRank
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (targetParity := targetParity)
      (targetLocalization := targetLocalization)
      (targetConstruction := targetConstruction)
      (targetSectionTwo := targetSectionTwo)
      (targetBinaryScaling := targetBinaryScaling)
      (targetQuaternaryScaling := targetQuaternaryScaling)
      (targetLemma49 := targetLemma49) (targetLemma47 := targetLemma47)
      (structuralV := structuralV) (structuralW := structuralW)
      (classificationV := classificationV) (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      (sectionFiveW := sectionFiveW)
      (sectionFourW := sectionFourW) (sectionFourV := sectionFourV)
      (deepWW := deepWW)
      d hfirst ambient selectedConditions hcase with ⟨D⟩
  have hTa : Nonempty (Beli2019Lemma92Transform D.transformed) := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    letI : Beli2009AlphaParityLaws.{u, v} K := targetParity
    letI : Beli2009AlphaLocalizationLaws.{u, v} K := targetLocalization
    letI : BeliLemma43ConstructionLaws.{u, v} K := targetConstruction
    letI : Beli2006SectionTwoLaws.{u, v} K := targetSectionTwo
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    letI : DyadicBinaryFirstScalingLaws.{u, v} K := targetBinaryScaling
    letI : DyadicQuaternaryFirstScalingLaws.{u, v} K :=
      targetQuaternaryScaling
    letI : BeliLemma49Laws.{u, v} K := targetLemma49
    letI : BeliLemma47Laws.{u, v} K := targetLemma47
    exact D.transformed.beli2019Lemma92
  rcases hTa with ⟨Ta⟩
  refine ⟨Beli2019Lemma93NormalizedPair.ofTransforms
    (classificationV := classificationV) (classificationW := classificationW)
    a b rootConditions D.transformed d ?_ Ta Tb⟩
  exact D.firstValue_eq.trans d.firstUnarySegment_valueUnit_zero

/-- Lemmas 9.1 and 9.2 produce the normalized pair in the ordinary branch of
Lemma 9.3. -/
theorem exists_beli2019Lemma93NormalizedPair_of_lemma91Alternative
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [targetParity : Beli2009AlphaParityLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [targetLocalization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [targetConstruction : BeliLemma43ConstructionLaws.{u, v} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [targetSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [targetBinaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [targetQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [targetLemma49 : BeliLemma49Laws.{u, v} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [targetLemma47 : BeliLemma47Laws.{u, v} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFiveW : Beli2019SectionFiveLaws.{u, w} K]
    [sectionFourW : Beli2019SectionFourLaws.{u, w} K]
    [sectionFourV : Beli2019SectionFourLaws.{u, v} K]
    [deepWW : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hfirst : a.order (0 : Fin (N + 4)) =
      b.order (0 : Fin (N + 4)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (hcase : a.Lemma91Alternative b) :
    Nonempty (Beli2019Lemma93NormalizedPair a b) := by
  rcases a.beli2019Lemma91_sameRank
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (targetParity := targetParity)
      (targetLocalization := targetLocalization)
      (targetConstruction := targetConstruction)
      (targetSectionTwo := targetSectionTwo)
      (targetBinaryScaling := targetBinaryScaling)
      (targetQuaternaryScaling := targetQuaternaryScaling)
      (targetLemma49 := targetLemma49) (targetLemma47 := targetLemma47)
      (structuralV := structuralV) (structuralW := structuralW)
      (classificationV := classificationV) (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      (sectionFiveW := sectionFiveW)
      (sectionFourW := sectionFourW) (sectionFourV := sectionFourV)
      (deepWW := deepWW)
      b hfirst ambient conditions hcase with ⟨D⟩
  have hTa : Nonempty (Beli2019Lemma92Transform D.transformed) := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    letI : Beli2009AlphaParityLaws.{u, v} K := targetParity
    letI : Beli2009AlphaLocalizationLaws.{u, v} K := targetLocalization
    letI : BeliLemma43ConstructionLaws.{u, v} K := targetConstruction
    letI : Beli2006SectionTwoLaws.{u, v} K := targetSectionTwo
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    letI : DyadicBinaryFirstScalingLaws.{u, v} K := targetBinaryScaling
    letI : DyadicQuaternaryFirstScalingLaws.{u, v} K :=
      targetQuaternaryScaling
    letI : BeliLemma49Laws.{u, v} K := targetLemma49
    letI : BeliLemma47Laws.{u, v} K := targetLemma47
    exact D.transformed.beli2019Lemma92
  rcases hTa with ⟨Ta⟩
  have hTb : Nonempty (Beli2019Lemma92Transform b) := by
    letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
    letI : Beli2009AlphaParityLaws.{u, w} K := sourceParity
    letI : Beli2009AlphaLocalizationLaws.{u, w} K := sourceLocalization
    letI : BeliLemma43ConstructionLaws.{u, w} K := sourceConstruction
    letI : Beli2006SectionTwoLaws.{u, w} K := sourceSectionTwo
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    letI : DyadicBinaryFirstScalingLaws.{u, w} K := sourceBinaryScaling
    letI : DyadicQuaternaryFirstScalingLaws.{u, w} K :=
      sourceQuaternaryScaling
    letI : BeliLemma49Laws.{u, w} K := sourceLemma49
    letI : BeliLemma47Laws.{u, w} K := sourceLemma47
    exact b.beli2019Lemma92
  rcases hTb with ⟨Tb⟩
  refine ⟨Beli2019Lemma93NormalizedPair.ofTransforms
    (classificationV := classificationV) (classificationW := classificationW)
    a b conditions D.transformed b ?_ Ta Tb⟩
  exact D.firstValue_eq.trans b.firstUnarySegment_valueUnit_zero

end BONG.GoodBONG

end Bong
