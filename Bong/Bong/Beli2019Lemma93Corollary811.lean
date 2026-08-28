/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Corollary811
import Bong.Bong.Beli2019Lemma92Propagation
import Bong.Bong.Beli2019Lemma93LowBounds

/-!
# Beli (2019), Lemma 9.3: the Corollary 8.11 normalization

In the first ordinary branch of the paper, Corollary 8.11 is applied to the
second and third source vectors.  Once the global alpha at that boundary is
realized by the literal binary segment, deleting the first vector preserves
the alpha there.  The propagation result from Lemma 9.2 then gives the same
identity at every later boundary.
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

/-- If the alpha at the second boundary is realized on the literal binary
segment, deleting the head preserves that alpha.  This is the local
inequality argument used immediately after Corollary 8.11 in Lemma 9.3. -/
theorem alphaValue_one_eq_tail_zero_of_adjacentBinaryAlpha_one
    (c : GoodBONG q L (N + 3))
    (hlocal :
      c.adjacentBinaryAlpha (1 : Fin (N + 2)) =
        (c.alphaValue (1 : Fin (N + 2)) : WithTop ℚ)) :
    c.alphaValue (1 : Fin (N + 2)) =
      c.tail.alphaValue (0 : Fin (N + 1)) := by
  have hshift := c.alpha_shift_le_tail (0 : Fin (N + 1))
  have hhalf := c.tail.alpha_le_halfGapCandidate (0 : Fin (N + 1))
  rw [c.halfGapCandidate_tail] at hhalf
  have hleft := c.tail.alpha_le_leftDefectCandidate
    (i := (0 : Fin (N + 1))) (j := (0 : Fin (N + 1))) le_rfl
  rw [c.leftDefectCandidate_tail] at hleft
  have htailLocal :
      c.tail.alpha (0 : Fin (N + 1)) ≤
        c.adjacentBinaryAlpha (1 : Fin (N + 2)) := by
    unfold adjacentBinaryAlpha
    exact le_min hhalf hleft
  rw [c.coe_alphaValue] at hlocal
  apply WithTop.coe_injective
  rw [c.coe_alphaValue, c.tail.coe_alphaValue]
  exact le_antisymm hshift (htailLocal.trans_eq hlocal)

/-- Corollary 8.11 at the second boundary, followed by the propagation lemma,
produces a BONG whose shifted alphas agree with all alphas of its tail. -/
structure Beli2019Lemma93SourceTailNormalization
    (b : GoodBONG q L (N + 4)) where
  transformed : GoodBONG q L (N + 4)
  adjacentBinaryAlpha_eq :
    transformed.adjacentBinaryAlpha (1 : Fin (N + 3)) =
      (transformed.alphaValue (1 : Fin (N + 3)) : WithTop ℚ)
  alpha_shift_eq_tail : ∀ i : Fin (N + 2),
    transformed.alphaValue i.succ = transformed.tail.alphaValue i

/-- The source normalization used in Case 1 of the ordinary branch of
Beli's proof of Lemma 9.3. -/
theorem exists_beli2019Lemma93SourceTailNormalization
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
    (b : GoodBONG q L (N + 4)) :
    Nonempty (Beli2019Lemma93SourceTailNormalization b) := by
  rcases b.beli2019Corollary811 (1 : Fin (N + 3)) with ⟨D⟩
  have hbase :
      D.transformed.alphaValue (1 : Fin (N + 3)) =
        D.transformed.tail.alphaValue (0 : Fin (N + 2)) :=
    D.transformed.alphaValue_one_eq_tail_zero_of_adjacentBinaryAlpha_one
      D.adjacentBinaryAlpha_eq
  refine ⟨{
    transformed := D.transformed
    adjacentBinaryAlpha_eq := D.adjacentBinaryAlpha_eq
    alpha_shift_eq_tail := ?_
  }⟩
  intro i
  exact D.transformed.alphaValue_shift_eq_tail_of_base_eq
    (0 : Fin (N + 2)) i (Fin.zero_le i) hbase

/-- The five alternatives in Lemma 9.1 are lattice invariants on the source
side.  This justifies applying Corollary 8.11 to the source before invoking
Lemma 9.1, exactly as in the paper. -/
theorem lemma91Alternative_changeSource_iff
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    (a : GoodBONG q L (N + 4))
    (b c : GoodBONG r M (N + 4)) :
    a.Lemma91Alternative b ↔ a.Lemma91Alternative c := by
  have horders : b.SameOrders c := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact b.order_invariant c
  have halphas : b.SameAlphas c := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact b.alpha_invariant c
  have hdefect := a.truncatedPrefixDefect_invariant
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    a b c (-1) 3 1
  unfold Lemma91Alternative
  rw [horders (1 : Fin (N + 4)), halphas (0 : Fin (N + 3)), hdefect]

/-- The Corollary 8.11 source normal form itself is already a valid Lemma
9.2 transform, and in fact satisfies a stronger equality at every boundary. -/
noncomputable def Beli2019Lemma93SourceTailNormalization.toLemma92Transform
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    {b : GoodBONG q L (N + 4)}
    (D : Beli2019Lemma93SourceTailNormalization b) :
    Beli2019Lemma92Transform D.transformed :=
  lemma92TransformOfSelfTailAgreement D.transformed D.transformed rfl
    (fun i _ ↦ D.alpha_shift_eq_tail i)
    (fun _ ↦ D.alpha_shift_eq_tail (1 : Fin (N + 2)))

/-- The selected pair in Case 1, together with the stronger source-side
normalization that Corollary 8.11 supplies beyond the statement of Lemma
9.2. -/
structure Beli2019Lemma93CaseOneNormalizedPair
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4)) where
  normalized : Beli2019Lemma93NormalizedPair a b
  sourceAlpha_shift_eq_tail : ∀ i : Fin (N + 2),
    normalized.sourceTransform.transformed.alphaValue i.succ =
      normalized.sourceTransform.transformed.tail.alphaValue i

/-- Case 1 of the ordinary branch, through the point where both BONGs have
been selected.  Corollary 8.11 is performed first on the source; the four
conditions and the Lemma 9.1 alternatives are transported to that choice;
then Lemmas 9.1 and 9.2 select the target.  The resulting source transform
retains the stronger alpha equality at every tail boundary. -/
theorem exists_beli2019Lemma93NormalizedPair_caseOne
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
    Nonempty (Beli2019Lemma93CaseOneNormalizedPair a b) := by
  have hsource :
      Nonempty (Beli2019Lemma93SourceTailNormalization b) := by
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
    letI : BONGStructuralLaws.{u, w} K := structuralW
    exact b.exists_beli2019Lemma93SourceTailNormalization
  rcases hsource with ⟨S⟩
  have hsourceOrders : b.SameOrders S.transformed := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact b.order_invariant S.transformed
  have hfirstSelected :
      a.order (0 : Fin (N + 4)) =
        S.transformed.order (0 : Fin (N + 4)) :=
    hfirst.trans (hsourceOrders (0 : Fin (N + 4)))
  have selectedConditions :
      RepresentationConditions a S.transformed (Nat.le_refl (N + 3)) :=
    (a.representationConditions_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      a b S.transformed (Nat.le_refl (N + 3))).mp conditions
  have hcaseSelected : a.Lemma91Alternative S.transformed :=
    (a.lemma91Alternative_changeSource_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      b S.transformed).mp hcase
  let Tb : Beli2019Lemma92Transform S.transformed := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact S.toLemma92Transform
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
      S.transformed hfirstSelected ambient selectedConditions hcaseSelected with
    ⟨H⟩
  have hTa : Nonempty (Beli2019Lemma92Transform H.transformed) := by
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
    exact H.transformed.beli2019Lemma92
  rcases hTa with ⟨Ta⟩
  let P : Beli2019Lemma93NormalizedPair a b :=
    Beli2019Lemma93NormalizedPair.ofTransforms
      (classificationV := classificationV) (classificationW := classificationW)
      a b conditions H.transformed S.transformed
        (H.firstValue_eq.trans
          S.transformed.firstUnarySegment_valueUnit_zero)
        Ta Tb
  refine ⟨{
    normalized := P
    sourceAlpha_shift_eq_tail := ?_
  }⟩
  intro i
  change S.transformed.alphaValue i.succ =
    S.transformed.tail.alphaValue i
  exact S.alpha_shift_eq_tail i

end BONG.GoodBONG

end Bong
