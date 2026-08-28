/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009BinaryConnectivityRankFive
import Bong.Dyadic.HilbertCongruenceProof

namespace Bong

open Dyadic
open BONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace Beli2009FinalRemarksProof.LargeResidueConnectivity

/-! ## Path-refined Lemma 9.1 -/

/-- Path-refined equal-rank form of Beli (2019), Lemma 9.1.  The existing
endpoint theorem is used only to prove that the Lemma 8.14 exceptional
predicate is false.  The endpoint itself is then reconstructed by the
complete adjacent-binary path theorem for Lemma 8.14. -/
theorem reachableLemma91_sameRank_of_largeResidue
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [parity : Beli2009AlphaParityLaws.{u, v} K]
    [localization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [construction : BeliLemma43ConstructionLaws.{u, v} K]
    [sectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [binaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [quaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [lemma49 : BeliLemma49Laws.{u, v} K]
    [lemma47 : BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    {N : Nat} (a : BONG.GoodBONG q L (N + 3))
    (c : BONG.GoodBONG q L (N + 3))
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (N + 3)))
    (ambient : q.Represents q)
    (conditions : RepresentationConditions a c (Nat.le_refl (N + 2)))
    (hcase : a.Lemma91Alternative c) :
    Nonempty (ReachablePrescribedFirstValueTransform
      a c.firstUnarySegment) := by
  have unaryConditions : a.Lemma813Conditions c.firstUnarySegment :=
    BONG.GoodBONG.lemma813Conditions_firstUnarySegment_of_lowerData_sameRank
      (alphaV := alpha) (alphaW := alpha)
      (structuralW := structural) (classificationW := classification)
      (sectionFiveW := sectionFive)
      (sectionFourW := sectionFour) (sectionFourV := sectionFour)
      (deepWW := deep)
      (n := N + 1) a c hfirst ambient conditions
  have horder : a.order (0 : Fin (N + 3)) =
      c.firstUnarySegment.order (0 : Fin 1) :=
    hfirst.trans c.firstUnarySegment_order_zero.symm
  have endpoint : Nonempty
      (a.Beli2019PrescribedFirstValueTransform c.firstUnarySegment) :=
    a.beli2019Lemma91_sameRank
      (targetLaws := alpha) (sourceLaws := alpha)
      (targetParity := parity)
      (targetLocalization := localization)
      (targetConstruction := construction)
      (targetSectionTwo := sectionTwo)
      (classificationV := classification)
      (classificationW := classification)
      (targetBinaryScaling := binaryScaling)
      (targetQuaternaryScaling := quaternaryScaling)
      (targetLemma49 := lemma49) (targetLemma47 := lemma47)
      (structuralV := structural) (structuralW := structural)
      (prefixChangeV := prefixChange) (prefixChangeW := prefixChange)
      (sectionFiveW := sectionFive)
      (sectionFourW := sectionFour) (sectionFourV := sectionFour)
      (deepWW := deep)
      c hfirst ambient conditions hcase
  have hnotExceptional :
      ¬a.Beli2019Lemma814Exceptional c.firstUnarySegment :=
    (a.beli2019Lemma814Explicit
      (classificationV := classification)
      (classificationW := classification)
      (prefixChangeV := prefixChange) (prefixChangeW := prefixChange)
      c.firstUnarySegment horder unaryConditions).mp endpoint
  exact reachableLemma814_complete_of_largeResidue
    a c.firstUnarySegment horder unaryConditions hnotExceptional hres

/-! ## Path-refined ordinary Lemma 9.3 -/

/-- A normalized Lemma 9.3 pair together with the two paths that select it
and the reverse inequalities needed for head deletion. -/
structure ReachableLemma93CertifiedPair
    {N : Nat} (a b : BONG.GoodBONG q L (N + 4)) where
  normalized : ReachableLemma93NormalizedPair a b
  certificate : BONG.GoodBONG.Beli2019Lemma93LowReverseCertificate
    a b normalized.pair

/-- Path-refined Case 1 of Lemma 9.3.  Corollary 8.11 first normalizes the
source tail, reachable Lemma 9.1 matches the head, and reachable Lemma 9.2
normalizes the target. -/
theorem reachableLemma93CertifiedPair_caseOne_of_largeResidue
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [parity : Beli2009AlphaParityLaws.{u, v} K]
    [localization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [construction : BeliLemma43ConstructionLaws.{u, v} K]
    [sectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [binaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [quaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [lemma49 : BeliLemma49Laws.{u, v} K]
    [lemma47 : BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    {N : Nat} (a b : BONG.GoodBONG q L (N + 4))
    (hfirst : a.order (0 : Fin (N + 4)) =
      b.order (0 : Fin (N + 4)))
    (ambient : q.Represents q)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (hlemma91 : a.Lemma91Alternative b)
    (hcase : a.Beli2019Lemma93CaseOneCondition b) :
    Nonempty (ReachableLemma93CertifiedPair a b) := by
  rcases reachableLemma93SourceTailNormalization_of_largeResidue b hres with
    ⟨S⟩
  have hsourceOrders : b.SameOrders S.data.transformed :=
    b.order_invariant S.data.transformed
  have hfirstSelected : a.order (0 : Fin (N + 4)) =
      S.data.transformed.order (0 : Fin (N + 4)) :=
    hfirst.trans (hsourceOrders (0 : Fin (N + 4)))
  have selectedConditions : RepresentationConditions a S.data.transformed
      (Nat.le_refl (N + 3)) :=
    (a.representationConditions_changeBONG_iff
      (classificationV := classification) (classificationW := classification)
      a b S.data.transformed (Nat.le_refl (N + 3))).mp conditions
  have hlemma91Selected : a.Lemma91Alternative S.data.transformed :=
    (a.lemma91Alternative_changeSource_iff
      (classificationV := classification) (classificationW := classification)
      (prefixChangeV := prefixChange) (prefixChangeW := prefixChange)
      b S.data.transformed).mp hlemma91
  rcases reachableLemma91_sameRank_of_largeResidue
      (alpha := alpha) (parity := parity) (localization := localization)
      (construction := construction) (sectionTwo := sectionTwo)
      (classification := classification) (binaryScaling := binaryScaling)
      (quaternaryScaling := quaternaryScaling) (lemma49 := lemma49)
      (lemma47 := lemma47) (structural := structural)
      (prefixChange := prefixChange) (sectionFive := sectionFive)
      (sectionFour := sectionFour) (deep := deep)
      hres a S.data.transformed hfirstSelected ambient selectedConditions
        hlemma91Selected with ⟨H⟩
  rcases reachableLemma92Transform_of_largeResidue hres
      H.transform.transformed with ⟨Ta⟩
  let Tb : ReachableLemma92Transform S.data.transformed := {
    transform := S.data.toLemma92Transform
    reachable := beli2009BinaryReachable_refl _
  }
  let P : ReachableLemma93NormalizedPair a b :=
    ReachableLemma93NormalizedPair.ofTransforms a b conditions
      H.transform.transformed S.data.transformed
      (H.transform.firstValue_eq.trans
        S.data.transformed.firstUnarySegment_valueUnit_zero)
      H.reachable S.reachable Ta Tb
  let C : BONG.GoodBONG.Beli2019Lemma93CaseOneNormalizedPair a b := {
    normalized := P.pair
    sourceAlpha_shift_eq_tail := S.data.alpha_shift_eq_tail
  }
  exact ⟨{
    normalized := P
    certificate := C.lowReverse_of_caseOne
      (alphaV := alpha) (alphaW := alpha)
      (classificationV := classification) (classificationW := classification)
      (prefixChangeV := prefixChange) (prefixChangeW := prefixChange)
      hlemma91 hcase
  }⟩

/-- The first Case-2 source choice together with its actual adjacent-binary
path. -/
structure ReachableLemma93CaseTwoSourceHeadNormalization
    {N : Nat} (a b : BONG.GoodBONG q L (N + 4)) where
  data : BONG.GoodBONG.Beli2019Lemma93CaseTwoSourceHeadNormalization a b
  reachable : Beli2009BinaryReachable (K := K)
    (fun i => b.valueUnit i) (fun i => data.transformed.valueUnit i)

/-- Path-refined source-head normalization in ordinary Case 2.  If the raw
defect is already sharp the path is reflexive; otherwise path-refined Lemma
8.8 supplies exactly the multiplier used in the paper's sharp-product
calculation. -/
theorem reachableCaseTwoSourceHeadNormalization_of_largeResidue
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    {N : Nat} (a b : BONG.GoodBONG q L (N + 4))
    (hfirst : a.order (0 : Fin (N + 4)) =
      b.order (0 : Fin (N + 4)))
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    Nonempty (ReachableLemma93CaseTwoSourceHeadNormalization a b) := by
  let raw := BONG.GoodBONG.defectOrder (K := K)
    ((-1) * a.prefixProduct 3 * b.prefixProduct 1)
  have hrawLe : (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) ≤ raw := by
    have hle := a.truncatedPrefixDefect_le_defect b (-1) 3 1
    exact hcase.1 ▸ hle
  by_cases hrawEq : raw =
      (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ)
  · exact ⟨{
      data := {
        transformed := b
        firstThirdRawDefect_eq := hrawEq
      }
      reachable := beli2009BinaryReachable_refl _
    }⟩
  · have hstrict := a.sourceFirstAlpha_lt_halfGap_of_caseTwo
      b hfirst hcase
    have hnotExceptional : ¬b.Beli2019Lemma88Exceptional := by
      rintro ⟨hhalf, _⟩
      exact (ne_of_lt hstrict) hhalf
    rcases reachableLemma88_sufficiency_of_largeResidue
        b hnotExceptional hres with ⟨T⟩
    have hstrictRaw :
        (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) < raw :=
      lt_of_le_of_ne hrawLe (fun h => hrawEq h.symm)
    have hproduct :
        (-1 : Kˣ) * a.prefixProduct 3 *
              T.transform.transformed.prefixProduct 1 =
          T.transform.epsilon *
            ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
      rw [T.transform.prefixProduct_one_eq]
      ac_rfl
    refine ⟨{
      data := {
        transformed := T.transform.transformed
        firstThirdRawDefect_eq := ?_
      }
      reachable := T.reachable
    }⟩
    rw [hproduct,
      BONG.GoodBONG.defectOrder_mul_eq_left_of_lt_right (K := K)
        (T.transform.epsilon_defect ▸ hstrictRaw),
      T.transform.epsilon_defect]

/-- Path-refined Case 2 of Lemma 9.3.  Both source choices and both target
choices are concatenated explicitly; the exact raw defect is transported
through the same selected endpoints used by those paths. -/
theorem reachableLemma93CertifiedPair_caseTwo_of_largeResidue
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [parity : Beli2009AlphaParityLaws.{u, v} K]
    [localization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [construction : BeliLemma43ConstructionLaws.{u, v} K]
    [sectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [binaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [quaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [lemma49 : BeliLemma49Laws.{u, v} K]
    [lemma47 : BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    {N : Nat} (a b : BONG.GoodBONG q L (N + 4))
    (hfirst : a.order (0 : Fin (N + 4)) =
      b.order (0 : Fin (N + 4)))
    (ambient : q.Represents q)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (hlemma91 : a.Lemma91Alternative b)
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    Nonempty (ReachableLemma93CertifiedPair a b) := by
  rcases reachableCaseTwoSourceHeadNormalization_of_largeResidue
      hres a b hfirst hcase with ⟨H⟩
  rcases reachableLemma92Transform_of_largeResidue hres
      H.data.transformed with ⟨Tb⟩
  have hrawSource : BONG.GoodBONG.defectOrder (K := K)
      ((-1) * a.prefixProduct 3 *
        Tb.transform.transformed.prefixProduct 1) =
      (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := by
    rw [Tb.transform.prefixProduct_one_eq]
    exact H.data.firstThirdRawDefect_eq
  have hsourceOrders : b.SameOrders H.data.transformed :=
    b.order_invariant H.data.transformed
  have hfirstSelected : a.order (0 : Fin (N + 4)) =
      H.data.transformed.order (0 : Fin (N + 4)) :=
    hfirst.trans (hsourceOrders (0 : Fin (N + 4)))
  have selectedConditions : RepresentationConditions a H.data.transformed
      (Nat.le_refl (N + 3)) :=
    (a.representationConditions_changeBONG_iff
      (classificationV := classification) (classificationW := classification)
      a b H.data.transformed (Nat.le_refl (N + 3))).mp conditions
  have hlemma91Selected : a.Lemma91Alternative H.data.transformed :=
    (a.lemma91Alternative_changeSource_iff
      (classificationV := classification) (classificationW := classification)
      (prefixChangeV := prefixChange) (prefixChangeW := prefixChange)
      b H.data.transformed).mp hlemma91
  rcases reachableLemma91_sameRank_of_largeResidue
      (alpha := alpha) (parity := parity) (localization := localization)
      (construction := construction) (sectionTwo := sectionTwo)
      (classification := classification) (binaryScaling := binaryScaling)
      (quaternaryScaling := quaternaryScaling) (lemma49 := lemma49)
      (lemma47 := lemma47) (structural := structural)
      (prefixChange := prefixChange) (sectionFive := sectionFive)
      (sectionFour := sectionFour) (deep := deep)
      hres a H.data.transformed hfirstSelected ambient selectedConditions
        hlemma91Selected with ⟨G⟩
  rcases reachableLemma92Transform_of_largeResidue hres
      G.transform.transformed with ⟨Ta⟩
  let P : ReachableLemma93NormalizedPair a b :=
    ReachableLemma93NormalizedPair.ofTransforms a b conditions
      G.transform.transformed H.data.transformed
      (G.transform.firstValue_eq.trans
        H.data.transformed.firstUnarySegment_valueUnit_zero)
      G.reachable H.reachable Ta Tb
  have hrawTarget : BONG.GoodBONG.defectOrder (K := K)
      ((-1) * Ta.transform.transformed.prefixProduct 3 *
        Tb.transform.transformed.prefixProduct 1) =
      (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) :=
    BONG.GoodBONG.firstThirdRawDefect_changeTarget_eq_of_lt_alphaThree
      (prefixChangeV := prefixChange)
      a Ta.transform.transformed Tb.transform.transformed
      (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ)
      hrawSource hcase.2.2
  have hsourceAlpha : b.alphaValue (0 : Fin (N + 3)) =
      Tb.transform.transformed.alphaValue (0 : Fin (N + 3)) :=
    b.alpha_invariant Tb.transform.transformed (0 : Fin (N + 3))
  let C : BONG.GoodBONG.Beli2019Lemma93CaseTwoNormalizedPair a b := {
    normalized := P.pair
    firstThirdRawDefect_eq_sourceFirstAlpha :=
      hrawTarget.trans
        (congrArg (fun z : ℚ => (z : WithTop ℚ)) hsourceAlpha)
  }
  exact ⟨{
    normalized := P
    certificate := C.toLowReverseCertificate_of_original
      (targetLaws := alpha) (sourceLaws := alpha)
      (classificationV := classification) (classificationW := classification)
      (prefixChangeV := prefixChange) (prefixChangeW := prefixChange)
      hlemma91 hcase
  }⟩

/-- For two good BONGs of one lattice, order invariance supplies the
`R₂ = S₂` alternative of Lemma 9.1.  Hence the ordinary Case-1/Case-2
split is exhaustive and produces a path-refined certified pair in every
rank at least four. -/
theorem reachableLemma93CertifiedPair_of_largeResidue
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [parity : Beli2009AlphaParityLaws.{u, v} K]
    [localization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [construction : BeliLemma43ConstructionLaws.{u, v} K]
    [sectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [binaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [quaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [lemma49 : BeliLemma49Laws.{u, v} K]
    [lemma47 : BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    {N : Nat} (a b : BONG.GoodBONG q L (N + 4)) :
    Nonempty (ReachableLemma93CertifiedPair a b) := by
  let ambient : q.Represents q := QuadraticSpace.represents_refl q
  have conditions : RepresentationConditions a b (Nat.le_refl (N + 3)) :=
    beli2019_necessity (sourceLaws := alpha) (targetLaws := alpha)
      a b (Nat.le_refl (N + 3)) (Lattice.represents_refl q L)
  have horders : a.SameOrders b := a.order_invariant b
  have hfirst : a.order (0 : Fin (N + 4)) =
      b.order (0 : Fin (N + 4)) := horders _
  have hlemma91 : a.Lemma91Alternative b :=
    Or.inr (Or.inl (horders (1 : Fin (N + 4))))
  by_cases hcase : a.Beli2019Lemma93CaseOneCondition b
  · exact reachableLemma93CertifiedPair_caseOne_of_largeResidue
      (alpha := alpha) (parity := parity) (localization := localization)
      (construction := construction) (sectionTwo := sectionTwo)
      (classification := classification) (binaryScaling := binaryScaling)
      (quaternaryScaling := quaternaryScaling) (lemma49 := lemma49)
      (lemma47 := lemma47) (structural := structural)
      (prefixChange := prefixChange) (sectionFive := sectionFive)
      (sectionFour := sectionFour) (deep := deep)
      hres a b hfirst ambient conditions hlemma91 hcase
  · have hcaseTwo : a.Beli2019Lemma93CaseTwoCondition b :=
      (a.beli2019Lemma93CaseTwoCondition_iff_not_caseOneCondition b).2 hcase
    exact reachableLemma93CertifiedPair_caseTwo_of_largeResidue
      (alpha := alpha) (parity := parity) (localization := localization)
      (construction := construction) (sectionTwo := sectionTwo)
      (classification := classification) (binaryScaling := binaryScaling)
      (quaternaryScaling := quaternaryScaling) (lemma49 := lemma49)
      (lemma47 := lemma47) (structural := structural)
      (prefixChange := prefixChange) (sectionFive := sectionFive)
      (sectionFour := sectionFour) (deep := deep)
      hres a b hfirst ambient conditions hlemma91 hcaseTwo

/-! ## Completion of the all-rank connectivity induction -/

/-- Beli's positive final remark over residue fields with more than two
elements, proved for every rank.  Ranks one and two are direct, rank three
is the completed ternary path theorem, and every larger rank is reduced by
the path-refined Lemma 9.3 pair to a projected lattice of rank one less. -/
theorem reachable_of_largeResidue_proved
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [parity : Beli2009AlphaParityLaws.{u, v} K]
    [localization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [construction : BeliLemma43ConstructionLaws.{u, v} K]
    [sectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [binaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [quaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [lemma49 : BeliLemma49Laws.{u, v} K]
    [lemma47 : BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    {n : Nat} (a b : BONG.GoodBONG q L (n + 1)) :
    Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => b.valueUnit i) := by
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      cases n with
      | zero =>
          exact reachable_rankOne a b
      | succ n =>
          cases n with
          | zero =>
              exact reachable_rankTwo a b
          | succ n =>
              cases n with
              | zero =>
                  exact reachable_rankThree_of_largeResidue hres a b
              | succ N =>
                  rcases reachableLemma93CertifiedPair_of_largeResidue
                      (alpha := alpha) (parity := parity)
                      (localization := localization)
                      (construction := construction) (sectionTwo := sectionTwo)
                      (classification := classification)
                      (binaryScaling := binaryScaling)
                      (quaternaryScaling := quaternaryScaling)
                      (lemma49 := lemma49) (lemma47 := lemma47)
                      (structural := structural) (prefixChange := prefixChange)
                      (sectionFive := sectionFive) (sectionFour := sectionFour)
                      (deep := deep) hres a b with ⟨D⟩
                  let ambient : q.Represents q :=
                    QuadraticSpace.represents_refl q
                  have conditions : RepresentationConditions a b
                      (Nat.le_refl (N + 3)) :=
                    beli2019_necessity
                      (sourceLaws := alpha) (targetLaws := alpha)
                      a b (Nat.le_refl (N + 3))
                        (Lattice.represents_refl q L)
                  apply reachable_of_normalizedPair_of_tailConnectivity
                    a b ambient conditions D.normalized D.certificate
                  intro x y
                  exact ih (N + 2) (by omega) x y

/-- The preceding theorem with every local-law interface instantiated by
its concrete proof module. -/
theorem reachable_of_largeResidue_unconditional
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (a b : BONG.GoodBONG q L (n + 1)) :
    Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => b.valueUnit i) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  letI : BeliHilbertCongruenceLaws K :=
    Dyadic.beliHilbertCongruenceLawsProved
  letI : BONGStructuralLaws.{u, v} K := bongStructuralLawsProved K
  letI : BONGGoodExistenceLaws.{u, v} K :=
    BONGStructuralLaws.toBONGGoodExistenceLaws
  letI : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K :=
    goodBONGDeepIntegralExtensionLaws K
  letI : BONGReverseDualLaws.{u, v} K :=
    BONGStructuralLaws.toBONGReverseDualLaws
  letI : BeliLemma43ConstructionLaws.{u, v} K :=
    beliLemma43ConstructionLawsProved K
  letI : BeliLemma47Laws.{u, v} K := beliLemma47LawsProved K
  letI : BeliLemma49Laws.{u, v} K :=
    @BONG.beliLemma49LawsOfReverseDual.{u, v} K _ _ _ _ _
      (inferInstance : BeliLemma47Laws.{u, v} K)
      (inferInstance : BONGReverseDualLaws.{u, v} K)
  letI : Beli2006AlphaLaws.{u, v} K :=
    @beli2006AlphaLaws_proved.{u, v} K _ _ _ _ _ _ _ _
  letI : GoodBONGClassificationLaws.{u, v, v} K :=
    goodBONGClassificationLawsProved K
  exact reachable_of_largeResidue_proved hres a b

/-- Concrete discharge of both assertions in Beli's unnumbered final
remarks: all-rank connectivity for larger residue fields and the
parameterized rank-four obstruction for residue field two. -/
noncomputable instance beli2009BinaryTransformationLawsProved :
    Beli2009BinaryTransformationLaws.{u, v} (K := K) where
  reachable_of_large_residue hres a b :=
    reachable_of_largeResidue_unconditional hres a b
  parametric_counterexample_of_residue_two
      hres d hdpos hdlt hdodd epsilon eta hepsilon heta :=
    Beli2009FinalRemarksProof.beli2009Section5_residueTwoParametricCounterexample_proved
      hres d hdpos hdlt hdodd epsilon eta hepsilon heta

end Beli2009FinalRemarksProof.LargeResidueConnectivity

/-- Beli (2009/2010), final positive remark, with every lower-level local
law discharged: over a residue field with more than two elements, any two
good BONGs of one lattice are connected by finitely many adjacent binary
transformations. -/
theorem beli2009Section5_largeResidueConnectivity_proved
    (hres : BONG.HasResidueFieldMoreThanTwoElements (K := K))
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (a b : BONG.GoodBONG q L (n + 1)) :
    Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => b.valueUnit i) := by
  exact Beli2009FinalRemarksProof.LargeResidueConnectivity.reachable_of_largeResidue_unconditional
    hres a b

/-- Unconditional public form of Beli's final Section 5 dichotomy: binary
transformations connect all good BONGs over larger residue fields, while a
rank-four obstruction exists when the residue field has two elements. -/
theorem beli2009Section5_binaryTransformationDichotomy_proved :
    (BONG.HasResidueFieldMoreThanTwoElements (K := K) →
      ∀ {V : Type v} [AddCommGroup V] [Module K V]
        {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
        (a b : BONG.GoodBONG q L (n + 1)),
        Beli2009BinaryReachable (K := K)
          (fun i => a.valueUnit i) (fun i => b.valueUnit i)) ∧
      (¬BONG.HasResidueFieldMoreThanTwoElements (K := K) →
        Nonempty
          (Beli2009BinaryTransformationCounterexample.{u, u}
            (K := K))) :=
  beli2009Section5_binaryTransformationDichotomy (K := K)

end Bong
