/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma91
import Bong.Bong.Beli2019RankCompletion
import Bong.Bong.Beli2019SameRankCommonSpaceCore

/-!
# Beli (2019), Lemma 9.1: the unary transitivity bridge

The paper's relation `N ≤ M` is an ambient quadratic-space representation
together with the four conditions of Theorem 2.1.  In Lemma 9.1 the unary
prefix `[b₁]` first satisfies `[b₁] ≤ N`; transitivity then gives
`[b₁] ≤ M`, which is the `Lemma813Conditions` input used by Lemma 8.14.

This file implements that step in equal rank.  The unary prefix is completed
inside `N` by a sufficiently deep complement, Section 4 composes the two
same-rank condition packages, and Lemma 2.20 descends the result back to the
literal unary prefix.
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
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

set_option maxHeartbeats 1000000 in
-- The dependent rank-completion/transitivity composition requires extra reduction.
/-- The exact transitivity argument invoked at the start of Lemma 9.1 in the
equal-rank setting used by Section 9.  It assumes no lattice representation
of `M` by `N`. -/
theorem lemma813Conditions_firstUnarySegment_of_lowerData_sameRank
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [sectionFiveW : Beli2019SectionFiveLaws.{u, w} K]
    [sectionFourW : Beli2019SectionFourLaws.{u, w} K]
    [sectionFourV : Beli2019SectionFourLaws.{u, v} K]
    [deepWW : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K]
    (a : GoodBONG q L (n + 2)) (c : GoodBONG r M (n + 2))
    (hfirst : a.order (0 : Fin (n + 2)) =
      c.order (0 : Fin (n + 2)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c (Nat.le_refl (n + 1))) :
    a.Lemma813Conditions c.firstUnarySegment := by
  let b := c.firstUnarySegment
  rcases c.firstUnaryPrefix_represents with ⟨prefixRepresentation⟩
  rcases GoodBONGDeepIntegralExtensionLaws.extension
      (m := n + 1) (n := 0) c b (by omega)
      prefixRepresentation
      (a.rankCompletionOrderBound (n := 0))
      (a.rankCompletionAlphaBound b) with ⟨D⟩
  have hcompleted : RepresentationConditions c D.completedBONG
      (Nat.le_refl (n + 1)) := by
    letI : Beli2019SectionFourLaws.{u, w} K := sectionFourW
    exact c.representationConditions_of_lattice_le
      D.completedBONG D.completed_le
  let C : Beli2019SameRankCommonSpace a c :=
    Beli2019SameRankCommonSpace.ofAmbient ambient
  let cImage := C.sourceImageBONG
  let completedImage := D.completedBONG.map C.ambientIsometry
  have hcompletedAgreement : ScalarAgreement
      D.completedBONG completedImage := by
    constructor
    intro i
    apply Units.ext
    change D.completedBONG.value i = completedImage.value i
    exact (BONG.value_map C.ambientIsometry D.completedBONG.toBONG i).symm
  have hconditionsImage : RepresentationConditions a cImage
      (Nat.le_refl (n + 1)) :=
    C.conditions conditions
  have hcompletedImage : RepresentationConditions cImage completedImage
      (Nat.le_refl (n + 1)) :=
    C.source_scalarAgreement.representationConditions_transport
      hcompletedAgreement hcompleted
  have htransitivity : SectionFourTransitivityData
      a cImage completedImage := by
    letI : Beli2019SectionFourLaws.{u, v} K := sectionFourV
    exact Beli2019SectionFourLaws.data a cImage completedImage
      hconditionsImage hcompletedImage
  have hacompletedImage : RepresentationConditions a completedImage
      (Nat.le_refl (n + 1)) :=
    representationConditions_trans_sameRank a cImage completedImage
      hconditionsImage hcompletedImage htransitivity
  have hacompleted : RepresentationConditions a D.completedBONG
      (Nat.le_refl (n + 1)) :=
    (ScalarAgreement.refl a).representationConditions_transport
      hcompletedAgreement.symm hacompletedImage
  have hacompletedPrime : RepresentationConditionsPrime
      a D.completedBONG (Nat.le_refl (n + 1)) :=
    RepresentationConditions.toPrime
      (sourceLaws := alphaV) (targetLaws := alphaW) hacompleted
  have habPrime : RepresentationConditionsPrime a b (Nat.zero_le (n + 1)) :=
    representationConditionsPrime_of_prefixAgreement
      (K := K) (V := V) (U := W)
      (q := q) (s := r) (L := L) (C := D.completedLattice)
      (m := n + 1) (n := 0)
      (a := a) (c := D.completedBONG) (b := b)
      (hRank := Nat.zero_le (n + 1))
      (alphaV := alphaV) (alphaW := alphaW)
      D.prefixAgreement (by omega) D.boundaryOrder D.boundaryAlpha
        hacompletedPrime
  have htrigger := a.beli2019Lemma216
    (sourceLaws := alphaV) (targetLaws := alphaW)
    b (Nat.zero_le (n + 1)) habPrime.orderCondition
      habPrime.defectCondition
  have hab : RepresentationConditions a b (Nat.zero_le (n + 1)) :=
    (representationConditions_iff_prime a b (Nat.zero_le (n + 1))
      htrigger).mpr habPrime
  have hfirstUnary : a.order (0 : Fin (n + 2)) =
      b.order (0 : Fin 1) :=
    hfirst.trans c.firstUnarySegment_order_zero.symm
  have hunaryAmbient : q.Represents
      (r.restrict c.firstUnaryPrefixWitness.carrier
        c.firstUnaryPrefixWitness.nondegenerate) :=
    ambient.trans (Lattice.Represents.ambient
      c.firstUnaryPrefix_represents)
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  exact (a.representationConditions_iff_lemma813
    b hfirstUnary hunaryAmbient).mp hab

/-- Paper-facing equal-rank form of Beli (2019), Lemma 9.1.  The unary input
needed by the arithmetic core is derived from the paper's relation `N ≤ M`
by `lemma813Conditions_firstUnarySegment_of_lowerData_sameRank`. -/
theorem beli2019Lemma91_sameRank
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
    [targetBinaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [targetQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [targetLemma49 : BeliLemma49Laws.{u, v} K]
    [targetLemma47 : BeliLemma47Laws.{u, v} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
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
    (a : GoodBONG q L (n + 3)) (c : GoodBONG r M (n + 3))
    (hfirst : a.order (0 : Fin (n + 3)) =
      c.order (0 : Fin (n + 3)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c (Nat.le_refl (n + 2)))
    (hcase : a.Lemma91Alternative c) :
    Nonempty
      (a.Beli2019PrescribedFirstValueTransform c.firstUnarySegment) := by
  have unaryConditions : a.Lemma813Conditions c.firstUnarySegment :=
    lemma813Conditions_firstUnarySegment_of_lowerData_sameRank
      (alphaV := targetLaws) (alphaW := sourceLaws)
      (structuralW := structuralW) (classificationW := classificationW)
      (sectionFiveW := sectionFiveW)
      (sectionFourW := sectionFourW) (sectionFourV := sectionFourV)
      (deepWW := deepWW)
      (n := n + 1) a c hfirst ambient conditions
  exact beli2019Lemma91
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (targetParity := targetParity)
    (targetLocalization := targetLocalization)
    (targetConstruction := targetConstruction)
    (targetSectionTwo := targetSectionTwo)
    (targetBinaryScaling := targetBinaryScaling)
    (targetQuaternaryScaling := targetQuaternaryScaling)
    (targetLemma49 := targetLemma49) (targetLemma47 := targetLemma47)
    (structuralV := structuralV)
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    (N := n) (S := n + 1) a c (Nat.le_refl (n + 2))
      hfirst ambient conditions unaryConditions hcase

end BONG.GoodBONG

end Bong
