/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma912SectionNine
import Bong.Bong.Beli2019RepresentationProblemReindex

/-!
# Beli (2019), Section 9: the complete equal-norm reduction

At common rank at least five, the exhaustive Section 9 trichotomy always
produces a strictly smaller counterexample.  The ordinary and exceptional
branches use the literal projected-lattice problems of Lemmas 9.3 and 9.6;
the residual branch is the concrete construction of Lemma 9.12.
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

section Laws

variable
    [QuadraticDefectLaws K]
    [PerfectResidueFieldLaws K]
    [disc : DyadicDiscriminantClassLaws K]
    [DyadicMaximalDefectClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [constructionV : BeliLemma43ConstructionLaws.{u, v} K]
    [constructionW : BeliLemma43ConstructionLaws.{u, w} K]
    [sectionTwoV : Beli2006SectionTwoLaws.{u, v} K]
    [sectionTwoW : Beli2006SectionTwoLaws.{u, w} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [structuralModel : BONGStructuralLaws.{u, u} K]
    [ScaledHyperbolicMaximalLaws.{u, u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [alphaModel : Beli2006AlphaLaws.{u, u} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [parityW : Beli2009AlphaParityLaws.{u, w} K]
    [localizationV : Beli2009AlphaLocalizationLaws.{u, v} K]
    [localizationW : Beli2009AlphaLocalizationLaws.{u, w} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [classificationModel : GoodBONGClassificationLaws.{u, v, u} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [binaryScalingV : DyadicBinaryFirstScalingLaws.{u, v} K]
    [binaryScalingW : DyadicBinaryFirstScalingLaws.{u, w} K]
    [quaternaryScalingV : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [quaternaryScalingW : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [lemma49V : BeliLemma49Laws.{u, v} K]
    [lemma49W : BeliLemma49Laws.{u, w} K]
    [lemma47V : BeliLemma47Laws.{u, v} K]
    [lemma47W : BeliLemma47Laws.{u, w} K]
    [BeliCorollary44Laws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [sectionFiveV : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFiveW : Beli2019SectionFiveLaws.{u, w} K]
    [sectionFourV : Beli2019SectionFourLaws.{u, v} K]
    [sectionFourW : Beli2019SectionFourLaws.{u, w} K]
    [deepWW : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K]

set_option maxHeartbeats 24000000 in
-- The arbitrary-rank descent expands the complete Lemmas 9.3, 9.6, and 9.12 split.
/-- At equal norm and common rank at least five, one of Lemmas 9.3, 9.6,
or 9.12 constructs a strictly smaller concrete counterexample. -/
theorem beli2019SectionNine_counterexampleDescent
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c (Nat.le_refl (N + 4)))
    (hp : (Beli2019RepresentationProblem.ofData
      a c (Nat.le_refl (N + 4)) ambient conditions).Counterexample)
    (hequal : (Beli2019RepresentationProblem.ofData
      a c (Nat.le_refl (N + 4)) ambient conditions).EqualNorm) :
    ∃ next, next.Counterexample ∧
      next.sourceIndex = next.targetIndex ∧
      Beli2019ProblemSmaller Beli2019RepresentationProblem.measure next
        (Beli2019RepresentationProblem.ofData
          a c (Nat.le_refl (N + 4)) ambient conditions) := by
  let p := Beli2019RepresentationProblem.ofData
    a c (Nat.le_refl (N + 4)) ambient conditions
  have hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)) := by
    exact (Beli2019RepresentationProblem.equalNorm_iff_firstOrder_eq p).mp
      hequal
  cases beli2019SectionNine_cases p with
  | lemma93 ordinary =>
      rcases ordinary with ⟨input⟩
      let reduction := input.headReduction
        (targetLaws := alphaW) (sourceLaws := alphaV)
      exact ⟨reduction.next,
        Beli2019RepresentationProblem.HeadReduction.nextCounterexample
          p reduction hp,
        rfl,
        Beli2019RepresentationProblem.HeadReduction.smaller p reduction⟩
  | lemma96 exceptional =>
      rcases exceptional with ⟨input⟩
      let reduction := input.headReduction
        (targetLaws := alphaV) (sourceLaws := alphaW)
      exact ⟨reduction.next,
        Beli2019RepresentationProblem.HeadReduction.nextCounterexample
          p reduction hp,
        rfl,
        Beli2019RepresentationProblem.HeadReduction.smaller p reduction⟩
  | lemma912 residual =>
      rcases a.exists_beli2019Lemma912_indexPReduction_of_sectionNineResidual
        (K := K) (V := V) (W := W) (q := q) (r := r)
        (L := L) (M := M) (N := N)
        (disc := disc)
        (constructionV := constructionV) (constructionW := constructionW)
        (sectionTwoV := sectionTwoV) (sectionTwoW := sectionTwoW)
        (structuralV := structuralV) (structuralW := structuralW)
        (structuralModel := structuralModel)
        (alphaV := alphaV) (alphaW := alphaW) (alphaModel := alphaModel)
        (parityV := parityV) (parityW := parityW)
        (localizationV := localizationV) (localizationW := localizationW)
        (classificationModel := classificationModel)
        (classificationV := classificationV)
        (classificationW := classificationW)
        (binaryScalingV := binaryScalingV) (binaryScalingW := binaryScalingW)
        (quaternaryScalingV := quaternaryScalingV)
        (quaternaryScalingW := quaternaryScalingW)
        (lemma49V := lemma49V) (lemma49W := lemma49W)
        (lemma47V := lemma47V) (lemma47W := lemma47W)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        (sectionFiveV := sectionFiveV) (sectionFiveW := sectionFiveW)
        (sectionFourV := sectionFourV) (sectionFourW := sectionFourW)
        (deepWW := deepWW)
        c hfirst ambient conditions residual with ⟨reduction⟩
      exact ⟨reduction.next,
        reduction.nextCounterexample p hp,
        rfl,
        reduction.smaller⟩

/-- Bundled form of the Section 9 reduction.  It applies to every equal-rank
recursive problem whose common rank is at least five. -/
theorem beli2019SectionNine_counterexampleDescent_of_problem
    (p : Beli2019RepresentationProblem.{u, v, w} K)
    (hindex : p.sourceIndex = p.targetIndex)
    (hrank : 4 ≤ p.sourceIndex) (hp : p.Counterexample)
    (hequal : p.EqualNorm) :
    ∃ next, next.Counterexample ∧
      next.sourceIndex = next.targetIndex ∧
      Beli2019ProblemSmaller Beli2019RepresentationProblem.measure
        next p := by
  letI : AddCommGroup p.Target := p.targetAddCommGroup
  letI : Module K p.Target := p.targetModule
  letI : AddCommGroup p.Source := p.sourceAddCommGroup
  letI : Module K p.Source := p.sourceModule
  let t := p.sourceIndex - 4
  have hsource : p.sourceIndex = t + 4 := by
    dsimp only [t]
    omega
  have htarget : p.targetIndex = t + 4 := by omega
  let a := p.targetBONG.castLength
    (show p.targetIndex + 1 = t + 5 by omega)
  let c := p.sourceBONG.castLength
    (show p.sourceIndex + 1 = t + 5 by omega)
  let conditions' :=
    Beli2019RepresentationProblem.representationConditions_castIndices
      p.targetBONG p.sourceBONG p.rankBound p.conditions htarget hsource
  let p' := Beli2019RepresentationProblem.ofData a c
    (Nat.le_refl (t + 4)) p.ambient conditions'
  have hproblem : p' = p := by
    dsimp only [p', a, c, conditions']
    exact (Beli2019RepresentationProblem.ofData_castIndices_eq
      p.targetBONG p.sourceBONG p.rankBound p.ambient p.conditions
        htarget hsource).trans
      (Beli2019RepresentationProblem.ofData_self p)
  have hp' : p'.Counterexample := by rwa [hproblem]
  have hequal' : p'.EqualNorm := by rwa [hproblem]
  have H := beli2019SectionNine_counterexampleDescent
    (K := K) (V := p.Target) (W := p.Source)
    (q := p.targetQ) (r := p.sourceQ)
    (L := p.targetLattice) (M := p.sourceLattice) (N := t)
    (disc := disc)
    (constructionV := constructionV) (constructionW := constructionW)
    (sectionTwoV := sectionTwoV) (sectionTwoW := sectionTwoW)
    (structuralV := structuralV) (structuralW := structuralW)
    (structuralModel := structuralModel)
    (alphaV := alphaV) (alphaW := alphaW) (alphaModel := alphaModel)
    (parityV := parityV) (parityW := parityW)
    (localizationV := localizationV) (localizationW := localizationW)
    (classificationModel := classificationModel)
    (classificationV := classificationV) (classificationW := classificationW)
    (binaryScalingV := binaryScalingV) (binaryScalingW := binaryScalingW)
    (quaternaryScalingV := quaternaryScalingV)
    (quaternaryScalingW := quaternaryScalingW)
    (lemma49V := lemma49V) (lemma49W := lemma49W)
    (lemma47V := lemma47V) (lemma47W := lemma47W)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    (sectionFiveV := sectionFiveV) (sectionFiveW := sectionFiveW)
    (sectionFourV := sectionFourV) (sectionFourW := sectionFourW)
    (deepWW := deepWW)
    a c p.ambient conditions' hp' hequal'
  simpa only [p', hproblem] using H

end Laws

end BONG.GoodBONG

end Bong
