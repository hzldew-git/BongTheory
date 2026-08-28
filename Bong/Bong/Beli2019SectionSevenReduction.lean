/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionSevenEqualGapCommonSpace
import Bong.Bong.Beli2019SectionSevenStrictCommonSpace
import Bong.Bong.Beli2019RepresentationProblemReindex

/-!
# Beli (2019), Section 7: the complete positive-rank reduction

For equal-rank lattices of rank at least three, Section 7 either reaches
equal norm ideals or replaces the target by a strict sublattice.  The latter
case is split exactly as in the paper according to whether the first order
gap is `-2e`.
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

section Laws

variable
    [defect : QuadraticDefectLaws K]
    [perfect : PerfectResidueFieldLaws K]
    [disc : DyadicDiscriminantClassLaws K]
    [unramified : DyadicUnramifiedNormLaws K]
    [residueDefect : DyadicResidueDefectProductLaws K]
    [hilbertChoice : DyadicHilbertDefectChoiceLaws K]
    [unitParity : UnitQuadraticDefectParityLaws K]
    [unitSpectrum : DyadicUnitDefectSpectrumLaws K]
    [hilbert : HilbertSymbolLaws K]
    [diagonal : DyadicDiagonalClassificationLaws K]
    [structuralModel : BONGStructuralLaws.{u, u} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [goodExistenceModel : BONGGoodExistenceLaws.{u, u} K]
    [weight : Beli2009WeightIdealData.{u, u} K]
    [unaryBinary : Beli2019UnaryBinaryJordanLaws.{u} K]
    [jordanOrder : Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaModel : Beli2006AlphaLaws.{u, u} K]
    [constructionModel : BeliLemma43ConstructionLaws.{u, u} K]
    [sectionTwoModel : Beli2006SectionTwoLaws.{u, u} K]
    [classificationModel : GoodBONGClassificationLaws.{u, u, u} K]
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [constructionV : BeliLemma43ConstructionLaws.{u, v} K]
    [sectionTwoV : Beli2006SectionTwoLaws.{u, v} K]
    [sectionFourV : BONGReverseDualLaws.{u, v} K]
    [corollary44V : BeliCorollary44Laws.{u, v} K]
    [binaryLocal : BinaryNormGeneratorLocalLaws.{u, v} K]
    [lemma49 : BeliLemma49Laws.{u, v} K]
    [towerRepresentation :
      DyadicAlternatingEndpointTowerRepresentationLaws K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [lemma310 : Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [Beli2019SectionFiveLaws.{u, v} K]
    [Beli2019SectionFourLaws.{u, v} K]

/-- Section 7 in the disjunctive form used by the final well-founded
induction.  The first disjunct is the literal equality of norm ideals; the
second contains an actual smaller counterexample obtained from a strict
target sublattice. -/
theorem sectionSeven_equalNorm_or_counterexampleDescent
    (a : GoodBONG q L (n + 3)) (b : GoodBONG r M (n + 3))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b le_rfl)
    (hp : (Beli2019RepresentationProblem.ofData
      a b le_rfl ambient conditions).Counterexample) :
    (Beli2019RepresentationProblem.ofData
      a b le_rfl ambient conditions).EqualNorm ∨
      ∃ next, next.Counterexample ∧
        next.sourceIndex = next.targetIndex ∧
        Beli2019ProblemSmaller Beli2019RepresentationProblem.measure next
          (Beli2019RepresentationProblem.ofData
            a b le_rfl ambient conditions) := by
  let p := Beli2019RepresentationProblem.ofData
    a b le_rfl ambient conditions
  by_cases hequal : p.EqualNorm
  · exact Or.inl hequal
  · right
    let i0 : Fin (n + 3) := ⟨0, by omega⟩
    have hzero : i0 = (0 : Fin (n + 3)) := by
      apply Fin.ext
      simp [i0]
    have hfirstLe : a.order i0 ≤ b.order i0 := by
      rcases conditions.orderCondition i0 with h | h
      · exact h
      · rcases h with ⟨hpos, _⟩
        change 0 < i0.val at hpos
        simp only [i0] at hpos
        omega
    have hfirstNe : a.order i0 ≠ b.order i0 := by
      intro hfirst
      apply hequal
      unfold p Beli2019RepresentationProblem.EqualNorm
      change Lattice.normIdeal q L = Lattice.normIdeal r M
      rw [a.toBONG.normIdeal_eq_powerIdeal_order_zero,
        b.toBONG.normIdeal_eq_powerIdeal_order_zero]
      rw [hzero] at hfirst
      change a.toBONG.order 0 = b.toBONG.order 0 at hfirst
      rw [hfirst]
    have hfirstLt : a.order i0 < b.order i0 :=
      lt_of_le_of_ne hfirstLe hfirstNe
    have hfirstLtZero : a.order (0 : Fin (n + 3)) <
        b.order (0 : Fin (n + 3)) := by
      simpa only [hzero] using hfirstLt
    have hnorm : Lattice.normIdeal r M < Lattice.normIdeal q L := by
      rw [a.toBONG.normIdeal_eq_powerIdeal_order_zero,
        b.toBONG.normIdeal_eq_powerIdeal_order_zero,
        Lattice.powerIdeal_lt_iff]
      exact hfirstLtZero
    by_cases hgap : a.order (1 : Fin (n + 3)) -
        a.order (0 : Fin (n + 3)) =
          -(2 * (ramificationIndex K : Int))
    · rcases exists_sectionSevenEqualGapSublatticeReduction_of_ambient
          (defect := defect) (perfect := perfect) (laws := disc)
          (unramified := unramified) (residueDefect := residueDefect)
          (hilbertChoice := hilbertChoice) (unitParity := unitParity)
          (unitSpectrum := unitSpectrum) (hilbert := hilbert)
          (diagonal := diagonal)
          (structuralModel := structuralModel)
          (weight := weight) (unaryBinary := unaryBinary)
          (jordanOrder := jordanOrder) (alphaModel := alphaModel)
          (constructionModel := constructionModel)
          (sectionTwoModel := sectionTwoModel)
          (classificationModel := classificationModel)
          (alphaV := alphaV) (parityV := parityV)
          (constructionV := constructionV) (sectionTwoV := sectionTwoV)
          (sectionFourV := sectionFourV) (corollary44V := corollary44V)
          (binaryLocal := binaryLocal) (lemma49 := lemma49)
          (towerRepresentation := towerRepresentation)
          (classificationV := classificationV) (lemma310 := lemma310)
          a b ambient conditions hgap hnorm with ⟨R⟩
      exact ⟨R.next, R.nextCounterexample p hp, rfl, R.smaller⟩
    · let R := sectionSevenStrictIndexPReduction_of_ambient
          (n := n + 1) a b ambient conditions hgap hnorm
      exact ⟨R.next, R.nextCounterexample p hp, rfl, R.smaller⟩

/-- Bundled form of the complete Section 7 reduction.  The only rank
requirement is the literal one used by the construction: common rank at
least three. -/
theorem sectionSeven_equalNorm_or_counterexampleDescent_of_problem
    (p : Beli2019RepresentationProblem.{u, v, w} K)
    (hindex : p.sourceIndex = p.targetIndex)
    (hrank : 2 ≤ p.sourceIndex) (hp : p.Counterexample) :
    p.EqualNorm ∨
      ∃ next, next.Counterexample ∧
        next.sourceIndex = next.targetIndex ∧
        Beli2019ProblemSmaller Beli2019RepresentationProblem.measure
          next p := by
  letI : AddCommGroup p.Target := p.targetAddCommGroup
  letI : Module K p.Target := p.targetModule
  letI : AddCommGroup p.Source := p.sourceAddCommGroup
  letI : Module K p.Source := p.sourceModule
  let t := p.sourceIndex - 2
  have hsource : p.sourceIndex = t + 2 := by
    dsimp only [t]
    omega
  have htarget : p.targetIndex = t + 2 := by omega
  let a := p.targetBONG.castLength
    (show p.targetIndex + 1 = t + 3 by omega)
  let b := p.sourceBONG.castLength
    (show p.sourceIndex + 1 = t + 3 by omega)
  let conditions' :=
    Beli2019RepresentationProblem.representationConditions_castIndices
      p.targetBONG p.sourceBONG p.rankBound p.conditions htarget hsource
  let p' := Beli2019RepresentationProblem.ofData a b
    (Nat.le_refl (t + 2)) p.ambient conditions'
  have hproblem : p' = p := by
    dsimp only [p', a, b, conditions']
    exact (Beli2019RepresentationProblem.ofData_castIndices_eq
      p.targetBONG p.sourceBONG p.rankBound p.ambient p.conditions
        htarget hsource).trans
      (Beli2019RepresentationProblem.ofData_self p)
  have hp' : p'.Counterexample := by
    rwa [hproblem]
  have H := sectionSeven_equalNorm_or_counterexampleDescent
    (K := K) (V := p.Target) (W := p.Source)
    (q := p.targetQ) (r := p.sourceQ)
    (L := p.targetLattice) (M := p.sourceLattice) (n := t)
    (defect := defect) (perfect := perfect) (disc := disc)
    (unramified := unramified) (residueDefect := residueDefect)
    (hilbertChoice := hilbertChoice) (unitParity := unitParity)
    (unitSpectrum := unitSpectrum) (hilbert := hilbert)
    (diagonal := diagonal) (structuralModel := structuralModel)
    (structuralV := structuralV)
    (goodExistenceModel := goodExistenceModel)
    (weight := weight) (unaryBinary := unaryBinary)
    (jordanOrder := jordanOrder) (alphaModel := alphaModel)
    (constructionModel := constructionModel)
    (sectionTwoModel := sectionTwoModel)
    (classificationModel := classificationModel)
    (alphaV := alphaV) (parityV := parityV)
    (constructionV := constructionV) (sectionTwoV := sectionTwoV)
    (sectionFourV := sectionFourV) (corollary44V := corollary44V)
    (binaryLocal := binaryLocal) (lemma49 := lemma49)
    (towerRepresentation := towerRepresentation)
    (classificationV := classificationV) (lemma310 := lemma310)
    a b p.ambient conditions' hp'
  simpa only [p', hproblem] using H

end Laws

end BONG.GoodBONG

end Bong
