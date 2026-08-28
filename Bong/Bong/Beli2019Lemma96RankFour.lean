/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma96V2Assembly

/-!
# Beli (2019), Lemma 9.6 in rank at least four

The printed hypotheses of Lemma 9.6 only refer to the first four BONG
positions.  This file states them at their natural lower bound `N + 4` and
reuses the already formalized normalization, ternary split, projected tail,
and input assembly.  In particular, the rank-four case has a unary projected
tail and does not require an artificial fifth index.
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

/-- The v2 hypothesis of Lemma 9.6 at its natural rank-four lower bound. -/
def Beli2019Lemma96RankFourHypothesis
    (a : GoodBONG q L (N + 4)) (c : GoodBONG r M (N + 4)) : Prop :=
  a.order (0 : Fin (N + 4)) = a.order (2 : Fin (N + 4)) ∧
    a.order (0 : Fin (N + 4)) = c.order (0 : Fin (N + 4)) ∧
    a.orderGap (0 : Fin (N + 3)) =
      2 * (ramificationIndex K : Int) - 2 ∧
    a.Beli2019Lemma96DefectBound c ∧
    a.Lemma814FirstThreeAnisotropic

set_option maxHeartbeats 2400000 in
-- The proof elaborates the complete normalization and projected-tail chain.
/-- The printed Lemma 9.6 hypothesis produces its recursive input in every
rank `N + 4`, including the four-dimensional boundary. -/
theorem exists_beli2019Lemma96Input_rankFour
    [QuadraticDefectLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicMaximalDefectClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [targetAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceAlpha : Beli2006AlphaLaws.{u, w} K]
    [modelAlpha : Beli2006AlphaLaws.{u, u} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [modelClassification : GoodBONGClassificationLaws.{u, v, u} K]
    [targetClassification : GoodBONGClassificationLaws.{u, v, v} K]
    [sourceClassification : GoodBONGClassificationLaws.{u, w, w} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [BeliCorollary44Laws.{u, v} K]
    (a : GoodBONG q L (N + 4)) (c : GoodBONG r M (N + 4))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c (Nat.le_refl (N + 3)))
    (hlemma96 : a.Beli2019Lemma96RankFourHypothesis c) :
    Nonempty (Beli2019RepresentationProblem.Lemma96Input
      (Beli2019RepresentationProblem.ofData a c (Nat.le_refl (N + 3))
        ambient conditions)) := by
  rcases hlemma96 with
    ⟨houter, hfirst, hfirstGap, hdefect, hanisotropic⟩
  have hfirstGap' :
      a.order (1 : Fin (N + 4)) - a.order (0 : Fin (N + 4)) =
        2 * (ramificationIndex K : Int) - 2 := by
    exact hfirstGap
  have horders := a.beli2019Lemma96_initialOrderConsequences
    (targetLaws := targetAlpha) (sourceLaws := sourceAlpha)
    c (by omega) ⟨houter, hfirst⟩ hdefect
  have hzeroIndex :
      (⟨0, by omega⟩ : Fin (N + 4)) = (0 : Fin (N + 4)) := by
    apply Fin.ext
    simp
  have honeIndex :
      (⟨1, by omega⟩ : Fin (N + 4)) = (1 : Fin (N + 4)) := by
    apply Fin.ext
    change 1 = 1 % (N + 4)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hthreeIndex :
      (⟨3, by omega⟩ : Fin (N + 4)) = (3 : Fin (N + 4)) := by
    apply Fin.ext
    change 3 = 3 % (N + 4)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        c.order (1 : Fin (N + 4)) - c.order (0 : Fin (N + 4)) := by
    letI : Beli2006AlphaLaws.{u, w} K := sourceAlpha
    simpa only [hzeroIndex, honeIndex] using
      a.lemma96_sourceFirstGap_ge_twoE c (by omega) hdefect
  have hfourth :
      a.order (0 : Fin (N + 4)) + 2 * (ramificationIndex K : Int) ≤
        a.order (3 : Fin (N + 4)) := by
    simpa only [hthreeIndex] using horders.targetFourthOrder_ge
  rcases a.beli2019Lemma96_headReduction
      (targetAlpha := targetAlpha) (sourceAlpha := sourceAlpha)
      (modelAlpha := modelAlpha)
      (modelClassification := modelClassification)
      (targetClassification := targetClassification)
      c conditions houter hfirstGap' hfirst.symm hdefect hanisotropic with
    ⟨D⟩
  have houterD :
      D.targetBONG.order (0 : Fin (N + 4)) =
        D.targetBONG.order (2 : Fin (N + 4)) := by
    rw [← D.sameOrders (0 : Fin (N + 4)),
      ← D.sameOrders (2 : Fin (N + 4))]
    exact houter
  have hfirstGapD :
      D.targetBONG.order (1 : Fin (N + 4)) -
          D.targetBONG.order (0 : Fin (N + 4)) =
        2 * (ramificationIndex K : Int) - 2 := by
    rw [← D.sameOrders (1 : Fin (N + 4)),
      ← D.sameOrders (0 : Fin (N + 4))]
    exact hfirstGap'
  have hfourthD :
      D.targetBONG.order (0 : Fin (N + 4)) +
          2 * (ramificationIndex K : Int) ≤
        D.targetBONG.order (3 : Fin (N + 4)) := by
    rw [← D.sameOrders (0 : Fin (N + 4)),
      ← D.sameOrders (3 : Fin (N + 4))]
    exact hfourth
  have hsourceFirstOrderD :
      c.order (0 : Fin (N + 4)) =
        D.targetBONG.order (0 : Fin (N + 4)) :=
    hfirst.symm.trans (D.sameOrders (0 : Fin (N + 4)))
  have conditionsD : RepresentationConditions D.targetBONG c
      (Nat.le_refl (N + 3)) :=
    (a.representationConditions_changeBONG_iff
      (classificationV := targetClassification)
      (classificationW := sourceClassification)
      D.targetBONG c c (Nat.le_refl (N + 3))).mp conditions
  let prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K := by
    exact @prefixChangeLawsOfClassification K _ _ _ _ _
      targetClassification
  let prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K := by
    exact @prefixChangeLawsOfClassification K _ _ _ _ _
      sourceClassification
  have hdefectD : D.targetBONG.Beli2019Lemma96DefectBound c := by
    unfold Beli2019Lemma96DefectBound at hdefect ⊢
    rw [← a.truncatedPrefixDefect_invariant
      (classificationV := targetClassification)
      (classificationW := sourceClassification)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      D.targetBONG c c (-1) 3 1]
    exact hdefect
  rcases D.matchedNormalForm.exists_initialThreeSplit
      houterD hfourthD with ⟨S⟩
  exact ⟨Beli2019RepresentationProblem.Lemma96Input.ofMatchedNormalForm
    (p := Beli2019RepresentationProblem.ofData a c
      (Nat.le_refl (N + 3)) ambient conditions)
    (targetLaws := targetAlpha) (sourceLaws := sourceAlpha)
    N (by rfl) (by rfl) D.targetBONG c conditionsD
      D.matchedNormalForm S houterD hfirstGapD hfourthD
      hsourceFirstOrderD hsourceFirstGap hdefectD⟩

end BONG.GoodBONG

end Bong
