/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma912Profile
import Bong.Bong.Beli2019Lemma96DeltaScaling
import Bong.Bong.Beli2019Lemma96InputAssembly
import Bong.Bong.Beli2019Corollary311

/-!
# Beli (2019), Lemma 9.6: the printed v2 hypothesis gives the recursive input

The v2 statement of Lemma 9.6 is expressed only in terms of the first three
orders, the critical first gap, the capped defect, and anisotropy.  The proof
may replace the target good BONG by its critical `Delta`-scaled version.  This
file transports all numerical and representation data across that replacement
and assembles the literal `Lemma96Input` consumed by the Section 9 induction.
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

set_option maxHeartbeats 2400000 in
-- The proof elaborates the full head-normalization and projected-tail chain.
/-- The hypotheses printed in the v2 statement of Lemma 9.6 produce the
concrete projected-tail input used by the well-founded induction.

The target BONG stored in the input is allowed to be the `Delta`-scaled BONG
constructed in the square branch.  It is a good BONG of the same target
lattice, so Corollary 3.11 transports all four representation conditions.
-/
theorem exists_beli2019Lemma96Input_v2Hypothesis
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
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c (Nat.le_refl (N + 4)))
    (hlemma96 : a.Beli2019Lemma96V2Hypothesis c) :
    Nonempty (Beli2019RepresentationProblem.Lemma96Input
      (Beli2019RepresentationProblem.ofData a c (Nat.le_refl (N + 4))
        ambient conditions)) := by
  rcases hlemma96 with
    ⟨houter, hfirst, hfirstGap, hdefect, hanisotropic⟩
  have hfirstGap' :
      a.order (1 : Fin (N + 5)) - a.order (0 : Fin (N + 5)) =
        2 * (ramificationIndex K : Int) - 2 := by
    exact hfirstGap
  have horders := a.beli2019Lemma96_initialOrderConsequences
    (targetLaws := targetAlpha) (sourceLaws := sourceAlpha)
    c (by omega) ⟨houter, hfirst⟩ hdefect
  have hzeroIndex :
      (⟨0, by omega⟩ : Fin (N + 5)) = (0 : Fin (N + 5)) := by
    apply Fin.ext
    simp
  have honeIndex :
      (⟨1, by omega⟩ : Fin (N + 5)) = (1 : Fin (N + 5)) := by
    apply Fin.ext
    change 1 = 1 % (N + 5)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hthreeIndex :
      (⟨3, by omega⟩ : Fin (N + 5)) = (3 : Fin (N + 5)) := by
    apply Fin.ext
    change 3 = 3 % (N + 5)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        c.order (1 : Fin (N + 5)) - c.order (0 : Fin (N + 5)) := by
    letI : Beli2006AlphaLaws.{u, w} K := sourceAlpha
    simpa only [hzeroIndex, honeIndex] using
      a.lemma96_sourceFirstGap_ge_twoE c (by omega) hdefect
  have hfourth :
      a.order (0 : Fin (N + 5)) + 2 * (ramificationIndex K : Int) ≤
        a.order (3 : Fin (N + 5)) := by
    simpa only [hthreeIndex] using horders.targetFourthOrder_ge
  rcases a.beli2019Lemma96_headReduction
      (targetAlpha := targetAlpha) (sourceAlpha := sourceAlpha)
      (modelAlpha := modelAlpha)
      (modelClassification := modelClassification)
      (targetClassification := targetClassification)
      c conditions houter hfirstGap' hfirst.symm hdefect hanisotropic with
    ⟨D⟩
  have houterD :
      D.targetBONG.order (0 : Fin (N + 5)) =
        D.targetBONG.order (2 : Fin (N + 5)) := by
    rw [← D.sameOrders (0 : Fin (N + 5)),
      ← D.sameOrders (2 : Fin (N + 5))]
    exact houter
  have hfirstGapD :
      D.targetBONG.order (1 : Fin (N + 5)) -
          D.targetBONG.order (0 : Fin (N + 5)) =
        2 * (ramificationIndex K : Int) - 2 := by
    rw [← D.sameOrders (1 : Fin (N + 5)),
      ← D.sameOrders (0 : Fin (N + 5))]
    exact hfirstGap'
  have hfourthD :
      D.targetBONG.order (0 : Fin (N + 5)) +
          2 * (ramificationIndex K : Int) ≤
        D.targetBONG.order (3 : Fin (N + 5)) := by
    rw [← D.sameOrders (0 : Fin (N + 5)),
      ← D.sameOrders (3 : Fin (N + 5))]
    exact hfourth
  have hsourceFirstOrderD :
      c.order (0 : Fin (N + 5)) =
        D.targetBONG.order (0 : Fin (N + 5)) :=
    hfirst.symm.trans (D.sameOrders (0 : Fin (N + 5)))
  have conditionsD : RepresentationConditions D.targetBONG c
      (Nat.le_refl (N + 4)) :=
    (a.representationConditions_changeBONG_iff
      (classificationV := targetClassification)
      (classificationW := sourceClassification)
      D.targetBONG c c (Nat.le_refl (N + 4))).mp conditions
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
      (Nat.le_refl (N + 4)) ambient conditions)
    (targetLaws := targetAlpha) (sourceLaws := sourceAlpha)
    (N + 1) (by rfl) (by rfl) D.targetBONG c conditionsD
      D.matchedNormalForm S houterD hfirstGapD hfourthD
      hsourceFirstOrderD hsourceFirstGap hdefectD⟩

end BONG.GoodBONG

end Bong
