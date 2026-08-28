/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328HeadAlignedReduction

/-!
# Named raw and stabilized data for O'Meara 93:28, Step 8

The exceptional branch is deliberately factored into opaque named
constructions.  This keeps later dependent carrier types small and prevents
the elaborator from repeatedly expanding the entire Step-8 pipeline.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition
namespace Omeara9328RankFourReductionSystem.StepEightCase

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {W : Type u} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}
  (S : Omeara9328RankFourReductionSystem J H)

/-- The intrinsic Step-8 case gives the raw first scale gap. -/
theorem sourceScaleGap (E : S.StepEightCase) :
    1 < ordUnit K (S.sourceJordan.scaleGenerator 1) -
      ordUnit K (S.sourceJordan.scaleGenerator 0) := by
  have hrelative := S.relativeSecondScale_order
  simpa only [fundamentalScaleOrder] using hrelative.symm ▸ E.scaleGap_gt_one

/-- Source raw Step-8 splitting. -/
noncomputable def rawSource (E : S.StepEightCase) :=
  S.sourceJordan.stepEightJordan (E.sourceScaleGap S)

/-- Target raw Step-8 splitting aligned to the source scale generators. -/
noncomputable def rawTarget (E : S.StepEightCase) :=
  S.residualFundamentalType.targetStepEightJordan (E.sourceScaleGap S)

/-- Complete fundamental type of the raw Step-8 pair. -/
noncomputable def rawFundamentalType (E : S.StepEightCase) :=
  S.residualFundamentalType.stepEight S.sourceJordan_isSaturated
    S.targetJordan_isSaturated (E.sourceScaleGap S)

/-- Coherent source norm generators after Step 8. -/
noncomputable def rawChoice
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (E : S.StepEightCase) :=
  S.sourceJordan.stepEightFundamentalNormGeneratorChoice A
    S.sourceJordan_isSaturated (E.sourceScaleGap S)
      E.normGap_atLeastTwo E.firstNorm_below_twoScale

/-- The three 93:28 conditions after Step 8. -/
theorem rawConditions
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith S.targetJordan A)
    (E : S.StepEightCase) :
    (E.rawSource S).Omeara9328ConditionsWith (E.rawTarget S)
      (E.rawChoice S A) :=
  S.residualFundamentalType.omeara9328ConditionsWith_stepEight A
    S.sourceJordan_isSaturated (E.sourceScaleGap S)
      E.normGap_atLeastTwo E.firstNorm_below_twoScale conditions

/-- Ambient isometry of the raw Step-8 pair. -/
theorem rawAmbient
    (ambient : q.IsIsometric r) (E : S.StepEightCase) :
    (BONG.blockOrthogonalForm (n + 2)
      S.sourceJordan.stepEightCarrier
      S.sourceJordan.stepEightForm).IsIsometric
      (BONG.blockOrthogonalForm (n + 2)
        S.targetJordan.stepEightCarrier
        S.targetJordan.stepEightForm) := by
  let residualAmbient :
      (BONG.blockOrthogonalForm (n + 1)
        S.sourceCarrier S.sourceForm).IsIsometric
        (BONG.blockOrthogonalForm (n + 1)
          S.targetCarrier S.targetForm) :=
    ⟨S.residualAmbientIsometry ambient⟩
  exact S.residualFundamentalType.stepEightAmbientIsometry residualAmbient

/-- Stabilized source of the raw Step-8 pair. -/
noncomputable def stableSource (E : S.StepEightCase) :=
  (E.rawSource S).saturationStableJordan

/-- Stabilized target of the raw Step-8 pair. -/
noncomputable def stableTarget (E : S.StepEightCase) :=
  (E.rawTarget S).saturationStableJordan

/-- Complete fundamental type after stabilization. -/
noncomputable def stableFundamentalType (E : S.StepEightCase) :=
  (E.rawFundamentalType S).saturationStable

/-- Coherent source norm generators after stabilization. -/
noncomputable def stableChoice
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (E : S.StepEightCase) :=
  (E.rawChoice S A).saturationStable

/-- The three 93:28 conditions after stabilization. -/
theorem stableConditions
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith S.targetJordan A)
    (E : S.StepEightCase) :
    (E.stableSource S).Omeara9328ConditionsWith (E.stableTarget S)
      (E.stableChoice S A) :=
  omeara9328ConditionsWith_saturationStable (E.rawFundamentalType S)
    (E.rawChoice S A) (E.rawConditions S A conditions)

/-- Ambient isometry after stabilization. -/
theorem stableAmbient
    (ambient : q.IsIsometric r) (E : S.StepEightCase) :
    (BONG.blockOrthogonalForm (n + 2)
      (E.rawSource S).saturationStableCarrier
      (E.rawSource S).saturationStableForm).IsIsometric
      (BONG.blockOrthogonalForm (n + 2)
        (E.rawTarget S).saturationStableCarrier
        (E.rawTarget S).saturationStableForm) :=
  (E.rawFundamentalType S).saturationStableAmbientIsometry (E.rawAmbient S ambient)

/-- Every stabilized Step-8 component has rank at least three. -/
theorem stableComponentRank_atLeastThree (E : S.StepEightCase) :
    ∀ i, 3 ≤ (E.stableSource S).componentRank i := by
  intro i
  change 3 ≤ (E.rawSource S).saturationStableJordan.componentRank i
  rw [saturationStableJordan_componentRank]
  omega

end Omeara9328RankFourReductionSystem.StepEightCase
end Lattice.JordanDecomposition

end Bong
