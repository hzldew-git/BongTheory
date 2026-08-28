/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightNormalizedRaw

/-!
# Abstract common-adjunction certificate for O'Meara 93:28, Step 8

The concrete 93:21 splitting and common adjunction are hidden behind a short
certificate.  Besides the 93:28 hypotheses it exposes only the scale orders
and the integral cancellation back to the raw Step-8 pair.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

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

/-- The common-adjunction stage of Step 8, with its concrete carrier hidden. -/
structure Omeara9328StepEightCommonCore
    (S : Omeara9328RankFourReductionSystem J H)
    (E : S.StepEightCase) where
  sourceCarrier : Type u
  [sourceAddCommGroup : AddCommGroup sourceCarrier]
  [sourceModule : Module K sourceCarrier]
  targetCarrier : Type u
  [targetAddCommGroup : AddCommGroup targetCarrier]
  [targetModule : Module K targetCarrier]
  sourceForm : QuadraticSpace K sourceCarrier
  targetForm : QuadraticSpace K targetCarrier
  sourceLattice : Lattice K sourceCarrier
  targetLattice : Lattice K targetCarrier
  sourceJordan : JordanDecomposition sourceForm sourceLattice (n + 3)
  targetJordan : JordanDecomposition targetForm targetLattice (n + 3)
  ambient : sourceForm.IsIsometric targetForm
  sourceSaturated : sourceJordan.IsSaturated
  targetSaturated : targetJordan.IsSaturated
  fundamentalType : SameFundamentalType sourceJordan targetJordan
  choice : FundamentalNormGeneratorChoice sourceJordan
  conditions : sourceJordan.Omeara9328ConditionsWith targetJordan choice
  componentRank_atLeastTwo : ∀ i, 2 ≤ sourceJordan.componentRank i
  scaleOrder_eq_raw : ∀ i,
    ordUnit K (sourceJordan.scaleGenerator i) =
      ordUnit K ((E.rawSource S).scaleGenerator i)

namespace Omeara9328RankFourReductionSystem.StepEightCase

/-- Construct the abstract common-adjunction certificate from 93:21. -/
set_option maxHeartbeats 1000000 in
-- The constructor checks the concrete common adjunction and two cancellation layers.
noncomputable def commonCore
    (S : Omeara9328RankFourReductionSystem J H)
    (ambient : q.IsIsometric r)
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith S.targetJordan A)
    (E : S.StepEightCase) : Omeara9328StepEightCommonCore S E := by
  let EJ := E.rawSource S
  let EH := E.rawTarget S
  let EJS := E.stableSource S
  let EHS := E.stableTarget S
  let FS := E.stableFundamentalType S
  let AS := E.stableChoice S A
  let CS := E.stableConditions S A conditions
  let P := EJS.saturatedJordanOfComponentRanksAtLeastThreeNonempty
    (E.stableComponentRank_atLeastThree S)
  let hP : P.IsSaturated :=
    EJS.saturatedJordanOfComponentRanksAtLeastThreeNonempty_isSaturated
      (E.stableComponentRank_atLeastThree S)
  let FPJ : SameFundamentalType P EJS :=
    (SameFundamentalType.saturatedJordanOfComponentRanksAtLeastThreeNonempty
      EJS (E.stableComponentRank_atLeastThree S)).symm
  let FPH : SameFundamentalType P EHS := FPJ.trans FS
  let CJ := P.commonAdjunctionJordan EJS FPJ hP
  let CH := P.commonAdjunctionJordan EHS FPH hP
  let FC : SameFundamentalType CJ CH := FPJ.commonAdjunction FPH FS hP
  let AC : FundamentalNormGeneratorChoice CJ := AS.commonAdjunction FPJ hP
  let CC : CJ.Omeara9328ConditionsWith CH AC :=
    omeara9328ConditionsWith_commonAdjunction FPJ FPH AS hP CS
  have hCJ : CJ.IsSaturated :=
    P.commonAdjunctionJordan_isSaturated EJS FPJ hP
  have hCH : CH.IsSaturated :=
    P.commonAdjunctionJordan_isSaturated EHS FPH hP
  have hrankCJ : ∀ i, 2 ≤ CJ.componentRank i := by
    intro i
    change 2 ≤ (P.commonAdjunctionJordan EJS FPJ hP).componentRank i
    rw [commonAdjunctionJordan_componentRank]
    have hi := E.stableComponentRank_atLeastThree S i
    omega
  let ambientC := FPJ.commonAdjunctionAmbientIsometry FPH hP
    (E.stableAmbient S ambient)
  refine {
    sourceCarrier := BONG.BlockProductSpace (n + 2)
      (P.commonAdjunctionCarrier EJS)
    sourceAddCommGroup := inferInstance
    sourceModule := inferInstance
    targetCarrier := BONG.BlockProductSpace (n + 2)
      (P.commonAdjunctionCarrier EHS)
    targetAddCommGroup := inferInstance
    targetModule := inferInstance
    sourceForm := BONG.blockOrthogonalForm (n + 2)
      (P.commonAdjunctionCarrier EJS) (P.commonAdjunctionForm EJS)
    targetForm := BONG.blockOrthogonalForm (n + 2)
      (P.commonAdjunctionCarrier EHS) (P.commonAdjunctionForm EHS)
    sourceLattice := BONG.blockProductLattice (n + 2)
      (P.commonAdjunctionCarrier EJS) (P.commonAdjunctionLattice EJS)
    targetLattice := BONG.blockProductLattice (n + 2)
      (P.commonAdjunctionCarrier EHS) (P.commonAdjunctionLattice EHS)
    sourceJordan := CJ
    targetJordan := CH
    ambient := ambientC
    sourceSaturated := hCJ
    targetSaturated := hCH
    fundamentalType := FC
    choice := AC
    conditions := CC
    componentRank_atLeastTwo := hrankCJ
    scaleOrder_eq_raw := ?_ }
  intro i
  calc
    ordUnit K (CJ.scaleGenerator i) = ordUnit K (P.scaleGenerator i) :=
      congrArg (ordUnit K)
        (P.commonAdjunctionJordan_scaleGenerator EJS FPJ hP i)
    _ = ordUnit K (EJS.scaleGenerator i) :=
      (FPJ.scaleGenerator_order_eq_sameIndex i).symm
    _ = ordUnit K (EJ.scaleGenerator i) :=
      congrArg (ordUnit K) (EJ.saturationStableJordan_scaleGenerator i)

end Omeara9328RankFourReductionSystem.StepEightCase
end Lattice.JordanDecomposition

end Bong
