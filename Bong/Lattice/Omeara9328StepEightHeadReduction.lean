/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightBundledReduced

/-!
# The Step-8 head-aligned reduction in O'Meara 93:28

The large concrete adjunctions are sealed in `commonBundle`; this file only
builds the final rank-four residual pair, aligns its head, proves strict
decrease of the scale spread, and composes the certified descent maps.
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

/-- The exceptional Step-8 branch produces an aligned pair whose exact tail
has strictly smaller scale spread. -/
noncomputable def Omeara9328RankFourReductionSystem.stepEightHeadData
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (S : Omeara9328RankFourReductionSystem J H)
    (ambient : q.IsIsometric r)
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith S.targetJordan A)
    (E : S.StepEightCase) : Omeara9328HeadAlignedData J H := by
  let C := E.commonBundle S
  let S₂ := E.bundledReductionSystem S
  let A₂ := E.bundledReducedChoice S A
  let R₂ := E.bundledReducedReplacement S A conditions
  refine {
    sourceCarrier := BONG.BlockProductSpace (n + 2) S₂.sourceCarrier
    sourceAddCommGroup := inferInstance
    sourceModule := inferInstance
    targetCarrier := BONG.BlockProductSpace (n + 2) S₂.targetCarrier
    targetAddCommGroup := inferInstance
    targetModule := inferInstance
    sourceForm := BONG.blockOrthogonalForm (n + 2)
      S₂.sourceCarrier S₂.sourceForm
    targetForm := BONG.blockOrthogonalForm (n + 2)
      S₂.targetCarrier S₂.targetForm
    sourceLattice := BONG.blockProductLattice (n + 2)
      S₂.sourceCarrier S₂.sourceLattice
    targetLattice := BONG.blockProductLattice (n + 2)
      S₂.targetCarrier S₂.targetLattice
    nextN := n + 1
    sourceJordan := S₂.sourceJordan
    targetJordan := R₂.target
    ambient := ⟨S₂.residualAmbientIsometry (C.ambientOf ambient)⟩
    sourceSaturated := S₂.sourceJordan_isSaturated
    targetSaturated := R₂.saturated
    fundamentalType := R₂.fundamentalType
    choice := A₂
    conditions := R₂.conditions
    head := R₂.head
    componentRank_atLeastTwo := ?_
    tailScaleSpread_lt := ?_ }
  · intro i
    rw [S₂.sourceJordan_componentRank]
    omega
  · calc
      S₂.sourceJordan.tail.scaleSpread =
          (E.rawSource S).tail.scaleSpread :=
        E.bundledTail_scaleSpread_eq_raw S
      _ < S.sourceJordan.scaleSpread :=
        S.sourceJordan.stepEightJordan_tail_scaleSpread_lt (E.sourceScaleGap S)
      _ = J.scaleSpread := scaleSpread_eq_of_scaleGenerator_order_eq J
        S.sourceJordan (fun i ↦ by rw [S.sourceJordan_scaleGenerator])

/-- Complete Step-8 branch, including integral descent through the final
rank-four reduction and every preceding adjunction. -/
noncomputable def Omeara9328RankFourReductionSystem.stepEightHeadReduction
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (S : Omeara9328RankFourReductionSystem J H)
    (ambient : q.IsIsometric r)
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith S.targetJordan A)
    (E : S.StepEightCase) : Omeara9328HeadAlignedReduction J H := by
  let C := E.commonBundle S
  let S₂ := E.bundledReductionSystem S
  refine {
    toData := S.stepEightHeadData ambient A conditions E
    unwind := ?_ }
  intro f
  exact C.unwind (S₂.originalIsometryOfResidualIsometry f)

end Lattice.JordanDecomposition

end Bong
