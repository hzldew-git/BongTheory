/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightReductionScale

/-!
# Head-aligned reductions for O'Meara 93:28

This structure is the short interface consumed by the scale-spread
recursion.  A reduction supplies a saturated head-aligned pair, proves that
deleting its head strictly lowers the original scale spread, and records how
an isometry of the aligned pair descends to the original pair.
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

/-- A head-aligned classification problem of smaller scale spread together
with the integral descent back to the original lattices. -/
structure Omeara9328HeadAlignedData
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2)) where
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
  nextN : Nat
  sourceJordan : JordanDecomposition sourceForm sourceLattice (nextN + 2)
  targetJordan : JordanDecomposition targetForm targetLattice (nextN + 2)
  ambient : sourceForm.IsIsometric targetForm
  sourceSaturated : sourceJordan.IsSaturated
  targetSaturated : targetJordan.IsSaturated
  fundamentalType : SameFundamentalType sourceJordan targetJordan
  choice : FundamentalNormGeneratorChoice sourceJordan
  conditions : sourceJordan.Omeara9328ConditionsWith targetJordan choice
  head : Isometry (sourceJordan.component 0).space
    (targetJordan.component 0).space (sourceJordan.component 0).lattice
      (targetJordan.component 0).lattice
  componentRank_atLeastTwo : ∀ i, 2 ≤ sourceJordan.componentRank i
  tailScaleSpread_lt : sourceJordan.tail.scaleSpread < J.scaleSpread

/-- A head-aligned data package together with integral descent to the
original pair.  Keeping descent separate makes the Step-8 construction
compile at a clean mathematical boundary. -/
structure Omeara9328HeadAlignedReduction
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2)) where
  toData : Omeara9328HeadAlignedData J H
  unwind :
    letI := toData.sourceAddCommGroup
    letI := toData.sourceModule
    letI := toData.targetAddCommGroup
    letI := toData.targetModule
    Isometry toData.sourceForm toData.targetForm
        toData.sourceLattice toData.targetLattice →
      Isometry q r L M

/-- The branch in which Steps 4--7 have already aligned the first residual
components. -/
noncomputable def Omeara9328RankFourReductionSystem.alignedHeadData
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (S : Omeara9328RankFourReductionSystem J H)
    (ambient : q.IsIsometric r)
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (R : Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A) :
    Omeara9328HeadAlignedData J H where
  sourceCarrier := BONG.BlockProductSpace (n + 1) S.sourceCarrier
  sourceAddCommGroup := inferInstance
  sourceModule := inferInstance
  targetCarrier := BONG.BlockProductSpace (n + 1) S.targetCarrier
  targetAddCommGroup := inferInstance
  targetModule := inferInstance
  sourceForm := BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm
  targetForm := BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm
  sourceLattice := BONG.blockProductLattice (n + 1)
    S.sourceCarrier S.sourceLattice
  targetLattice := BONG.blockProductLattice (n + 1)
    S.targetCarrier S.targetLattice
  nextN := n
  sourceJordan := S.sourceJordan
  targetJordan := R.target
  ambient := ⟨S.residualAmbientIsometry ambient⟩
  sourceSaturated := S.sourceJordan_isSaturated
  targetSaturated := R.saturated
  fundamentalType := R.fundamentalType
  choice := A
  conditions := R.conditions
  head := R.head
  componentRank_atLeastTwo := by
    intro i
    rw [S.sourceJordan_componentRank]
    omega
  tailScaleSpread_lt := by
    calc
      S.sourceJordan.tail.scaleSpread < S.sourceJordan.scaleSpread :=
        S.sourceJordan.tail_scaleSpread_lt
      _ = J.scaleSpread := scaleSpread_eq_of_scaleGenerator_order_eq J
        S.sourceJordan (fun i ↦ by rw [S.sourceJordan_scaleGenerator])

/-- Complete ordinary aligned branch, including descent through the initial
rank-four reduction. -/
noncomputable def Omeara9328RankFourReductionSystem.alignedHeadReduction
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (S : Omeara9328RankFourReductionSystem J H)
    (ambient : q.IsIsometric r)
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (R : Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A) :
    Omeara9328HeadAlignedReduction J H where
  toData := S.alignedHeadData ambient A R
  unwind := S.originalIsometryOfResidualIsometry

end Lattice.JordanDecomposition

end Bong
