/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightCommonBundle

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

/-- Project the established common bundle to the smaller data-only interface. -/
noncomputable def commonCore
    (S : Omeara9328RankFourReductionSystem J H)
    (ambient : q.IsIsometric r)
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith S.targetJordan A)
    (E : S.StepEightCase) : Omeara9328StepEightCommonCore S E := by
  let C := E.commonBundle S
  refine {
    sourceCarrier := C.sourceCarrier
    sourceAddCommGroup := C.sourceAddCommGroup
    sourceModule := C.sourceModule
    targetCarrier := C.targetCarrier
    targetAddCommGroup := C.targetAddCommGroup
    targetModule := C.targetModule
    sourceForm := C.sourceForm
    targetForm := C.targetForm
    sourceLattice := C.sourceLattice
    targetLattice := C.targetLattice
    sourceJordan := C.sourceJordan
    targetJordan := C.targetJordan
    ambient := C.ambientOf ambient
    sourceSaturated := C.sourceSaturated
    targetSaturated := C.targetSaturated
    fundamentalType := C.fundamentalType
    choice := C.choice A
    conditions := C.conditions A conditions
    componentRank_atLeastTwo := C.componentRank_atLeastTwo
    scaleOrder_eq_raw := C.scaleOrder_eq_raw }

end Omeara9328RankFourReductionSystem.StepEightCase
end Lattice.JordanDecomposition

end Bong
