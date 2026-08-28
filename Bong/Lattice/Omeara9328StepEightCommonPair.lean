/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightSaturated

/-!
# Abstract common-adjunction pair in O'Meara 93:28, Step 8

The concrete componentwise product has very large inferred type-class terms.
This structure gives its two carriers, forms, lattices, and Jordan splittings
stable names.  Subsequent theorem statements can therefore expose the actual
mathematics without repeatedly expanding the dependent products.
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

/-- The two concrete common-adjunction splittings, with their dependent
ambient carriers hidden behind projections. -/
structure Omeara9328StepEightCommonPair (m : Nat) where
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
  sourceJordan : JordanDecomposition sourceForm sourceLattice m
  targetJordan : JordanDecomposition targetForm targetLattice m

namespace Omeara9328RankFourReductionSystem.StepEightCase

/-- Package the saturated common adjunction of the stabilized Step-8 pair. -/
noncomputable def commonPair
    (S : Omeara9328RankFourReductionSystem J H)
    (E : S.StepEightCase) :
    Omeara9328StepEightCommonPair (K := K) (n + 3) := by
  let P := E.saturatedSource S
  let EJS := E.stableSource S
  let EHS := E.stableTarget S
  let FPJ := E.saturatedToStable S
  let FPH := E.saturatedToTarget S
  let hP := E.saturatedSource_isSaturated S
  exact {
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
    sourceJordan := P.commonAdjunctionJordan EJS FPJ hP
    targetJordan := P.commonAdjunctionJordan EHS FPH hP }

/-- Named additive structure on the packaged source carrier. -/
noncomputable instance commonPairSourceAddCommGroup
    (S : Omeara9328RankFourReductionSystem J H) (E : S.StepEightCase) :
    AddCommGroup (E.commonPair S).sourceCarrier :=
  (E.commonPair S).sourceAddCommGroup

/-- Named module structure on the packaged source carrier. -/
noncomputable instance commonPairSourceModule
    (S : Omeara9328RankFourReductionSystem J H) (E : S.StepEightCase) :
    Module K (E.commonPair S).sourceCarrier :=
  (E.commonPair S).sourceModule

/-- Named additive structure on the packaged target carrier. -/
noncomputable instance commonPairTargetAddCommGroup
    (S : Omeara9328RankFourReductionSystem J H) (E : S.StepEightCase) :
    AddCommGroup (E.commonPair S).targetCarrier :=
  (E.commonPair S).targetAddCommGroup

/-- Named module structure on the packaged target carrier. -/
noncomputable instance commonPairTargetModule
    (S : Omeara9328RankFourReductionSystem J H) (E : S.StepEightCase) :
    Module K (E.commonPair S).targetCarrier :=
  (E.commonPair S).targetModule

end Omeara9328RankFourReductionSystem.StepEightCase
end Lattice.JordanDecomposition

end Bong
