/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328ScaleSpreadInduction
import Bong.Lattice.OmearaCommonAdjunctionCancellation
import Bong.Lattice.Omeara9328StabilizationCancellation

/-!
# General reduction for the sufficiency half of O'Meara 93:28

For arbitrary Jordan splittings, Step 2 first adjoins two hyperbolic planes
at every scale, chooses the saturated splitting supplied by 93:21, and
adjoins that same splitting to both sides.  The resulting pair is saturated,
satisfies the same three conditions, and has components of rank at least
two.  Classification of that pair therefore descends by common-adjunction
and stabilization cancellation to the original lattices.
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

/-- A closed saturated problem together with integral descent to the
original arbitrary pair. -/
structure Omeara9328GeneralReduction
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2)) where
  problem : Omeara9328SaturatedProblem (K := K)
  unwind : problem.Solution → Isometry q r L M

set_option maxHeartbeats 2000000 in
/-- Execute O'Meara 93:28, Step 2, using only the saturated splitting
constructed from 93:21. -/
noncomputable def omeara9328GeneralReduction
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2))
    (ambient : q.IsIsometric r)
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (conditions : J.Omeara9328ConditionsWith H A) :
    Omeara9328GeneralReduction J H := by
  let JS := J.saturationStableJordan
  let HS := H.saturationStableJordan
  let FS := F.saturationStable
  let AS := A.saturationStable
  let CS := omeara9328ConditionsWith_saturationStable F A conditions
  have hrankJS : ∀ i, 3 ≤ JS.componentRank i := by
    intro i
    change 3 ≤ J.saturationStableJordan.componentRank i
    rw [J.saturationStableJordan_componentRank]
    have hpos := J.component_finrank_pos i
    change 0 < J.componentRank i at hpos
    omega
  let P := JS.saturatedJordanOfComponentRanksAtLeastThreeNonempty hrankJS
  let hP : P.IsSaturated :=
    JS.saturatedJordanOfComponentRanksAtLeastThreeNonempty_isSaturated hrankJS
  let FPJ : SameFundamentalType P JS :=
    (SameFundamentalType.saturatedJordanOfComponentRanksAtLeastThreeNonempty
      JS hrankJS).symm
  let FPH : SameFundamentalType P HS := FPJ.trans FS
  let CJ := P.commonAdjunctionJordan JS FPJ hP
  let CH := P.commonAdjunctionJordan HS FPH hP
  let FC : SameFundamentalType CJ CH := FPJ.commonAdjunction FPH FS hP
  let AC : FundamentalNormGeneratorChoice CJ := AS.commonAdjunction FPJ hP
  let CC : CJ.Omeara9328ConditionsWith CH AC :=
    omeara9328ConditionsWith_commonAdjunction FPJ FPH AS hP CS
  have hCJ : CJ.IsSaturated :=
    P.commonAdjunctionJordan_isSaturated JS FPJ hP
  have hCH : CH.IsSaturated :=
    P.commonAdjunctionJordan_isSaturated HS FPH hP
  have hrankCJ : ∀ i, 2 ≤ CJ.componentRank i := by
    intro i
    change 2 ≤ (P.commonAdjunctionJordan JS FPJ hP).componentRank i
    rw [commonAdjunctionJordan_componentRank]
    have hi : 3 ≤ JS.componentRank i := hrankJS i
    omega
  let ambientS := F.saturationStableAmbientIsometry ambient
  let ambientC := FPJ.commonAdjunctionAmbientIsometry FPH hP ambientS
  refine {
    problem := {
      sourceCarrier := BONG.BlockProductSpace (n + 1)
        (P.commonAdjunctionCarrier JS)
      sourceAddCommGroup := inferInstance
      sourceModule := inferInstance
      targetCarrier := BONG.BlockProductSpace (n + 1)
        (P.commonAdjunctionCarrier HS)
      targetAddCommGroup := inferInstance
      targetModule := inferInstance
      sourceForm := BONG.blockOrthogonalForm (n + 1)
        (P.commonAdjunctionCarrier JS) (P.commonAdjunctionForm JS)
      targetForm := BONG.blockOrthogonalForm (n + 1)
        (P.commonAdjunctionCarrier HS) (P.commonAdjunctionForm HS)
      sourceLattice := BONG.blockProductLattice (n + 1)
        (P.commonAdjunctionCarrier JS) (P.commonAdjunctionLattice JS)
      targetLattice := BONG.blockProductLattice (n + 1)
        (P.commonAdjunctionCarrier HS) (P.commonAdjunctionLattice HS)
      componentPred := n + 1
      sourceJordan := CJ
      targetJordan := CH
      ambient := ambientC
      sourceSaturated := hCJ
      targetSaturated := hCH
      fundamentalType := FC
      choice := AC
      conditions := CC
      componentRank_atLeastTwo := hrankCJ }
    unwind := ?_ }
  intro f
  let stableIsometry := P.cancelCommonAdjunction JS HS FPJ FPH hP f
  exact isometryOfSaturationStableJordanIsometry J H F stableIsometry

/-- Unconditional sufficiency of O'Meara 93:28 for a chosen coherent family
of fundamental norm generators. -/
noncomputable def omeara9328SufficiencyWith
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2))
    (ambient : q.IsIsometric r)
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (conditions : J.Omeara9328ConditionsWith H A) :
    Isometry q r L M := by
  let R := omeara9328GeneralReduction J H ambient F A conditions
  exact R.unwind R.problem.solve

end Lattice.JordanDecomposition

end Bong
