/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328ConditionCancellation
import Bong.Lattice.Omeara9328Sufficiency

/-!
# O'Meara 93:28: necessity and the complete criterion

An arbitrary pair is stabilized, saturated by a common adjunction, reduced
to rank four, and handled by the boundary necessity theorem.  The auxiliary
summands are then cancelled.  The resulting public theorem has no local
classification-law parameter and no saturation or component-rank hypothesis.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- An integral isometry extends through O'Meara's simultaneous paired
hyperbolic stabilization. -/
noncomputable def saturationStableIsometryOfOriginalIsometry
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2))
    (F : SameFundamentalType J H)
    (f : Isometry q r L M) :
    Isometry
      (BONG.blockOrthogonalForm (n + 1) J.saturationStableCarrier
        J.saturationStableForm)
      (BONG.blockOrthogonalForm (n + 1) H.saturationStableCarrier
        H.saturationStableForm)
      (BONG.blockProductLattice (n + 1) J.saturationStableCarrier
        J.saturationStableLattice)
      (BONG.blockProductLattice (n + 1) H.saturationStableCarrier
        H.saturationStableLattice) := by
  let sourceBaseForm := BONG.blockOrthogonalForm (n + 1)
    (fun i => (J.component i).carrier)
    (fun i => (J.component i).space)
  let targetBaseForm := BONG.blockOrthogonalForm (n + 1)
    (fun i => (H.component i).carrier)
    (fun i => (H.component i).space)
  let sourceBaseLattice := BONG.blockProductLattice (n + 1)
    (fun i => (J.component i).carrier)
    (fun i => (J.component i).lattice)
  let targetBaseLattice := BONG.blockProductLattice (n + 1)
    (fun i => (H.component i).carrier)
    (fun i => (H.component i).lattice)
  let gatherJ := gatherPairedHyperbolicBlockProduct
    (fun i => (J.component i).carrier)
    (fun i => (J.component i).space)
    (fun i => (J.component i).lattice)
    J.scaleGenerator
  let gatherH := gatherPairedHyperbolicBlockProduct
    (fun i => (H.component i).carrier)
    (fun i => (H.component i).space)
    (fun i => (H.component i).lattice)
    H.scaleGenerator
  let sourceProduct :=
    BONG.orthogonalDecompositionProductIsometry J.toOrthogonalDecomposition
  let targetProduct :=
    BONG.orthogonalDecompositionProductIsometry H.toOrthogonalDecomposition
  let base : Isometry sourceBaseForm targetBaseForm
      sourceBaseLattice targetBaseLattice :=
    sourceProduct.trans (f.trans targetProduct.symm)
  let extendBase := pairedHyperbolicExtensionIsometry base
    (n + 2) J.scaleGenerator
  let normalizeTarget := pairedHyperbolicExtensionChangeScale
    targetBaseForm targetBaseLattice (n + 2) J.scaleGenerator
      H.scaleGenerator
      (fun i => (F.scaleGenerator_order_eq_sameIndex i).symm)
  exact gatherJ.trans (extendBase.trans (normalizeTarget.trans gatherH.symm))

/-- Adjoin the same saturated lattice componentwise to both sides of an
integral isometry. -/
noncomputable def commonAdjunctionIsometryOfRightIsometry
    {X : Type*} [AddCommGroup X] [Module K X]
    {p : QuadraticSpace K X} {P₀ : Lattice K X}
    (P : JordanDecomposition p P₀ (n + 2))
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2))
    (FPJ : SameFundamentalType P J)
    (FPH : SameFundamentalType P H)
    (hP : P.IsSaturated)
    (f : Isometry q r L M) :
    Isometry
      (BONG.blockOrthogonalForm (n + 1)
        (P.commonAdjunctionCarrier J) (P.commonAdjunctionForm J))
      (BONG.blockOrthogonalForm (n + 1)
        (P.commonAdjunctionCarrier H) (P.commonAdjunctionForm H))
      (BONG.blockProductLattice (n + 1)
        (P.commonAdjunctionCarrier J) (P.commonAdjunctionLattice J))
      (BONG.blockProductLattice (n + 1)
        (P.commonAdjunctionCarrier H) (P.commonAdjunctionLattice H)) := by
  let middle := (Isometry.refl p P₀).orthogonalProductBasic f
  exact (P.commonAdjunctionProductIsometry J).trans <|
    middle.trans (P.commonAdjunctionProductIsometry H).symm

/-- The complete necessity direction of O'Meara 93:28 for arbitrary
Jordan decompositions.  No saturation or component-rank hypothesis remains
in the statement. -/
theorem omeara9328ConditionsWith_of_isometry
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2))
    (A : FundamentalNormGeneratorChoice J)
    (f : Isometry q r L M) :
    J.Omeara9328ConditionsWith H A := by
  let F : SameFundamentalType J H := sameFundamentalTypeOfIsometry J H f
  let JS := J.saturationStableJordan
  let HS := H.saturationStableJordan
  let FS := F.saturationStable
  let AS := A.saturationStable
  let fStable := saturationStableIsometryOfOriginalIsometry J H F f
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
  let FC : SameFundamentalType CJ CH :=
    SameFundamentalType.commonAdjunction
      (P := P) (J := JS) (H := HS) FPJ FPH FS hP
  let AC : FundamentalNormGeneratorChoice CJ := AS.commonAdjunction FPJ hP
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
  let R : Omeara9328RankFourReductionSystem CJ CH :=
    { sourceSaturated := hCJ
      targetSaturated := hCH
      fundamentalType := FC
      componentRank_atLeastTwo := hrankCJ }
  let fCommon := commonAdjunctionIsometryOfRightIsometry
    P JS HS FPJ FPH hP fStable
  have hCommon : CJ.Omeara9328ConditionsWith CH AC :=
    R.conditionsWith_of_isometry fCommon AC
  have hStable : JS.Omeara9328ConditionsWith HS AS :=
    omeara9328ConditionsWith_of_commonAdjunction
      FPJ FPH AS hP hCommon
  exact omeara9328ConditionsWith_of_saturationStable F A hStable

/-- Canonical-generator form of the necessity direction. -/
theorem omeara9328Conditions_of_isometry
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2))
    (f : Isometry q r L M) :
    J.Omeara9328Conditions H := by
  exact (J.omeara9328ConditionsWith_canonical_iff H).1
    (omeara9328ConditionsWith_of_isometry J H
      (canonicalFundamentalNormGeneratorChoice J) f)

/-- O'Meara 93:28 in its coherent chosen-generator form. -/
theorem isIsometric_iff_omeara9328ConditionsWith
    {V₀ W₀ : Type u} [AddCommGroup V₀] [Module K V₀]
    [AddCommGroup W₀] [Module K W₀]
    {q₀ : QuadraticSpace K V₀} {r₀ : QuadraticSpace K W₀}
    {L₀ : Lattice K V₀} {M₀ : Lattice K W₀}
    (J : JordanDecomposition q₀ L₀ (n + 2))
    (H : JordanDecomposition r₀ M₀ (n + 2))
    (ambient : q₀.IsIsometric r₀)
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J) :
    Lattice.IsIsometric q₀ r₀ L₀ M₀ ↔ J.Omeara9328ConditionsWith H A := by
  constructor
  · rintro ⟨f⟩
    exact omeara9328ConditionsWith_of_isometry J H A f
  · intro h
    exact ⟨omeara9328SufficiencyWith J H ambient F A h⟩

/-- O'Meara 93:28 with the canonical fundamental norm generators. -/
theorem isIsometric_iff_omeara9328Conditions
    {V₀ W₀ : Type u} [AddCommGroup V₀] [Module K V₀]
    [AddCommGroup W₀] [Module K W₀]
    {q₀ : QuadraticSpace K V₀} {r₀ : QuadraticSpace K W₀}
    {L₀ : Lattice K V₀} {M₀ : Lattice K W₀}
    (J : JordanDecomposition q₀ L₀ (n + 2))
    (H : JordanDecomposition r₀ M₀ (n + 2))
    (ambient : q₀.IsIsometric r₀)
    (F : SameFundamentalType J H) :
    Lattice.IsIsometric q₀ r₀ L₀ M₀ ↔ J.Omeara9328Conditions H := by
  rw [← J.omeara9328ConditionsWith_canonical_iff H]
  exact isIsometric_iff_omeara9328ConditionsWith J H ambient F
    (canonicalFundamentalNormGeneratorChoice J)

end Lattice.JordanDecomposition

end Bong
