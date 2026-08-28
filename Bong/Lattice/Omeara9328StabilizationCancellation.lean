/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaSaturationStabilization
import Bong.Lattice.ScaledHyperbolicChangeScale
import Bong.Lattice.ProjectionScaling

/-!
# Cancellation after O'Meara's simultaneous rank stabilization

In the stabilization step of O'Meara 93:28, two standard hyperbolic
planes are adjoined at every Jordan scale on both sides.  The independently
chosen scale generators need not be equal, but equality of fundamental type
shows that their valuations agree.  We first normalize the generators by an
explicit integral isometry and then apply O'Meara 93:14 twice at every scale.

Consequently an isometry of the two stabilized coordinate products already
implies an isometry of the original lattices.  This is the cancellation
bridge needed to use saturation and rank reduction in the proof of 93:28.
-/

namespace Bong

open Dyadic Module

namespace Lattice
namespace JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} {W : Type w}
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Equal fundamental type identifies the valuations of the scale
generators when the two decompositions have the same component count. -/
theorem SameFundamentalType.scaleGenerator_order_eq_sameIndex
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (F : SameFundamentalType J H) (i : Fin (n + 2)) :
    ordUnit K (H.scaleGenerator i) = ordUnit K (J.scaleGenerator i) := by
  have h := F.scaleOrder_eq i
  rw [F.indexEquiv_apply_eq_self] at h
  exact h

/-- An ambient isometry of the original spaces extends to the simultaneous
two-plane stabilizations.  The hyperbolic generators on the two sides need
only have the same valuation; `scaledHyperbolicChangeScaleIsometry`
normalizes them component by component. -/
theorem SameFundamentalType.saturationStableAmbientIsometry
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (F : SameFundamentalType J H) (ambient : q.IsIsometric r) :
    (BONG.blockOrthogonalForm (n + 1) J.saturationStableCarrier
      J.saturationStableForm).IsIsometric
      (BONG.blockOrthogonalForm (n + 1) H.saturationStableCarrier
        H.saturationStableForm) := by
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
  let ambientIsometry : QuadraticSpace.Isometry q r := Classical.choice ambient
  let baseSpaceIsometry : QuadraticSpace.Isometry sourceBaseForm targetBaseForm :=
    sourceProduct.toQuadraticSpaceIsometry.trans
      (ambientIsometry.trans targetProduct.symm.toQuadraticSpaceIsometry)
  let baseIntegral := Isometry.toMap sourceBaseForm baseSpaceIsometry
    sourceBaseLattice
  let extendBase := pairedHyperbolicExtensionIsometry baseIntegral
    (n + 2) J.scaleGenerator
  let normalizeTarget := pairedHyperbolicExtensionChangeScale
    targetBaseForm targetBaseLattice (n + 2) J.scaleGenerator
      H.scaleGenerator
      (fun i => (F.scaleGenerator_order_eq_sameIndex i).symm)
  exact ⟨gatherJ.toQuadraticSpaceIsometry.trans
    (extendBase.toQuadraticSpaceIsometry.trans
      (normalizeTarget.toQuadraticSpaceIsometry.trans
        gatherH.symm.toQuadraticSpaceIsometry))⟩

/-- Simultaneous two-plane stabilization preserves O'Meara's complete
fundamental type. -/
noncomputable def SameFundamentalType.saturationStable
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (F : SameFundamentalType J H) :
    SameFundamentalType J.saturationStableJordan
      H.saturationStableJordan where
  indexEquiv := F.indexEquiv
  index_val := F.index_val
  componentRank_eq i := by
    rw [H.saturationStableJordan_componentRank,
      J.saturationStableJordan_componentRank,
      F.componentRank_eq]
  scaleOrder_eq i := by
    simpa only [fundamentalScaleOrder,
      saturationStableJordan_scaleGenerator] using F.scaleOrder_eq i
  normGroup_eq i := by
    rw [H.saturationStableJordan_fundamentalNormGroup,
      J.saturationStableJordan_fundamentalNormGroup,
      F.normGroup_eq]

/-- An isometry of the twice-hyperbolically stabilized component products
descends to an isometry of the unstabilized component products. -/
noncomputable def cancelSaturationStableBlockProduct
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2))
    (F : SameFundamentalType J H)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) J.saturationStableCarrier
        J.saturationStableForm)
      (BONG.blockOrthogonalForm (n + 1) H.saturationStableCarrier
        H.saturationStableForm)
      (BONG.blockProductLattice (n + 1) J.saturationStableCarrier
        J.saturationStableLattice)
      (BONG.blockProductLattice (n + 1) H.saturationStableCarrier
        H.saturationStableLattice)) :
    Isometry
      (BONG.blockOrthogonalForm (n + 1)
        (fun i => (J.component i).carrier)
        (fun i => (J.component i).space))
      (BONG.blockOrthogonalForm (n + 1)
        (fun i => (H.component i).carrier)
        (fun i => (H.component i).space))
      (BONG.blockProductLattice (n + 1)
        (fun i => (J.component i).carrier)
        (fun i => (J.component i).lattice))
      (BONG.blockProductLattice (n + 1)
        (fun i => (H.component i).carrier)
        (fun i => (H.component i).lattice)) := by
  let Jform := BONG.blockOrthogonalForm (n + 1)
    (fun i => (J.component i).carrier)
    (fun i => (J.component i).space)
  let Hform := BONG.blockOrthogonalForm (n + 1)
    (fun i => (H.component i).carrier)
    (fun i => (H.component i).space)
  let Jlattice := BONG.blockProductLattice (n + 1)
    (fun i => (J.component i).carrier)
    (fun i => (J.component i).lattice)
  let Hlattice := BONG.blockProductLattice (n + 1)
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
  let normalizeH := pairedHyperbolicExtensionChangeScale
    Hform Hlattice (n + 2) H.scaleGenerator J.scaleGenerator
      (F.scaleGenerator_order_eq_sameIndex)
  let towerIsometry : Isometry
      (pairedHyperbolicExtensionForm Jform (n + 2) J.scaleGenerator)
      (pairedHyperbolicExtensionForm Hform (n + 2) J.scaleGenerator)
      (pairedHyperbolicExtensionLattice Jlattice (n + 2))
      (pairedHyperbolicExtensionLattice Hlattice (n + 2)) :=
    gatherJ.symm.trans <| f.trans <| gatherH.trans normalizeH
  exact cancelPairedHyperbolicExtension (n + 2) J.scaleGenerator towerIsometry

/-- O'Meara's simultaneous stabilization is cancellable on the original
ambient lattices, even when the two Jordan splittings use different scale
generators. -/
noncomputable def isometryOfSaturationStableJordanIsometry
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2))
    (F : SameFundamentalType J H)
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) J.saturationStableCarrier
        J.saturationStableForm)
      (BONG.blockOrthogonalForm (n + 1) H.saturationStableCarrier
        H.saturationStableForm)
      (BONG.blockProductLattice (n + 1) J.saturationStableCarrier
        J.saturationStableLattice)
      (BONG.blockProductLattice (n + 1) H.saturationStableCarrier
        H.saturationStableLattice)) :
    Isometry q r L M :=
  (BONG.orthogonalDecompositionProductIsometry
      J.toOrthogonalDecomposition).symm |>.trans
    ((cancelSaturationStableBlockProduct J H F f).trans
      (BONG.orthogonalDecompositionProductIsometry
        H.toOrthogonalDecomposition))

end JordanDecomposition
end Lattice

end Bong
