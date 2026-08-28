/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328RankFourJordanReduction
import Bong.Lattice.BlockOrthogonalPairDistribution
import Bong.QuadraticSpace.OrthogonalSumCancellation

/-!
# Ambient-space reduction to the rank-four Jordan systems

The componentwise 93:18(v) decompositions have different residual spaces
but the same hyperbolic-tower lengths on the source and target.  We assemble
the displayed component isometries, gather all tower factors on the left,
and cancel that literally common finite nondegenerate summand.

The intermediate negative adjunction is handled globally: the product of
the source blocks is `(-q) ⊥ q`, while the target blocks form `(-q) ⊥ r`.
Thus an ambient isometry `q ≃ r` supplies the middle isometry without any
componentwise assumption.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

/-- Rewrite the displayed tower length of a rank-four reduction along a
specified equality.  Isolating this dependent transport avoids exposing the
recursively generated module instances at application sites. -/
noncomputable def rankFourReductionDisplayedIsometryOfPlaneCountEq
    {X : Type z} [AddCommGroup X] [Module K X]
    {p : QuadraticSpace K X} {N : Lattice K X} {s : Kˣ}
    (D : Omeara9318RankFourReductionData p N s)
    (k : Nat) (h : D.planeCount = k) :
    Isometry p (rankFourReductionTowerForm D.form s k) N
      (rankFourReductionTowerLattice D.lattice k) := by
  subst k
  exact D.displayedIsometry

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- Carrier of the tower split from the `i`th source component.  The target
tower is transported to this same carrier using `planeCount_eq`. -/
noncomputable abbrev commonTowerCarrier (i : Fin (n + 2)) :=
  HyperbolicExtension K (Fin 0 → K)
    (S.pair i).source.planeCount

/-- The common scaled hyperbolic tower at component `i`. -/
noncomputable abbrev commonTowerForm (i : Fin (n + 2)) :
    QuadraticSpace K (S.commonTowerCarrier i) :=
  QuadraticSpace.scaledZeroOmearaTowerForm (J.scaleGenerator i)
    (S.pair i).source.planeCount

/-- The standard lattice on the common tower. -/
noncomputable abbrev commonTowerLattice (i : Fin (n + 2)) :
    Lattice K (S.commonTowerCarrier i) :=
  hyperbolicExtensionLattice (zeroCoordinateLattice (K := K))
    (S.pair i).source.planeCount

/-- The target displayed decomposition, rewritten to use the source tower
length. -/
noncomputable def targetDisplayedIsometryToCommonTower
    (i : Fin (n + 2)) :
    Isometry (negativeAdjunctionTargetForm J H i)
      ((S.commonTowerForm i).orthogonalSum (S.targetForm i))
      (negativeAdjunctionTargetLattice J H i)
      (product (S.commonTowerLattice i) (S.targetLattice i)) :=
  rankFourReductionDisplayedIsometryOfPlaneCountEq
    (S.pair i).target (S.pair i).source.planeCount
      (S.pair i).planeCount_eq

/-- Assemble all source displayed reductions before gathering their tower
factors. -/
noncomputable def sourceDisplayedBlockIsometry :
    Isometry
      (BONG.blockOrthogonalForm (n + 1)
        (fun i ↦ (J.component i).carrier × (J.component i).carrier)
        (fun i ↦ negativeAdjunctionSourceForm J i))
      (BONG.blockOrthogonalForm (n + 1)
        (fun i ↦ S.commonTowerCarrier i × S.sourceCarrier i)
        (fun i ↦ (S.commonTowerForm i).orthogonalSum (S.sourceForm i)))
      (BONG.blockProductLattice (n + 1)
        (fun i ↦ (J.component i).carrier × (J.component i).carrier)
        (fun i ↦ negativeAdjunctionSourceLattice J i))
      (BONG.blockProductLattice (n + 1)
        (fun i ↦ S.commonTowerCarrier i × S.sourceCarrier i)
        (fun i ↦ product (S.commonTowerLattice i) (S.sourceLattice i))) :=
  BONG.blockProductLatticeIsometry
    (fun i ↦ negativeAdjunctionSourceForm J i)
    (fun i ↦ (S.commonTowerForm i).orthogonalSum (S.sourceForm i))
    (fun i ↦ negativeAdjunctionSourceLattice J i)
    (fun i ↦ product (S.commonTowerLattice i) (S.sourceLattice i))
    (fun i ↦ (S.pair i).source.displayedIsometry)

/-- Assemble all target displayed reductions, with the common source tower
lengths already substituted. -/
noncomputable def targetDisplayedBlockIsometry :
    Isometry
      (BONG.blockOrthogonalForm (n + 1)
        (fun i ↦ (J.component i).carrier × (H.component i).carrier)
        (fun i ↦ negativeAdjunctionTargetForm J H i))
      (BONG.blockOrthogonalForm (n + 1)
        (fun i ↦ S.commonTowerCarrier i × S.targetCarrier i)
        (fun i ↦ (S.commonTowerForm i).orthogonalSum (S.targetForm i)))
      (BONG.blockProductLattice (n + 1)
        (fun i ↦ (J.component i).carrier × (H.component i).carrier)
        (fun i ↦ negativeAdjunctionTargetLattice J H i))
      (BONG.blockProductLattice (n + 1)
        (fun i ↦ S.commonTowerCarrier i × S.targetCarrier i)
        (fun i ↦ product (S.commonTowerLattice i) (S.targetLattice i))) :=
  BONG.blockProductLatticeIsometry
    (fun i ↦ negativeAdjunctionTargetForm J H i)
    (fun i ↦ (S.commonTowerForm i).orthogonalSum (S.targetForm i))
    (fun i ↦ negativeAdjunctionTargetLattice J H i)
    (fun i ↦ product (S.commonTowerLattice i) (S.targetLattice i))
    S.targetDisplayedIsometryToCommonTower

/-- Source reduction with all component towers gathered into one common
block summand. -/
noncomputable def sourceGatheredReduction :
    Isometry
      (BONG.blockOrthogonalForm (n + 1)
        (fun i ↦ (J.component i).carrier × (J.component i).carrier)
        (fun i ↦ negativeAdjunctionSourceForm J i))
      ((BONG.blockOrthogonalForm (n + 1) S.commonTowerCarrier
          S.commonTowerForm).orthogonalSum
        (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm))
      (BONG.blockProductLattice (n + 1)
        (fun i ↦ (J.component i).carrier × (J.component i).carrier)
        (fun i ↦ negativeAdjunctionSourceLattice J i))
      (product
        (BONG.blockProductLattice (n + 1) S.commonTowerCarrier
          S.commonTowerLattice)
        (BONG.blockProductLattice (n + 1) S.sourceCarrier
          S.sourceLattice)) :=
  S.sourceDisplayedBlockIsometry.trans <|
    BONG.blockOrthogonalPairLatticeIsometry
      S.commonTowerCarrier S.sourceCarrier S.commonTowerForm S.sourceForm
      S.commonTowerLattice S.sourceLattice

/-- Target reduction with exactly the same gathered tower summand. -/
noncomputable def targetGatheredReduction :
    Isometry
      (BONG.blockOrthogonalForm (n + 1)
        (fun i ↦ (J.component i).carrier × (H.component i).carrier)
        (fun i ↦ negativeAdjunctionTargetForm J H i))
      ((BONG.blockOrthogonalForm (n + 1) S.commonTowerCarrier
          S.commonTowerForm).orthogonalSum
        (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm))
      (BONG.blockProductLattice (n + 1)
        (fun i ↦ (J.component i).carrier × (H.component i).carrier)
        (fun i ↦ negativeAdjunctionTargetLattice J H i))
      (product
        (BONG.blockProductLattice (n + 1) S.commonTowerCarrier
          S.commonTowerLattice)
        (BONG.blockProductLattice (n + 1) S.targetCarrier
          S.targetLattice)) :=
  S.targetDisplayedBlockIsometry.trans <|
    BONG.blockOrthogonalPairLatticeIsometry
      S.commonTowerCarrier S.targetCarrier S.commonTowerForm S.targetForm
      S.commonTowerLattice S.targetLattice

/-- The product of all source negative adjunctions is integrally isometric
to `(-q) ⊥ q`. -/
noncomputable def sourceNegativeAdjunctionProductIsometry :
    Isometry
      (BONG.blockOrthogonalForm (n + 1)
        (fun i ↦ (J.component i).carrier × (J.component i).carrier)
        (fun i ↦ negativeAdjunctionSourceForm J i))
      ((q.rescaleUnit (-1 : Kˣ)).orthogonalSum q)
      (BONG.blockProductLattice (n + 1)
        (fun i ↦ (J.component i).carrier × (J.component i).carrier)
        (fun i ↦ negativeAdjunctionSourceLattice J i))
      (product L L) := by
  let baseForm := BONG.blockOrthogonalForm (n + 1)
    (fun i ↦ (J.component i).carrier)
    (fun i ↦ (J.component i).space)
  let baseLattice := BONG.blockProductLattice (n + 1)
    (fun i ↦ (J.component i).carrier)
    (fun i ↦ (J.component i).lattice)
  let distribute := BONG.blockOrthogonalPairLatticeIsometry
    (fun i ↦ (J.component i).carrier)
    (fun i ↦ (J.component i).carrier)
    (fun i ↦ (J.component i).space.rescaleUnit (-1 : Kˣ))
    (fun i ↦ (J.component i).space)
    (fun i ↦ (J.component i).lattice)
    (fun i ↦ (J.component i).lattice)
  let rescaleBlocks := BONG.blockOrthogonalRescaleLatticeIsometry
    (fun i ↦ (J.component i).carrier)
    (fun i ↦ (J.component i).space)
    (fun i ↦ (J.component i).lattice) (-1 : Kˣ)
  let productPresentation :=
    BONG.orthogonalDecompositionProductIsometry J.toOrthogonalDecomposition
  exact distribute.trans <|
    rescaleBlocks.orthogonalProductBasic (Isometry.refl baseForm baseLattice)
      |>.trans <|
        (productPresentation.rescaleUnitBoth (-1 : Kˣ)).orthogonalProductBasic
          productPresentation

/-- The product of all target negative adjunctions is integrally isometric
to `(-q) ⊥ r`. -/
noncomputable def targetNegativeAdjunctionProductIsometry :
    Isometry
      (BONG.blockOrthogonalForm (n + 1)
        (fun i ↦ (J.component i).carrier × (H.component i).carrier)
        (fun i ↦ negativeAdjunctionTargetForm J H i))
      ((q.rescaleUnit (-1 : Kˣ)).orthogonalSum r)
      (BONG.blockProductLattice (n + 1)
        (fun i ↦ (J.component i).carrier × (H.component i).carrier)
        (fun i ↦ negativeAdjunctionTargetLattice J H i))
      (product L M) := by
  let sourceBaseForm := BONG.blockOrthogonalForm (n + 1)
    (fun i ↦ (J.component i).carrier)
    (fun i ↦ (J.component i).space)
  let sourceBaseLattice := BONG.blockProductLattice (n + 1)
    (fun i ↦ (J.component i).carrier)
    (fun i ↦ (J.component i).lattice)
  let targetBaseForm := BONG.blockOrthogonalForm (n + 1)
    (fun i ↦ (H.component i).carrier)
    (fun i ↦ (H.component i).space)
  let targetBaseLattice := BONG.blockProductLattice (n + 1)
    (fun i ↦ (H.component i).carrier)
    (fun i ↦ (H.component i).lattice)
  let distribute := BONG.blockOrthogonalPairLatticeIsometry
    (fun i ↦ (J.component i).carrier)
    (fun i ↦ (H.component i).carrier)
    (fun i ↦ (J.component i).space.rescaleUnit (-1 : Kˣ))
    (fun i ↦ (H.component i).space)
    (fun i ↦ (J.component i).lattice)
    (fun i ↦ (H.component i).lattice)
  let rescaleBlocks := BONG.blockOrthogonalRescaleLatticeIsometry
    (fun i ↦ (J.component i).carrier)
    (fun i ↦ (J.component i).space)
    (fun i ↦ (J.component i).lattice) (-1 : Kˣ)
  let sourcePresentation :=
    BONG.orthogonalDecompositionProductIsometry J.toOrthogonalDecomposition
  let targetPresentation :=
    BONG.orthogonalDecompositionProductIsometry H.toOrthogonalDecomposition
  exact distribute.trans <|
    rescaleBlocks.orthogonalProductBasic
      (Isometry.refl targetBaseForm targetBaseLattice)
      |>.trans <|
        (sourcePresentation.rescaleUnitBoth (-1 : Kˣ)).orthogonalProductBasic
          targetPresentation

/-- The global negative-adjunction products are ambient-isometric whenever
the original ambient spaces are. -/
noncomputable def negativeAdjunctionProductAmbientIsometry
    (ambient : q.IsIsometric r) :
    QuadraticSpace.Isometry
      (BONG.blockOrthogonalForm (n + 1)
        (fun i ↦ (J.component i).carrier × (J.component i).carrier)
        (fun i ↦ negativeAdjunctionSourceForm J i))
      (BONG.blockOrthogonalForm (n + 1)
        (fun i ↦ (J.component i).carrier × (H.component i).carrier)
        (fun i ↦ negativeAdjunctionTargetForm J H i)) :=
  (sourceNegativeAdjunctionProductIsometry (J := J)).toQuadraticSpaceIsometry.trans <|
    ((QuadraticSpace.Isometry.refl (q.rescaleUnit (-1 : Kˣ))).orthogonalSum
      (Classical.choice ambient)).trans
        (targetNegativeAdjunctionProductIsometry
          (J := J) (H := H)).symm.toQuadraticSpaceIsometry

/-- After the explicit negative adjunction and repeated 93:18(v)
decompositions, Witt cancellation supplies an ambient isometry of the two
rank-four residual block products. -/
noncomputable def residualAmbientIsometry
    (ambient : q.IsIsometric r) :
    QuadraticSpace.Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm) := by
  let commonLattice := BONG.blockProductLattice (n + 1)
    S.commonTowerCarrier S.commonTowerLattice
  let sourceResidualLattice := BONG.blockProductLattice (n + 1)
    S.sourceCarrier S.sourceLattice
  let targetResidualLattice := BONG.blockProductLattice (n + 1)
    S.targetCarrier S.targetLattice
  letI : Module.Finite K (BONG.BlockProductSpace (n + 1)
      S.commonTowerCarrier) := commonLattice.moduleFinite
  letI : Module.Finite K (BONG.BlockProductSpace (n + 1)
      S.sourceCarrier) := sourceResidualLattice.moduleFinite
  letI : Module.Finite K (BONG.BlockProductSpace (n + 1)
      S.targetCarrier) := targetResidualLattice.moduleFinite
  let common := BONG.blockOrthogonalForm (n + 1)
    S.commonTowerCarrier S.commonTowerForm
  let total : QuadraticSpace.Isometry
      (common.orthogonalSum
        (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm))
      (common.orthogonalSum
        (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)) :=
    S.sourceGatheredReduction.symm.toQuadraticSpaceIsometry.trans <|
      (negativeAdjunctionProductAmbientIsometry
        (J := J) (H := H) ambient).trans
        S.targetGatheredReduction.toQuadraticSpaceIsometry
  exact QuadraticSpace.orthogonalSumLeftCancel common
    (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
    (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm) total

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
