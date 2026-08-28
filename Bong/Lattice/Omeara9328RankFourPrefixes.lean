/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328RankFourAmbientReduction
import Bong.Lattice.OrthogonalDecompositionPrefixProduct

/-!
# Prefix geometry of the rank-four reduction in O'Meara 93:28

The global negative-adjunction reduction admits the same construction on
every nonempty Jordan prefix.  The resulting source and target reductions
share a literal block product of scaled hyperbolic towers.  We also expose
the alternative presentations as `(-J_{(k)}) ⊥ J_{(k)}` and
`(-J_{(k)}) ⊥ H_{(k)}`.  These two presentations are the geometric input
for transporting all three conditions of 93:28 to the rank-four system.
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
  {L : Lattice K V} {M : Lattice K W} {n m : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- The actual full-decomposition index represented by a standard prefix
coordinate. -/
noncomputable def prefixIndex (S : Omeara9328RankFourReductionSystem J H)
    (hk : m + 1 ≤ n + 2) (i : Fin (m + 1)) : Fin (n + 2) :=
  (S.sourceJordan.toOrthogonalDecomposition.prefixIndexEquiv
    (m + 1) hk i).1

@[simp]
theorem prefixIndex_val (hk : m + 1 ≤ n + 2) (i : Fin (m + 1)) :
    (S.prefixIndex hk i).val = i.val :=
  rfl

abbrev prefixSourceCarrier (hk : m + 1 ≤ n + 2)
    (i : Fin (m + 1)) := S.sourceCarrier (S.prefixIndex hk i)

noncomputable abbrev prefixSourceForm (hk : m + 1 ≤ n + 2)
    (i : Fin (m + 1)) := S.sourceForm (S.prefixIndex hk i)

noncomputable abbrev prefixSourceLattice (hk : m + 1 ≤ n + 2)
    (i : Fin (m + 1)) := S.sourceLattice (S.prefixIndex hk i)

abbrev prefixTargetCarrier (hk : m + 1 ≤ n + 2)
    (i : Fin (m + 1)) := S.targetCarrier (S.prefixIndex hk i)

noncomputable abbrev prefixTargetForm (hk : m + 1 ≤ n + 2)
    (i : Fin (m + 1)) := S.targetForm (S.prefixIndex hk i)

noncomputable abbrev prefixTargetLattice (hk : m + 1 ≤ n + 2)
    (i : Fin (m + 1)) := S.targetLattice (S.prefixIndex hk i)

abbrev prefixCommonTowerCarrier (hk : m + 1 ≤ n + 2)
    (i : Fin (m + 1)) := S.commonTowerCarrier (S.prefixIndex hk i)

noncomputable abbrev prefixCommonTowerForm (hk : m + 1 ≤ n + 2)
    (i : Fin (m + 1)) := S.commonTowerForm (S.prefixIndex hk i)

noncomputable abbrev prefixCommonTowerLattice (hk : m + 1 ≤ n + 2)
    (i : Fin (m + 1)) := S.commonTowerLattice (S.prefixIndex hk i)

/-- Raw residual source prefix to the intrinsic prefix of the assembled
source Jordan decomposition. -/
noncomputable def rawSourceResidualPrefixIsometry
    (hk : m + 1 ≤ n + 2) :
    Isometry
      (BONG.blockOrthogonalForm m (S.prefixSourceCarrier hk)
        (S.prefixSourceForm hk))
      (S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (m + 1)).space
      (BONG.blockProductLattice m (S.prefixSourceCarrier hk)
        (S.prefixSourceLattice hk))
      (S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (m + 1)).lattice := by
  let D := S.sourceJordan.toOrthogonalDecomposition
  let component : ∀ i : Fin (m + 1), Isometry
      (S.prefixSourceForm hk i)
      (D.prefixBlockSpace hk i)
      (S.prefixSourceLattice hk i)
      (D.prefixBlockLattice hk i) := fun i ↦ by
    let f := BONG.blockProductComponentIsometry
      S.sourceCarrier S.sourceForm S.sourceLattice (S.prefixIndex hk i)
    exact f
  exact (BONG.blockProductLatticeIsometry
    (S.prefixSourceForm hk) (D.prefixBlockSpace hk)
    (S.prefixSourceLattice hk) (D.prefixBlockLattice hk) component).trans
      (D.prefixBlockProductIsometry hk)

/-- Raw residual target prefix to the intrinsic prefix of the assembled
target Jordan decomposition. -/
noncomputable def rawTargetResidualPrefixIsometry
    (hk : m + 1 ≤ n + 2) :
    Isometry
      (BONG.blockOrthogonalForm m (S.prefixTargetCarrier hk)
        (S.prefixTargetForm hk))
      (S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (m + 1)).space
      (BONG.blockProductLattice m (S.prefixTargetCarrier hk)
        (S.prefixTargetLattice hk))
      (S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (m + 1)).lattice := by
  let D := S.targetJordan.toOrthogonalDecomposition
  let component : ∀ i : Fin (m + 1), Isometry
      (S.prefixTargetForm hk i)
      (D.prefixBlockSpace hk i)
      (S.prefixTargetLattice hk i)
      (D.prefixBlockLattice hk i) := fun i ↦ by
    let f := BONG.blockProductComponentIsometry
      S.targetCarrier S.targetForm S.targetLattice (S.prefixIndex hk i)
    exact f
  exact (BONG.blockProductLatticeIsometry
    (S.prefixTargetForm hk) (D.prefixBlockSpace hk)
    (S.prefixTargetLattice hk) (D.prefixBlockLattice hk) component).trans
      (D.prefixBlockProductIsometry hk)

/-- The componentwise displayed 93:18(v) reductions on a source prefix. -/
noncomputable def sourcePrefixDisplayedBlockIsometry
    (hk : m + 1 ≤ n + 2) :
    Isometry
      (BONG.blockOrthogonalForm m
        (fun i ↦ (J.component (S.prefixIndex hk i)).carrier ×
          (J.component (S.prefixIndex hk i)).carrier)
        (fun i ↦ negativeAdjunctionSourceForm J (S.prefixIndex hk i)))
      (BONG.blockOrthogonalForm m
        (fun i ↦ S.prefixCommonTowerCarrier hk i ×
          S.prefixSourceCarrier hk i)
        (fun i ↦ (S.prefixCommonTowerForm hk i).orthogonalSum
          (S.prefixSourceForm hk i)))
      (BONG.blockProductLattice m
        (fun i ↦ (J.component (S.prefixIndex hk i)).carrier ×
          (J.component (S.prefixIndex hk i)).carrier)
        (fun i ↦ negativeAdjunctionSourceLattice J (S.prefixIndex hk i)))
      (BONG.blockProductLattice m
        (fun i ↦ S.prefixCommonTowerCarrier hk i ×
          S.prefixSourceCarrier hk i)
        (fun i ↦ product (S.prefixCommonTowerLattice hk i)
          (S.prefixSourceLattice hk i))) :=
  BONG.blockProductLatticeIsometry
    (fun i ↦ negativeAdjunctionSourceForm J (S.prefixIndex hk i))
    (fun i ↦ (S.prefixCommonTowerForm hk i).orthogonalSum
      (S.prefixSourceForm hk i))
    (fun i ↦ negativeAdjunctionSourceLattice J (S.prefixIndex hk i))
    (fun i ↦ product (S.prefixCommonTowerLattice hk i)
      (S.prefixSourceLattice hk i))
    (fun i ↦ (S.pair (S.prefixIndex hk i)).source.displayedIsometry)

/-- The componentwise displayed 93:18(v) reductions on a target prefix. -/
noncomputable def targetPrefixDisplayedBlockIsometry
    (hk : m + 1 ≤ n + 2) :
    Isometry
      (BONG.blockOrthogonalForm m
        (fun i ↦ (J.component (S.prefixIndex hk i)).carrier ×
          (H.component (S.prefixIndex hk i)).carrier)
        (fun i ↦ negativeAdjunctionTargetForm J H (S.prefixIndex hk i)))
      (BONG.blockOrthogonalForm m
        (fun i ↦ S.prefixCommonTowerCarrier hk i ×
          S.prefixTargetCarrier hk i)
        (fun i ↦ (S.prefixCommonTowerForm hk i).orthogonalSum
          (S.prefixTargetForm hk i)))
      (BONG.blockProductLattice m
        (fun i ↦ (J.component (S.prefixIndex hk i)).carrier ×
          (H.component (S.prefixIndex hk i)).carrier)
        (fun i ↦ negativeAdjunctionTargetLattice J H (S.prefixIndex hk i)))
      (BONG.blockProductLattice m
        (fun i ↦ S.prefixCommonTowerCarrier hk i ×
          S.prefixTargetCarrier hk i)
        (fun i ↦ product (S.prefixCommonTowerLattice hk i)
          (S.prefixTargetLattice hk i))) :=
  BONG.blockProductLatticeIsometry
    (fun i ↦ negativeAdjunctionTargetForm J H (S.prefixIndex hk i))
    (fun i ↦ (S.prefixCommonTowerForm hk i).orthogonalSum
      (S.prefixTargetForm hk i))
    (fun i ↦ negativeAdjunctionTargetLattice J H (S.prefixIndex hk i))
    (fun i ↦ product (S.prefixCommonTowerLattice hk i)
      (S.prefixTargetLattice hk i))
    (fun i ↦ S.targetDisplayedIsometryToCommonTower (S.prefixIndex hk i))

/-- Gather the common towers in a source prefix and identify the residual
block with its intrinsic prefix sublattice. -/
noncomputable def sourcePrefixGatheredReduction
    (hk : m + 1 ≤ n + 2) :
    Isometry
      (BONG.blockOrthogonalForm m
        (fun i ↦ (J.component (S.prefixIndex hk i)).carrier ×
          (J.component (S.prefixIndex hk i)).carrier)
        (fun i ↦ negativeAdjunctionSourceForm J (S.prefixIndex hk i)))
      ((BONG.blockOrthogonalForm m (S.prefixCommonTowerCarrier hk)
          (S.prefixCommonTowerForm hk)).orthogonalSum
        (S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).space)
      (BONG.blockProductLattice m
        (fun i ↦ (J.component (S.prefixIndex hk i)).carrier ×
          (J.component (S.prefixIndex hk i)).carrier)
        (fun i ↦ negativeAdjunctionSourceLattice J (S.prefixIndex hk i)))
      (product
        (BONG.blockProductLattice m (S.prefixCommonTowerCarrier hk)
          (S.prefixCommonTowerLattice hk))
        (S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).lattice) :=
  S.sourcePrefixDisplayedBlockIsometry hk |>.trans <|
    (BONG.blockOrthogonalPairLatticeIsometry
      (S.prefixCommonTowerCarrier hk) (S.prefixSourceCarrier hk)
      (S.prefixCommonTowerForm hk) (S.prefixSourceForm hk)
      (S.prefixCommonTowerLattice hk) (S.prefixSourceLattice hk)).trans <|
        (Isometry.refl
          (BONG.blockOrthogonalForm m (S.prefixCommonTowerCarrier hk)
            (S.prefixCommonTowerForm hk))
          (BONG.blockProductLattice m (S.prefixCommonTowerCarrier hk)
            (S.prefixCommonTowerLattice hk))).orthogonalProductBasic
              (S.rawSourceResidualPrefixIsometry hk)

/-- Gather the same towers in a target prefix. -/
noncomputable def targetPrefixGatheredReduction
    (hk : m + 1 ≤ n + 2) :
    Isometry
      (BONG.blockOrthogonalForm m
        (fun i ↦ (J.component (S.prefixIndex hk i)).carrier ×
          (H.component (S.prefixIndex hk i)).carrier)
        (fun i ↦ negativeAdjunctionTargetForm J H (S.prefixIndex hk i)))
      ((BONG.blockOrthogonalForm m (S.prefixCommonTowerCarrier hk)
          (S.prefixCommonTowerForm hk)).orthogonalSum
        (S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).space)
      (BONG.blockProductLattice m
        (fun i ↦ (J.component (S.prefixIndex hk i)).carrier ×
          (H.component (S.prefixIndex hk i)).carrier)
        (fun i ↦ negativeAdjunctionTargetLattice J H (S.prefixIndex hk i)))
      (product
        (BONG.blockProductLattice m (S.prefixCommonTowerCarrier hk)
          (S.prefixCommonTowerLattice hk))
        (S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).lattice) :=
  S.targetPrefixDisplayedBlockIsometry hk |>.trans <|
    (BONG.blockOrthogonalPairLatticeIsometry
      (S.prefixCommonTowerCarrier hk) (S.prefixTargetCarrier hk)
      (S.prefixCommonTowerForm hk) (S.prefixTargetForm hk)
      (S.prefixCommonTowerLattice hk) (S.prefixTargetLattice hk)).trans <|
        (Isometry.refl
          (BONG.blockOrthogonalForm m (S.prefixCommonTowerCarrier hk)
            (S.prefixCommonTowerForm hk))
          (BONG.blockProductLattice m (S.prefixCommonTowerCarrier hk)
            (S.prefixCommonTowerLattice hk))).orthogonalProductBasic
              (S.rawTargetResidualPrefixIsometry hk)

/-- Alternative presentation of a source negative-adjunction prefix as
`(-J_(k)) ⊥ J_(k)`. -/
noncomputable def sourceNegativeAdjunctionPrefixProductIsometry
    (hk : m + 1 ≤ n + 2) :
    Isometry
      (BONG.blockOrthogonalForm m
        (fun i ↦ (J.component (S.prefixIndex hk i)).carrier ×
          (J.component (S.prefixIndex hk i)).carrier)
        (fun i ↦ negativeAdjunctionSourceForm J (S.prefixIndex hk i)))
      (((J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).space.rescaleUnit (-1 : Kˣ)).orthogonalSum
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).space)
      (BONG.blockProductLattice m
        (fun i ↦ (J.component (S.prefixIndex hk i)).carrier ×
          (J.component (S.prefixIndex hk i)).carrier)
        (fun i ↦ negativeAdjunctionSourceLattice J (S.prefixIndex hk i)))
      (product
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).lattice
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).lattice) := by
  let D := J.toOrthogonalDecomposition
  let distribute := BONG.blockOrthogonalPairLatticeIsometry
    (D.prefixBlockCarrier hk) (D.prefixBlockCarrier hk)
    (fun i ↦ (D.prefixBlockSpace hk i).rescaleUnit (-1 : Kˣ))
    (D.prefixBlockSpace hk) (D.prefixBlockLattice hk)
    (D.prefixBlockLattice hk)
  let rescaleBlocks := BONG.blockOrthogonalRescaleLatticeIsometry
    (D.prefixBlockCarrier hk) (D.prefixBlockSpace hk)
    (D.prefixBlockLattice hk) (-1 : Kˣ)
  let present := D.prefixBlockProductIsometry hk
  exact distribute.trans <|
    rescaleBlocks.orthogonalProductBasic
      (Isometry.refl
        (BONG.blockOrthogonalForm m (D.prefixBlockCarrier hk)
          (D.prefixBlockSpace hk))
        (BONG.blockProductLattice m (D.prefixBlockCarrier hk)
          (D.prefixBlockLattice hk))) |>.trans <|
      (present.rescaleUnitBoth (-1 : Kˣ)).orthogonalProductBasic present

/-- Alternative presentation of a target negative-adjunction prefix as
`(-J_(k)) ⊥ H_(k)`. -/
noncomputable def targetNegativeAdjunctionPrefixProductIsometry
    (hk : m + 1 ≤ n + 2) :
    Isometry
      (BONG.blockOrthogonalForm m
        (fun i ↦ (J.component (S.prefixIndex hk i)).carrier ×
          (H.component (S.prefixIndex hk i)).carrier)
        (fun i ↦ negativeAdjunctionTargetForm J H (S.prefixIndex hk i)))
      (((J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).space.rescaleUnit (-1 : Kˣ)).orthogonalSum
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).space)
      (BONG.blockProductLattice m
        (fun i ↦ (J.component (S.prefixIndex hk i)).carrier ×
          (H.component (S.prefixIndex hk i)).carrier)
        (fun i ↦ negativeAdjunctionTargetLattice J H (S.prefixIndex hk i)))
      (product
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).lattice
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).lattice) := by
  let DJ := J.toOrthogonalDecomposition
  let DH := H.toOrthogonalDecomposition
  let distribute := BONG.blockOrthogonalPairLatticeIsometry
    (DJ.prefixBlockCarrier hk) (DH.prefixBlockCarrier hk)
    (fun i ↦ (DJ.prefixBlockSpace hk i).rescaleUnit (-1 : Kˣ))
    (DH.prefixBlockSpace hk) (DJ.prefixBlockLattice hk)
    (DH.prefixBlockLattice hk)
  let rescaleBlocks := BONG.blockOrthogonalRescaleLatticeIsometry
    (DJ.prefixBlockCarrier hk) (DJ.prefixBlockSpace hk)
    (DJ.prefixBlockLattice hk) (-1 : Kˣ)
  let presentJ := DJ.prefixBlockProductIsometry hk
  let presentH := DH.prefixBlockProductIsometry hk
  exact distribute.trans <|
    rescaleBlocks.orthogonalProductBasic
      (Isometry.refl
        (BONG.blockOrthogonalForm m (DH.prefixBlockCarrier hk)
          (DH.prefixBlockSpace hk))
        (BONG.blockProductLattice m (DH.prefixBlockCarrier hk)
          (DH.prefixBlockLattice hk))) |>.trans <|
      (presentJ.rescaleUnitBoth (-1 : Kˣ)).orthogonalProductBasic presentH

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
