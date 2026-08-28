/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328RankFourCancellation
import Bong.Lattice.OmearaCommonAdjunctionCancellation
import Bong.Lattice.OmearaFundamentalTypeAlgebra

/-!
# O'Meara 93:28 necessity: integral rank-four residuals

The rank-four reduction is useful in both directions of Theorem 93:28.  In
the necessary direction an isometry of the original lattices gives an
isometry of their negative adjunctions.  The componentwise 93:18(v)
decompositions display these as a common product of hyperbolic towers and
the two rank-four residual products.  Iterated 93:14a cancels the common
towers and leaves an *integral* isometry of the residual products.

This is stronger than the ambient Witt cancellation used by sufficiency and
is the exact input needed for the projection calculation in Step 1 of
O'Meara's proof.
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
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- Every common tower split from a source negative-adjunction component is
modular at the corresponding Jordan scale. -/
theorem commonTower_modular (i : Fin (n + 2)) :
    IsModular (S.commonTowerForm i) (S.commonTowerLattice i)
      (J.scaleGenerator i) := by
  have htotal : IsModular
      (negativeAdjunctionSourceForm J i)
      (negativeAdjunctionSourceLattice J i) (J.scaleGenerator i) :=
    negativeAdjunctionSource_modular J i
  have hdisplayed : IsModular
      ((S.commonTowerForm i).orthogonalSum (S.sourceForm i))
      (product (S.commonTowerLattice i) (S.sourceLattice i))
      (J.scaleGenerator i) := by
    simpa only [commonTowerForm, commonTowerLattice, sourceForm,
      sourceLattice, rankFourReductionTowerForm,
      rankFourReductionTowerLattice] using
        htotal.mapLatticeIsometry (S.pair i).source.displayedIsometry
  exact hdisplayed.left_of_orthogonalProduct

/-- The norm group of a common tower is contained in the scale truncation
of the complete source residual product at the same Jordan scale. -/
theorem commonTower_normGroup_subset_sourceResidualTruncation
    (i : Fin (n + 2)) :
    normGroupSet (S.commonTowerForm i) (S.commonTowerLattice i) ⊆
      normGroupSet
        (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
        (omearaScaleTruncation
          (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
          (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
          (J.scaleGenerator i)) := by
  intro z hz
  have hzProduct : z ∈ normGroupSet
      ((S.commonTowerForm i).orthogonalSum (S.sourceForm i))
      (product (S.commonTowerLattice i) (S.sourceLattice i)) := by
    rw [mem_normGroupSet_orthogonalProduct_iff]
    exact ⟨z, hz, 0, zero_mem_normGroupSet _ _, by simp⟩
  have hproduct :
      normGroupSet
          ((S.commonTowerForm i).orthogonalSum (S.sourceForm i))
          (product (S.commonTowerLattice i) (S.sourceLattice i)) =
        normGroupSet (S.sourceForm i) (S.sourceLattice i) := by
    calc
      normGroupSet
          ((S.commonTowerForm i).orthogonalSum (S.sourceForm i))
          (product (S.commonTowerLattice i) (S.sourceLattice i)) =
          normGroupSet (negativeAdjunctionSourceForm J i)
            (negativeAdjunctionSourceLattice J i) :=
        normGroupSet_eq_of_latticeIsometry
          (S.pair i).source.displayedIsometry
      _ = normGroupSet (J.component i).space (J.component i).lattice :=
        negativeAdjunctionSource_normGroupSet_eq J i
      _ = normGroupSet (S.sourceForm i) (S.sourceLattice i) :=
        (S.pair i).sourceResidualNormGroupSet_eq.symm
  rw [hproduct] at hzProduct
  have hrawComponent :
      normGroupSet (S.sourceForm i) (S.sourceLattice i) =
        normGroupSet (S.sourceJordan.component i).space
          (S.sourceJordan.component i).lattice := by
    exact (S.pair i).sourceResidualNormGroupSet_eq.trans
      (S.sourceJordan_component_normGroupSet i).symm
  rw [hrawComponent] at hzProduct
  have hsubset :=
    S.sourceJordan_isSaturated.componentNormGroup_subset_sameTypeTruncation
      S.sourceJordan S.sourceJordan (SameFundamentalType.refl S.sourceJordan) i
  simpa only [sourceJordan_scaleGenerator] using hsubset hzProduct

/-- The same common tower norm group is contained in the corresponding
target residual scale truncation. -/
theorem commonTower_normGroup_subset_targetResidualTruncation
    (i : Fin (n + 2)) :
    normGroupSet (S.commonTowerForm i) (S.commonTowerLattice i) ⊆
      normGroupSet
        (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
        (omearaScaleTruncation
          (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
          (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)
          (J.scaleGenerator i)) := by
  intro z hz
  have hzProduct : z ∈ normGroupSet
      ((S.commonTowerForm i).orthogonalSum (S.targetForm i))
      (product (S.commonTowerLattice i) (S.targetLattice i)) := by
    rw [mem_normGroupSet_orthogonalProduct_iff]
    exact ⟨z, hz, 0, zero_mem_normGroupSet _ _, by simp⟩
  have hproduct :
      normGroupSet
          ((S.commonTowerForm i).orthogonalSum (S.targetForm i))
          (product (S.commonTowerLattice i) (S.targetLattice i)) =
        normGroupSet (S.targetForm i) (S.targetLattice i) := by
    calc
      normGroupSet
          ((S.commonTowerForm i).orthogonalSum (S.targetForm i))
          (product (S.commonTowerLattice i) (S.targetLattice i)) =
          normGroupSet (negativeAdjunctionTargetForm J H i)
            (negativeAdjunctionTargetLattice J H i) :=
        normGroupSet_eq_of_latticeIsometry
          (S.targetDisplayedIsometryToCommonTower i)
      _ = normGroupSet (J.component i).space (J.component i).lattice :=
        negativeAdjunctionTarget_normGroupSet_eq J H i
          S.sourceSaturated S.targetSaturated S.fundamentalType
      _ = normGroupSet (S.targetForm i) (S.targetLattice i) :=
        (S.pair i).targetResidualNormGroupSet_eq.symm
  rw [hproduct] at hzProduct
  have hrawComponent :
      normGroupSet (S.targetForm i) (S.targetLattice i) =
        normGroupSet (S.targetJordan.component i).space
          (S.targetJordan.component i).lattice := by
    exact (S.pair i).targetResidualNormGroupSet_eq.trans
      (S.targetJordan_component_normGroupSet i).symm
  rw [hrawComponent] at hzProduct
  have hsubset :=
    S.targetJordan_isSaturated.componentNormGroup_subset_sameTypeTruncation
      S.targetJordan S.targetJordan (SameFundamentalType.refl S.targetJordan) i
  simpa only [targetJordan_scaleGenerator] using hsubset hzProduct

/-- An integral isometry of the original lattices descends, after the
componentwise negative-adjunction reduction and 93:14a cancellation, to an
integral isometry of the two rank-four residual products. -/
noncomputable def residualIsometryOfOriginalIsometry
    (f : Isometry q r L M) :
    Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice) := by
  let original : Isometry
      ((q.rescaleUnit (-1 : Kˣ)).orthogonalSum q)
      ((q.rescaleUnit (-1 : Kˣ)).orthogonalSum r)
      (product L L) (product L M) :=
    (Isometry.refl (q.rescaleUnit (-1 : Kˣ)) L).orthogonalProductBasic f
  let total : Isometry
      ((BONG.blockOrthogonalForm (n + 1) S.commonTowerCarrier
          S.commonTowerForm).orthogonalSum
        (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm))
      ((BONG.blockOrthogonalForm (n + 1) S.commonTowerCarrier
          S.commonTowerForm).orthogonalSum
        (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm))
      (product
        (BONG.blockProductLattice (n + 1) S.commonTowerCarrier
          S.commonTowerLattice)
        (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice))
      (product
        (BONG.blockProductLattice (n + 1) S.commonTowerCarrier
          S.commonTowerLattice)
        (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :=
    S.sourceGatheredReduction.symm.trans <|
      (sourceNegativeAdjunctionProductIsometry (J := J)).trans <|
        original.trans <|
          (targetNegativeAdjunctionProductIsometry (J := J) (H := H)).symm.trans
            S.targetGatheredReduction
  exact cancelCommonBlockProduct (n + 1) S.commonTowerCarrier
    S.commonTowerForm S.commonTowerLattice J.scaleGenerator
    S.commonTower_modular
    (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
    (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
    (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
    (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)
    S.commonTower_normGroup_subset_sourceResidualTruncation
    S.commonTower_normGroup_subset_targetResidualTruncation total

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
