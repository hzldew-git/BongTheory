/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9318RankFourReduction
import Bong.Lattice.Omeara9328StabilizationCancellation

/-!
# Hyperbolicized Jordan components in O'Meara 93:28

Step 2 of the sufficiency proof of O'Meara 93:28 adjoins the negative of
each source Jordan component to the corresponding source and target
components.  The two enlarged components are modular at the same chosen
source scale and have the same norm group.  Their ranks agree and are even,
so O'Meara 93:18(v) reduces both to rank four after the preliminary rank
stabilization.

This file records those facts for the actual component lattices.  In
particular, none of modularity, equality of norm groups, or the common scale
is left as a paper-specific law parameter.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- Negating the quadratic form does not change modularity or its scale
parameter. -/
theorem IsModular.rescaleUnit_neg_one
    {X : Type*} [AddCommGroup X] [Module K X]
    {p : QuadraticSpace K X} {N : Lattice K X} {s : Kˣ}
    (h : IsModular p N s) :
    IsModular (p.rescaleUnit (-1 : Kˣ)) N s := by
  rw [IsModular, dualLattice_rescaleUnit_neg_one]
  exact h

namespace JordanDecomposition

variable {t : Nat}
  (J : JordanDecomposition q L t) (H : JordanDecomposition r M t)
  (i : Fin t)

/-- The source component after adjoining the negative source component. -/
noncomputable abbrev negativeAdjunctionSourceForm :
    QuadraticSpace K ((J.component i).carrier × (J.component i).carrier) :=
  ((J.component i).space.rescaleUnit (-1 : Kˣ)).orthogonalSum
    (J.component i).space

/-- The lattice carried by the hyperbolicized source component. -/
noncomputable abbrev negativeAdjunctionSourceLattice :
    Lattice K ((J.component i).carrier × (J.component i).carrier) :=
  product (J.component i).lattice (J.component i).lattice

/-- The target component after adjoining the same negative source
component. -/
noncomputable abbrev negativeAdjunctionTargetForm :
    QuadraticSpace K ((J.component i).carrier × (H.component i).carrier) :=
  ((J.component i).space.rescaleUnit (-1 : Kˣ)).orthogonalSum
    (H.component i).space

/-- The lattice carried by the hyperbolicized target component. -/
noncomputable abbrev negativeAdjunctionTargetLattice :
    Lattice K ((J.component i).carrier × (H.component i).carrier) :=
  product (J.component i).lattice (H.component i).lattice

/-- The hyperbolicized source component is modular at the original source
scale. -/
theorem negativeAdjunctionSource_modular :
    IsModular (negativeAdjunctionSourceForm J i)
      (negativeAdjunctionSourceLattice J i) (J.scaleGenerator i) :=
  (J.modular i).rescaleUnit_neg_one.orthogonalProduct (J.modular i)

/-- Corresponding scale generators determine the same principal ideal. -/
theorem SameFundamentalType.componentScaleIdeal_eq_sameIndex
    (F : SameFundamentalType J H) :
    principalIdeal (K := K) (H.scaleGenerator i : K) =
      principalIdeal (K := K) (J.scaleGenerator i : K) := by
  have h := F.scaleOrder_eq i
  rw [F.indexEquiv_apply_eq_self] at h
  exact (principalIdeal_eq_iff_ordUnit_eq _ _).2 h

/-- The hyperbolicized target component is modular at the same source scale.
The change from the target's chosen generator is justified by equality of
the corresponding principal scale ideals. -/
theorem negativeAdjunctionTarget_modular
    (F : SameFundamentalType J H) :
    IsModular (negativeAdjunctionTargetForm J H i)
      (negativeAdjunctionTargetLattice J H i) (J.scaleGenerator i) := by
  have htarget : IsModular (H.component i).space (H.component i).lattice
      (J.scaleGenerator i) :=
    (H.modular i).of_principalIdeal_eq
      (SameFundamentalType.componentScaleIdeal_eq_sameIndex J H i F)
  exact (J.modular i).rescaleUnit_neg_one.orthogonalProduct htarget

/-- The negative adjunction does not change the source component's norm
group. -/
theorem negativeAdjunctionSource_normGroupSet_eq :
    normGroupSet (negativeAdjunctionSourceForm J i)
        (negativeAdjunctionSourceLattice J i) =
      normGroupSet (J.component i).space (J.component i).lattice := by
  calc
    normGroupSet (negativeAdjunctionSourceForm J i)
        (negativeAdjunctionSourceLattice J i) =
        normGroupSet ((J.component i).space.rescaleUnit (-1 : Kˣ))
          (J.component i).lattice :=
      normGroupSet_orthogonalProduct_eq_of_eq <|
        normGroupSet_rescaleUnit_neg_one (J.component i).space
          (J.component i).lattice
    _ = normGroupSet (J.component i).space (J.component i).lattice :=
      normGroupSet_rescaleUnit_neg_one (J.component i).space
        (J.component i).lattice

/-- For saturated splittings of the same fundamental type, the target
negative adjunction has the same norm group as the source component. -/
theorem negativeAdjunctionTarget_normGroupSet_eq
    (hJ : J.IsSaturated) (hH : H.IsSaturated)
    (F : SameFundamentalType J H) :
    normGroupSet (negativeAdjunctionTargetForm J H i)
        (negativeAdjunctionTargetLattice J H i) =
      normGroupSet (J.component i).space (J.component i).lattice := by
  calc
    normGroupSet (negativeAdjunctionTargetForm J H i)
        (negativeAdjunctionTargetLattice J H i) =
        normGroupSet ((J.component i).space.rescaleUnit (-1 : Kˣ))
          (J.component i).lattice :=
      normGroupSet_orthogonalProduct_eq_of_eq <|
        (normGroupSet_rescaleUnit_neg_one (J.component i).space
          (J.component i).lattice).trans
            (hJ.componentNormGroup_eq hH F i).symm
    _ = normGroupSet (J.component i).space (J.component i).lattice :=
      normGroupSet_rescaleUnit_neg_one (J.component i).space
        (J.component i).lattice

/-- The source negative adjunction has twice the rank of the original
component. -/
theorem negativeAdjunctionSource_finrank :
    finrank K ((J.component i).carrier × (J.component i).carrier) =
      2 * J.componentRank i := by
  letI : Module.Finite K (J.component i).carrier :=
    (J.component i).lattice.moduleFinite
  rw [Module.finrank_prod]
  unfold componentRank
  omega

/-- Equality of fundamental dimensions makes the target negative adjunction
have the same doubled rank. -/
theorem negativeAdjunctionTarget_finrank
    (F : SameFundamentalType J H) :
    finrank K ((J.component i).carrier × (H.component i).carrier) =
      2 * J.componentRank i := by
  letI : Module.Finite K (J.component i).carrier :=
    (J.component i).lattice.moduleFinite
  letI : Module.Finite K (H.component i).carrier :=
    (H.component i).lattice.moduleFinite
  have hrank := F.componentRank_eq i
  rw [F.indexEquiv_apply_eq_self] at hrank
  rw [Module.finrank_prod]
  unfold componentRank at hrank ⊢
  omega

/-- Repeated 93:18(v) reduction of the hyperbolicized source component. -/
noncomputable def negativeAdjunctionSourceRankFourReduction
    (hrank : 2 ≤ J.componentRank i) :
    Omeara9318RankFourReductionData
      (negativeAdjunctionSourceForm J i)
      (negativeAdjunctionSourceLattice J i) (J.scaleGenerator i) := by
  apply Omeara9318RankFourReductionData.reduce
    (negativeAdjunctionSourceForm J i)
    (negativeAdjunctionSourceLattice J i) (J.scaleGenerator i)
    (negativeAdjunctionSource_modular J i)
  · rw [negativeAdjunctionSource_finrank J i]
    omega
  · rw [negativeAdjunctionSource_finrank J i]
    exact ⟨J.componentRank i, by omega⟩

/-- Repeated 93:18(v) reduction of the corresponding hyperbolicized target
component. -/
noncomputable def negativeAdjunctionTargetRankFourReduction
    (F : SameFundamentalType J H) (hrank : 2 ≤ J.componentRank i) :
    Omeara9318RankFourReductionData
      (negativeAdjunctionTargetForm J H i)
      (negativeAdjunctionTargetLattice J H i) (J.scaleGenerator i) := by
  apply Omeara9318RankFourReductionData.reduce
    (negativeAdjunctionTargetForm J H i)
    (negativeAdjunctionTargetLattice J H i) (J.scaleGenerator i)
    (negativeAdjunctionTarget_modular J H i F)
  · rw [negativeAdjunctionTarget_finrank J H i F]
    omega
  · rw [negativeAdjunctionTarget_finrank J H i F]
    exact ⟨J.componentRank i, by omega⟩

/-- The paired rank-four reductions occurring in step 2 of O'Meara 93:28.
The source residual is exhibited as a four-dimensional hyperbolic space,
and both residual norm groups are identified with the norm group of the
original source component. -/
structure Omeara9328RankFourComponentPairData
    (J : JordanDecomposition q L t) (H : JordanDecomposition r M t)
    (i : Fin t) where
  source : Omeara9318RankFourReductionData
    (negativeAdjunctionSourceForm J i)
    (negativeAdjunctionSourceLattice J i) (J.scaleGenerator i)
  target : Omeara9318RankFourReductionData
    (negativeAdjunctionTargetForm J H i)
    (negativeAdjunctionTargetLattice J H i) (J.scaleGenerator i)
  planeCount_eq : target.planeCount = source.planeCount
  sourceResidualSpaceIsometry : QuadraticSpace.Isometry source.form
    (QuadraticSpace.scaledZeroOmearaTowerForm (J.scaleGenerator i) 2)
  sourceResidualNormGroupSet_eq :
    normGroupSet source.form source.lattice =
      normGroupSet (J.component i).space (J.component i).lattice
  targetResidualNormGroupSet_eq :
    normGroupSet target.form target.lattice =
      normGroupSet (J.component i).space (J.component i).lattice

namespace Omeara9328RankFourComponentPairData

/-- Construct the paired rank-four reductions from saturation, equality of
fundamental type, and the rank bound supplied by the preliminary two-plane
stabilization. -/
noncomputable def ofSaturated
    (J : JordanDecomposition q L t) (H : JordanDecomposition r M t)
    (i : Fin t) (hJ : J.IsSaturated) (hH : H.IsSaturated)
    (F : SameFundamentalType J H) (hrank : 2 ≤ J.componentRank i) :
    Omeara9328RankFourComponentPairData J H i := by
  let S := negativeAdjunctionSourceRankFourReduction J i hrank
  let T := negativeAdjunctionTargetRankFourReduction J H i F hrank
  have hSambient := S.ambient_finrank_eq
  have hTambient := T.ambient_finrank_eq
  rw [negativeAdjunctionSource_finrank J i] at hSambient
  rw [negativeAdjunctionTarget_finrank J H i F] at hTambient
  have hplanes : T.planeCount = S.planeCount := by omega
  have hrankTower : J.componentRank i = 2 + S.planeCount := by omega
  letI : Module.Finite K (J.component i).carrier :=
    (J.component i).lattice.moduleFinite
  let hyperbolic : QuadraticSpace.Isometry
      (negativeAdjunctionSourceForm J i)
      (hyperbolicExtensionForm
        (zeroCoordinateQuadraticSpace (K := K)) (J.componentRank i)) :=
    negativeQuadraticHyperbolicIsometry (J.component i).space
  let full : QuadraticSpace.Isometry
      (negativeAdjunctionSourceForm J i)
      (QuadraticSpace.scaledZeroOmearaTowerForm
        (J.scaleGenerator i) (2 + S.planeCount)) := by
    rw [← hrankTower]
    exact hyperbolic.trans
      (QuadraticSpace.hyperbolicExtensionToScaledZeroOmearaTowerSpaceIsometry
        (J.scaleGenerator i) (J.componentRank i))
  exact
    { source := S
      target := T
      planeCount_eq := hplanes
      sourceResidualSpaceIsometry :=
        S.residualSpaceIsometryOfFullTowerIsometry full
      sourceResidualNormGroupSet_eq :=
        S.residual_normGroupSet_eq.trans
          (negativeAdjunctionSource_normGroupSet_eq J i)
      targetResidualNormGroupSet_eq :=
        T.residual_normGroupSet_eq.trans
          (negativeAdjunctionTarget_normGroupSet_eq J H i hJ hH F) }

end Omeara9328RankFourComponentPairData

end JordanDecomposition

end Lattice

end Bong
