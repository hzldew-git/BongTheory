/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.JordanReplaceFirstPair
import Bong.Lattice.JordanIsometry
import Bong.Lattice.OrthogonalProductDecomposition
import Bong.Lattice.OmearaSaturationCriterion

/-!
# Producing a Jordan pair replacement from an integral isometry

An isometry from a displayed orthogonal product onto the amalgamated first
two Jordan components produces a new two-component splitting there.  If the
two displayed factors have the old modular scale and norm ideals, the generic
replacement theorem then supplies a Jordan decomposition of the original
lattice.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v x y

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {X : Type x} [AddCommGroup X] [Module K X]
  {Y : Type y} [AddCommGroup Y] [Module K Y]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
  {p : QuadraticSpace K X} {s : QuadraticSpace K Y}
  {N : Lattice K X} {R : Lattice K Y}

/-- The two-factor decomposition transported onto the amalgamated first pair
of a Jordan decomposition. -/
noncomputable def firstPairDecompositionOfIsometry
    (J : JordanDecomposition q L (n + 2))
    (f : Isometry (p.orthogonalSum s) (J.firstPairSublattice).space
      (product N R) (J.firstPairSublattice).lattice) :
    OrthogonalDecomposition (J.firstPairSublattice).space
      (J.firstPairSublattice).lattice 2 :=
  (orthogonalProductDecomposition p s N R).mapIsometry f

/-- The first displayed factor is integrally isometric to the first component
of the transported pair decomposition. -/
noncomputable def firstPairDecompositionOfIsometry_left
    (J : JordanDecomposition q L (n + 2))
    (f : Isometry (p.orthogonalSum s) (J.firstPairSublattice).space
      (product N R) (J.firstPairSublattice).lattice) :
    Isometry p ((J.firstPairDecompositionOfIsometry f).component 0).space
      N ((J.firstPairDecompositionOfIsometry f).component 0).lattice := by
  let D := orthogonalProductDecomposition p s N R
  exact (orthogonalProductLeftComponentIsometry p s N).trans
    ((D.component 0).mapLatticeIsometry f)

/-- The second displayed factor is integrally isometric to the second
component of the transported pair decomposition. -/
noncomputable def firstPairDecompositionOfIsometry_right
    (J : JordanDecomposition q L (n + 2))
    (f : Isometry (p.orthogonalSum s) (J.firstPairSublattice).space
      (product N R) (J.firstPairSublattice).lattice) :
    Isometry s ((J.firstPairDecompositionOfIsometry f).component 1).space
      R ((J.firstPairDecompositionOfIsometry f).component 1).lattice := by
  let D := orthogonalProductDecomposition p s N R
  exact (orthogonalProductRightComponentIsometry p s R).trans
    ((D.component 1).mapLatticeIsometry f)

/-- The first displayed factor maps all the way to the corresponding
quadratic sublattice in the original ambient space. -/
noncomputable def firstPairReplacementLeftIsometry
    (J : JordanDecomposition q L (n + 2))
    (f : Isometry (p.orthogonalSum s) (J.firstPairSublattice).space
      (product N R) (J.firstPairSublattice).lattice) :
    Isometry p
      ((J.firstPairSublattice).liftNested
        ((J.firstPairDecompositionOfIsometry f).component 0)).space
      N
      ((J.firstPairSublattice).liftNested
        ((J.firstPairDecompositionOfIsometry f).component 0)).lattice :=
  (J.firstPairDecompositionOfIsometry_left f).trans
    ((J.firstPairSublattice).liftNestedIsometry
      ((J.firstPairDecompositionOfIsometry f).component 0))

/-- The analogous integral map for the second displayed factor. -/
noncomputable def firstPairReplacementRightIsometry
    (J : JordanDecomposition q L (n + 2))
    (f : Isometry (p.orthogonalSum s) (J.firstPairSublattice).space
      (product N R) (J.firstPairSublattice).lattice) :
    Isometry s
      ((J.firstPairSublattice).liftNested
        ((J.firstPairDecompositionOfIsometry f).component 1)).space
      R
      ((J.firstPairSublattice).liftNested
        ((J.firstPairDecompositionOfIsometry f).component 1)).lattice :=
  (J.firstPairDecompositionOfIsometry_right f).trans
    ((J.firstPairSublattice).liftNestedIsometry
      ((J.firstPairDecompositionOfIsometry f).component 1))

/-- Replace the first pair directly from an integral isometry of a displayed
orthogonal product.  All scale and norm verification is transported through
the two component isometries. -/
noncomputable def replaceFirstPairOfIsometry
    (J : JordanDecomposition q L (n + 2))
    (f : Isometry (p.orthogonalSum s) (J.firstPairSublattice).space
      (product N R) (J.firstPairSublattice).lattice)
    (hpModular : IsModular p N (J.scaleGenerator 0))
    (hsModular : IsModular s R (J.scaleGenerator 1))
    (hpScale : scaleIdeal p N =
      principalIdeal (K := K) (J.scaleGenerator 0 : K))
    (hsScale : scaleIdeal s R =
      principalIdeal (K := K) (J.scaleGenerator 1 : K))
    (hpNorm : normIdeal p N =
      principalIdeal (K := K) (J.normGenerator 0 : K))
    (hsNorm : normIdeal s R =
      principalIdeal (K := K) (J.normGenerator 1 : K)) :
    JordanDecomposition q L (n + 2) := by
  let P := J.firstPairDecompositionOfIsometry f
  let g0 := J.firstPairReplacementLeftIsometry f
  let g1 := J.firstPairReplacementRightIsometry f
  apply J.replaceFirstPair P
  · exact hpModular.mapLatticeIsometry g0
  · exact hsModular.mapLatticeIsometry g1
  · calc
      scaleIdeal
          ((J.firstPairSublattice).liftNested (P.component 0)).space
          ((J.firstPairSublattice).liftNested (P.component 0)).lattice =
          scaleIdeal p N := by
        rw [← g0.map_eq]
        exact scaleIdeal_map_isometry g0.toQuadraticSpaceIsometry N
      _ = principalIdeal (K := K) (J.scaleGenerator 0 : K) := hpScale
  · calc
      scaleIdeal
          ((J.firstPairSublattice).liftNested (P.component 1)).space
          ((J.firstPairSublattice).liftNested (P.component 1)).lattice =
          scaleIdeal s R := by
        rw [← g1.map_eq]
        exact scaleIdeal_map_isometry g1.toQuadraticSpaceIsometry R
      _ = principalIdeal (K := K) (J.scaleGenerator 1 : K) := hsScale
  · calc
      normIdeal
          ((J.firstPairSublattice).liftNested (P.component 0)).space
          ((J.firstPairSublattice).liftNested (P.component 0)).lattice =
          normIdeal p N := by
        rw [← g0.map_eq]
        exact normIdeal_map_isometry g0.toQuadraticSpaceIsometry N
      _ = principalIdeal (K := K) (J.normGenerator 0 : K) := hpNorm
  · calc
      normIdeal
          ((J.firstPairSublattice).liftNested (P.component 1)).space
          ((J.firstPairSublattice).liftNested (P.component 1)).lattice =
          normIdeal s R := by
        rw [← g1.map_eq]
        exact normIdeal_map_isometry g1.toQuadraticSpaceIsometry R
      _ = principalIdeal (K := K) (J.normGenerator 1 : K) := hsNorm

/-- The displayed left factor maps integrally onto the first component of
the Jordan decomposition produced by `replaceFirstPairOfIsometry`. -/
noncomputable def replaceFirstPairOfIsometry_leftIsometry
    (J : JordanDecomposition q L (n + 2))
    (f : Isometry (p.orthogonalSum s) (J.firstPairSublattice).space
      (product N R) (J.firstPairSublattice).lattice)
    (hpModular : IsModular p N (J.scaleGenerator 0))
    (hsModular : IsModular s R (J.scaleGenerator 1))
    (hpScale : scaleIdeal p N =
      principalIdeal (K := K) (J.scaleGenerator 0 : K))
    (hsScale : scaleIdeal s R =
      principalIdeal (K := K) (J.scaleGenerator 1 : K))
    (hpNorm : normIdeal p N =
      principalIdeal (K := K) (J.normGenerator 0 : K))
    (hsNorm : normIdeal s R =
      principalIdeal (K := K) (J.normGenerator 1 : K)) :
    Isometry p
      ((J.replaceFirstPairOfIsometry f hpModular hsModular hpScale hsScale
        hpNorm hsNorm).component 0).space
      N
      ((J.replaceFirstPairOfIsometry f hpModular hsModular hpScale hsScale
        hpNorm hsNorm).component 0).lattice := by
  unfold replaceFirstPairOfIsometry
  rw [replaceFirstPair_component_zero]
  exact J.firstPairReplacementLeftIsometry f

/-- The analogous integral isometry for the displayed right factor. -/
noncomputable def replaceFirstPairOfIsometry_rightIsometry
    (J : JordanDecomposition q L (n + 2))
    (f : Isometry (p.orthogonalSum s) (J.firstPairSublattice).space
      (product N R) (J.firstPairSublattice).lattice)
    (hpModular : IsModular p N (J.scaleGenerator 0))
    (hsModular : IsModular s R (J.scaleGenerator 1))
    (hpScale : scaleIdeal p N =
      principalIdeal (K := K) (J.scaleGenerator 0 : K))
    (hsScale : scaleIdeal s R =
      principalIdeal (K := K) (J.scaleGenerator 1 : K))
    (hpNorm : normIdeal p N =
      principalIdeal (K := K) (J.normGenerator 0 : K))
    (hsNorm : normIdeal s R =
      principalIdeal (K := K) (J.normGenerator 1 : K)) :
    Isometry s
      ((J.replaceFirstPairOfIsometry f hpModular hsModular hpScale hsScale
        hpNorm hsNorm).component 1).space
      R
      ((J.replaceFirstPairOfIsometry f hpModular hsModular hpScale hsScale
        hpNorm hsNorm).component 1).lattice := by
  unfold replaceFirstPairOfIsometry
  rw [replaceFirstPair_component_one]
  exact J.firstPairReplacementRightIsometry f

/-- A pair replacement is a different Jordan splitting of the same lattice,
so its complete fundamental type agrees with the original splitting. -/
noncomputable def replaceFirstPairOfIsometry_sameFundamentalType
    (J : JordanDecomposition q L (n + 2))
    (f : Isometry (p.orthogonalSum s) (J.firstPairSublattice).space
      (product N R) (J.firstPairSublattice).lattice)
    (hpModular) (hsModular) (hpScale) (hsScale) (hpNorm) (hsNorm) :
    SameFundamentalType J
      (J.replaceFirstPairOfIsometry f hpModular hsModular hpScale hsScale
        hpNorm hsNorm) :=
  sameFundamentalTypeOfIsometry J _ (Isometry.refl q L)

/-- Saturation is retained when each new component norm group contains the
old corresponding saturated component norm group.  The opposite inclusion is
automatic because every displayed component lies in its intrinsic scale
layer. -/
theorem replaceFirstPairOfIsometry_isSaturated
    (J : JordanDecomposition q L (n + 2))
    (f : Isometry (p.orthogonalSum s) (J.firstPairSublattice).space
      (product N R) (J.firstPairSublattice).lattice)
    (hpModular : IsModular p N (J.scaleGenerator 0))
    (hsModular : IsModular s R (J.scaleGenerator 1))
    (hpScale : scaleIdeal p N =
      principalIdeal (K := K) (J.scaleGenerator 0 : K))
    (hsScale : scaleIdeal s R =
      principalIdeal (K := K) (J.scaleGenerator 1 : K))
    (hpNorm : normIdeal p N =
      principalIdeal (K := K) (J.normGenerator 0 : K))
    (hsNorm : normIdeal s R =
      principalIdeal (K := K) (J.normGenerator 1 : K))
    (hJ : J.IsSaturated)
    (hpContains : normGroupSet (J.component 0).space
        (J.component 0).lattice ⊆ normGroupSet p N)
    (hsContains : normGroupSet (J.component 1).space
        (J.component 1).lattice ⊆ normGroupSet s R) :
    (J.replaceFirstPairOfIsometry f hpModular hsModular hpScale hsScale
      hpNorm hsNorm).IsSaturated := by
  let T := J.replaceFirstPairOfIsometry f hpModular hsModular hpScale hsScale
    hpNorm hsNorm
  let F : SameFundamentalType J T :=
    J.replaceFirstPairOfIsometry_sameFundamentalType f hpModular hsModular
      hpScale hsScale hpNorm hsNorm
  intro i
  by_cases hi0 : i = 0
  · subst i
    let g0 := J.firstPairReplacementLeftIsometry f
    have hfund := F.normGroup_eq (0 : Fin (n + 2))
    rw [F.indexEquiv_apply_eq_self] at hfund
    apply Set.Subset.antisymm
    · exact T.componentNormGroup_subset_fundamental 0
    · intro z hz
      rw [hfund] at hz
      have hzOld : z ∈ normGroupSet (J.component 0).space
          (J.component 0).lattice := by
        rw [hJ 0]
        exact hz
      have hzSource : z ∈ normGroupSet p N := hpContains hzOld
      change z ∈ normGroupSet
        ((J.firstPairSublattice).liftNested
          ((J.firstPairDecompositionOfIsometry f).component 0)).space
        ((J.firstPairSublattice).liftNested
          ((J.firstPairDecompositionOfIsometry f).component 0)).lattice
      rw [normGroupSet_eq_of_latticeIsometry g0]
      exact hzSource
  · by_cases hi1 : i = 1
    · subst i
      let g1 := J.firstPairReplacementRightIsometry f
      have hfund := F.normGroup_eq (1 : Fin (n + 2))
      rw [F.indexEquiv_apply_eq_self] at hfund
      apply Set.Subset.antisymm
      · exact T.componentNormGroup_subset_fundamental 1
      · intro z hz
        rw [hfund] at hz
        have hzOld : z ∈ normGroupSet (J.component 1).space
            (J.component 1).lattice := by
          rw [hJ 1]
          exact hz
        have hzSource : z ∈ normGroupSet s R := hsContains hzOld
        change z ∈ normGroupSet
          ((J.firstPairSublattice).liftNested
            ((J.firstPairDecompositionOfIsometry f).component 1)).space
          ((J.firstPairSublattice).liftNested
            ((J.firstPairDecompositionOfIsometry f).component 1)).lattice
        rw [normGroupSet_eq_of_latticeIsometry g1]
        exact hzSource
    · have hfund := F.normGroup_eq i
      rw [F.indexEquiv_apply_eq_self] at hfund
      have hcomponent : T.component i = J.component i := by
        change
          (J.toOrthogonalDecomposition.replacePair firstIndex_ne_secondIndex
            (J.firstPairDecompositionOfIsometry f)).component i =
            J.component i
        exact J.toOrthogonalDecomposition.replacePair_component_other
          firstIndex_ne_secondIndex (J.firstPairDecompositionOfIsometry f)
            i hi0 hi1
      change normGroupSet (T.component i).space (T.component i).lattice =
        T.fundamentalNormGroup i
      rw [hcomponent, hfund]
      exact hJ i

end Lattice.JordanDecomposition

end Bong
