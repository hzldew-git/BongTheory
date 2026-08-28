/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma45Proof
import Bong.Bong.BeliLemma41AdaptedBinary
import Bong.Bong.JordanProfileOrder
import Bong.Lattice.OmearaRawJordan
import Bong.Lattice.OrthogonalDecompositionReplacePair
import Bong.Lattice.OrthogonalProductDecomposition
import Bong.Lattice.RankOneNormScale

/-!
# Proof of Beli (2003), Lemma 4.6

This file implements Beli's terminating modular-block replacement argument.
Starting from O'Meara's scale-ordered unary/binary decomposition, a bad norm
component is paired with a component attaining the effective norm at its
scale.  Lemma 4.5 changes only that bad norm.  The finite bad-index set
strictly shrinks, and the terminal decomposition is a maximal norm splitting.
-/

namespace Bong

open Dyadic
open Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Lattice.ModularPairSplitting

variable {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- Transport a modular pair splitting through an integral isometry. -/
noncomputable def mapIsometry (P : ModularPairSplitting q L)
    (f : Lattice.Isometry q r L M) : ModularPairSplitting r M where
  toOrthogonalDecomposition := P.toOrthogonalDecomposition.mapIsometry f
  scaleGenerator := P.scaleGenerator
  normGenerator := P.normGenerator
  modular := by
    intro i
    exact (P.modular i).mapLatticeIsometry
      ((P.component i).mapLatticeIsometry f)
  scaleIdeal_eq := by
    intro i
    let g := (P.component i).mapLatticeIsometry f
    calc
      Lattice.scaleIdeal ((P.component i).mapIsometry f).space
          ((P.component i).mapIsometry f).lattice =
          Lattice.scaleIdeal (P.component i).space
            (P.component i).lattice := by
        rw [← g.map_eq]
        exact Lattice.scaleIdeal_map_isometry
          g.toQuadraticSpaceIsometry _
      _ = Lattice.principalIdeal (K := K)
          (P.scaleGenerator i : K) := P.scaleIdeal_eq i
  normIdeal_eq := by
    intro i
    let g := (P.component i).mapLatticeIsometry f
    calc
      Lattice.normIdeal ((P.component i).mapIsometry f).space
          ((P.component i).mapIsometry f).lattice =
          Lattice.normIdeal (P.component i).space
            (P.component i).lattice := by
        rw [← g.map_eq]
        exact Lattice.normIdeal_map_isometry
          g.toQuadraticSpaceIsometry _
      _ = Lattice.principalIdeal (K := K)
          (P.normGenerator i : K) := P.normIdeal_eq i
  first_rank := by
    change finrank K ((P.component 0).mapIsometry f).carrier = 2
    rw [Lattice.QuadraticSublattice.finrank_mapIsometry]
    exact P.first_rank

@[simp]
theorem mapIsometry_component (P : ModularPairSplitting q L)
    (f : Lattice.Isometry q r L M) (i : Fin 2) :
    (P.mapIsometry f).component i = (P.component i).mapIsometry f :=
  rfl

@[simp]
theorem mapIsometry_scaleGenerator (P : ModularPairSplitting q L)
    (f : Lattice.Isometry q r L M) (i : Fin 2) :
    (P.mapIsometry f).scaleGenerator i = P.scaleGenerator i :=
  rfl

@[simp]
theorem mapIsometry_normGenerator (P : ModularPairSplitting q L)
    (f : Lattice.Isometry q r L M) (i : Fin 2) :
    (P.mapIsometry f).normGenerator i = P.normGenerator i :=
  rfl

@[simp]
theorem mapIsometry_componentRank (P : ModularPairSplitting q L)
    (f : Lattice.Isometry q r L M) (i : Fin 2) :
    (P.mapIsometry f).componentRank i = P.componentRank i := by
  exact (P.component i).finrank_mapIsometry f

@[simp]
theorem mapIsometry_scaleOrder (P : ModularPairSplitting q L)
    (f : Lattice.Isometry q r L M) (i : Fin 2) :
    (P.mapIsometry f).scaleOrder i = P.scaleOrder i :=
  rfl

@[simp]
theorem mapIsometry_normOrder (P : ModularPairSplitting q L)
    (f : Lattice.Isometry q r L M) (i : Fin 2) :
    (P.mapIsometry f).normOrder i = P.normOrder i :=
  rfl

@[simp]
theorem mapIsometry_dualNormOrder (P : ModularPairSplitting q L)
    (f : Lattice.Isometry q r L M) (i : Fin 2) :
    (P.mapIsometry f).dualNormOrder i = P.dualNormOrder i :=
  rfl

/-- Preserving exact scale ideals preserves their valuation orders. -/
theorem scaleOrder_eq_of_preserves (P P' : ModularPairSplitting q L)
    (hpres : P.PreservesRanksAndScales P') (i : Fin 2) :
    P'.scaleOrder i = P.scaleOrder i := by
  apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
  calc
    Lattice.principalIdeal (K := K) (P'.scaleGenerator i : K) =
        Lattice.scaleIdeal (P'.component i).space
          (P'.component i).lattice := (P'.scaleIdeal_eq i).symm
    _ = Lattice.scaleIdeal (P.component i).space
          (P.component i).lattice := (hpres i).2
    _ = Lattice.principalIdeal (K := K)
          (P.scaleGenerator i : K) := P.scaleIdeal_eq i

/-- Lemma 4.5(i)'s exact norm-ideal statement gives equality of norm
orders with the old second component. -/
theorem normOrder_eq_oldSecond_of_normsEqual
    (P P' : ModularPairSplitting q L)
    (hnorms : P.NormsEqualOldSecond P') (i : Fin 2) :
    P'.normOrder i = P.normOrder 1 := by
  apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
  calc
    Lattice.principalIdeal (K := K) (P'.normGenerator i : K) =
        Lattice.normIdeal (P'.component i).space
          (P'.component i).lattice := (P'.normIdeal_eq i).symm
    _ = Lattice.normIdeal (P.component 1).space
          (P.component 1).lattice := hnorms i
    _ = Lattice.principalIdeal (K := K)
          (P.normGenerator 1 : K) := P.normIdeal_eq 1

end Lattice.ModularPairSplitting

namespace Lattice.RawJordanDecomposition

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The canonical product-space modular pair formed from two components,
with the component at `i` placed first. -/
noncomputable def pairProduct (R : RawJordanDecomposition q L t)
    (i j : Fin t)
    (hi : finrank K (R.component i).carrier = 2) :
    ModularPairSplitting
      ((R.component i).space.orthogonalSum (R.component j).space)
      (Lattice.product (R.component i).lattice
        (R.component j).lattice) := by
  let E := Lattice.orthogonalProductDecomposition
    (R.component i).space (R.component j).space
    (R.component i).lattice (R.component j).lattice
  let scale : Fin 2 → Kˣ :=
    Fin.cases (R.scaleGenerator i) (fun _ ↦ R.scaleGenerator j)
  let norm : Fin 2 → Kˣ :=
    Fin.cases (R.normGenerator i) (fun _ ↦ R.normGenerator j)
  exact {
    toOrthogonalDecomposition := E
    scaleGenerator := scale
    normGenerator := norm
    modular := by
      intro k
      fin_cases k
      · change Lattice.IsModular
          (Lattice.orthogonalProductLeftComponent
            (R.component i).space (R.component j).space
            (R.component i).lattice).space
          (Lattice.orthogonalProductLeftComponent
            (R.component i).space (R.component j).space
            (R.component i).lattice).lattice
          (R.scaleGenerator i)
        exact (R.modular i).mapLatticeIsometry
          (Lattice.orthogonalProductLeftComponentIsometry
            (R.component i).space (R.component j).space
            (R.component i).lattice)
      · change Lattice.IsModular
          (Lattice.orthogonalProductRightComponent
            (R.component i).space (R.component j).space
            (R.component j).lattice).space
          (Lattice.orthogonalProductRightComponent
            (R.component i).space (R.component j).space
            (R.component j).lattice).lattice
          (R.scaleGenerator j)
        exact (R.modular j).mapLatticeIsometry
          (Lattice.orthogonalProductRightComponentIsometry
            (R.component i).space (R.component j).space
            (R.component j).lattice)
    scaleIdeal_eq := by
      intro k
      fin_cases k
      · let f := Lattice.orthogonalProductLeftComponentIsometry
            (R.component i).space (R.component j).space
            (R.component i).lattice
        calc
          Lattice.scaleIdeal
              (Lattice.orthogonalProductLeftComponent
                (R.component i).space (R.component j).space
                (R.component i).lattice).space
              (Lattice.orthogonalProductLeftComponent
                (R.component i).space (R.component j).space
                (R.component i).lattice).lattice =
              Lattice.scaleIdeal (R.component i).space
                (R.component i).lattice := by
            rw [← f.map_eq]
            exact Lattice.scaleIdeal_map_isometry
              f.toQuadraticSpaceIsometry _
          _ = Lattice.principalIdeal (K := K)
              (R.scaleGenerator i : K) := R.scaleIdeal_eq i
      · let f := Lattice.orthogonalProductRightComponentIsometry
            (R.component i).space (R.component j).space
            (R.component j).lattice
        calc
          Lattice.scaleIdeal
              (Lattice.orthogonalProductRightComponent
                (R.component i).space (R.component j).space
                (R.component j).lattice).space
              (Lattice.orthogonalProductRightComponent
                (R.component i).space (R.component j).space
                (R.component j).lattice).lattice =
              Lattice.scaleIdeal (R.component j).space
                (R.component j).lattice := by
            rw [← f.map_eq]
            exact Lattice.scaleIdeal_map_isometry
              f.toQuadraticSpaceIsometry _
          _ = Lattice.principalIdeal (K := K)
              (R.scaleGenerator j : K) := R.scaleIdeal_eq j
    normIdeal_eq := by
      intro k
      fin_cases k
      · let f := Lattice.orthogonalProductLeftComponentIsometry
            (R.component i).space (R.component j).space
            (R.component i).lattice
        calc
          Lattice.normIdeal
              (Lattice.orthogonalProductLeftComponent
                (R.component i).space (R.component j).space
                (R.component i).lattice).space
              (Lattice.orthogonalProductLeftComponent
                (R.component i).space (R.component j).space
                (R.component i).lattice).lattice =
              Lattice.normIdeal (R.component i).space
                (R.component i).lattice := by
            rw [← f.map_eq]
            exact Lattice.normIdeal_map_isometry
              f.toQuadraticSpaceIsometry _
          _ = Lattice.principalIdeal (K := K)
              (R.normGenerator i : K) := R.normIdeal_eq i
      · let f := Lattice.orthogonalProductRightComponentIsometry
            (R.component i).space (R.component j).space
            (R.component j).lattice
        calc
          Lattice.normIdeal
              (Lattice.orthogonalProductRightComponent
                (R.component i).space (R.component j).space
                (R.component j).lattice).space
              (Lattice.orthogonalProductRightComponent
                (R.component i).space (R.component j).space
                (R.component j).lattice).lattice =
              Lattice.normIdeal (R.component j).space
                (R.component j).lattice := by
            rw [← f.map_eq]
            exact Lattice.normIdeal_map_isometry
              f.toQuadraticSpaceIsometry _
          _ = Lattice.principalIdeal (K := K)
              (R.normGenerator j : K) := R.normIdeal_eq j
    first_rank := by
      let f := Lattice.orthogonalProductLeftComponentIsometry
        (R.component i).space (R.component j).space
        (R.component i).lattice
      have hrank := f.toLinearEquiv.finrank_eq
      change finrank K
        (Lattice.orthogonalProductLeftComponent
          (R.component i).space (R.component j).space
          (R.component i).lattice).carrier = 2
      omega
  }

@[simp]
theorem pairProduct_scaleGenerator_zero
    (R : RawJordanDecomposition q L t) (i j : Fin t)
    (hi : finrank K (R.component i).carrier = 2) :
    (R.pairProduct i j hi).scaleGenerator 0 = R.scaleGenerator i :=
  rfl

@[simp]
theorem pairProduct_scaleGenerator_one
    (R : RawJordanDecomposition q L t) (i j : Fin t)
    (hi : finrank K (R.component i).carrier = 2) :
    (R.pairProduct i j hi).scaleGenerator 1 = R.scaleGenerator j :=
  rfl

@[simp]
theorem pairProduct_normGenerator_zero
    (R : RawJordanDecomposition q L t) (i j : Fin t)
    (hi : finrank K (R.component i).carrier = 2) :
    (R.pairProduct i j hi).normGenerator 0 = R.normGenerator i :=
  rfl

@[simp]
theorem pairProduct_normGenerator_one
    (R : RawJordanDecomposition q L t) (i j : Fin t)
    (hi : finrank K (R.component i).carrier = 2) :
    (R.pairProduct i j hi).normGenerator 1 = R.normGenerator j :=
  rfl

/-- The same modular pair in the carrier of the two old components. -/
noncomputable def pairSplitting (R : RawJordanDecomposition q L t)
    (i j : Fin t) (hij : i ≠ j)
    (hi : finrank K (R.component i).carrier = 2) :
    ModularPairSplitting
      (R.toOrthogonalDecomposition.orthogonalSup hij).space
      (R.toOrthogonalDecomposition.orthogonalSup hij).lattice :=
  (R.pairProduct i j hi).mapIsometry
    (R.toOrthogonalDecomposition.orthogonalSupLatticeIsometry hij)

@[simp]
theorem pairSplitting_componentRank_zero
    (R : RawJordanDecomposition q L t)
    (i j : Fin t) (hij : i ≠ j)
    (hi : finrank K (R.component i).carrier = 2) :
    (R.pairSplitting i j hij hi).componentRank 0 =
      finrank K (R.component i).carrier := by
  rw [pairSplitting, Lattice.ModularPairSplitting.mapIsometry_componentRank]
  change finrank K
      (Lattice.orthogonalProductLeftComponent
        (R.component i).space (R.component j).space
        (R.component i).lattice).carrier = _
  let f := Lattice.orthogonalProductLeftComponentIsometry
    (R.component i).space (R.component j).space
    (R.component i).lattice
  exact f.toLinearEquiv.finrank_eq.symm

@[simp]
theorem pairSplitting_componentRank_one
    (R : RawJordanDecomposition q L t)
    (i j : Fin t) (hij : i ≠ j)
    (hi : finrank K (R.component i).carrier = 2) :
    (R.pairSplitting i j hij hi).componentRank 1 =
      finrank K (R.component j).carrier := by
  rw [pairSplitting, Lattice.ModularPairSplitting.mapIsometry_componentRank]
  change finrank K
      (Lattice.orthogonalProductRightComponent
        (R.component i).space (R.component j).space
        (R.component j).lattice).carrier = _
  let f := Lattice.orthogonalProductRightComponentIsometry
    (R.component i).space (R.component j).space
    (R.component j).lattice
  exact f.toLinearEquiv.finrank_eq.symm

@[simp]
theorem pairSplitting_scaleOrder_zero
    (R : RawJordanDecomposition q L t)
    (i j : Fin t) (hij : i ≠ j)
    (hi : finrank K (R.component i).carrier = 2) :
    (R.pairSplitting i j hij hi).scaleOrder 0 =
      ordUnit K (R.scaleGenerator i) :=
  rfl

@[simp]
theorem pairSplitting_scaleOrder_one
    (R : RawJordanDecomposition q L t)
    (i j : Fin t) (hij : i ≠ j)
    (hi : finrank K (R.component i).carrier = 2) :
    (R.pairSplitting i j hij hi).scaleOrder 1 =
      ordUnit K (R.scaleGenerator j) :=
  rfl

@[simp]
theorem pairSplitting_normOrder_zero
    (R : RawJordanDecomposition q L t)
    (i j : Fin t) (hij : i ≠ j)
    (hi : finrank K (R.component i).carrier = 2) :
    (R.pairSplitting i j hij hi).normOrder 0 =
      ordUnit K (R.normGenerator i) :=
  rfl

@[simp]
theorem pairSplitting_normOrder_one
    (R : RawJordanDecomposition q L t)
    (i j : Fin t) (hij : i ≠ j)
    (hi : finrank K (R.component i).carrier = 2) :
    (R.pairSplitting i j hij hi).normOrder 1 =
      ordUnit K (R.normGenerator j) :=
  rfl

/-- Norm generators after replacing positions `i,j` by a new modular pair. -/
noncomputable def rebalancedNormGenerator
    (R : RawJordanDecomposition q L t) (i j : Fin t) (hij : i ≠ j)
    (P' : ModularPairSplitting
      (R.toOrthogonalDecomposition.orthogonalSup hij).space
      (R.toOrthogonalDecomposition.orthogonalSup hij).lattice)
    (k : Fin t) : Kˣ :=
  if k = i then P'.normGenerator 0
  else if k = j then P'.normGenerator 1
  else R.normGenerator k

@[simp]
theorem rebalancedNormGenerator_left
    (R : RawJordanDecomposition q L t) (i j : Fin t) (hij : i ≠ j)
    (P' : ModularPairSplitting
      (R.toOrthogonalDecomposition.orthogonalSup hij).space
      (R.toOrthogonalDecomposition.orthogonalSup hij).lattice) :
    @rebalancedNormGenerator K _ _ _ _ _ V _ _ q L t R i j hij P' i =
      P'.normGenerator 0 := by
  simp [rebalancedNormGenerator]

@[simp]
theorem rebalancedNormGenerator_right
    (R : RawJordanDecomposition q L t) (i j : Fin t) (hij : i ≠ j)
    (P' : ModularPairSplitting
      (R.toOrthogonalDecomposition.orthogonalSup hij).space
      (R.toOrthogonalDecomposition.orthogonalSup hij).lattice) :
    @rebalancedNormGenerator K _ _ _ _ _ V _ _ q L t R i j hij P' j =
      P'.normGenerator 1 := by
  simp [rebalancedNormGenerator, hij.symm]

@[simp]
theorem rebalancedNormGenerator_other
    (R : RawJordanDecomposition q L t) (i j : Fin t) (hij : i ≠ j)
    (P' : ModularPairSplitting
      (R.toOrthogonalDecomposition.orthogonalSup hij).space
      (R.toOrthogonalDecomposition.orthogonalSup hij).lattice)
    (k : Fin t) (hki : k ≠ i) (hkj : k ≠ j) :
    @rebalancedNormGenerator K _ _ _ _ _ V _ _ q L t R i j hij P' k =
      R.normGenerator k := by
  simp [rebalancedNormGenerator, hki, hkj]

/-- Put a Lemma 4.5 replacement pair back into a raw scale-ordered
decomposition.  Scale generators stay fixed; the two norm generators are
read from the replacement. -/
noncomputable def rebalancePair
    (R : RawJordanDecomposition q L t) (i j : Fin t) (hij : i ≠ j)
    (hi : finrank K (R.component i).carrier = 2)
    (P' : ModularPairSplitting
      (R.toOrthogonalDecomposition.orthogonalSup hij).space
      (R.toOrthogonalDecomposition.orthogonalSup hij).lattice)
    (hpres : (R.pairSplitting i j hij hi).PreservesRanksAndScales P') :
    RawJordanDecomposition q L t := by
  let C := R.toOrthogonalDecomposition.orthogonalSup hij
  let P := R.pairSplitting i j hij hi
  let D := R.toOrthogonalDecomposition.replacePair hij
    P'.toOrthogonalDecomposition
  have hDleft : D.component i = C.liftNested (P'.component 0) := by
    dsimp only [D, C]
    exact R.toOrthogonalDecomposition.replacePair_component_left
      hij P'.toOrthogonalDecomposition
  have hDright : D.component j = C.liftNested (P'.component 1) := by
    dsimp only [D, C]
    exact R.toOrthogonalDecomposition.replacePair_component_right
      hij P'.toOrthogonalDecomposition
  have hDother (k : Fin t) (hki : k ≠ i) (hkj : k ≠ j) :
      D.component k = R.component k := by
    dsimp only [D]
    exact R.toOrthogonalDecomposition.replacePair_component_other
      hij P'.toOrthogonalDecomposition k hki hkj
  exact {
    toOrthogonalDecomposition := D
    scaleGenerator := R.scaleGenerator
    normGenerator := @rebalancedNormGenerator K _ _ _ _ _ V _ _
      q L t R i j hij P'
    modular := by
      intro k
      by_cases hki : k = i
      · subst k
        rw [hDleft]
        change Lattice.IsModular
          (C.liftNested (P'.component 0)).space
          (C.liftNested (P'.component 0)).lattice
          (R.scaleGenerator i)
        have hprincipal : Lattice.principalIdeal (K := K)
              (P'.scaleGenerator 0 : K) =
            Lattice.principalIdeal (K := K)
              (R.scaleGenerator i : K) :=
          (P'.scaleIdeal_eq 0).symm.trans
            ((hpres 0).2.trans (P.scaleIdeal_eq 0))
        exact Lattice.QuadraticSublattice.IsModular.liftNested
          C (P'.component 0)
            ((P'.modular 0).of_principalIdeal_eq hprincipal)
      · by_cases hkj : k = j
        · subst k
          rw [hDright]
          change Lattice.IsModular
            (C.liftNested (P'.component 1)).space
            (C.liftNested (P'.component 1)).lattice
            (R.scaleGenerator j)
          have hprincipal : Lattice.principalIdeal (K := K)
                (P'.scaleGenerator 1 : K) =
              Lattice.principalIdeal (K := K)
                (R.scaleGenerator j : K) :=
            (P'.scaleIdeal_eq 1).symm.trans
              ((hpres 1).2.trans (P.scaleIdeal_eq 1))
          exact Lattice.QuadraticSublattice.IsModular.liftNested
            C (P'.component 1)
              ((P'.modular 1).of_principalIdeal_eq hprincipal)
        · rw [hDother k hki hkj]
          change Lattice.IsModular (R.component k).space
            (R.component k).lattice (R.scaleGenerator k)
          exact R.modular k
    scaleIdeal_eq := by
      intro k
      by_cases hki : k = i
      · subst k
        rw [hDleft]
        change Lattice.scaleIdeal
            (C.liftNested (P'.component 0)).space
            (C.liftNested (P'.component 0)).lattice =
          Lattice.principalIdeal (K := K) (R.scaleGenerator i : K)
        let g := C.liftNestedIsometry (P'.component 0)
        calc
          Lattice.scaleIdeal
              (C.liftNested (P'.component 0)).space
              (C.liftNested (P'.component 0)).lattice =
              Lattice.scaleIdeal (P'.component 0).space
                (P'.component 0).lattice := by
            rw [← g.map_eq]
            exact Lattice.scaleIdeal_map_isometry
              g.toQuadraticSpaceIsometry _
          _ = Lattice.scaleIdeal (P.component 0).space
              (P.component 0).lattice := (hpres 0).2
          _ = Lattice.principalIdeal (K := K)
              (R.scaleGenerator i : K) := P.scaleIdeal_eq 0
      · by_cases hkj : k = j
        · subst k
          rw [hDright]
          change Lattice.scaleIdeal
              (C.liftNested (P'.component 1)).space
              (C.liftNested (P'.component 1)).lattice =
            Lattice.principalIdeal (K := K) (R.scaleGenerator j : K)
          let g := C.liftNestedIsometry (P'.component 1)
          calc
            Lattice.scaleIdeal
                (C.liftNested (P'.component 1)).space
                (C.liftNested (P'.component 1)).lattice =
                Lattice.scaleIdeal (P'.component 1).space
                  (P'.component 1).lattice := by
              rw [← g.map_eq]
              exact Lattice.scaleIdeal_map_isometry
                g.toQuadraticSpaceIsometry _
            _ = Lattice.scaleIdeal (P.component 1).space
                (P.component 1).lattice := (hpres 1).2
            _ = Lattice.principalIdeal (K := K)
                (R.scaleGenerator j : K) := P.scaleIdeal_eq 1
        · rw [hDother k hki hkj]
          change Lattice.scaleIdeal (R.component k).space
              (R.component k).lattice =
            Lattice.principalIdeal (K := K) (R.scaleGenerator k : K)
          exact R.scaleIdeal_eq k
    normIdeal_eq := by
      intro k
      by_cases hki : k = i
      · subst k
        rw [hDleft]
        rw [R.rebalancedNormGenerator_left i j hij P']
        change Lattice.normIdeal
            (C.liftNested (P'.component 0)).space
            (C.liftNested (P'.component 0)).lattice =
          Lattice.principalIdeal (K := K) (P'.normGenerator 0 : K)
        let g := C.liftNestedIsometry (P'.component 0)
        calc
          Lattice.normIdeal
              (C.liftNested (P'.component 0)).space
              (C.liftNested (P'.component 0)).lattice =
              Lattice.normIdeal (P'.component 0).space
                (P'.component 0).lattice := by
            rw [← g.map_eq]
            exact Lattice.normIdeal_map_isometry
              g.toQuadraticSpaceIsometry _
          _ = Lattice.principalIdeal (K := K)
              (P'.normGenerator 0 : K) := P'.normIdeal_eq 0
      · by_cases hkj : k = j
        · subst k
          rw [hDright]
          rw [R.rebalancedNormGenerator_right i j hij P']
          change Lattice.normIdeal
              (C.liftNested (P'.component 1)).space
              (C.liftNested (P'.component 1)).lattice =
            Lattice.principalIdeal (K := K) (P'.normGenerator 1 : K)
          let g := C.liftNestedIsometry (P'.component 1)
          calc
            Lattice.normIdeal
                (C.liftNested (P'.component 1)).space
                (C.liftNested (P'.component 1)).lattice =
                Lattice.normIdeal (P'.component 1).space
                  (P'.component 1).lattice := by
              rw [← g.map_eq]
              exact Lattice.normIdeal_map_isometry
                g.toQuadraticSpaceIsometry _
            _ = Lattice.principalIdeal (K := K)
                (P'.normGenerator 1 : K) := P'.normIdeal_eq 1
        · rw [hDother k hki hkj]
          rw [R.rebalancedNormGenerator_other i j hij P' k hki hkj]
          change Lattice.normIdeal (R.component k).space
              (R.component k).lattice =
            Lattice.principalIdeal (K := K) (R.normGenerator k : K)
          exact R.normIdeal_eq k
    rank_one_or_two := by
      intro k
      by_cases hki : k = i
      · subst k
        rw [hDleft]
        have hrank : finrank K (C.liftNested (P'.component 0)).carrier =
            finrank K (R.component i).carrier := by
          calc
            finrank K (C.liftNested (P'.component 0)).carrier =
                finrank K (P'.component 0).carrier :=
              C.finrank_liftNested (P'.component 0)
            _ = finrank K (P.component 0).carrier := (hpres 0).1
            _ = finrank K (R.component i).carrier := by
              exact R.pairSplitting_componentRank_zero i j hij hi
        change finrank K (C.liftNested (P'.component 0)).carrier = 1 ∨
          finrank K (C.liftNested (P'.component 0)).carrier = 2
        rw [hrank]
        exact R.rank_one_or_two i
      · by_cases hkj : k = j
        · subst k
          rw [hDright]
          have hrank : finrank K (C.liftNested (P'.component 1)).carrier =
              finrank K (R.component j).carrier := by
            calc
              finrank K (C.liftNested (P'.component 1)).carrier =
                  finrank K (P'.component 1).carrier :=
                C.finrank_liftNested (P'.component 1)
              _ = finrank K (P.component 1).carrier := (hpres 1).1
              _ = finrank K (R.component j).carrier := by
                exact R.pairSplitting_componentRank_one i j hij hi
          change finrank K (C.liftNested (P'.component 1)).carrier = 1 ∨
            finrank K (C.liftNested (P'.component 1)).carrier = 2
          rw [hrank]
          exact R.rank_one_or_two j
        · rw [hDother k hki hkj]
          change finrank K (R.component k).carrier = 1 ∨
            finrank K (R.component k).carrier = 2
          exact R.rank_one_or_two k
    scaleOrder_mono := R.scaleOrder_mono
  }

@[simp]
theorem rebalancePair_scaleGenerator
    (R : RawJordanDecomposition q L t) (i j : Fin t) (hij : i ≠ j)
    (hi : finrank K (R.component i).carrier = 2)
    (P' : ModularPairSplitting
      (R.toOrthogonalDecomposition.orthogonalSup hij).space
      (R.toOrthogonalDecomposition.orthogonalSup hij).lattice)
    (hpres : (R.pairSplitting i j hij hi).PreservesRanksAndScales P')
    (k : Fin t) :
    (R.rebalancePair i j hij hi P' hpres).scaleGenerator k =
      R.scaleGenerator k :=
  rfl

@[simp]
theorem rebalancePair_normGenerator_left
    (R : RawJordanDecomposition q L t) (i j : Fin t) (hij : i ≠ j)
    (hi : finrank K (R.component i).carrier = 2)
    (P' : ModularPairSplitting
      (R.toOrthogonalDecomposition.orthogonalSup hij).space
      (R.toOrthogonalDecomposition.orthogonalSup hij).lattice)
    (hpres : (R.pairSplitting i j hij hi).PreservesRanksAndScales P') :
    (R.rebalancePair i j hij hi P' hpres).normGenerator i =
      P'.normGenerator 0 := by
  exact R.rebalancedNormGenerator_left i j hij P'

@[simp]
theorem rebalancePair_normGenerator_right
    (R : RawJordanDecomposition q L t) (i j : Fin t) (hij : i ≠ j)
    (hi : finrank K (R.component i).carrier = 2)
    (P' : ModularPairSplitting
      (R.toOrthogonalDecomposition.orthogonalSup hij).space
      (R.toOrthogonalDecomposition.orthogonalSup hij).lattice)
    (hpres : (R.pairSplitting i j hij hi).PreservesRanksAndScales P') :
    (R.rebalancePair i j hij hi P' hpres).normGenerator j =
      P'.normGenerator 1 := by
  exact R.rebalancedNormGenerator_right i j hij P'

@[simp]
theorem rebalancePair_normGenerator_other
    (R : RawJordanDecomposition q L t) (i j : Fin t) (hij : i ≠ j)
    (hi : finrank K (R.component i).carrier = 2)
    (P' : ModularPairSplitting
      (R.toOrthogonalDecomposition.orthogonalSup hij).space
      (R.toOrthogonalDecomposition.orthogonalSup hij).lattice)
    (hpres : (R.pairSplitting i j hij hi).PreservesRanksAndScales P')
    (k : Fin t) (hki : k ≠ i) (hkj : k ≠ j) :
    (R.rebalancePair i j hij hi P' hpres).normGenerator k =
      R.normGenerator k := by
  exact R.rebalancedNormGenerator_other i j hij P' k hki hkj

/-- Scale-order family of a raw O'Meara decomposition. -/
noncomputable def scaleOrder
    (R : RawJordanDecomposition q L t) (i : Fin t) : Int :=
  ordUnit K (R.scaleGenerator i)

/-- Norm-order family of a raw O'Meara decomposition. -/
noncomputable def normOrder
    (R : RawJordanDecomposition q L t) (i : Fin t) : Int :=
  ordUnit K (R.normGenerator i)

/-- Contribution of one raw component at an arbitrary target scale. -/
noncomputable def adjustedNormOrderAt
    (R : RawJordanDecomposition q L t) (r : Int) (j : Fin t) : Int :=
  JordanProfileOrder.adjustedAt R.scaleOrder R.normOrder r j

/-- Effective norm order of a nonempty raw component family. -/
noncomputable def effectiveNormOrderAt
    (R : RawJordanDecomposition q L (t + 1))
    (anchor : Fin (t + 1)) (r : Int) : Int :=
  JordanProfileOrder.effectiveAt R.scaleOrder R.normOrder anchor r

/-- The norm order of every modular component dominates its scale order. -/
theorem scaleOrder_le_normOrder
    (R : RawJordanDecomposition q L t) (i : Fin t) :
    R.scaleOrder i ≤ R.normOrder i := by
  have hideal : Lattice.principalIdeal (K := K)
        (R.normGenerator i : K) ≤
      Lattice.principalIdeal (K := K) (R.scaleGenerator i : K) := by
    rw [← R.normIdeal_eq i, ← R.scaleIdeal_eq i]
    exact Lattice.normIdeal_le_scaleIdeal
      (R.component i).space (R.component i).lattice
  have hord := (Lattice.principalIdeal_le_iff_ord_ge
    (Units.ne_zero (R.normGenerator i))
    (Units.ne_zero (R.scaleGenerator i))).mp hideal
  apply WithTop.coe_le_coe.mp
  simpa only [scaleOrder, normOrder, coe_ordUnit] using hord

/-- The effective norm at a target scale is never below that target. -/
theorem target_le_effectiveNormOrderAt
    (R : RawJordanDecomposition q L (t + 1))
    (anchor : Fin (t + 1)) (r : Int) :
    r ≤ R.effectiveNormOrderAt anchor r := by
  apply JordanProfileOrder.target_le_effectiveAt
  intro j
  exact R.scaleOrder_le_normOrder j

/-- At its own scale, a component bounds the effective norm from above. -/
theorem effectiveNormOrderAt_le_normOrder
    (R : RawJordanDecomposition q L (t + 1))
    (i : Fin (t + 1)) :
    R.effectiveNormOrderAt i (R.scaleOrder i) ≤ R.normOrder i := by
  calc
    R.effectiveNormOrderAt i (R.scaleOrder i) ≤
        R.adjustedNormOrderAt (R.scaleOrder i) i :=
      JordanProfileOrder.effectiveAt_le _ _ i i _
    _ = R.normOrder i := by
      simp [adjustedNormOrderAt, JordanProfileOrder.adjustedAt]

/-- A source component attains every effective finite minimum. -/
theorem exists_adjustedNormOrderAt_eq_effective
    (R : RawJordanDecomposition q L (t + 1))
    (anchor : Fin (t + 1)) (r : Int) :
    ∃ j : Fin (t + 1),
      R.adjustedNormOrderAt r j = R.effectiveNormOrderAt anchor r := by
  obtain ⟨j, _hj, hjmin⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (Fin (t + 1))))
    ⟨anchor, Finset.mem_univ anchor⟩
    (R.adjustedNormOrderAt r)
  exact ⟨j, hjmin.symm⟩

/-- Closing one norm value under the effective-norm operator leaves the
whole effective-norm function unchanged. -/
theorem effectiveAt_eq_of_singleClosure {s : Nat}
    (scale norm norm' : Fin (s + 1) → Int)
    (i anchor anchor' : Fin (s + 1))
    (hi : norm' i =
      JordanProfileOrder.effectiveAt scale norm i (scale i))
    (hother : ∀ j, j ≠ i → norm' j = norm j)
    (r : Int) :
    JordanProfileOrder.effectiveAt scale norm' anchor' r =
      JordanProfileOrder.effectiveAt scale norm anchor r := by
  apply le_antisymm
  · apply JordanProfileOrder.effectiveAt_mono anchor' anchor r
    intro j
    apply JordanProfileOrder.adjustedAt_mono_norm
    by_cases hji : j = i
    · subst j
      rw [hi]
      calc
        JordanProfileOrder.effectiveAt scale norm i (scale i) ≤
            JordanProfileOrder.adjustedAt scale norm (scale i) i :=
          JordanProfileOrder.effectiveAt_le scale norm i i (scale i)
        _ = norm i := by
          simp [JordanProfileOrder.adjustedAt]
    · rw [hother j hji]
  · apply JordanProfileOrder.le_effectiveAt
    intro j
    by_cases hji : j = i
    · subst j
      unfold JordanProfileOrder.adjustedAt
      rw [hi]
      by_cases hir : scale i < r
      · rw [if_pos hir]
        exact JordanProfileOrder.effectiveAt_target_le_add_two_mul_sub
          scale norm i anchor hir.le
      · rw [if_neg hir]
        exact JordanProfileOrder.effectiveAt_mono_target
          scale norm anchor i (le_of_not_gt hir)
    · unfold JordanProfileOrder.adjustedAt
      rw [hother j hji]
      exact JordanProfileOrder.effectiveAt_le scale norm anchor j r

/-- A component is bad when its norm is strictly larger than the intrinsic
effective norm at its own scale. -/
def IsBad (R : RawJordanDecomposition q L (t + 1))
    (i : Fin (t + 1)) : Prop :=
  R.effectiveNormOrderAt i (R.scaleOrder i) < R.normOrder i

/-- The finite set of bad components used as Beli's termination measure. -/
noncomputable def badIndices
    (R : RawJordanDecomposition q L (t + 1)) : Finset (Fin (t + 1)) :=
  by
    classical
    exact Finset.univ.filter R.IsBad

/-- Number of bad components. -/
noncomputable def badCount
    (R : RawJordanDecomposition q L (t + 1)) : Nat :=
  R.badIndices.card

@[simp]
theorem mem_badIndices_iff
    (R : RawJordanDecomposition q L (t + 1)) (i : Fin (t + 1)) :
    i ∈ R.badIndices ↔ R.IsBad i := by
  simp [badIndices]

/-- A bad component cannot be unary, hence is modular binary. -/
theorem rank_eq_two_of_isBad
    (R : RawJordanDecomposition q L (t + 1))
    (i : Fin (t + 1)) (hbad : R.IsBad i) :
    finrank K (R.component i).carrier = 2 := by
  rcases R.rank_one_or_two i with hone | htwo
  · have heq :=
      Lattice.ordUnit_normGenerator_eq_scaleGenerator_of_finrank_eq_one
        (R.component i).space (R.component i).lattice
        (R.scaleGenerator i) (R.normGenerator i)
        hone (R.modular i) (R.normIdeal_eq i)
    have htarget := R.target_le_effectiveNormOrderAt i (R.scaleOrder i)
    change R.normOrder i = R.scaleOrder i at heq
    unfold IsBad at hbad
    omega
  · exact htwo

/-- A source attaining a strict improvement is different from the bad
component itself. -/
theorem source_ne_of_isBad
    (R : RawJordanDecomposition q L (t + 1))
    (i j : Fin (t + 1)) (hbad : R.IsBad i)
    (hsource : R.adjustedNormOrderAt (R.scaleOrder i) j =
      R.effectiveNormOrderAt i (R.scaleOrder i)) :
    j ≠ i := by
  intro hji
  subst j
  have hself : R.adjustedNormOrderAt (R.scaleOrder i) i =
      R.normOrder i := by
    simp [adjustedNormOrderAt, JordanProfileOrder.adjustedAt]
  rw [hself] at hsource
  unfold IsBad at hbad
  omega

/-- One application of Lemma 4.5 closes a selected bad component, preserves
all scales, and leaves every other norm order unchanged. -/
theorem exists_rebalance_of_isBad
    (R : RawJordanDecomposition q L (t + 1))
    (i : Fin (t + 1)) (hbad : R.IsBad i) :
    ∃ R' : RawJordanDecomposition q L (t + 1),
      (∀ k, R'.scaleOrder k = R.scaleOrder k) ∧
      R'.normOrder i = R.effectiveNormOrderAt i (R.scaleOrder i) ∧
      ∀ k, k ≠ i → R'.normOrder k = R.normOrder k := by
  classical
  have hi : finrank K (R.component i).carrier = 2 :=
    R.rank_eq_two_of_isBad i hbad
  obtain ⟨j, hsource⟩ :=
    R.exists_adjustedNormOrderAt_eq_effective i (R.scaleOrder i)
  have hji : j ≠ i := R.source_ne_of_isBad i j hbad hsource
  rcases lt_or_gt_of_ne hji.symm with hij | hjiLt
  · let P := R.pairSplitting i j hji.symm hi
    have hscaleRaw : R.scaleOrder i ≤ R.scaleOrder j := by
      exact R.scaleOrder_mono hij
    have hsourceNorm : R.normOrder j =
        R.effectiveNormOrderAt i (R.scaleOrder i) := by
      have hadj : R.adjustedNormOrderAt (R.scaleOrder i) j =
          R.normOrder j := by
        unfold adjustedNormOrderAt JordanProfileOrder.adjustedAt
        rw [if_neg (not_lt_of_ge hscaleRaw)]
      exact hadj.symm.trans hsource
    have hnormRaw : R.normOrder j < R.normOrder i := by
      unfold IsBad at hbad
      rw [hsourceNorm]
      exact hbad
    have hscale : P.scaleOrder 0 ≤ P.scaleOrder 1 := by
      change R.scaleOrder i ≤ R.scaleOrder j
      exact hscaleRaw
    have hnorm : P.normOrder 1 < P.normOrder 0 := by
      change R.normOrder j < R.normOrder i
      exact hnormRaw
    rcases P.beliLemma45_i hscale hnorm with
      ⟨P', hpres, hnorms⟩
    let R' := R.rebalancePair i j hji.symm hi P' hpres
    refine ⟨R', ?_, ?_, ?_⟩
    · intro k
      rfl
    · unfold normOrder
      dsimp only [R']
      rw [R.rebalancePair_normGenerator_left i j hji.symm hi P' hpres]
      change P'.normOrder 0 =
        R.effectiveNormOrderAt i (R.scaleOrder i)
      exact (P.normOrder_eq_oldSecond_of_normsEqual P' hnorms 0).trans
        (by
          change P.normOrder 1 = _
          exact hsourceNorm)
    · intro k hki
      by_cases hkj : k = j
      · subst k
        unfold normOrder
        dsimp only [R']
        rw [R.rebalancePair_normGenerator_right i j hji.symm hi P' hpres]
        change P'.normOrder 1 = R.normOrder j
        exact P.normOrder_eq_oldSecond_of_normsEqual P' hnorms 1
      · unfold normOrder
        dsimp only [R']
        rw [R.rebalancePair_normGenerator_other i j hji.symm hi P' hpres
          k hki hkj]
  · let P := R.pairSplitting i j hji.symm hi
    have hscaleRaw : R.scaleOrder j ≤ R.scaleOrder i := by
      exact R.scaleOrder_mono hjiLt
    have hdual : P.dualNormOrder 1 < P.dualNormOrder 0 := by
      change R.normOrder j - 2 * R.scaleOrder j <
        R.normOrder i - 2 * R.scaleOrder i
      unfold adjustedNormOrderAt JordanProfileOrder.adjustedAt at hsource
      unfold IsBad at hbad
      by_cases hscaleStrict : R.scaleOrder j < R.scaleOrder i
      · rw [if_pos hscaleStrict] at hsource
        omega
      · rw [if_neg hscaleStrict] at hsource
        have hscaleEq : R.scaleOrder j = R.scaleOrder i :=
          le_antisymm hscaleRaw (le_of_not_gt hscaleStrict)
        omega
    have hscale : P.scaleOrder 1 ≤ P.scaleOrder 0 := by
      change R.scaleOrder j ≤ R.scaleOrder i
      exact hscaleRaw
    rcases P.beliLemma45_ii hscale hdual with
      ⟨P', hpres, hduals⟩
    have hs0 := P.scaleOrder_eq_of_preserves P' hpres 0
    have hs1 := P.scaleOrder_eq_of_preserves P' hpres 1
    have hd0 := hduals 0
    have hd1 := hduals 1
    change P'.scaleOrder 0 = R.scaleOrder i at hs0
    change P'.scaleOrder 1 = R.scaleOrder j at hs1
    change P'.normOrder 0 - 2 * P'.scaleOrder 0 =
      R.normOrder j - 2 * R.scaleOrder j at hd0
    change P'.normOrder 1 - 2 * P'.scaleOrder 1 =
      R.normOrder j - 2 * R.scaleOrder j at hd1
    have hnewI : P'.normOrder 0 =
        R.effectiveNormOrderAt i (R.scaleOrder i) := by
      unfold adjustedNormOrderAt JordanProfileOrder.adjustedAt at hsource
      by_cases hscaleStrict : R.scaleOrder j < R.scaleOrder i
      · rw [if_pos hscaleStrict] at hsource
        omega
      · rw [if_neg hscaleStrict] at hsource
        have hscaleEq : R.scaleOrder j = R.scaleOrder i :=
          le_antisymm hscaleRaw (le_of_not_gt hscaleStrict)
        omega
    have hnewJ : P'.normOrder 1 = R.normOrder j := by
      omega
    let R' := R.rebalancePair i j hji.symm hi P' hpres
    refine ⟨R', ?_, ?_, ?_⟩
    · intro k
      rfl
    · unfold normOrder
      dsimp only [R']
      rw [R.rebalancePair_normGenerator_left i j hji.symm hi P' hpres]
      exact hnewI
    · intro k hki
      by_cases hkj : k = j
      · subst k
        unfold normOrder
        dsimp only [R']
        rw [R.rebalancePair_normGenerator_right i j hji.symm hi P' hpres]
        exact hnewJ
      · unfold normOrder
        dsimp only [R']
        rw [R.rebalancePair_normGenerator_other i j hji.symm hi P' hpres
          k hki hkj]

/-- The pointwise description of one rebalance implies invariance of the
effective norm at every target scale. -/
theorem effectiveNormOrderAt_eq_of_rebalance
    (R R' : RawJordanDecomposition q L (t + 1))
    (i : Fin (t + 1))
    (hscale : ∀ k, R'.scaleOrder k = R.scaleOrder k)
    (hi : R'.normOrder i =
      R.effectiveNormOrderAt i (R.scaleOrder i))
    (hother : ∀ k, k ≠ i → R'.normOrder k = R.normOrder k)
    (anchor' anchor : Fin (t + 1)) (r : Int) :
    R'.effectiveNormOrderAt anchor' r =
      R.effectiveNormOrderAt anchor r := by
  have hs : R'.scaleOrder = R.scaleOrder := funext hscale
  unfold effectiveNormOrderAt
  rw [hs]
  apply effectiveAt_eq_of_singleClosure
    R.scaleOrder R.normOrder R'.normOrder i anchor anchor'
  · exact hi
  · exact hother

/-- A single rebalance removes exactly the selected bad index. -/
theorem badIndices_rebalance_eq_erase
    (R R' : RawJordanDecomposition q L (t + 1))
    (i : Fin (t + 1))
    (hscale : ∀ k, R'.scaleOrder k = R.scaleOrder k)
    (hi : R'.normOrder i =
      R.effectiveNormOrderAt i (R.scaleOrder i))
    (hother : ∀ k, k ≠ i → R'.normOrder k = R.normOrder k) :
    R'.badIndices = R.badIndices.erase i := by
  classical
  have heffective := R.effectiveNormOrderAt_eq_of_rebalance
    R' i hscale hi hother
  apply Finset.ext
  intro k
  by_cases hki : k = i
  · subst k
    have hnot : ¬R'.IsBad i := by
      unfold IsBad
      rw [hscale i, heffective i i (R.scaleOrder i), hi]
      exact lt_irrefl _
    simp [R'.mem_badIndices_iff, hnot]
  · have hbad : R'.IsBad k ↔ R.IsBad k := by
      unfold IsBad
      rw [hscale k, hother k hki,
        heffective k k (R.scaleOrder k)]
    rw [R'.mem_badIndices_iff, Finset.mem_erase,
      R.mem_badIndices_iff]
    constructor
    · intro hk
      exact ⟨hki, hbad.mp hk⟩
    · rintro ⟨_, hk⟩
      exact hbad.mpr hk

/-- Every bad raw decomposition admits another one with strictly smaller
termination measure. -/
theorem exists_badCount_lt_of_exists_isBad
    (R : RawJordanDecomposition q L (t + 1))
    (i : Fin (t + 1)) (hbad : R.IsBad i) :
    ∃ R' : RawJordanDecomposition q L (t + 1),
      R'.badCount < R.badCount := by
  classical
  rcases R.exists_rebalance_of_isBad i hbad with
    ⟨R', hscale, hi, hother⟩
  refine ⟨R', ?_⟩
  have herase := R.badIndices_rebalance_eq_erase
    R' i hscale hi hother
  have hmem : i ∈ R.badIndices := R.mem_badIndices_iff i |>.2 hbad
  unfold badCount
  rw [herase, Finset.card_erase_of_mem hmem]
  have hpos : 0 < R.badIndices.card := Finset.card_pos.mpr ⟨i, hmem⟩
  omega

/-- Repeated Lemma 4.5 replacements terminate at a raw decomposition with
no bad component. -/
theorem exists_noBad
    (R : RawJordanDecomposition q L (t + 1)) :
    ∃ R' : RawJordanDecomposition q L (t + 1),
      ∀ i, ¬R'.IsBad i := by
  classical
  generalize hn : R.badCount = n
  induction n using Nat.strong_induction_on generalizing R with
  | h n ih =>
      by_cases hterminal : ∀ i, ¬R.IsBad i
      · exact ⟨R, hterminal⟩
      · push_neg at hterminal
        obtain ⟨i, hbad⟩ := hterminal
        obtain ⟨R', hlt⟩ := R.exists_badCount_lt_of_exists_isBad i hbad
        exact ih R'.badCount (by omega) R' rfl

/-- At a terminal decomposition every component norm equals the effective
norm at its scale. -/
theorem normOrder_eq_effective_of_noBad
    (R : RawJordanDecomposition q L (t + 1))
    (hno : ∀ i, ¬R.IsBad i) (i : Fin (t + 1)) :
    R.normOrder i = R.effectiveNormOrderAt i (R.scaleOrder i) := by
  apply le_antisymm
  · exact le_of_not_gt (hno i)
  · exact R.effectiveNormOrderAt_le_normOrder i

/-- A terminal raw decomposition is a maximal norm splitting. -/
noncomputable def toMaximalNormSplittingOfNoBad
    (R : RawJordanDecomposition q L (t + 1))
    (hno : ∀ i, ¬R.IsBad i) :
    Lattice.MaximalNormSplitting q L (t + 1) where
  toOrthogonalDecomposition := R.toOrthogonalDecomposition
  scaleGenerator := R.scaleGenerator
  normGenerator := R.normGenerator
  scaleIdeal_eq := R.scaleIdeal_eq
  normIdeal_eq := R.normIdeal_eq
  unary_or_modular_binary := by
    intro i
    rcases R.rank_one_or_two i with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, R.modular i⟩
  scaleOrder_mono := R.scaleOrder_mono
  normGap_bounds := by
    intro i j hij
    have hscale : R.scaleOrder i ≤ R.scaleOrder j :=
      R.scaleOrder_mono hij
    have hi := R.normOrder_eq_effective_of_noBad hno i
    have hj := R.normOrder_eq_effective_of_noBad hno j
    have hlower : R.normOrder i ≤ R.normOrder j := by
      calc
        R.normOrder i =
            R.effectiveNormOrderAt i (R.scaleOrder i) := hi
        _ ≤ R.adjustedNormOrderAt (R.scaleOrder i) j :=
          JordanProfileOrder.effectiveAt_le _ _ i j _
        _ = R.normOrder j := by
          unfold adjustedNormOrderAt JordanProfileOrder.adjustedAt
          rw [if_neg (not_lt_of_ge hscale)]
    have hupper : R.normOrder j ≤
        R.normOrder i + 2 * (R.scaleOrder j - R.scaleOrder i) := by
      calc
        R.normOrder j =
            R.effectiveNormOrderAt j (R.scaleOrder j) := hj
        _ ≤ R.adjustedNormOrderAt (R.scaleOrder j) i :=
          JordanProfileOrder.effectiveAt_le _ _ j i _
        _ = R.normOrder i +
            2 * (R.scaleOrder j - R.scaleOrder i) := by
          unfold adjustedNormOrderAt JordanProfileOrder.adjustedAt
          by_cases hstrict : R.scaleOrder i < R.scaleOrder j
          · rw [if_pos hstrict]
          · rw [if_neg hstrict]
            have heq : R.scaleOrder i = R.scaleOrder j :=
              le_antisymm hscale (le_of_not_gt hstrict)
            omega
    change 0 ≤ R.normOrder j - R.normOrder i ∧
      R.normOrder j - R.normOrder i ≤
        2 * (R.scaleOrder j - R.scaleOrder i)
    omega

/-- The empty raw decomposition is already maximal. -/
noncomputable def toMaximalNormSplittingZero
    (R : RawJordanDecomposition q L 0) :
    Lattice.MaximalNormSplitting q L 0 where
  toOrthogonalDecomposition := R.toOrthogonalDecomposition
  scaleGenerator := R.scaleGenerator
  normGenerator := R.normGenerator
  scaleIdeal_eq := R.scaleIdeal_eq
  normIdeal_eq := R.normIdeal_eq
  unary_or_modular_binary := fun i ↦ Fin.elim0 i
  scaleOrder_mono := fun {i} _ _ ↦ Fin.elim0 i
  normGap_bounds := fun {i} _ _ ↦ Fin.elim0 i

/-- Every raw O'Meara decomposition can be normalized to a maximal norm
splitting with the same number of unary/binary blocks. -/
theorem exists_maximalNormSplitting_ofRaw
    (R : RawJordanDecomposition q L t) :
    Nonempty (Lattice.MaximalNormSplitting q L t) := by
  cases t with
  | zero => exact ⟨R.toMaximalNormSplittingZero⟩
  | succ t =>
      obtain ⟨R', hno⟩ := R.exists_noBad
      exact ⟨R'.toMaximalNormSplittingOfNoBad hno⟩

end Lattice.RawJordanDecomposition

/-- Unconditional form of Beli (2003), Lemma 4.6. -/
theorem exists_maximalNormSplitting_beliLemma46
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) :
    ∃ t : Nat, Nonempty (Lattice.MaximalNormSplitting q L t) := by
  let R := Lattice.omearaRawJordanDecomposition q L
  exact ⟨_, R.exists_maximalNormSplitting_ofRaw⟩

/-- The law interface for Beli (2003), Lemma 4.6 is discharged by the
terminating replacement construction above. -/
instance beliLemma46LawsProved : BeliLemma46Laws.{u, v} K where
  exists_maximalNormSplitting q L :=
    exists_maximalNormSplitting_beliLemma46 q L

/-- Good BONG existence is now unconditional: Lemma 4.6 supplies a maximal
norm splitting and the already proved Section 4 construction supplies the
good BONG. -/
instance bongGoodExistenceLawsProved : BONGGoodExistenceLaws.{u, v} K where
  exists_good_bong q L := exists_good_bong_of_sectionFour q L

end Bong
