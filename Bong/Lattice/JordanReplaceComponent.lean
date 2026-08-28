/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.JordanRemoveComponent
import Bong.Lattice.JordanIsometry
import Bong.Lattice.OrthogonalDecompositionCons

/-!
# Replacing one Jordan component

This file isolates the finite-index bookkeeping needed in O'Meara 93:21.
After one component has been changed, the unchanged complement is transported
by an integral isometry, the selected component is temporarily put first, and
the cyclic permutation restores the original scale order.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

variable (J : JordanDecomposition q L (n + 2)) (i : Fin (n + 2))

/-- Scale labels in selected-first order. -/
noncomputable def selectedFirstScaleGenerator : Fin (n + 2) → Kˣ :=
  Fin.cases (J.scaleGenerator i)
    (fun j ↦ J.scaleGenerator (i.succAbove j))

/-- Norm labels in selected-first order, with a new label on the selected
component. -/
noncomputable def selectedFirstNormGenerator (a : Kˣ) :
    Fin (n + 2) → Kˣ :=
  Fin.cases a (fun j ↦ J.normGenerator (i.succAbove j))

@[simp]
theorem selectedFirstScaleGenerator_zero :
    J.selectedFirstScaleGenerator i 0 = J.scaleGenerator i :=
  rfl

@[simp]
theorem selectedFirstScaleGenerator_succ (j : Fin (n + 1)) :
    J.selectedFirstScaleGenerator i j.succ =
      J.scaleGenerator (i.succAbove j) :=
  rfl

@[simp]
theorem selectedFirstNormGenerator_zero (a : Kˣ) :
    J.selectedFirstNormGenerator i a 0 = a :=
  rfl

@[simp]
theorem selectedFirstNormGenerator_succ (a : Kˣ) (j : Fin (n + 1)) :
    J.selectedFirstNormGenerator i a j.succ =
      J.normGenerator (i.succAbove j) :=
  rfl

/-- Restoring the original indexing restores every scale label. -/
@[simp]
theorem selectedFirstScaleGenerator_cycleRange (j : Fin (n + 2)) :
    J.selectedFirstScaleGenerator i (i.cycleRange j) =
      J.scaleGenerator j := by
  generalize hk : i.cycleRange j = k
  cases k using Fin.cases with
  | zero =>
      have hji : j = i := by
        apply i.cycleRange.injective
        rw [hk, Fin.cycleRange_self]
      subst j
      rfl
  | succ k =>
      have hjk : j = i.succAbove k := by
        apply i.cycleRange.injective
        rw [hk, Fin.cycleRange_succAbove]
      subst j
      rfl

/-- After restoring the original indexing, a nonselected norm label is
unchanged and the selected label is the supplied replacement. -/
theorem selectedFirstNormGenerator_cycleRange (a : Kˣ)
    (j : Fin (n + 2)) :
    J.selectedFirstNormGenerator i a (i.cycleRange j) =
      if j = i then a else J.normGenerator j := by
  generalize hk : i.cycleRange j = k
  cases k using Fin.cases with
  | zero =>
      have hji : j = i := by
        apply i.cycleRange.injective
        rw [hk, Fin.cycleRange_self]
      subst j
      simp
  | succ k =>
      have hjk : j = i.succAbove k := by
        apply i.cycleRange.injective
        rw [hk, Fin.cycleRange_succAbove]
      subst j
      have hne : i.succAbove k ≠ i := by
        exact Fin.succAbove_ne i k
      simp [hne]

/-- Replace one component while transporting the unchanged exact
orthogonal complement.  The resulting Jordan decomposition has the same
scales, the supplied norm generator at `i`, and all old norm generators
elsewhere. -/
noncomputable def replaceComponent
    (P : OrthogonalDecomposition q L 2)
    (tailIsometry : Isometry (J.selectedRemainder i).space
      (P.component 1).space (J.selectedRemainder i).lattice
      (P.component 1).lattice)
    (a : Kˣ)
    (hheadModular : IsModular (P.component 0).space
      (P.component 0).lattice (J.scaleGenerator i))
    (hheadScale : scaleIdeal (P.component 0).space
      (P.component 0).lattice =
        principalIdeal (K := K) (J.scaleGenerator i : K))
    (hheadNorm : normIdeal (P.component 0).space
      (P.component 0).lattice = principalIdeal (K := K) (a : K)) :
    JordanDecomposition q L (n + 2) := by
  let H := (J.removeComponent i).mapIsometry tailIsometry
  let E := P.prependNested H.toOrthogonalDecomposition
  let D := E.reindex i.cycleRange
  refine {
    toOrthogonalDecomposition := D
    scaleGenerator := J.scaleGenerator
    normGenerator := fun j ↦ if j = i then a else J.normGenerator j
    modular := ?_
    scaleIdeal_eq := ?_
    normIdeal_eq := ?_
    scaleOrder_strict := J.scaleOrder_strict
  }
  · intro j
    generalize hk : i.cycleRange j = k
    cases k using Fin.cases with
    | zero =>
        have hji : j = i := by
          apply i.cycleRange.injective
          rw [hk, Fin.cycleRange_self]
        subst j
        change IsModular (E.component (i.cycleRange i)).space
          (E.component (i.cycleRange i)).lattice (J.scaleGenerator i)
        rw [Fin.cycleRange_self]
        change IsModular (P.component 0).space (P.component 0).lattice
          (J.scaleGenerator i)
        exact hheadModular
    | succ k =>
        have hjk : j = i.succAbove k := by
          apply i.cycleRange.injective
          rw [hk, Fin.cycleRange_succAbove]
        subst j
        change IsModular
          (E.component (i.cycleRange (i.succAbove k))).space
          (E.component (i.cycleRange (i.succAbove k))).lattice
          (J.scaleGenerator (i.succAbove k))
        rw [Fin.cycleRange_succAbove]
        change IsModular
          ((P.component 1).liftNested (H.component k)).space
          ((P.component 1).liftNested (H.component k)).lattice
          (J.scaleGenerator (i.succAbove k))
        exact QuadraticSublattice.IsModular.liftNested
          (P.component 1) (H.component k) (H.modular k)
  · intro j
    generalize hk : i.cycleRange j = k
    cases k using Fin.cases with
    | zero =>
        have hji : j = i := by
          apply i.cycleRange.injective
          rw [hk, Fin.cycleRange_self]
        subst j
        change scaleIdeal (E.component (i.cycleRange i)).space
            (E.component (i.cycleRange i)).lattice =
          principalIdeal (K := K) (J.scaleGenerator i : K)
        rw [Fin.cycleRange_self]
        change scaleIdeal (P.component 0).space (P.component 0).lattice =
          principalIdeal (K := K) (J.scaleGenerator i : K)
        exact hheadScale
    | succ k =>
        have hjk : j = i.succAbove k := by
          apply i.cycleRange.injective
          rw [hk, Fin.cycleRange_succAbove]
        subst j
        change scaleIdeal
            (E.component (i.cycleRange (i.succAbove k))).space
            (E.component (i.cycleRange (i.succAbove k))).lattice =
          principalIdeal (K := K) (J.scaleGenerator (i.succAbove k) : K)
        rw [Fin.cycleRange_succAbove]
        change scaleIdeal
            ((P.component 1).liftNested (H.component k)).space
            ((P.component 1).liftNested (H.component k)).lattice =
          principalIdeal (K := K) (J.scaleGenerator (i.succAbove k) : K)
        calc
          scaleIdeal
              ((P.component 1).liftNested (H.component k)).space
              ((P.component 1).liftNested (H.component k)).lattice =
              scaleIdeal (H.component k).space (H.component k).lattice :=
            scaleIdeal_map_isometry
              ((P.component 1).liftNestedIsometry
                (H.component k)).toQuadraticSpaceIsometry
              (H.component k).lattice
          _ = principalIdeal (K := K)
              (J.scaleGenerator (i.succAbove k) : K) := H.scaleIdeal_eq k
  · intro j
    generalize hk : i.cycleRange j = k
    cases k using Fin.cases with
    | zero =>
        have hji : j = i := by
          apply i.cycleRange.injective
          rw [hk, Fin.cycleRange_self]
        subst j
        simp only [ite_true]
        change normIdeal (E.component (i.cycleRange i)).space
            (E.component (i.cycleRange i)).lattice =
          principalIdeal (K := K) (a : K)
        rw [Fin.cycleRange_self]
        change normIdeal (P.component 0).space (P.component 0).lattice =
          principalIdeal (K := K) (a : K)
        exact hheadNorm
    | succ k =>
        have hjk : j = i.succAbove k := by
          apply i.cycleRange.injective
          rw [hk, Fin.cycleRange_succAbove]
        subst j
        have hne : i.succAbove k ≠ i := Fin.succAbove_ne i k
        rw [if_neg hne]
        change normIdeal
            (E.component (i.cycleRange (i.succAbove k))).space
            (E.component (i.cycleRange (i.succAbove k))).lattice =
          principalIdeal (K := K) (J.normGenerator (i.succAbove k) : K)
        rw [Fin.cycleRange_succAbove]
        change normIdeal
            ((P.component 1).liftNested (H.component k)).space
            ((P.component 1).liftNested (H.component k)).lattice =
          principalIdeal (K := K) (J.normGenerator (i.succAbove k) : K)
        calc
          normIdeal
              ((P.component 1).liftNested (H.component k)).space
              ((P.component 1).liftNested (H.component k)).lattice =
              normIdeal (H.component k).space (H.component k).lattice :=
            normIdeal_map_isometry
              ((P.component 1).liftNestedIsometry
                (H.component k)).toQuadraticSpaceIsometry
              (H.component k).lattice
          _ = principalIdeal (K := K)
              (J.normGenerator (i.succAbove k) : K) := H.normIdeal_eq k

@[simp]
theorem replaceComponent_scaleGenerator
    (P : OrthogonalDecomposition q L 2)
    (tailIsometry : Isometry (J.selectedRemainder i).space
      (P.component 1).space (J.selectedRemainder i).lattice
      (P.component 1).lattice)
    (a : Kˣ)
    (hheadModular) (hheadScale) (hheadNorm) (j : Fin (n + 2)) :
    (J.replaceComponent i P tailIsometry a hheadModular hheadScale
      hheadNorm).scaleGenerator j = J.scaleGenerator j :=
  rfl

@[simp]
theorem replaceComponent_normGenerator_self
    (P : OrthogonalDecomposition q L 2)
    (tailIsometry : Isometry (J.selectedRemainder i).space
      (P.component 1).space (J.selectedRemainder i).lattice
      (P.component 1).lattice)
    (a : Kˣ)
    (hheadModular) (hheadScale) (hheadNorm) :
    (J.replaceComponent i P tailIsometry a hheadModular hheadScale
      hheadNorm).normGenerator i = a := by
  simp [replaceComponent]

@[simp]
theorem replaceComponent_normGenerator_of_ne
    (P : OrthogonalDecomposition q L 2)
    (tailIsometry : Isometry (J.selectedRemainder i).space
      (P.component 1).space (J.selectedRemainder i).lattice
      (P.component 1).lattice)
    (a : Kˣ)
    (hheadModular) (hheadScale) (hheadNorm)
    {j : Fin (n + 2)} (hji : j ≠ i) :
    (J.replaceComponent i P tailIsometry a hheadModular hheadScale
      hheadNorm).normGenerator j = J.normGenerator j := by
  simp [replaceComponent, hji]

@[simp]
theorem replaceComponent_component_self
    (P : OrthogonalDecomposition q L 2)
    (tailIsometry : Isometry (J.selectedRemainder i).space
      (P.component 1).space (J.selectedRemainder i).lattice
      (P.component 1).lattice)
    (a : Kˣ)
    (hheadModular) (hheadScale) (hheadNorm) :
    (J.replaceComponent i P tailIsometry a hheadModular hheadScale
      hheadNorm).component i = P.component 0 := by
  change (P.prependNested
    (((J.removeComponent i).mapIsometry tailIsometry).toOrthogonalDecomposition)).component
      (i.cycleRange i) = P.component 0
  rw [Fin.cycleRange_self]
  rfl

/-- Every unselected old component is transported integrally to its copy in
the replacement decomposition.  This is the preservation map needed to
iterate O'Meara's componentwise saturation step. -/
noncomputable def replaceComponent_otherComponentIsometry
    (P : OrthogonalDecomposition q L 2)
    (tailIsometry : Isometry (J.selectedRemainder i).space
      (P.component 1).space (J.selectedRemainder i).lattice
      (P.component 1).lattice)
    (a : Kˣ)
    (hheadModular : IsModular (P.component 0).space
      (P.component 0).lattice (J.scaleGenerator i))
    (hheadScale : scaleIdeal (P.component 0).space
      (P.component 0).lattice =
        principalIdeal (K := K) (J.scaleGenerator i : K))
    (hheadNorm : normIdeal (P.component 0).space
      (P.component 0).lattice = principalIdeal (K := K) (a : K))
    {j : Fin (n + 2)} (hji : j ≠ i) :
    Isometry (J.component j).space
      ((J.replaceComponent i P tailIsometry a hheadModular hheadScale
        hheadNorm).component j).space
      (J.component j).lattice
      ((J.replaceComponent i P tailIsometry a hheadModular hheadScale
        hheadNorm).component j).lattice := by
  let k := Classical.choose (Fin.exists_succAbove_eq hji)
  have hk : i.succAbove k = j :=
    Classical.choose_spec (Fin.exists_succAbove_eq hji)
  let E := J.selectedFirstOrthogonalDecomposition i
  let R := J.removeComponent i
  let H := R.mapIsometry tailIsometry
  let g₀ : Isometry (J.component (i.succAbove k)).space
      (R.component k).space (J.component (i.succAbove k)).lattice
      (R.component k).lattice := by
    let g := E.tailComponentIsometry k
    have hcomponent : E.component k.succ =
        J.component (i.succAbove k) := by
      exact J.selectedFirst_component_succ i k
    rw [hcomponent] at g
    exact g
  let g₁ : Isometry (R.component k).space (H.component k).space
      (R.component k).lattice (H.component k).lattice :=
    (R.component k).mapLatticeIsometry tailIsometry
  let g₂ : Isometry (H.component k).space
      ((P.component 1).liftNested (H.component k)).space
      (H.component k).lattice
      ((P.component 1).liftNested (H.component k)).lattice :=
    (P.component 1).liftNestedIsometry (H.component k)
  let g : Isometry (J.component (i.succAbove k)).space
      ((J.replaceComponent i P tailIsometry a hheadModular hheadScale
        hheadNorm).component (i.succAbove k)).space
      (J.component (i.succAbove k)).lattice
      ((J.replaceComponent i P tailIsometry a hheadModular hheadScale
        hheadNorm).component (i.succAbove k)).lattice := by
    change Isometry (J.component (i.succAbove k)).space
      ((P.prependNested H.toOrthogonalDecomposition).component
        (i.cycleRange (i.succAbove k))).space
      (J.component (i.succAbove k)).lattice
      ((P.prependNested H.toOrthogonalDecomposition).component
        (i.cycleRange (i.succAbove k))).lattice
    rw [Fin.cycleRange_succAbove]
    change Isometry (J.component (i.succAbove k)).space
      ((P.component 1).liftNested (H.component k)).space
      (J.component (i.succAbove k)).lattice
      ((P.component 1).liftNested (H.component k)).lattice
    exact g₀.trans (g₁.trans g₂)
  exact hk ▸ g

end Lattice.JordanDecomposition

end Bong
