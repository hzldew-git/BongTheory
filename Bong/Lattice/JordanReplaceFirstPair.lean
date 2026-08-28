/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalDecompositionReplacePair

/-!
# Replacing the first two components of a Jordan decomposition

O'Meara's coefficient changes alter the first two displayed modular
components while leaving every later component fixed.  This file upgrades the
corresponding orthogonal-pair replacement to a Jordan decomposition once the
scale and norm data of the two new components have been verified.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The first and second indices of a decomposition with at least two
components are distinct. -/
theorem firstIndex_ne_secondIndex :
    (0 : Fin (n + 2)) ≠ (1 : Fin (n + 2)) := by
  exact Fin.zero_ne_one

/-- The quadratic sublattice obtained by amalgamating the first two Jordan
components. -/
noncomputable abbrev firstPairSublattice
    (J : JordanDecomposition q L (n + 2)) : QuadraticSublattice q :=
  J.toOrthogonalDecomposition.orthogonalSup firstIndex_ne_secondIndex

/-- Replace the first two components by a new orthogonal splitting of their
amalgamated lattice.  The new components must be checked at the old two scale
and norm generators; every later Jordan datum is then inherited verbatim. -/
noncomputable def replaceFirstPair
    (J : JordanDecomposition q L (n + 2))
    (P : OrthogonalDecomposition (J.firstPairSublattice).space
      (J.firstPairSublattice).lattice 2)
    (hzeroModular : IsModular
      ((J.firstPairSublattice).liftNested (P.component 0)).space
      ((J.firstPairSublattice).liftNested (P.component 0)).lattice
      (J.scaleGenerator 0))
    (honeModular : IsModular
      ((J.firstPairSublattice).liftNested (P.component 1)).space
      ((J.firstPairSublattice).liftNested (P.component 1)).lattice
      (J.scaleGenerator 1))
    (hzeroScale : scaleIdeal
      ((J.firstPairSublattice).liftNested (P.component 0)).space
      ((J.firstPairSublattice).liftNested (P.component 0)).lattice =
        principalIdeal (K := K) (J.scaleGenerator 0 : K))
    (honeScale : scaleIdeal
      ((J.firstPairSublattice).liftNested (P.component 1)).space
      ((J.firstPairSublattice).liftNested (P.component 1)).lattice =
        principalIdeal (K := K) (J.scaleGenerator 1 : K))
    (hzeroNorm : normIdeal
      ((J.firstPairSublattice).liftNested (P.component 0)).space
      ((J.firstPairSublattice).liftNested (P.component 0)).lattice =
        principalIdeal (K := K) (J.normGenerator 0 : K))
    (honeNorm : normIdeal
      ((J.firstPairSublattice).liftNested (P.component 1)).space
      ((J.firstPairSublattice).liftNested (P.component 1)).lattice =
        principalIdeal (K := K) (J.normGenerator 1 : K)) :
    JordanDecomposition q L (n + 2) := by
  let D := J.toOrthogonalDecomposition
  let E := D.replacePair firstIndex_ne_secondIndex P
  refine {
    toOrthogonalDecomposition := E
    scaleGenerator := J.scaleGenerator
    normGenerator := J.normGenerator
    modular := ?_
    scaleIdeal_eq := ?_
    normIdeal_eq := ?_
    scaleOrder_strict := J.scaleOrder_strict
  }
  · intro i
    by_cases hi0 : i = 0
    · subst i
      change IsModular (E.component 0).space (E.component 0).lattice
        (J.scaleGenerator 0)
      rw [OrthogonalDecomposition.replacePair_component_left]
      exact hzeroModular
    · by_cases hi1 : i = 1
      · subst i
        change IsModular (E.component 1).space (E.component 1).lattice
          (J.scaleGenerator 1)
        rw [OrthogonalDecomposition.replacePair_component_right]
        exact honeModular
      · change IsModular (E.component i).space (E.component i).lattice
          (J.scaleGenerator i)
        rw [OrthogonalDecomposition.replacePair_component_other
          (hij := firstIndex_ne_secondIndex) (hki := hi0) (hkj := hi1)]
        exact J.modular i
  · intro i
    by_cases hi0 : i = 0
    · subst i
      change scaleIdeal (E.component 0).space (E.component 0).lattice =
        principalIdeal (K := K) (J.scaleGenerator 0 : K)
      rw [OrthogonalDecomposition.replacePair_component_left]
      exact hzeroScale
    · by_cases hi1 : i = 1
      · subst i
        change scaleIdeal (E.component 1).space (E.component 1).lattice =
          principalIdeal (K := K) (J.scaleGenerator 1 : K)
        rw [OrthogonalDecomposition.replacePair_component_right]
        exact honeScale
      · change scaleIdeal (E.component i).space (E.component i).lattice =
          principalIdeal (K := K) (J.scaleGenerator i : K)
        rw [OrthogonalDecomposition.replacePair_component_other
          (hij := firstIndex_ne_secondIndex) (hki := hi0) (hkj := hi1)]
        exact J.scaleIdeal_eq i
  · intro i
    by_cases hi0 : i = 0
    · subst i
      change normIdeal (E.component 0).space (E.component 0).lattice =
        principalIdeal (K := K) (J.normGenerator 0 : K)
      rw [OrthogonalDecomposition.replacePair_component_left]
      exact hzeroNorm
    · by_cases hi1 : i = 1
      · subst i
        change normIdeal (E.component 1).space (E.component 1).lattice =
          principalIdeal (K := K) (J.normGenerator 1 : K)
        rw [OrthogonalDecomposition.replacePair_component_right]
        exact honeNorm
      · change normIdeal (E.component i).space (E.component i).lattice =
          principalIdeal (K := K) (J.normGenerator i : K)
        rw [OrthogonalDecomposition.replacePair_component_other
          (hij := firstIndex_ne_secondIndex) (hki := hi0) (hkj := hi1)]
        exact J.normIdeal_eq i

@[simp]
theorem replaceFirstPair_scaleGenerator
    (J : JordanDecomposition q L (n + 2))
    (P : OrthogonalDecomposition (J.firstPairSublattice).space
      (J.firstPairSublattice).lattice 2)
    (hzeroModular) (honeModular) (hzeroScale) (honeScale)
    (hzeroNorm) (honeNorm) (i : Fin (n + 2)) :
    (J.replaceFirstPair P hzeroModular honeModular hzeroScale honeScale
      hzeroNorm honeNorm).scaleGenerator i = J.scaleGenerator i :=
  rfl

@[simp]
theorem replaceFirstPair_normGenerator
    (J : JordanDecomposition q L (n + 2))
    (P : OrthogonalDecomposition (J.firstPairSublattice).space
      (J.firstPairSublattice).lattice 2)
    (hzeroModular) (honeModular) (hzeroScale) (honeScale)
    (hzeroNorm) (honeNorm) (i : Fin (n + 2)) :
    (J.replaceFirstPair P hzeroModular honeModular hzeroScale honeScale
      hzeroNorm honeNorm).normGenerator i = J.normGenerator i :=
  rfl

@[simp]
theorem replaceFirstPair_component_zero
    (J : JordanDecomposition q L (n + 2))
    (P : OrthogonalDecomposition (J.firstPairSublattice).space
      (J.firstPairSublattice).lattice 2)
    (hzeroModular) (honeModular) (hzeroScale) (honeScale)
    (hzeroNorm) (honeNorm) :
    (J.replaceFirstPair P hzeroModular honeModular hzeroScale honeScale
      hzeroNorm honeNorm).component 0 =
      (J.firstPairSublattice).liftNested (P.component 0) := by
  change
    (J.toOrthogonalDecomposition.replacePair firstIndex_ne_secondIndex P).component 0 = _
  exact J.toOrthogonalDecomposition.replacePair_component_left
    firstIndex_ne_secondIndex P

@[simp]
theorem replaceFirstPair_component_one
    (J : JordanDecomposition q L (n + 2))
    (P : OrthogonalDecomposition (J.firstPairSublattice).space
      (J.firstPairSublattice).lattice 2)
    (hzeroModular) (honeModular) (hzeroScale) (honeScale)
    (hzeroNorm) (honeNorm) :
    (J.replaceFirstPair P hzeroModular honeModular hzeroScale honeScale
      hzeroNorm honeNorm).component 1 =
      (J.firstPairSublattice).liftNested (P.component 1) := by
  change
    (J.toOrthogonalDecomposition.replacePair firstIndex_ne_secondIndex P).component 1 = _
  exact J.toOrthogonalDecomposition.replacePair_component_right
    firstIndex_ne_secondIndex P

@[simp]
theorem replaceFirstPair_component_of_ne
    (J : JordanDecomposition q L (n + 2))
    (P : OrthogonalDecomposition (J.firstPairSublattice).space
      (J.firstPairSublattice).lattice 2)
    (hzeroModular) (honeModular) (hzeroScale) (honeScale)
    (hzeroNorm) (honeNorm) (i : Fin (n + 2))
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    (J.replaceFirstPair P hzeroModular honeModular hzeroScale honeScale
      hzeroNorm honeNorm).component i = J.component i := by
  change
    (J.toOrthogonalDecomposition.replacePair firstIndex_ne_secondIndex P).component i =
      J.toOrthogonalDecomposition.component i
  exact J.toOrthogonalDecomposition.replacePair_component_other
    firstIndex_ne_secondIndex P i hi0 hi1

end Lattice.JordanDecomposition

end Bong
