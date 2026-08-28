/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.NestedSublattice

/-!
# Prepending an orthogonal component

This file flattens one step of a nested orthogonal decomposition.  If a
lattice first splits as `H ⊥ C` and `C` is itself orthogonally decomposed,
then the nested components of `C`, lifted to the original space, may be
prepended by `H`.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

namespace OrthogonalDecomposition

/-- The component family obtained by retaining the first block of a
two-block splitting and lifting a decomposition of its second block. -/
noncomputable def prependNestedComponents
    (P : OrthogonalDecomposition q L 2)
    (D : OrthogonalDecomposition (P.component 1).space
      (P.component 1).lattice t) :
    Fin (t + 1) → QuadraticSublattice q :=
  Fin.cases (P.component 0)
    (fun i ↦ (P.component 1).liftNested (D.component i))

@[simp]
theorem prependNestedComponents_zero
    (P : OrthogonalDecomposition q L 2)
    (D : OrthogonalDecomposition (P.component 1).space
      (P.component 1).lattice t) :
    prependNestedComponents P D 0 = P.component 0 :=
  rfl

@[simp]
theorem prependNestedComponents_succ
    (P : OrthogonalDecomposition q L 2)
    (D : OrthogonalDecomposition (P.component 1).space
      (P.component 1).lattice t) (i : Fin t) :
    prependNestedComponents P D i.succ =
      (P.component 1).liftNested (D.component i) :=
  rfl

/-- Flatten a two-block splitting followed by an orthogonal decomposition
inside its second block. -/
noncomputable def prependNested
    (P : OrthogonalDecomposition q L 2)
    (D : OrthogonalDecomposition (P.component 1).space
      (P.component 1).lattice t) :
    OrthogonalDecomposition q L (t + 1) where
  component := prependNestedComponents P D
  orthogonal := by
    intro i j hij x y
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact False.elim (hij rfl)
      | succ j =>
        let y' : (P.component 1).carrier :=
          ⟨y, (P.component 1).nestedCarrier_le (D.component j) y.property⟩
        exact P.orthogonal 0 1 (by decide) x y'
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        let x' : (P.component 1).carrier :=
          ⟨x, (P.component 1).nestedCarrier_le (D.component i) x.property⟩
        exact P.orthogonal 1 0 (by decide) x' y
      | succ j =>
        let x' : (D.component i).carrier :=
          ((P.component 1).nestedCarrierEquiv (D.component i)).symm x
        let y' : (D.component j).carrier :=
          ((P.component 1).nestedCarrierEquiv (D.component j)).symm y
        have hij' : i ≠ j := by simpa using hij
        have horth := D.orthogonal i j hij' x' y'
        change q.bilin ((x' : (P.component 1).carrier) : V)
          ((y' : (P.component 1).carrier) : V) = 0 at horth
        have hx : ((x' : (P.component 1).carrier) : V) = (x : V) := by
          rw [← (P.component 1).coe_nestedCarrierEquiv (D.component i) x']
          exact congrArg Subtype.val
            ((P.component 1).nestedCarrierEquiv
              (D.component i) |>.apply_symm_apply x)
        have hy : ((y' : (P.component 1).carrier) : V) = (y : V) := by
          rw [← (P.component 1).coe_nestedCarrierEquiv (D.component j) y']
          exact congrArg Subtype.val
            ((P.component 1).nestedCarrierEquiv
              (D.component j) |>.apply_symm_apply y)
        rwa [hx, hy] at horth
  sum_eq := by
    apply le_antisymm
    · apply iSup_le
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact P.component_ambientSubmodule_le 0
      · apply le_trans _ (P.component_ambientSubmodule_le 1)
        rw [← D.iSup_liftNested_ambientSubmodule]
        exact le_iSup
          (fun k ↦ ((P.component 1).liftNested
            (D.component k)).ambientSubmodule) j
    · rw [← P.sum_eq]
      apply iSup_le
      intro i
      fin_cases i
      · exact le_iSup
          (fun k ↦ (prependNestedComponents P D k).ambientSubmodule) 0
      · change (P.component 1).ambientSubmodule ≤
          ⨆ i, (prependNestedComponents P D i).ambientSubmodule
        rw [← D.iSup_liftNested_ambientSubmodule]
        apply iSup_le
        intro j
        exact le_iSup
          (fun k ↦ (prependNestedComponents P D k).ambientSubmodule) j.succ

/-- Version of `prependNested` whose second block is presented by an
explicit equality.  This isolates dependent transport when a canonical
splitting's second component is definitionally obscured. -/
noncomputable def prependNestedOfEq
    (P : OrthogonalDecomposition q L 2) (C : QuadraticSublattice q)
    (hC : P.component 1 = C)
    (D : OrthogonalDecomposition C.space C.lattice t) :
    OrthogonalDecomposition q L (t + 1) := by
  subst C
  exact P.prependNested D

@[simp]
theorem prependNestedOfEq_zero
    (P : OrthogonalDecomposition q L 2) (C : QuadraticSublattice q)
    (hC : P.component 1 = C)
    (D : OrthogonalDecomposition C.space C.lattice t) :
    (P.prependNestedOfEq C hC D).component 0 = P.component 0 := by
  subst C
  rfl

@[simp]
theorem prependNestedOfEq_succ
    (P : OrthogonalDecomposition q L 2) (C : QuadraticSublattice q)
    (hC : P.component 1 = C)
    (D : OrthogonalDecomposition C.space C.lattice t) (i : Fin t) :
    (P.prependNestedOfEq C hC D).component i.succ =
      C.liftNested (D.component i) := by
  subst C
  rfl

end OrthogonalDecomposition

end Lattice

end Bong
