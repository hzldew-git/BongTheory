/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaJordanTree
import Bong.Lattice.OrthogonalDecompositionCons
import Bong.Lattice.RawJordanDecomposition

/-!
# O'Meara's raw Jordan decomposition

The recursive tree of O'Meara 91C is flattened into one ambient orthogonal
decomposition.  Its unary or binary blocks are modular, carry explicit scale
and norm generators, and occur in nondecreasing scale order.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace OmearaJordanTree

/-- The number of blocks in the unamalgamated recursive splitting. -/
noncomputable def blockCount {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (T : OmearaJordanTree W r M) : Nat :=
  match T with
  | .nil _ _ _ => 0
  | .node _ _ _ _ tail => tail.blockCount + 1

/-- Forget the arithmetic labels and flatten the tree to an orthogonal
decomposition in its original ambient space. -/
noncomputable def toOrthogonalDecomposition
    (T : OmearaJordanTree V q L) :
    OrthogonalDecomposition q L T.blockCount := by
  induction T with
  | nil q L exhausted =>
      exact {
        component := Fin.elim0
        orthogonal := fun i ↦ Fin.elim0 i
        sum_eq := by
          apply le_antisymm
          · exact iSup_le fun i ↦ Fin.elim0 i
          · intro x hx
            have hx0 : x = 0 := exhausted.elim x 0
            subst x
            exact Submodule.zero_mem _
      }
  | node D z generator anisotropic tail ih =>
      exact D.canonicalSplitting.prependNested ih

/-- The scale ideal of the next recursive lattice is contained in the scale
ideal at the preceding stage. -/
theorem orthogonal_scaleIdeal_le (D : MinimalScaleComponentData q L) :
    scaleIdeal D.orthogonalComponent.space D.orthogonalComponent.lattice ≤
      scaleIdeal q L :=
  D.orthogonalComponent.scaleIdeal_le_of_ambientSubmodule_le
    (D.canonicalSplitting.component_ambientSubmodule_le 1)

/-- The scale order of the first tail block is no smaller than the head
scale. -/
theorem head_scaleOrder_le
    (D : MinimalScaleComponentData q L)
    (E : MinimalScaleComponentData D.orthogonalComponent.space
      D.orthogonalComponent.lattice) :
    ordUnit K D.scaleGenerator ≤ ordUnit K E.scaleGenerator := by
  have hle : principalIdeal (K := K) (E.scaleGenerator : K) ≤
      principalIdeal (K := K) (D.scaleGenerator : K) := by
    rw [← E.ambientScaleIdeal_eq, ← D.ambientScaleIdeal_eq]
    exact orthogonal_scaleIdeal_le D
  have hord := (principalIdeal_le_iff_ord_ge
    (Units.ne_zero E.scaleGenerator)
    (Units.ne_zero D.scaleGenerator)).1 hle
  apply WithTop.coe_le_coe.mp
  simpa only [coe_ordUnit] using hord

/-- The complete unamalgamated decomposition attached to a recursive tree. -/
noncomputable def toRawJordanDecomposition
    (T : OmearaJordanTree V q L) :
    RawJordanDecomposition q L T.blockCount := by
  induction T with
  | nil q L exhausted =>
      exact {
        toOrthogonalDecomposition := {
          component := Fin.elim0
          orthogonal := fun i ↦ Fin.elim0 i
          sum_eq := by
            apply le_antisymm
            · exact iSup_le fun i ↦ Fin.elim0 i
            · intro x hx
              have hx0 : x = 0 := exhausted.elim x 0
              subst x
              exact Submodule.zero_mem _
        }
        scaleGenerator := Fin.elim0
        normGenerator := Fin.elim0
        modular := fun i ↦ Fin.elim0 i
        scaleIdeal_eq := fun i ↦ Fin.elim0 i
        normIdeal_eq := fun i ↦ Fin.elim0 i
        rank_one_or_two := fun i ↦ Fin.elim0 i
        scaleOrder_mono := fun {i} ↦ Fin.elim0 i
      }
  | node D z generator anisotropic tail ih =>
      let tailRaw := ih
      let C := D.orthogonalComponent
      let scaleGenerator : Fin (tail.blockCount + 1) → Kˣ :=
        Fin.cases D.scaleGenerator tailRaw.scaleGenerator
      let normGenerator : Fin (tail.blockCount + 1) → Kˣ :=
        Fin.cases (Units.mk0 (D.component.space.quadratic z) anisotropic)
          tailRaw.normGenerator
      exact {
        toOrthogonalDecomposition :=
          D.canonicalSplitting.prependNestedOfEq D.orthogonalComponent
            D.canonicalSplitting_one tailRaw.toOrthogonalDecomposition
        scaleGenerator := scaleGenerator
        normGenerator := normGenerator
        modular := by
          intro i
          cases i using Fin.cases with
          | zero => exact D.modular
          | succ i =>
              change IsModular
                (C.liftNested (tailRaw.component i)).space
                (C.liftNested (tailRaw.component i)).lattice _
              exact QuadraticSublattice.IsModular.liftNested C _
                (tailRaw.modular i)
        scaleIdeal_eq := by
          intro i
          cases i using Fin.cases with
          | zero => exact D.component_scaleIdeal_eq
          | succ i =>
              change scaleIdeal
                (C.liftNested (tailRaw.component i)).space
                (C.liftNested (tailRaw.component i)).lattice = _
              apply (QuadraticSublattice.IsModular.liftNested C _
                (tailRaw.modular i)).scaleIdeal_eq_principal
              rw [C.finrank_liftNested]
              rcases tailRaw.rank_one_or_two i with h | h
              · rw [h]
                decide
              · rw [h]
                decide
        normIdeal_eq := by
          intro i
          cases i using Fin.cases with
          | zero => exact generator.normIdeal_eq
          | succ i =>
              calc
                normIdeal (C.liftNested (tailRaw.component i)).space
                    (C.liftNested (tailRaw.component i)).lattice =
                    normIdeal (tailRaw.component i).space
                      (tailRaw.component i).lattice :=
                  normIdeal_map_isometry
                    (C.liftNestedIsometry
                      (tailRaw.component i)).toQuadraticSpaceIsometry
                    (tailRaw.component i).lattice
                _ = principalIdeal (K := K)
                    (tailRaw.normGenerator i : K) := tailRaw.normIdeal_eq i
        rank_one_or_two := by
          intro i
          cases i using Fin.cases with
          | zero => exact D.rank_one_or_two
          | succ i =>
              rw [OrthogonalDecomposition.prependNestedOfEq_succ]
              change finrank K (C.liftNested
                (tailRaw.component i)).carrier = 1 ∨ _
              rw [C.finrank_liftNested]
              exact tailRaw.rank_one_or_two i
        scaleOrder_mono := by
          intro i j hij
          cases i using Fin.cases with
          | zero =>
              cases j using Fin.cases with
              | zero => exact False.elim (lt_irrefl _ hij)
              | succ j =>
                  cases tail with
                  | nil _ _ exhausted => exact Fin.elim0 j
                  | node E w hgen hw rest =>
                      have htail : ordUnit K E.scaleGenerator ≤
                          ordUnit K (tailRaw.scaleGenerator j) := by
                        have hle : principalIdeal (K := K)
                              (tailRaw.scaleGenerator j : K) ≤
                            principalIdeal (K := K)
                              (E.scaleGenerator : K) := by
                          rw [← tailRaw.scaleIdeal_eq j,
                            ← E.ambientScaleIdeal_eq]
                          exact QuadraticSublattice.scaleIdeal_le_of_ambientSubmodule_le
                            (tailRaw.component j)
                            (tailRaw.component_ambientSubmodule_le j)
                        have hord := (principalIdeal_le_iff_ord_ge
                          (Units.ne_zero (tailRaw.scaleGenerator j))
                          (Units.ne_zero E.scaleGenerator)).1 hle
                        apply WithTop.coe_le_coe.mp
                        simpa only [coe_ordUnit] using hord
                      exact (head_scaleOrder_le D E).trans htail
          | succ i =>
              cases j using Fin.cases with
              | zero => exact False.elim (Nat.not_lt_zero _ hij)
              | succ j =>
                  exact tailRaw.scaleOrder_mono
                    (Nat.succ_lt_succ_iff.mp hij)
      }

end OmearaJordanTree

/-- O'Meara 91C in its unamalgamated form. -/
noncomputable def omearaRawJordanDecomposition
    (q : QuadraticSpace K V) (L : Lattice K V) :
    RawJordanDecomposition q L (omearaJordanTree q L).blockCount :=
  (omearaJordanTree q L).toRawJordanDecomposition

end Lattice

end Bong
