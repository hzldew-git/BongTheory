/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalDecompositionCons
import Bong.Lattice.NormGenerator
import Bong.Lattice.ModularScale

/-!
# Prepending a component to a property-A Jordan decomposition

This is the lattice-level constructor used when projection of a binary
modular block leaves a rank-one component in front of an already known
property-A Jordan decomposition.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

namespace JordanDecomposition

/-- Prepend one modular component to a property-A decomposition.  The two
cross inequalities are stated against every old component, so the
constructor also covers the empty right decomposition without a separate
case. -/
noncomputable def prependPropertyAWitness
    (P : OrthogonalDecomposition q L 2)
    (H : JordanDecomposition (P.component 1).space
      (P.component 1).lattice t)
    (hH : H.HasPropertyA)
    (scale norm : Kˣ)
    (hmodular : IsModular (P.component 0).space
      (P.component 0).lattice scale)
    (hnorm : normIdeal (P.component 0).space
      (P.component 0).lattice =
        principalIdeal (K := K) (norm : K))
    (hrank : finrank K (P.component 0).carrier = 1 ∨
      finrank K (P.component 0).carrier = 2)
    (hcrossNorm : ∀ i : Fin t,
      ordUnit K norm < ordUnit K (H.normGenerator i))
    (hcrossDual : ∀ i : Fin t,
      2 * ordUnit K scale - ordUnit K norm <
        2 * ordUnit K (H.scaleGenerator i) -
          ordUnit K (H.normGenerator i)) :
    {J : JordanDecomposition q L (t + 1) // J.HasPropertyA} := by
  let D := P.prependNested H.toOrthogonalDecomposition
  let scaleGenerator : Fin (t + 1) → Kˣ :=
    Fin.cases scale H.scaleGenerator
  let normGenerator : Fin (t + 1) → Kˣ :=
    Fin.cases norm H.normGenerator
  let J : JordanDecomposition q L (t + 1) := {
    toOrthogonalDecomposition := D
    scaleGenerator := scaleGenerator
    normGenerator := normGenerator
    modular := by
      intro i
      cases i using Fin.cases with
      | zero =>
          change IsModular (P.component 0).space
            (P.component 0).lattice scale
          exact hmodular
      | succ i =>
          change IsModular
            ((P.component 1).liftNested (H.component i)).space
            ((P.component 1).liftNested (H.component i)).lattice
            (H.scaleGenerator i)
          exact QuadraticSublattice.IsModular.liftNested
            (P.component 1) (H.component i) (H.modular i)
    scaleIdeal_eq := by
      intro i
      cases i using Fin.cases with
      | zero =>
          change scaleIdeal (P.component 0).space
              (P.component 0).lattice =
            principalIdeal (K := K) (scale : K)
          apply hmodular.scaleIdeal_eq_principal
          rcases hrank with h | h <;> omega
      | succ i =>
          change scaleIdeal
              ((P.component 1).liftNested (H.component i)).space
              ((P.component 1).liftNested (H.component i)).lattice =
            principalIdeal (K := K) (H.scaleGenerator i : K)
          apply (QuadraticSublattice.IsModular.liftNested
            (P.component 1) (H.component i)
              (H.modular i)).scaleIdeal_eq_principal
          rw [(P.component 1).finrank_liftNested]
          change 0 < H.componentRank i
          rcases hH.1 i with h | h <;> omega
    normIdeal_eq := by
      intro i
      cases i using Fin.cases with
      | zero =>
          change normIdeal (P.component 0).space
              (P.component 0).lattice =
            principalIdeal (K := K) (norm : K)
          exact hnorm
      | succ i =>
          change normIdeal
              ((P.component 1).liftNested (H.component i)).space
              ((P.component 1).liftNested (H.component i)).lattice =
            principalIdeal (K := K) (H.normGenerator i : K)
          calc
            normIdeal
                ((P.component 1).liftNested (H.component i)).space
                ((P.component 1).liftNested (H.component i)).lattice =
                normIdeal (H.component i).space
                  (H.component i).lattice :=
              normIdeal_map_isometry
                ((P.component 1).liftNestedIsometry
                  (H.component i)).toQuadraticSpaceIsometry
                (H.component i).lattice
            _ = principalIdeal (K := K)
                (H.normGenerator i : K) := H.normIdeal_eq i
    scaleOrder_strict := by
      intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => exact (lt_irrefl _ hij).elim
          | succ j =>
              change ordUnit K scale <
                ordUnit K (H.scaleGenerator j)
              have hn := hcrossNorm j
              have hd := hcrossDual j
              omega
      | succ i =>
          cases j using Fin.cases with
          | zero => exact (Nat.not_lt_zero i.succ.val hij).elim
          | succ j =>
              change ordUnit K (H.scaleGenerator i) <
                ordUnit K (H.scaleGenerator j)
              exact H.scaleOrder_strict (Nat.succ_lt_succ_iff.mp hij) }
  have hproperty : J.HasPropertyA := by
    constructor
    · intro i
      cases i using Fin.cases with
      | zero =>
          change finrank K (P.component 0).carrier = 1 ∨
            finrank K (P.component 0).carrier = 2
          exact hrank
      | succ i =>
          change finrank K
              ((P.component 1).liftNested (H.component i)).carrier = 1 ∨
            finrank K
              ((P.component 1).liftNested (H.component i)).carrier = 2
          rw [(P.component 1).finrank_liftNested]
          exact hH.1 i
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => exact (lt_irrefl _ hij).elim
          | succ j =>
              change
                0 < ordUnit K (H.normGenerator j) - ordUnit K norm ∧
                ordUnit K (H.normGenerator j) - ordUnit K norm <
                  2 * (ordUnit K (H.scaleGenerator j) -
                    ordUnit K scale)
              have hn := hcrossNorm j
              have hd := hcrossDual j
              constructor <;> omega
      | succ i =>
          cases j using Fin.cases with
          | zero => exact (Nat.not_lt_zero i.succ.val hij).elim
          | succ j =>
              change
                0 < ordUnit K (H.normGenerator j) -
                    ordUnit K (H.normGenerator i) ∧
                ordUnit K (H.normGenerator j) -
                    ordUnit K (H.normGenerator i) <
                  2 * (ordUnit K (H.scaleGenerator j) -
                    ordUnit K (H.scaleGenerator i))
              exact hH.2 (Nat.succ_lt_succ_iff.mp hij)
  exact ⟨J, hproperty⟩

end JordanDecomposition

end Lattice

end Bong
