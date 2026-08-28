/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaSaturationShift

/-!
# Iterating O'Meara's rank-at-least-seven saturation step

The two coefficient shifts of 93:21 change one Jordan component while
transporting every other component integrally.  This file proves the rank
and norm-group preservation statements and iterates the construction through
the finite ordered set of Jordan components.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace JordanDecomposition

variable {n : Nat} (J : JordanDecomposition q L (n + 2))
  (i : Fin (n + 2))

/-- An unselected component is carried integrally through a saturation
replacement. -/
noncomputable def saturationReplaceComponent_otherComponentIsometry
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i)
    {j : Fin (n + 2)} (hji : j ≠ i) :
    Isometry (J.component j).space
      ((J.saturationReplaceComponent i S hrank).component j).space
      (J.component j).lattice
      ((J.saturationReplaceComponent i S hrank).component j).lattice := by
  exact J.replaceComponent_otherComponentIsometry i
    (J.saturationReplacementPair i S hrank)
    (J.saturationRemainderIsometry i S hrank)
    (J.fundamentalNormGenerator i)
    (J.saturationReplacementHead_modular i S hrank)
    (J.saturationReplacementHead_scaleIdeal_eq i S hrank)
    (J.saturationReplacementHead_normIdeal_eq i S hrank) hji

/-- Norm groups of all unselected components are unchanged. -/
theorem saturationReplaceComponent_other_normGroup_eq
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i)
    {j : Fin (n + 2)} (hji : j ≠ i) :
    normGroupSet ((J.saturationReplaceComponent i S hrank).component j).space
        ((J.saturationReplaceComponent i S hrank).component j).lattice =
      normGroupSet (J.component j).space (J.component j).lattice :=
  normGroupSet_eq_of_latticeIsometry
    (J.saturationReplaceComponent_otherComponentIsometry i S hrank hji)

/-- The shifted coordinate component has exactly the old component rank. -/
theorem saturationShiftedComponent_finrank_eq_componentRank
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) :
    finrank K
        ((Fin 2 → K) ×
          ((Fin 2 → K) × (S.decomposition.component 2).carrier)) =
      J.componentRank i := by
  letI : Module.Finite K (S.decomposition.component 2).carrier :=
    (S.decomposition.component 2).lattice.moduleFinite
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun,
    S.complement_finrank]
  unfold componentRank at hrank ⊢
  omega

/-- The selected replacement component has the old rank. -/
theorem saturationReplaceComponent_selected_componentRank
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) :
    (J.saturationReplaceComponent i S hrank).componentRank i =
      J.componentRank i := by
  change finrank K
    ((J.saturationReplaceComponent i S hrank).component i).carrier = _
  rw [saturationReplaceComponent, replaceComponent_component_self]
  rw [← (J.saturationShiftedComponentIsometry i S hrank).toLinearEquiv.finrank_eq]
  exact J.saturationShiftedComponent_finrank_eq_componentRank i S hrank

/-- Every unselected replacement component has the old rank. -/
theorem saturationReplaceComponent_other_componentRank
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i)
    {j : Fin (n + 2)} (hji : j ≠ i) :
    (J.saturationReplaceComponent i S hrank).componentRank j =
      J.componentRank j := by
  unfold componentRank
  exact (J.saturationReplaceComponent_otherComponentIsometry i S hrank
    hji).toLinearEquiv.finrank_eq.symm

/-- The complete public interface of one concrete saturation step.  The
large geometric construction is hidden behind these preservation fields so
that finite iteration never unfolds it again. -/
structure SaturationStepResult
    (J : JordanDecomposition q L (n + 2)) (i : Fin (n + 2)) where
  jordan : JordanDecomposition q L (n + 2)
  scaleGenerator_eq : ∀ j,
    jordan.scaleGenerator j = J.scaleGenerator j
  componentRank_eq : ∀ j,
    jordan.componentRank j = J.componentRank j
  fundamentalNormGroup_eq : ∀ j,
    jordan.fundamentalNormGroup j = J.fundamentalNormGroup j
  selectedSaturated :
    normGroupSet (jordan.component i).space (jordan.component i).lattice =
      jordan.fundamentalNormGroup i
  otherNormGroup_eq : ∀ {j}, j ≠ i →
    normGroupSet (jordan.component j).space (jordan.component j).lattice =
      normGroupSet (J.component j).space (J.component j).lattice

set_option maxHeartbeats 1000000 in
-- This command elaborates the dependent geometry once; clients use only the
-- small proof fields of `SaturationStepResult`.
/-- Construct the certified saturation result at one rank-at-least-seven
component. -/
noncomputable opaque saturationStepResult
    (hrank : 7 ≤ J.componentRank i) : SaturationStepResult J i := by
  let S := omearaTwoHyperbolicPlaneData (J.modular i) hrank
  let N := J.saturationReplaceComponent i S hrank
  refine {
    jordan := N
    scaleGenerator_eq := ?_
    componentRank_eq := ?_
    fundamentalNormGroup_eq := ?_
    selectedSaturated := ?_
    otherNormGroup_eq := ?_
  }
  · intro j
    exact J.saturationReplaceComponent_scaleGenerator i S hrank j
  · intro j
    by_cases hji : j = i
    · subst j
      exact J.saturationReplaceComponent_selected_componentRank i S hrank
    · exact J.saturationReplaceComponent_other_componentRank i S hrank hji
  · intro j
    exact J.saturationReplaceComponent_fundamentalNormGroup i S hrank j
  · exact J.saturationReplaceComponent_selected_isSaturated i S hrank
  · intro j hji
    exact J.saturationReplaceComponent_other_normGroup_eq i S hrank hji

/-- A state after processing all indices whose values are below `k`. -/
structure SaturationState (J : JordanDecomposition q L (n + 2))
    (k : Nat) where
  jordan : JordanDecomposition q L (n + 2)
  scaleGenerator_eq : ∀ j,
    jordan.scaleGenerator j = J.scaleGenerator j
  componentRank_eq : ∀ j,
    jordan.componentRank j = J.componentRank j
  saturatedBefore : ∀ j, j.val < k →
    normGroupSet (jordan.component j).space (jordan.component j).lattice =
      jordan.fundamentalNormGroup j

/-- Before the first index is processed, the original Jordan splitting is a
valid empty saturation state. -/
def initialSaturationState : SaturationState J 0 where
  jordan := J
  scaleGenerator_eq := fun _ ↦ rfl
  componentRank_eq := fun _ ↦ rfl
  saturatedBefore := by omega

set_option maxHeartbeats 1000000 in
-- The state transition composes dependent proof fields indexed by the
-- component currently being processed.
/-- Advance a saturation state by processing the component with index
`k`. -/
noncomputable def SaturationState.next
    {k : Nat} (T : SaturationState J k) (hk : k < n + 2)
    (hrank : ∀ j : Fin (n + 2), 7 ≤ J.componentRank j) :
    SaturationState J (k + 1) := by
  let i : Fin (n + 2) := ⟨k, hk⟩
  have hiRank : 7 ≤ T.jordan.componentRank i := by
    rw [T.componentRank_eq i]
    exact hrank i
  let R := T.jordan.saturationStepResult i hiRank
  refine {
    jordan := R.jordan
    scaleGenerator_eq := ?_
    componentRank_eq := ?_
    saturatedBefore := ?_
  }
  · intro j
    exact (R.scaleGenerator_eq j).trans
      (T.scaleGenerator_eq j)
  · intro j
    by_cases hji : j = i
    · subst j
      exact (R.componentRank_eq i).trans (T.componentRank_eq i)
    · exact (R.componentRank_eq j).trans
        (T.componentRank_eq j)
  · intro j hj
    by_cases hji : j = i
    · subst j
      exact R.selectedSaturated
    · have hjk : j.val < k := by
        have hval : j.val ≠ k := by
          intro h
          apply hji
          exact Fin.ext h
        omega
      calc
        normGroupSet (R.jordan.component j).space
            (R.jordan.component j).lattice =
            normGroupSet (T.jordan.component j).space
              (T.jordan.component j).lattice :=
          R.otherNormGroup_eq hji
        _ = T.jordan.fundamentalNormGroup j :=
          T.saturatedBefore j hjk
        _ = R.jordan.fundamentalNormGroup j := by
          symm
          exact R.fundamentalNormGroup_eq j

/-- Process the first `k` Jordan components in their scale order. -/
noncomputable def saturationStateUpTo
    (hrank : ∀ j : Fin (n + 2), 7 ≤ J.componentRank j) :
    (k : Nat) → k ≤ n + 2 → SaturationState J k
  | 0, _ => J.initialSaturationState
  | k + 1, hk =>
      let previous := saturationStateUpTo hrank k
        ((Nat.le_succ k).trans hk)
      SaturationState.next J previous (Nat.lt_of_succ_le hk) hrank

/-- The Jordan decomposition obtained after all rank-at-least-seven
components have been processed. -/
noncomputable def saturatedJordanOfComponentRanksAtLeastSeven
    (hrank : ∀ j : Fin (n + 2), 7 ≤ J.componentRank j) :
    JordanDecomposition q L (n + 2) :=
  (saturationStateUpTo (J := J) hrank (n + 2) le_rfl).jordan

/-- O'Meara 93:21 in the rank-at-least-seven case: every Jordan splitting
whose components have rank at least seven admits a saturated splitting of
the same lattice and with the same ordered scales. -/
theorem saturatedJordanOfComponentRanksAtLeastSeven_isSaturated
    (hrank : ∀ j : Fin (n + 2), 7 ≤ J.componentRank j) :
    (J.saturatedJordanOfComponentRanksAtLeastSeven hrank).IsSaturated := by
  intro j
  exact (saturationStateUpTo (J := J) hrank
    (n + 2) le_rfl).saturatedBefore
    j j.isLt

@[simp]
theorem saturatedJordanOfComponentRanksAtLeastSeven_scaleGenerator
    (hrank : ∀ j : Fin (n + 2), 7 ≤ J.componentRank j)
    (j : Fin (n + 2)) :
    (J.saturatedJordanOfComponentRanksAtLeastSeven hrank).scaleGenerator j =
      J.scaleGenerator j :=
  (saturationStateUpTo (J := J) hrank
    (n + 2) le_rfl).scaleGenerator_eq j

@[simp]
theorem saturatedJordanOfComponentRanksAtLeastSeven_componentRank
    (hrank : ∀ j : Fin (n + 2), 7 ≤ J.componentRank j)
    (j : Fin (n + 2)) :
    (J.saturatedJordanOfComponentRanksAtLeastSeven hrank).componentRank j =
      J.componentRank j :=
  (saturationStateUpTo (J := J) hrank
    (n + 2) le_rfl).componentRank_eq j

end JordanDecomposition

end Lattice

end Bong
