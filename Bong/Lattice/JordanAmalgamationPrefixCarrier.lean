/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.JordanAmalgamation
import Bong.Lattice.OrthogonalDecompositionPrefixCarrier
import Bong.Lattice.OrthogonalDecompositionReplacePairPrefix

/-!
# Prefix carriers under adjacent Jordan amalgamation

Merging an adjacent equal-scale pair leaves every numerical prefix ending
strictly before that pair unchanged as an ambient quadratic subspace.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice.WeakJordanDecomposition

/-- An adjacent merge does not change a prefix ending before the merged
pair.  The same numerical cut is used on the old and new decompositions. -/
theorem mergeAdjacentAt_prefixCarrier_eq_of_le {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (cut : Nat) (hcut : cut ≤ k.val) :
    (W.mergeAdjacentAt k heq).toOrthogonalDecomposition.prefixCarrier cut =
      W.toOrthogonalDecomposition.prefixCarrier cut := by
  let P := (W.mergeAdjacentAt k heq).toOrthogonalDecomposition
  let Q := W.toOrthogonalDecomposition
  apply le_antisymm
  · apply P.prefixCarrier_le_of_component_le_general Q cut cut
    intro i hi
    have hik : i < k := by
      change i.val < k.val
      omega
    rw [show P.component i = Q.component i.castSucc by
      simpa only [P, Q] using W.mergeAdjacentAt_component_of_lt k heq i hik]
    exact Q.component_carrier_le_prefixCarrier i.castSucc hi
  · apply Q.prefixCarrier_le_of_component_le_general P cut cut
    intro i hi
    have hit : i.val < t := by
      have hk := k.isLt
      omega
    let j : Fin t := ⟨i.val, hit⟩
    have hjk : j < k := by
      change i.val < k.val
      omega
    have hij : i = j.castSucc := by
      apply Fin.ext
      rfl
    rw [hij, ← show P.component j = Q.component j.castSucc by
      simpa only [P, Q] using W.mergeAdjacentAt_component_of_lt k heq j hjk]
    exact P.component_carrier_le_prefixCarrier j hi

/-- An adjacent merge also preserves every prefix containing both old
members of the merged pair.  The new decomposition has one fewer component,
so its numerical cut is shifted down by one. -/
theorem mergeAdjacentAt_prefixCarrier_eq_of_pair_le {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (cut : Nat) (hpair : k.val + 2 ≤ cut) (hcut : cut ≤ t + 1) :
    (W.mergeAdjacentAt k heq).toOrthogonalDecomposition.prefixCarrier
        (cut - 1) =
      W.toOrthogonalDecomposition.prefixCarrier cut := by
  cases t with
  | zero => exact Fin.elim0 k
  | succ t =>
    let P := (W.mergeAdjacentAt k heq).toOrthogonalDecomposition
    let Q := W.toOrthogonalDecomposition
    have hpairCarrier :
        (P.component k).carrier =
          (Q.component k.castSucc).carrier ⊔
            (Q.component k.succ).carrier := by
      rw [show P.component k = Q.orthogonalSup k.castSucc_lt_succ.ne by
        simpa only [P, Q] using W.mergeAdjacentAt_component_self k heq]
      exact Q.orthogonalSup_carrier_eq_sup k.castSucc_lt_succ.ne
    apply le_antisymm
    · apply P.prefixCarrier_le_of_component_le_general Q (cut - 1) cut
      intro i hi
      by_cases hik : i = k
      · subst i
        rw [hpairCarrier]
        exact _root_.sup_le
          (Q.component_carrier_le_prefixCarrier k.castSucc (by
            change k.val < cut
            omega))
          (Q.component_carrier_le_prefixCarrier k.succ (by
            change k.val + 1 < cut
            omega))
      · rw [show P.component i = Q.component (k.succ.succAbove i) by
          simpa only [P, Q] using
            W.mergeAdjacentAt_component_of_ne k heq i hik]
        apply Q.component_carrier_le_prefixCarrier
        by_cases hil : i < k
        · have hmap : k.succ.succAbove i = i.castSucc := by
            rw [Fin.succAbove_of_castSucc_lt]
            exact Fin.castSucc_lt_succ_iff.mpr hil.le
          rw [hmap]
          change i.val < cut
          omega
        · have hki : k < i := lt_of_le_of_ne (le_of_not_gt hil) (Ne.symm hik)
          have hmap : k.succ.succAbove i = i.succ := by
            rw [Fin.succAbove_of_le_castSucc]
            exact Fin.succ_le_castSucc_iff.mpr hki
          rw [hmap]
          change i.val + 1 < cut
          omega
    · apply Q.prefixCarrier_le_of_component_le_general P cut (cut - 1)
      intro i hi
      by_cases hil : i < k.castSucc
      · let j : Fin (t + 1) := ⟨i.val, by
          have hk := k.isLt
          omega⟩
        have hjk : j < k := by
          change i.val < k.val
          exact hil
        have hij : i = j.castSucc := by
          apply Fin.ext
          rfl
        rw [hij, ← show P.component j = Q.component j.castSucc by
          simpa only [P, Q] using
            W.mergeAdjacentAt_component_of_lt k heq j hjk]
        exact P.component_carrier_le_prefixCarrier j (by
          change j.val < cut - 1
          change i.val < k.val at hil
          omega)
      · by_cases hik : i = k.castSucc
        · subst i
          have hmerged := P.component_carrier_le_prefixCarrier k (by
            change k.val < cut - 1
            omega)
          rw [hpairCarrier] at hmerged
          exact _root_.le_sup_left.trans hmerged
        · by_cases his : i = k.succ
          · subst i
            have hmerged := P.component_carrier_le_prefixCarrier k (by
              change k.val < cut - 1
              omega)
            rw [hpairCarrier] at hmerged
            exact _root_.le_sup_right.trans hmerged
          · have hright : k.succ < i := by
              have hle : k.castSucc ≤ i := le_of_not_gt hil
              have hlt : k.castSucc < i := lt_of_le_of_ne hle (Ne.symm hik)
              have hsuccLe : k.succ ≤ i := by
                change k.val + 1 ≤ i.val
                change k.val < i.val at hlt
                omega
              exact lt_of_le_of_ne hsuccLe (Ne.symm his)
            let j : Fin (t + 1) := ⟨i.val - 1, by
              have hiBound := i.isLt
              omega⟩
            have hkj : k < j := by
              change k.val < i.val - 1
              change k.val + 1 < i.val at hright
              omega
            have hjk : j ≠ k := ne_of_gt hkj
            have hmap : k.succ.succAbove j = i := by
              apply Fin.ext
              rw [Fin.succAbove_of_le_castSucc]
              · change i.val - 1 + 1 = i.val
                omega
              · exact Fin.succ_le_castSucc_iff.mpr hkj
            rw [← hmap, ← show P.component j =
                Q.component (k.succ.succAbove j) by
              simpa only [P, Q] using
                W.mergeAdjacentAt_component_of_ne k heq j hjk]
            exact P.component_carrier_le_prefixCarrier j (by
              change i.val - 1 < cut - 1
              omega)

end Lattice.WeakJordanDecomposition

end Bong
