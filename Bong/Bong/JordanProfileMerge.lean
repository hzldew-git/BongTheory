/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.JordanEffectiveNorm
import Bong.Bong.JordanOrderProfileSequence
import Mathlib.Data.Finset.Sort

/-!
# Flattened Jordan profiles under adjacent amalgamation

This file proves that amalgamating equal-scale adjacent components does not
change the lexicographically flattened profile.  The local norm calculation
is in `JordanEffectiveNorm`; here we supply the global finite-index
bookkeeping needed in Beli (2019), Section 5.4.
-/

open scoped BigOperators

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace JordanProfileMergeIndexing

/-- The canonical increasing enumeration of the lexicographic dependent
family with fiber sizes `rank`. -/
noncomputable def lexSigmaRankOrderIsoFin {t : Nat} (rank : Fin t → Nat) :
    Fin (∑ k, rank k) ≃o Lex (Σ k : Fin t, Fin (rank k)) :=
  Fintype.orderIsoFinOfCardEq _ (by simp)

/-- The canonical enumeration assigns to `(k,j)` its prefix-rank offset plus
the local coordinate. -/
theorem lexSigmaRankOrderIsoFin_symm_val {t : Nat} (rank : Fin t → Nat)
    (k : Fin t) (j : Fin (rank k)) :
    ((lexSigmaRankOrderIsoFin rank).symm (toLex ⟨k, j⟩)).val =
      (∑ h ∈ Finset.Iio k, rank h) + j.val := by
  let e := lexSigmaRankOrderIsoFin rank
  calc
    (e.symm (toLex ⟨k, j⟩)).val =
        Fintype.card {x : Lex (Σ h : Fin t, Fin (rank h)) //
          x < e (e.symm (toLex ⟨k, j⟩))} :=
      JordanProfileIndexing.orderIso_fin_val_eq_card_Iio e _
    _ = Fintype.card {x : Lex (Σ h : Fin t, Fin (rank h)) //
          x < toLex ⟨k, j⟩} := by rw [e.apply_symm_apply]
    _ = (∑ h ∈ Finset.Iio k, rank h) + j.val :=
      JordanProfileIndexing.lexSigmaIio_card rank k j

/-- Split a finite linear order into the positions before, at, and after a
chosen index. -/
theorem sum_univ_eq_sum_Iio_add_self_add_sum_Ioi {t : Nat}
    (rank : Fin t → Nat) (k : Fin t) :
    (∑ i, rank i) =
      (∑ i ∈ Finset.Iio k, rank i) + rank k +
        ∑ i ∈ Finset.Ioi k, rank i := by
  classical
  have hleft : Disjoint (Finset.Iio k)
      ({k} ∪ Finset.Ioi k : Finset (Fin t)) := by
    rw [Finset.disjoint_left]
    intro i hi hrest
    simp only [Finset.mem_Iio, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_Ioi] at hi hrest
    rcases hrest with rfl | hki
    · exact (lt_irrefl _ hi).elim
    · exact (lt_asymm hi hki).elim
  have hright : Disjoint ({k} : Finset (Fin t)) (Finset.Ioi k) := by
    simp
  have hunion : Finset.Iio k ∪ ({k} ∪ Finset.Ioi k) =
      (Finset.univ : Finset (Fin t)) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_singleton,
      Finset.mem_Ioi, Finset.mem_univ, iff_true]
    rcases lt_trichotomy i k with hik | hik | hik
    · exact Or.inl hik
    · exact Or.inr (Or.inl hik)
    · exact Or.inr (Or.inr hik)
  change (∑ i ∈ (Finset.univ : Finset (Fin t)), rank i) = _
  rw [← hunion, Finset.sum_union hleft, Finset.sum_union hright]
  simp [add_assoc]

end JordanProfileMergeIndexing

namespace Lattice.WeakJordanDecomposition

/-- Adjacent amalgamation preserves the total sum of component ranks. -/
theorem sum_componentRank_mergeAdjacentAt {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    (∑ j, finrank K ((W.mergeAdjacentAt k heq).component j).carrier) =
      ∑ i, finrank K (W.component i).carrier := by
  classical
  let oldRank : Fin (t + 1) → Nat :=
    fun i ↦ finrank K (W.component i).carrier
  let newRank : Fin t → Nat :=
    fun j ↦ finrank K ((W.mergeAdjacentAt k heq).component j).carrier
  have hself : newRank k = oldRank k.castSucc + oldRank k.succ := by
    simpa only [newRank, oldRank] using
      W.mergeAdjacentAt_componentRank_self k heq
  have hother : ∀ j : Fin t, j ≠ k →
      newRank j = oldRank (k.succ.succAbove j) := by
    intro j hj
    simp only [newRank, oldRank]
    rw [W.mergeAdjacentAt_component_of_ne k heq j hj]
  have hnewSplit :
      (∑ j, newRank j) =
        (∑ j ∈ (Finset.univ : Finset (Fin t)).erase k, newRank j) + newRank k :=
    (Finset.sum_erase_add Finset.univ newRank (Finset.mem_univ k)).symm
  have hotherSum :
      (∑ j ∈ (Finset.univ : Finset (Fin t)).erase k, newRank j) =
        ∑ j ∈ (Finset.univ : Finset (Fin t)).erase k,
          oldRank (k.succ.succAbove j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hother j (Finset.ne_of_mem_erase hj)
  have hskipSplit :
      (∑ j, oldRank (k.succ.succAbove j)) =
        (∑ j ∈ (Finset.univ : Finset (Fin t)).erase k,
          oldRank (k.succ.succAbove j)) + oldRank k.castSucc := by
    simpa using
      (Finset.sum_erase_add Finset.univ
        (fun j : Fin t ↦ oldRank (k.succ.succAbove j))
        (Finset.mem_univ k)).symm
  have holdSplit :
      (∑ i, oldRank i) = oldRank k.succ +
        ∑ j, oldRank (k.succ.succAbove j) :=
    Fin.sum_univ_succAbove oldRank k.succ
  change (∑ j, newRank j) = ∑ i, oldRank i
  omega

/-- Before the retained merge position, the prefix-rank sum is unchanged. -/
theorem sum_componentRank_Iio_mergeAdjacentAt_self {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    (∑ j ∈ Finset.Iio k,
        finrank K ((W.mergeAdjacentAt k heq).component j).carrier) =
      ∑ i ∈ Finset.Iio k.castSucc,
        finrank K (W.component i).carrier := by
  rw [Fin.sum_Iio_castSucc]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≠ k := Fin.ne_of_lt (Finset.mem_Iio.mp hj)
  rw [W.mergeAdjacentAt_component_of_ne k heq j hjk]
  rw [Fin.succAbove_of_castSucc_lt]
  exact Fin.castSucc_lt_succ_iff.mpr (Finset.mem_Iio.mp hj).le

/-- Every prefix ending strictly before the retained merge position is
unchanged after embedding its indices by `Fin.castSucc`. -/
theorem sum_componentRank_Iio_mergeAdjacentAt_of_lt {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (j : Fin t) (hjk : j < k) :
    (∑ p ∈ Finset.Iio j,
        finrank K ((W.mergeAdjacentAt k heq).component p).carrier) =
      ∑ i ∈ Finset.Iio j.castSucc,
        finrank K (W.component i).carrier := by
  rw [Fin.sum_Iio_castSucc]
  apply Finset.sum_congr rfl
  intro p hp
  have hpk : p < k := (Finset.mem_Iio.mp hp).trans hjk
  rw [W.mergeAdjacentAt_component_of_ne k heq p (Fin.ne_of_lt hpk)]
  rw [Fin.succAbove_of_castSucc_lt]
  exact Fin.castSucc_lt_succ_iff.mpr hpk.le

/-- Every prefix ending strictly after the retained merge position agrees
with the prefix ending at the corresponding shifted old position. -/
theorem sum_componentRank_Iio_mergeAdjacentAt_of_gt {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (j : Fin t) (hkj : k < j) :
    (∑ p ∈ Finset.Iio j,
        finrank K ((W.mergeAdjacentAt k heq).component p).carrier) =
      ∑ i ∈ Finset.Iio j.succ,
        finrank K (W.component i).carrier := by
  let newRank : Fin t → Nat :=
    fun p ↦ finrank K ((W.mergeAdjacentAt k heq).component p).carrier
  let oldRank : Fin (t + 1) → Nat :=
    fun i ↦ finrank K (W.component i).carrier
  have htotal : (∑ p, newRank p) = ∑ i, oldRank i := by
    exact W.sum_componentRank_mergeAdjacentAt k heq
  have hcurrent : newRank j = oldRank j.succ := by
    dsimp only [newRank, oldRank]
    rw [W.mergeAdjacentAt_component_of_ne k heq j (Fin.ne_of_gt hkj)]
    rw [Fin.succAbove_of_le_castSucc]
    exact Fin.succ_le_castSucc_iff.mpr hkj
  have hsuffix : (∑ p ∈ Finset.Ioi j, newRank p) =
      ∑ i ∈ Finset.Ioi j.succ, oldRank i := by
    rw [Fin.sum_Ioi_succ]
    apply Finset.sum_congr rfl
    intro p hp
    have hjp : j < p := Finset.mem_Ioi.mp hp
    have hkp : k < p := hkj.trans hjp
    dsimp only [newRank, oldRank]
    rw [W.mergeAdjacentAt_component_of_ne k heq p (Fin.ne_of_gt hkp)]
    rw [Fin.succAbove_of_le_castSucc]
    exact Fin.succ_le_castSucc_iff.mpr hkp
  have hnewSplit :=
    JordanProfileMergeIndexing.sum_univ_eq_sum_Iio_add_self_add_sum_Ioi
      newRank j
  have holdSplit :=
    JordanProfileMergeIndexing.sum_univ_eq_sum_Iio_add_self_add_sum_Ioi
      oldRank j.succ
  change (∑ p ∈ Finset.Iio j, newRank p) =
    ∑ i ∈ Finset.Iio j.succ, oldRank i
  omega

/-- The prefix before the removed second position consists of the unchanged
prefix before the retained position followed by the first old component. -/
theorem sum_componentRank_Iio_succ {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    (∑ j ∈ Finset.Iio k,
        finrank K ((W.mergeAdjacentAt k heq).component j).carrier) +
        finrank K (W.component k.castSucc).carrier =
      ∑ i ∈ Finset.Iio k.succ, finrank K (W.component i).carrier := by
  have hprefix := W.sum_componentRank_Iio_mergeAdjacentAt_self k heq
  have hIio : Finset.Iio k.succ = Finset.Iic k.castSucc := by
    ext i
    simp only [Finset.mem_Iio, Finset.mem_Iic]
    change i.val < k.val + 1 ↔ i.val ≤ k.val
    exact Nat.lt_succ_iff
  rw [hIio, Finset.Iic_eq_cons_Iio, Finset.sum_cons]
  omega

/-- The canonical order isomorphism that splits the retained merged fiber
back into its two original adjacent fibers. -/
noncomputable def mergeIndexOrderIso {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    Lex (Σ j : Fin t,
      Fin (finrank K ((W.mergeAdjacentAt k heq).component j).carrier)) ≃o
      Lex (Σ i : Fin (t + 1), Fin (finrank K (W.component i).carrier)) :=
  (JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin
      (fun j ↦ finrank K ((W.mergeAdjacentAt k heq).component j).carrier)).symm |>.trans
    ((Fin.castOrderIso (W.sum_componentRank_mergeAdjacentAt k heq)).trans
      (JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin
        (fun i ↦ finrank K (W.component i).carrier)))

/-- The unwrapped equivalence underlying `mergeIndexOrderIso`. -/
noncomputable def mergeIndexEquiv {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    (Σ j : Fin t,
      Fin (finrank K ((W.mergeAdjacentAt k heq).component j).carrier)) ≃
      Σ i : Fin (t + 1), Fin (finrank K (W.component i).carrier) :=
  (toLex :
      (Σ j : Fin t,
        Fin (finrank K ((W.mergeAdjacentAt k heq).component j).carrier)) ≃ _).trans
    ((W.mergeIndexOrderIso k heq).toEquiv.trans toLex.symm)

@[simp]
theorem toLex_mergeIndexEquiv {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (z : Σ j : Fin t,
      Fin (finrank K ((W.mergeAdjacentAt k heq).component j).carrier)) :
    toLex (W.mergeIndexEquiv k heq z) =
      W.mergeIndexOrderIso k heq (toLex z) := by
  rfl

/-- The initial segment of the merged fiber maps to the first old fiber. -/
theorem mergeIndexOrderIso_left {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (j : Fin (finrank K (W.component k.castSucc).carrier)) :
    W.mergeIndexOrderIso k heq
        (toLex ⟨k, ⟨j.val, by
          rw [W.mergeAdjacentAt_componentRank_self k heq]
          omega⟩⟩) =
      toLex ⟨k.castSucc, j⟩ := by
  let newRank : Fin t → Nat :=
    fun h ↦ finrank K ((W.mergeAdjacentAt k heq).component h).carrier
  let oldRank : Fin (t + 1) → Nat :=
    fun h ↦ finrank K (W.component h).carrier
  let ell : Fin (newRank k) := ⟨j.val, by
    dsimp only [newRank]
    rw [W.mergeAdjacentAt_componentRank_self k heq]
    omega⟩
  let eNew := JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin newRank
  let eOld := JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin oldRank
  change eOld
      ((Fin.castOrderIso (W.sum_componentRank_mergeAdjacentAt k heq))
        (eNew.symm (toLex ⟨k, ell⟩))) =
    toLex ⟨k.castSucc, j⟩
  apply eOld.symm.injective
  rw [eOld.symm_apply_apply]
  apply Fin.ext
  change (eNew.symm (toLex ⟨k, ell⟩)).val =
    (eOld.symm (toLex ⟨k.castSucc, j⟩)).val
  rw [JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin_symm_val,
    JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin_symm_val]
  dsimp only [newRank, oldRank, ell, Fin.val_mk]
  rw [W.sum_componentRank_Iio_mergeAdjacentAt_self k heq]

/-- The final segment of the merged fiber maps to the second old fiber. -/
theorem mergeIndexOrderIso_right {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (j : Fin (finrank K (W.component k.succ).carrier)) :
    W.mergeIndexOrderIso k heq
        (toLex ⟨k, ⟨finrank K (W.component k.castSucc).carrier + j.val, by
          rw [W.mergeAdjacentAt_componentRank_self k heq]
          omega⟩⟩) =
      toLex ⟨k.succ, j⟩ := by
  let newRank : Fin t → Nat :=
    fun h ↦ finrank K ((W.mergeAdjacentAt k heq).component h).carrier
  let oldRank : Fin (t + 1) → Nat :=
    fun h ↦ finrank K (W.component h).carrier
  let ell : Fin (newRank k) :=
    ⟨finrank K (W.component k.castSucc).carrier + j.val, by
      dsimp only [newRank]
      rw [W.mergeAdjacentAt_componentRank_self k heq]
      omega⟩
  let eNew := JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin newRank
  let eOld := JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin oldRank
  change eOld
      ((Fin.castOrderIso (W.sum_componentRank_mergeAdjacentAt k heq))
        (eNew.symm (toLex ⟨k, ell⟩))) =
    toLex ⟨k.succ, j⟩
  apply eOld.symm.injective
  rw [eOld.symm_apply_apply]
  apply Fin.ext
  change (eNew.symm (toLex ⟨k, ell⟩)).val =
    (eOld.symm (toLex ⟨k.succ, j⟩)).val
  rw [JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin_symm_val,
    JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin_symm_val]
  dsimp only [newRank, oldRank, ell, Fin.val_mk]
  have hs := W.sum_componentRank_Iio_succ k heq
  omega

/-- A nonmerged component before the retained position keeps its numerical
component index after embedding by `Fin.castSucc`. -/
theorem mergeIndexOrderIso_of_lt {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (p : Fin t) (hpk : p < k)
    (j : Fin (finrank K ((W.mergeAdjacentAt k heq).component p).carrier)) :
    W.mergeIndexOrderIso k heq (toLex ⟨p, j⟩) =
      toLex ⟨p.castSucc, ⟨j.val, by
        have hrank :
            finrank K ((W.mergeAdjacentAt k heq).component p).carrier =
              finrank K (W.component p.castSucc).carrier := by
          rw [W.mergeAdjacentAt_component_of_ne k heq p (Fin.ne_of_lt hpk)]
          rw [Fin.succAbove_of_castSucc_lt]
          exact Fin.castSucc_lt_succ_iff.mpr hpk.le
        simpa only [hrank] using j.isLt⟩⟩ := by
  let newRank : Fin t → Nat :=
    fun h ↦ finrank K ((W.mergeAdjacentAt k heq).component h).carrier
  let oldRank : Fin (t + 1) → Nat :=
    fun h ↦ finrank K (W.component h).carrier
  let ell : Fin (oldRank p.castSucc) := ⟨j.val, by
    have hrank :
        finrank K ((W.mergeAdjacentAt k heq).component p).carrier =
          finrank K (W.component p.castSucc).carrier := by
      rw [W.mergeAdjacentAt_component_of_ne k heq p (Fin.ne_of_lt hpk)]
      rw [Fin.succAbove_of_castSucc_lt]
      exact Fin.castSucc_lt_succ_iff.mpr hpk.le
    simpa only [oldRank, hrank] using j.isLt⟩
  let eNew := JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin newRank
  let eOld := JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin oldRank
  change eOld
      ((Fin.castOrderIso (W.sum_componentRank_mergeAdjacentAt k heq))
        (eNew.symm (toLex ⟨p, j⟩))) =
    toLex ⟨p.castSucc, ell⟩
  apply eOld.symm.injective
  rw [eOld.symm_apply_apply]
  apply Fin.ext
  change (eNew.symm (toLex ⟨p, j⟩)).val =
    (eOld.symm (toLex ⟨p.castSucc, ell⟩)).val
  rw [JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin_symm_val,
    JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin_symm_val]
  dsimp only [newRank, oldRank, ell, Fin.val_mk]
  rw [W.sum_componentRank_Iio_mergeAdjacentAt_of_lt k heq p hpk]

/-- A nonmerged component after the retained position is shifted by one in
the original family. -/
theorem mergeIndexOrderIso_of_gt {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (p : Fin t) (hkp : k < p)
    (j : Fin (finrank K ((W.mergeAdjacentAt k heq).component p).carrier)) :
    W.mergeIndexOrderIso k heq (toLex ⟨p, j⟩) =
      toLex ⟨p.succ, ⟨j.val, by
        have hrank :
            finrank K ((W.mergeAdjacentAt k heq).component p).carrier =
              finrank K (W.component p.succ).carrier := by
          rw [W.mergeAdjacentAt_component_of_ne k heq p (Fin.ne_of_gt hkp)]
          rw [Fin.succAbove_of_le_castSucc]
          exact Fin.succ_le_castSucc_iff.mpr hkp
        simpa only [hrank] using j.isLt⟩⟩ := by
  let newRank : Fin t → Nat :=
    fun h ↦ finrank K ((W.mergeAdjacentAt k heq).component h).carrier
  let oldRank : Fin (t + 1) → Nat :=
    fun h ↦ finrank K (W.component h).carrier
  let ell : Fin (oldRank p.succ) := ⟨j.val, by
    have hrank :
        finrank K ((W.mergeAdjacentAt k heq).component p).carrier =
          finrank K (W.component p.succ).carrier := by
      rw [W.mergeAdjacentAt_component_of_ne k heq p (Fin.ne_of_gt hkp)]
      rw [Fin.succAbove_of_le_castSucc]
      exact Fin.succ_le_castSucc_iff.mpr hkp
    simpa only [oldRank, hrank] using j.isLt⟩
  let eNew := JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin newRank
  let eOld := JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin oldRank
  change eOld
      ((Fin.castOrderIso (W.sum_componentRank_mergeAdjacentAt k heq))
        (eNew.symm (toLex ⟨p, j⟩))) =
    toLex ⟨p.succ, ell⟩
  apply eOld.symm.injective
  rw [eOld.symm_apply_apply]
  apply Fin.ext
  change (eNew.symm (toLex ⟨p, j⟩)).val =
    (eOld.symm (toLex ⟨p.succ, ell⟩)).val
  rw [JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin_symm_val,
    JordanProfileMergeIndexing.lexSigmaRankOrderIsoFin_symm_val]
  dsimp only [newRank, oldRank, ell, Fin.val_mk]
  rw [W.sum_componentRank_Iio_mergeAdjacentAt_of_gt k heq p hkp]

/-- Unwrapped form of `mergeIndexOrderIso_left`. -/
theorem mergeIndexEquiv_left {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (j : Fin (finrank K (W.component k.castSucc).carrier)) :
    W.mergeIndexEquiv k heq
        ⟨k, ⟨j.val, by
          rw [W.mergeAdjacentAt_componentRank_self k heq]
          omega⟩⟩ =
      ⟨k.castSucc, j⟩ := by
  apply toLex_inj.mp
  rw [W.toLex_mergeIndexEquiv]
  exact W.mergeIndexOrderIso_left k heq j

/-- Unwrapped form of `mergeIndexOrderIso_right`. -/
theorem mergeIndexEquiv_right {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (j : Fin (finrank K (W.component k.succ).carrier)) :
    W.mergeIndexEquiv k heq
        ⟨k, ⟨finrank K (W.component k.castSucc).carrier + j.val, by
          rw [W.mergeAdjacentAt_componentRank_self k heq]
          omega⟩⟩ =
      ⟨k.succ, j⟩ := by
  apply toLex_inj.mp
  rw [W.toLex_mergeIndexEquiv]
  exact W.mergeIndexOrderIso_right k heq j

/-- Unwrapped form for a component before the merge. -/
theorem mergeIndexEquiv_of_lt {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (p : Fin t) (hpk : p < k)
    (j : Fin (finrank K ((W.mergeAdjacentAt k heq).component p).carrier)) :
    W.mergeIndexEquiv k heq ⟨p, j⟩ =
      ⟨p.castSucc, ⟨j.val, by
        have hrank :
            finrank K ((W.mergeAdjacentAt k heq).component p).carrier =
              finrank K (W.component p.castSucc).carrier := by
          rw [W.mergeAdjacentAt_component_of_ne k heq p (Fin.ne_of_lt hpk)]
          rw [Fin.succAbove_of_castSucc_lt]
          exact Fin.castSucc_lt_succ_iff.mpr hpk.le
        simpa only [hrank] using j.isLt⟩⟩ := by
  apply toLex_inj.mp
  rw [W.toLex_mergeIndexEquiv]
  exact W.mergeIndexOrderIso_of_lt k heq p hpk j

/-- Unwrapped form for a component after the merge. -/
theorem mergeIndexEquiv_of_gt {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (p : Fin t) (hkp : k < p)
    (j : Fin (finrank K ((W.mergeAdjacentAt k heq).component p).carrier)) :
    W.mergeIndexEquiv k heq ⟨p, j⟩ =
      ⟨p.succ, ⟨j.val, by
        have hrank :
            finrank K ((W.mergeAdjacentAt k heq).component p).carrier =
              finrank K (W.component p.succ).carrier := by
          rw [W.mergeAdjacentAt_component_of_ne k heq p (Fin.ne_of_gt hkp)]
          rw [Fin.succAbove_of_le_castSucc]
          exact Fin.succ_le_castSucc_iff.mpr hkp
        simpa only [hrank] using j.isLt⟩⟩ := by
  apply toLex_inj.mp
  rw [W.toLex_mergeIndexEquiv]
  exact W.mergeIndexOrderIso_of_gt k heq p hkp j

end Lattice.WeakJordanDecomposition

namespace BONG

/-- The local profile prescribed by a weak Jordan family. -/
noncomputable def weakJordanExpectedOrder {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L t) (k : Fin t)
    (i : Fin (finrank K (W.component k).carrier)) : Int :=
  JordanProfileOrder.localOrder
    (ordUnit K (W.scaleGenerator k))
    (W.effectiveNormOrderAt k (ordUnit K (W.scaleGenerator k))) i.val

/-- Splitting an amalgamated equal-scale component recovers exactly the weak
profile of the two original components. -/
theorem weakJordanExpectedOrder_mergeIndexEquiv {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hstrict : StrictMono (fun i ↦
      ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator i)))
    (z : Σ p : Fin t,
      Fin (finrank K ((W.mergeAdjacentAt k heq).component p).carrier)) :
    jordanExpectedOrder ((W.mergeAdjacentAt k heq).toJordan hstrict) z.1 z.2 =
      weakJordanExpectedOrder W (W.mergeIndexEquiv k heq z).1
        (W.mergeIndexEquiv k heq z).2 := by
  rcases z with ⟨p, j⟩
  rcases lt_trichotomy p k with hpk | hpkEq | hkp
  · have hmap := W.mergeIndexEquiv_of_lt k heq p hpk j
    rw [hmap]
    simp only [weakJordanExpectedOrder]
    rw [W.jordanExpectedOrder_mergeAdjacentAt_of_ne k heq hstrict p]
    rw [Fin.succAbove_of_castSucc_lt]
    exact Fin.castSucc_lt_succ_iff.mpr hpk.le
  · subst p
    by_cases hj : j.val < finrank K (W.component k.castSucc).carrier
    · let left : Fin (finrank K (W.component k.castSucc).carrier) := ⟨j.val, hj⟩
      let mergedLeft : Fin
          (finrank K ((W.mergeAdjacentAt k heq).component k).carrier) :=
        ⟨left.val, by
          rw [W.mergeAdjacentAt_componentRank_self k heq]
          omega⟩
      have hjEq : j = mergedLeft := Fin.ext rfl
      have hmap : W.mergeIndexEquiv k heq ⟨k, mergedLeft⟩ =
          ⟨k.castSucc, left⟩ := by
        simpa only [mergedLeft, left, Fin.val_mk] using
          W.mergeIndexEquiv_left k heq left
      rw [hjEq, hmap]
      change jordanExpectedOrder ((W.mergeAdjacentAt k heq).toJordan hstrict)
          k mergedLeft =
        JordanProfileOrder.localOrder
          (ordUnit K (W.scaleGenerator k.castSucc))
          (W.effectiveNormOrderAt k.castSucc
            (ordUnit K (W.scaleGenerator k.castSucc))) left.val
      let canonicalLeft : Fin
          (finrank K ((W.mergeAdjacentAt k heq).component k).carrier) :=
        ⟨left.val, by
          rw [W.mergeAdjacentAt_componentRank_self k heq]
          omega⟩
      have hcoord : mergedLeft = canonicalLeft := Fin.ext rfl
      rw [hcoord]
      exact W.jordanExpectedOrder_mergeAdjacentAt_left
        k heq hstrict k.castSucc left
    · have hjBound :
          j.val - finrank K (W.component k.castSucc).carrier <
            finrank K (W.component k.succ).carrier := by
        have hrank := W.mergeAdjacentAt_componentRank_self k heq
        have hbound : j.val <
            finrank K (W.component k.castSucc).carrier +
              finrank K (W.component k.succ).carrier := by
          simpa only [hrank] using j.isLt
        omega
      let right : Fin (finrank K (W.component k.succ).carrier) :=
        ⟨j.val - finrank K (W.component k.castSucc).carrier, hjBound⟩
      let mergedRight : Fin
          (finrank K ((W.mergeAdjacentAt k heq).component k).carrier) :=
        ⟨finrank K (W.component k.castSucc).carrier + right.val, by
          rw [W.mergeAdjacentAt_componentRank_self k heq]
          omega⟩
      have hjEq : j = mergedRight := by
        apply Fin.ext
        dsimp only [mergedRight, right, Fin.val_mk]
        omega
      have hmap : W.mergeIndexEquiv k heq ⟨k, mergedRight⟩ =
          ⟨k.succ, right⟩ := by
        simpa only [mergedRight, right, Fin.val_mk] using
          W.mergeIndexEquiv_right k heq right
      rw [hjEq, hmap]
      change jordanExpectedOrder ((W.mergeAdjacentAt k heq).toJordan hstrict)
          k mergedRight =
        JordanProfileOrder.localOrder
          (ordUnit K (W.scaleGenerator k.succ))
          (W.effectiveNormOrderAt k.succ
            (ordUnit K (W.scaleGenerator k.succ))) right.val
      let canonicalRight : Fin
          (finrank K ((W.mergeAdjacentAt k heq).component k).carrier) :=
        ⟨finrank K (W.component k.castSucc).carrier + right.val, by
          rw [W.mergeAdjacentAt_componentRank_self k heq]
          omega⟩
      have hcoord : mergedRight = canonicalRight := Fin.ext rfl
      rw [hcoord]
      exact hW.jordanExpectedOrder_mergeAdjacentAt_right
        W k heq hstrict k.succ right
  · have hmap := W.mergeIndexEquiv_of_gt k heq p hkp j
    rw [hmap]
    simp only [weakJordanExpectedOrder]
    rw [W.jordanExpectedOrder_mergeAdjacentAt_of_ne k heq hstrict p]
    rw [Fin.succAbove_of_le_castSucc]
    exact Fin.succ_le_castSucc_iff.mpr hkp

/-- A good BONG profile indexed by a weak Jordan family.  Unlike
`JordanOrderProfileWitness`, this structure permits adjacent equal-scale
components and records their unamalgamated lexicographic profile. -/
structure WeakJordanOrderProfileWitness
    (b : BONG V q L n) {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L t) where
  indexEquiv : Fin n ≃
    Σ k : Fin t, Fin (finrank K (W.component k).carrier)
  order_iff : ∀ i j : Fin n,
    i < j ↔ toLex (indexEquiv i) < toLex (indexEquiv j)
  order_eq : ∀ i : Fin n,
    b.order i = weakJordanExpectedOrder W (indexEquiv i).1 (indexEquiv i).2

namespace WeakJordanOrderProfileWitness

/-- A strict weak Jordan family is already a valid weak-family profile. -/
noncomputable def ofStrict {b : BONG V q L n} {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L t)
    (hstrict : StrictMono (fun i ↦
      ordUnit K (W.scaleGenerator i)))
    (w : JordanOrderProfileWitness b (W.toJordan hstrict)) :
    WeakJordanOrderProfileWitness b W where
  indexEquiv := w.indexEquiv
  order_iff := by
    intro i j
    exact (w.order_iff i j).trans
      (JordanOrderProfileWitness.componentIndexBefore_iff_lex_lt
        (W.toJordan hstrict).toOrthogonalDecomposition
        (w.indexEquiv i) (w.indexEquiv j))
  order_eq := by
    intro i
    exact (w.order_eq i).trans <|
      W.jordanExpectedOrder_toJordan hstrict
        (w.indexEquiv i).1 (w.indexEquiv i).2

/-- A profile witness for the strict amalgamation canonically splits back to
the original weak equal-scale family. -/
noncomputable def ofMerge {b : BONG V q L n} {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hstrict : StrictMono (fun i ↦
      ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator i)))
    (w : JordanOrderProfileWitness b
      ((W.mergeAdjacentAt k heq).toJordan hstrict)) :
    WeakJordanOrderProfileWitness b W where
  indexEquiv := w.indexEquiv.trans (W.mergeIndexEquiv k heq)
  order_iff := by
    intro i j
    change i < j ↔
      toLex (W.mergeIndexEquiv k heq (w.indexEquiv i)) <
        toLex (W.mergeIndexEquiv k heq (w.indexEquiv j))
    rw [W.toLex_mergeIndexEquiv, W.toLex_mergeIndexEquiv,
      (W.mergeIndexOrderIso k heq).lt_iff_lt]
    exact (w.order_iff i j).trans
      (JordanOrderProfileWitness.componentIndexBefore_iff_lex_lt
        ((W.mergeAdjacentAt k heq).toJordan hstrict).toOrthogonalDecomposition
        (w.indexEquiv i) (w.indexEquiv j))
  order_eq := by
    intro i
    exact (w.order_eq i).trans <|
      weakJordanExpectedOrder_mergeIndexEquiv W hW k heq hstrict
        (w.indexEquiv i)

/-- A weak profile witness also determines the unique increasing index
enumeration. -/
noncomputable def indexOrderIso {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W) :
    Fin n ≃o Lex (Σ k : Fin t, Fin (finrank K (W.component k).carrier)) where
  toFun i := toLex (w.indexEquiv i)
  invFun z := w.indexEquiv.symm (ofLex z)
  left_inv i := by
    change w.indexEquiv.symm (w.indexEquiv i) = i
    exact w.indexEquiv.symm_apply_apply i
  right_inv z := by
    change toLex (w.indexEquiv (w.indexEquiv.symm (ofLex z))) = z
    rw [w.indexEquiv.apply_symm_apply]
    exact toLex_ofLex z
  map_rel_iff' := by
    intro i j
    change toLex (w.indexEquiv i) ≤ toLex (w.indexEquiv j) ↔ i ≤ j
    constructor
    · intro hij
      apply le_of_not_gt
      intro hji
      exact (not_lt_of_ge hij) ((w.order_iff j i).mp hji)
    · intro hij
      apply le_of_not_gt
      intro hji
      exact (not_lt_of_ge hij) ((w.order_iff j i).mpr hji)

/-- Weak profile witnesses whose component ranks agree pointwise select the
same component and the same numerical local coordinate at every global
index. -/
theorem indexEquiv_coordinates_eq_of_componentRank_eq
    {M : Lattice K V} {b : BONG V q L n} {c : BONG V q M n}
    {t : Nat} {W : Lattice.WeakJordanDecomposition q L t}
    {H : Lattice.WeakJordanDecomposition q M t}
    (x : WeakJordanOrderProfileWitness b W)
    (y : WeakJordanOrderProfileWitness c H)
    (hRank : (fun k ↦ finrank K (W.component k).carrier) =
      fun k ↦ finrank K (H.component k).carrier)
    (i : Fin n) :
    (x.indexEquiv i).1 = (y.indexEquiv i).1 ∧
      (x.indexEquiv i).2.val = (y.indexEquiv i).2.val := by
  let E := JordanProfileIndexing.lexSigmaRankOrderIso
    (fun k ↦ finrank K (W.component k).carrier)
    (fun k ↦ finrank K (H.component k).carrier) hRank
  have hIso : x.indexOrderIso.trans E = y.indexOrderIso :=
    Subsingleton.elim _ _
  have happ := congrArg (fun e ↦ e i) hIso
  have hfirst := congrArg (fun z ↦ (ofLex z).1) happ
  have hsecond := congrArg (fun z ↦ (ofLex z).2.val) happ
  exact ⟨by simpa [E, indexOrderIso] using hfirst,
    by simpa [E, indexOrderIso] using hsecond⟩

/-- The numerical global index is the prefix-rank offset plus its local
coordinate in the weak component family. -/
theorem index_val_eq_componentStart_add_local
    {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W) (i : Fin n) :
    i.val =
      (∑ k ∈ Finset.Iio (w.indexEquiv i).1,
        finrank K (W.component k).carrier) + (w.indexEquiv i).2.val := by
  calc
    i.val = Fintype.card {x : Lex (Σ k : Fin t,
        Fin (finrank K (W.component k).carrier)) //
        x < w.indexOrderIso i} :=
      JordanProfileIndexing.orderIso_fin_val_eq_card_Iio w.indexOrderIso i
    _ = _ := by
      change Fintype.card {x : Lex (Σ k : Fin t,
          Fin (finrank K (W.component k).carrier)) //
          x < toLex (w.indexEquiv i)} = _
      exact JordanProfileIndexing.lexSigmaIio_card
        (fun k ↦ finrank K (W.component k).carrier)
        (w.indexEquiv i).1 (w.indexEquiv i).2

/-- The inverse index map has the exact prefix-rank value. -/
theorem inverse_index_val {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W) (k : Fin t)
    (j : Fin (finrank K (W.component k).carrier)) :
    (w.indexEquiv.symm ⟨k, j⟩).val =
      (∑ h ∈ Finset.Iio k, finrank K (W.component h).carrier) + j.val := by
  have h := w.index_val_eq_componentStart_add_local
    (w.indexEquiv.symm ⟨k, j⟩)
  rw [w.indexEquiv.apply_symm_apply] at h
  exact h

/-- Evaluate the BONG order at a specified weak component coordinate. -/
theorem order_inverse_indexEquiv {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W) (k : Fin t)
    (j : Fin (finrank K (W.component k).carrier)) :
    b.order (w.indexEquiv.symm ⟨k, j⟩) = weakJordanExpectedOrder W k j := by
  have h := w.order_eq (w.indexEquiv.symm ⟨k, j⟩)
  rw [w.indexEquiv.apply_symm_apply] at h
  exact h

/-- Localized coordinate agreement for two weak profiles follows from equal
prefix ranks and equal current-component ranks. -/
theorem indexEquiv_coordinates_eq_of_prefix_and_rank_eq
    {M : Lattice K V} {b : BONG V q L n} {c : BONG V q M n}
    {t : Nat} {W : Lattice.WeakJordanDecomposition q L t}
    {H : Lattice.WeakJordanDecomposition q M t}
    (x : WeakJordanOrderProfileWitness b W)
    (y : WeakJordanOrderProfileWitness c H) (i : Fin n)
    (hPrefix :
      (∑ h ∈ Finset.Iio (x.indexEquiv i).1,
          finrank K (W.component h).carrier) =
        ∑ h ∈ Finset.Iio (x.indexEquiv i).1,
          finrank K (H.component h).carrier)
    (hRank : finrank K (W.component (x.indexEquiv i).1).carrier =
      finrank K (H.component (x.indexEquiv i).1).carrier) :
    (x.indexEquiv i).1 = (y.indexEquiv i).1 ∧
      (x.indexEquiv i).2.val = (y.indexEquiv i).2.val := by
  let j : Fin (finrank K (H.component (x.indexEquiv i).1).carrier) :=
    ⟨(x.indexEquiv i).2.val, by
      rw [← hRank]
      exact (x.indexEquiv i).2.isLt⟩
  let z : Fin n := y.indexEquiv.symm ⟨(x.indexEquiv i).1, j⟩
  have hzVal : z.val = i.val := by
    calc
      z.val =
          (∑ h ∈ Finset.Iio (x.indexEquiv i).1,
            finrank K (H.component h).carrier) + j.val := by
        exact y.inverse_index_val (x.indexEquiv i).1 j
      _ = (∑ h ∈ Finset.Iio (x.indexEquiv i).1,
            finrank K (W.component h).carrier) +
          (x.indexEquiv i).2.val := by rw [← hPrefix]
      _ = i.val := (x.index_val_eq_componentStart_add_local i).symm
  have hz : z = i := Fin.ext hzVal
  have hy : y.indexEquiv i = ⟨(x.indexEquiv i).1, j⟩ := by
    calc
      y.indexEquiv i = y.indexEquiv z := congrArg y.indexEquiv hz.symm
      _ = ⟨(x.indexEquiv i).1, j⟩ :=
        y.indexEquiv.apply_symm_apply _
  exact ⟨(congrArg Sigma.fst hy).symm,
    (congrArg (fun a ↦ a.2.val) hy).symm⟩

/-- Consecutive local coordinates in a weak component are consecutive global
coordinates. -/
theorem inverse_index_val_local_succ
    {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W) (k : Fin t)
    (j : Fin (finrank K (W.component k).carrier))
    (hnext : j.val + 1 < finrank K (W.component k).carrier) :
    (w.indexEquiv.symm ⟨k, ⟨j.val + 1, hnext⟩⟩).val =
      (w.indexEquiv.symm ⟨k, j⟩).val + 1 := by
  rw [w.inverse_index_val, w.inverse_index_val]
  dsimp only [Fin.val_mk]
  omega

/-- If a local successor exists, the next numerical global coordinate is
exactly that successor in the same weak Jordan component. -/
theorem indexEquiv_global_succ_eq_local_succ
    {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W)
    (I J : Fin n) (hsucc : J.val = I.val + 1)
    (hlocal : (w.indexEquiv I).2.val + 1 <
      finrank K (W.component (w.indexEquiv I).1).carrier) :
    w.indexEquiv J =
      ⟨(w.indexEquiv I).1,
        ⟨(w.indexEquiv I).2.val + 1, hlocal⟩⟩ := by
  let nextLocal : Fin
      (finrank K (W.component (w.indexEquiv I).1).carrier) :=
    ⟨(w.indexEquiv I).2.val + 1, hlocal⟩
  let nextGlobal := w.indexEquiv.symm
    ⟨(w.indexEquiv I).1, nextLocal⟩
  have hnextVal := w.inverse_index_val_local_succ
    (w.indexEquiv I).1 (w.indexEquiv I).2 hlocal
  have hcurrent : w.indexEquiv.symm (w.indexEquiv I) = I :=
    w.indexEquiv.symm_apply_apply I
  have hnextEq : nextGlobal = J := by
    apply Fin.ext
    dsimp only [nextGlobal, nextLocal, Fin.val_mk]
    rw [hnextVal, hcurrent, hsucc]
  calc
    w.indexEquiv J = w.indexEquiv nextGlobal := congrArg w.indexEquiv hnextEq.symm
    _ = ⟨(w.indexEquiv I).1, nextLocal⟩ := by
      dsimp only [nextGlobal]
      exact w.indexEquiv.apply_symm_apply _
    _ = ⟨(w.indexEquiv I).1,
        ⟨(w.indexEquiv I).2.val + 1, hlocal⟩⟩ := rfl

/-- A local successor in a weak Jordan component is also a valid next global
coordinate.  This is the bound counterpart of
`inverse_index_val_local_succ`. -/
theorem global_succ_lt_of_local_succ
    {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W) (i : Fin n)
    (hlocal : (w.indexEquiv i).2.val + 1 <
      finrank K (W.component (w.indexEquiv i).1).carrier) :
    i.val + 1 < n := by
  have hval := w.inverse_index_val_local_succ
    (w.indexEquiv i).1 (w.indexEquiv i).2 hlocal
  have hcurrent : w.indexEquiv.symm (w.indexEquiv i) = i :=
    w.indexEquiv.symm_apply_apply i
  have hnextBound :=
    (w.indexEquiv.symm
      ⟨(w.indexEquiv i).1,
        ⟨(w.indexEquiv i).2.val + 1, hlocal⟩⟩).isLt
  have hval' :
      (w.indexEquiv.symm
        ⟨(w.indexEquiv i).1,
          ⟨(w.indexEquiv i).2.val + 1, hlocal⟩⟩).val = i.val + 1 := by
    calc
      _ = (w.indexEquiv.symm (w.indexEquiv i)).val + 1 := by
        simpa using hval
      _ = i.val + 1 := by rw [hcurrent]
  exact hval' ▸ hnextBound

/-- The preceding local coordinate is one global position earlier. -/
theorem inverse_index_val_local_pred
    {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W) (k : Fin t)
    (j : Fin (finrank K (W.component k).carrier)) (hpos : 0 < j.val) :
    (w.indexEquiv.symm ⟨k, ⟨j.val - 1, by omega⟩⟩).val + 1 =
      (w.indexEquiv.symm ⟨k, j⟩).val := by
  rw [w.inverse_index_val, w.inverse_index_val]
  dsimp only [Fin.val_mk]
  omega

/-- The last coordinate of one weak component and the first coordinate of
the next are consecutive globally. -/
theorem inverse_index_val_next_component
    {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W)
    (k k' : Fin t) (hk' : k'.val = k.val + 1)
    (j : Fin (finrank K (W.component k).carrier))
    (hlast : j.val + 1 = finrank K (W.component k).carrier)
    (hpos : 0 < finrank K (W.component k').carrier) :
    (w.indexEquiv.symm ⟨k', ⟨0, hpos⟩⟩).val =
      (w.indexEquiv.symm ⟨k, j⟩).val + 1 := by
  classical
  have hset : Finset.Iio k' = insert k (Finset.Iio k) := by
    ext x
    simp only [Finset.mem_Iio, Finset.mem_insert]
    change (x.val < k'.val) ↔ x = k ∨ x.val < k.val
    constructor
    · intro hx
      by_cases hxl : x.val < k.val
      · exact Or.inr hxl
      · left
        apply Fin.ext
        omega
    · rintro (rfl | hx) <;> omega
  rw [w.inverse_index_val, w.inverse_index_val, hset,
    Finset.sum_insert (by simp)]
  dsimp only [Fin.val_mk]
  omega

/-- If consecutive global coordinates arrive at local coordinate zero, then
the first coordinate is the last coordinate of the immediately preceding
weak Jordan component.  The stronger `+ 1` conclusion rules out an apparent
gap between weak components; positive component rank makes every intervening
component contribute a global coordinate. -/
theorem terminal_and_component_succ_eq_of_global_succ_local_zero
    {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W)
    (I J : Fin n) (hsucc : J.val = I.val + 1)
    (hzero : (w.indexEquiv J).2.val = 0) :
    (w.indexEquiv I).1.val + 1 = (w.indexEquiv J).1.val ∧
      (w.indexEquiv I).2.val + 1 =
        finrank K (W.component (w.indexEquiv I).1).carrier := by
  have hIJ : I < J := by
    change I.val < J.val
    omega
  have hlex := (w.order_iff I J).mp hIJ
  change Sigma.Lex (fun i j : Fin t ↦ i < j)
    (fun _ i j ↦ i < j) (w.indexEquiv I) (w.indexEquiv J) at hlex
  rw [Sigma.lex_iff] at hlex
  have hcomponent : (w.indexEquiv I).1 < (w.indexEquiv J).1 := by
    rcases hlex with hcomponent | ⟨hcomponents, hlocal⟩
    · exact hcomponent
    · have htransport := eqRec_heq
        (φ := fun p ↦ Fin (finrank K (W.component p).carrier))
        hcomponents (w.indexEquiv I).2
      have htransportVal := Fin.val_eq_val_of_heq htransport
      have hlocalCastVal :
          (Eq.recOn (motive := fun p _ ↦
              Fin (finrank K (W.component p).carrier))
            hcomponents (w.indexEquiv I).2).val <
            (w.indexEquiv J).2.val := by
        exact hlocal
      omega
  have hterminal : (w.indexEquiv I).2.val + 1 =
      finrank K (W.component (w.indexEquiv I).1).carrier := by
    by_contra hnot
    have hlocalSucc : (w.indexEquiv I).2.val + 1 <
        finrank K (W.component (w.indexEquiv I).1).carrier := by
      have hbound := (w.indexEquiv I).2.isLt
      omega
    let localSucc : Fin
        (finrank K (W.component (w.indexEquiv I).1).carrier) :=
      ⟨(w.indexEquiv I).2.val + 1, hlocalSucc⟩
    let nextGlobal := w.indexEquiv.symm
      ⟨(w.indexEquiv I).1, localSucc⟩
    have hnextVal := w.inverse_index_val_local_succ
      (w.indexEquiv I).1 (w.indexEquiv I).2 hlocalSucc
    have hcurrent : w.indexEquiv.symm (w.indexEquiv I) = I :=
      w.indexEquiv.symm_apply_apply I
    have hnextEq : nextGlobal = J := by
      apply Fin.ext
      dsimp only [nextGlobal, localSucc, Fin.val_mk]
      rw [hnextVal, hcurrent, hsucc]
    have hcomponentsEq := congrArg (fun z ↦ (w.indexEquiv z).1) hnextEq
    have hnextComponent : (w.indexEquiv nextGlobal).1 =
        (w.indexEquiv I).1 := by
      dsimp only [nextGlobal]
      rw [w.indexEquiv.apply_symm_apply]
    exact hcomponent.ne (hnextComponent.symm.trans hcomponentsEq)
  let nextComponent : Fin t :=
    ⟨(w.indexEquiv I).1.val + 1, by
      have hbound := (w.indexEquiv J).1.isLt
      have hlt := hcomponent
      change (w.indexEquiv I).1.val < (w.indexEquiv J).1.val at hlt
      omega⟩
  let first : Fin (finrank K (W.component nextComponent).carrier) :=
    ⟨0, W.component_finrank_pos nextComponent⟩
  let nextGlobal := w.indexEquiv.symm ⟨nextComponent, first⟩
  have hnextVal := w.inverse_index_val_next_component
    (w.indexEquiv I).1 nextComponent (by rfl) (w.indexEquiv I).2
      hterminal (W.component_finrank_pos nextComponent)
  have hcurrent : w.indexEquiv.symm (w.indexEquiv I) = I :=
    w.indexEquiv.symm_apply_apply I
  have hnextEq : nextGlobal = J := by
    apply Fin.ext
    dsimp only [nextGlobal]
    rw [hnextVal, hcurrent, hsucc]
  have hnextCoordinates : w.indexEquiv nextGlobal =
      ⟨nextComponent, first⟩ := by
    dsimp only [nextGlobal]
    exact w.indexEquiv.apply_symm_apply _
  have hcomponentEq : (w.indexEquiv J).1 = nextComponent := by
    calc
      (w.indexEquiv J).1 = (w.indexEquiv nextGlobal).1 := by rw [hnextEq]
      _ = nextComponent := congrArg Sigma.fst hnextCoordinates
  constructor
  · rw [hcomponentEq]
  · exact hterminal

/-- A terminal weak-profile coordinate with a global successor cannot belong
to the final weak Jordan component. -/
theorem component_succ_lt_of_terminal_with_global_succ
    {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W)
    (I : Fin n)
    (hlast : (w.indexEquiv I).2.val + 1 =
      finrank K (W.component (w.indexEquiv I).1).carrier)
    (hsucc : I.val + 1 < n) :
    (w.indexEquiv I).1.val + 1 < t := by
  let J : Fin n := ⟨I.val + 1, hsucc⟩
  have hIJ : I < J := by
    change I.val < I.val + 1
    omega
  have hlex := (w.order_iff I J).mp hIJ
  change Sigma.Lex (fun i j : Fin t ↦ i < j)
    (fun _ i j ↦ i < j) (w.indexEquiv I) (w.indexEquiv J) at hlex
  rw [Sigma.lex_iff] at hlex
  have hcomponent : (w.indexEquiv I).1 < (w.indexEquiv J).1 := by
    rcases hlex with hcomponent | ⟨hcomponents, hlocal⟩
    · exact hcomponent
    · have htransport := eqRec_heq
        (φ := fun p ↦ Fin (finrank K (W.component p).carrier))
        hcomponents (w.indexEquiv I).2
      have htransportVal := Fin.val_eq_val_of_heq htransport
      have hlocalCastVal :
          (Eq.recOn (motive := fun p _ ↦
              Fin (finrank K (W.component p).carrier))
            hcomponents (w.indexEquiv I).2).val <
            (w.indexEquiv J).2.val := by
        exact hlocal
      have htargetBound := (w.indexEquiv J).2.isLt
      have hrankEq := congrArg
        (fun p ↦ finrank K (W.component p).carrier) hcomponents
      omega
  have htargetBound := (w.indexEquiv J).1.isLt
  change (w.indexEquiv I).1.val < (w.indexEquiv J).1.val at hcomponent
  omega

/-- The global successor of a terminal weak-profile coordinate is the first
coordinate of the immediately following component. -/
theorem indexEquiv_global_succ_of_terminal
    {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W)
    (I J : Fin n) (hsucc : J.val = I.val + 1)
    (hlast : (w.indexEquiv I).2.val + 1 =
      finrank K (W.component (w.indexEquiv I).1).carrier) :
    (w.indexEquiv J).1.val = (w.indexEquiv I).1.val + 1 ∧
      (w.indexEquiv J).2.val = 0 := by
  have hglobal : I.val + 1 < n := by
    rw [← hsucc]
    exact J.isLt
  have hcomponentNext : (w.indexEquiv I).1.val + 1 < t :=
    w.component_succ_lt_of_terminal_with_global_succ I hlast hglobal
  let nextComponent : Fin t :=
    ⟨(w.indexEquiv I).1.val + 1, hcomponentNext⟩
  have hnextRank : 0 < finrank K (W.component nextComponent).carrier :=
    W.component_finrank_pos nextComponent
  let first : Fin (finrank K (W.component nextComponent).carrier) :=
    ⟨0, hnextRank⟩
  let nextGlobal := w.indexEquiv.symm ⟨nextComponent, first⟩
  have hnextVal := w.inverse_index_val_next_component
    (w.indexEquiv I).1 nextComponent (by rfl) (w.indexEquiv I).2 hlast
      hnextRank
  have hcurrent : w.indexEquiv.symm (w.indexEquiv I) = I :=
    w.indexEquiv.symm_apply_apply I
  have hnextEq : nextGlobal = J := by
    apply Fin.ext
    dsimp only [nextGlobal]
    rw [hnextVal, hcurrent, hsucc]
  have hcoordinates : w.indexEquiv J = ⟨nextComponent, first⟩ := by
    rw [← hnextEq]
    dsimp only [nextGlobal]
    exact w.indexEquiv.apply_symm_apply _
  constructor
  · have hcomponent := congrArg (fun z ↦ z.1.val) hcoordinates
    simpa only [nextComponent] using hcomponent
  · have hlocal := congrArg (fun z ↦ z.2.val) hcoordinates
    simpa only [first] using hlocal

/-- A local successor evaluates to the weak profile at the next global
coordinate. -/
theorem order_succ_eq_weakJordanExpectedOrder_of_local_succ
    {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W)
    (i : Fin n) (hglobal : i.val + 1 < n)
    (hlocal : (w.indexEquiv i).2.val + 1 <
      finrank K (W.component (w.indexEquiv i).1).carrier) :
    b.order ⟨i.val + 1, hglobal⟩ =
      weakJordanExpectedOrder W (w.indexEquiv i).1
        ⟨(w.indexEquiv i).2.val + 1, hlocal⟩ := by
  have hval := w.inverse_index_val_local_succ
    (w.indexEquiv i).1 (w.indexEquiv i).2 hlocal
  have hcurrent : w.indexEquiv.symm (w.indexEquiv i) = i :=
    w.indexEquiv.symm_apply_apply i
  have hindex : (⟨i.val + 1, hglobal⟩ : Fin n) =
      w.indexEquiv.symm
        ⟨(w.indexEquiv i).1,
          ⟨(w.indexEquiv i).2.val + 1, hlocal⟩⟩ := by
    apply Fin.ext
    calc
      i.val + 1 = (w.indexEquiv.symm (w.indexEquiv i)).val + 1 := by
        rw [hcurrent]
      _ = (w.indexEquiv.symm
          ⟨(w.indexEquiv i).1,
            ⟨(w.indexEquiv i).2.val + 1, hlocal⟩⟩).val := hval.symm
  rw [hindex]
  exact w.order_inverse_indexEquiv _ _

/-- A local predecessor evaluates to the weak profile at the preceding global
coordinate. -/
theorem order_pred_eq_weakJordanExpectedOrder_of_local_pred
    {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W)
    (i : Fin n) (hpos : 0 < (w.indexEquiv i).2.val) :
    b.order ⟨i.val - 1, by have := i.isLt; omega⟩ =
      weakJordanExpectedOrder W (w.indexEquiv i).1
        ⟨(w.indexEquiv i).2.val - 1, by omega⟩ := by
  have hval := w.inverse_index_val_local_pred
    (w.indexEquiv i).1 (w.indexEquiv i).2 hpos
  have hcurrent : w.indexEquiv.symm (w.indexEquiv i) = i :=
    w.indexEquiv.symm_apply_apply i
  have hindex : (⟨i.val - 1, by have := i.isLt; omega⟩ : Fin n) =
      w.indexEquiv.symm
        ⟨(w.indexEquiv i).1,
          ⟨(w.indexEquiv i).2.val - 1, by omega⟩⟩ := by
    apply Fin.ext
    change i.val - 1 = _
    have hval' :
        (w.indexEquiv.symm
          ⟨(w.indexEquiv i).1,
            ⟨(w.indexEquiv i).2.val - 1, by omega⟩⟩).val + 1 = i.val := by
      calc
        _ = (w.indexEquiv.symm (w.indexEquiv i)).val := by simpa using hval
        _ = i.val := by rw [hcurrent]
    omega
  rw [hindex]
  exact w.order_inverse_indexEquiv _ _

/-- At a weak-component endpoint, the next component starts at the next
global coordinate. -/
theorem order_succ_eq_weakJordanExpectedOrder_of_next_component
    {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W)
    (i : Fin n) (hglobal : i.val + 1 < n)
    (k' : Fin t) (hk' : k'.val = (w.indexEquiv i).1.val + 1)
    (hlast : (w.indexEquiv i).2.val + 1 =
      finrank K (W.component (w.indexEquiv i).1).carrier)
    (hpos : 0 < finrank K (W.component k').carrier) :
    b.order ⟨i.val + 1, hglobal⟩ =
      weakJordanExpectedOrder W k' ⟨0, hpos⟩ := by
  have hval := w.inverse_index_val_next_component
    (w.indexEquiv i).1 k' hk' (w.indexEquiv i).2 hlast hpos
  have hcurrent : w.indexEquiv.symm (w.indexEquiv i) = i :=
    w.indexEquiv.symm_apply_apply i
  have hindex : (⟨i.val + 1, hglobal⟩ : Fin n) =
      w.indexEquiv.symm ⟨k', ⟨0, hpos⟩⟩ := by
    apply Fin.ext
    calc
      i.val + 1 = (w.indexEquiv.symm (w.indexEquiv i)).val + 1 := by
        rw [hcurrent]
      _ = (w.indexEquiv.symm ⟨k', ⟨0, hpos⟩⟩).val := hval.symm
  rw [hindex]
  exact w.order_inverse_indexEquiv _ _

/-- A positive-rank immediately preceding weak component forces a positive
global index. -/
theorem index_val_pos_of_previous_component
    {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W)
    (i : Fin n) (k : Fin t)
    (hk : (w.indexEquiv i).1.val = k.val + 1)
    (hpos : 0 < finrank K (W.component k).carrier) : 0 < i.val := by
  have hindex := w.index_val_eq_componentStart_add_local i
  have hmem : k ∈ Finset.Iio (w.indexEquiv i).1 := by
    simp only [Finset.mem_Iio]
    change k.val < (w.indexEquiv i).1.val
    omega
  have hsumPos : 0 < ∑ j ∈ Finset.Iio (w.indexEquiv i).1,
      finrank K (W.component j).carrier :=
    Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _) ⟨k, hmem, hpos⟩
  omega

/-- At the first coordinate of a weak component, the previous global entry
is the final weak-profile value of the preceding component. -/
theorem order_pred_eq_weakJordanExpectedOrder_of_previous_component
    {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W)
    (i : Fin n) (hglobal : 0 < i.val) (k : Fin t)
    (hk : (w.indexEquiv i).1.val = k.val + 1)
    (hfirst : (w.indexEquiv i).2.val = 0)
    (hpos : 0 < finrank K (W.component k).carrier)
    (hcurrentPos : 0 <
      finrank K (W.component (w.indexEquiv i).1).carrier) :
    b.order ⟨i.val - 1, by omega⟩ =
      weakJordanExpectedOrder W k
        ⟨finrank K (W.component k).carrier - 1, by omega⟩ := by
  let last : Fin (finrank K (W.component k).carrier) :=
    ⟨finrank K (W.component k).carrier - 1, by omega⟩
  have hlast : last.val + 1 = finrank K (W.component k).carrier := by
    simp only [last]
    omega
  have hval := w.inverse_index_val_next_component
    k (w.indexEquiv i).1 hk last hlast hcurrentPos
  have hzeroInverse :
      (w.indexEquiv.symm
        ⟨(w.indexEquiv i).1, ⟨0, hcurrentPos⟩⟩).val =
        (w.indexEquiv.symm (w.indexEquiv i)).val := by
    rw [w.inverse_index_val, w.inverse_index_val]
    simp only [hfirst, add_zero]
  have hcurrent : w.indexEquiv.symm (w.indexEquiv i) = i :=
    w.indexEquiv.symm_apply_apply i
  have hprevVal : (w.indexEquiv.symm ⟨k, last⟩).val + 1 = i.val := by
    calc
      _ = (w.indexEquiv.symm
          ⟨(w.indexEquiv i).1, ⟨0, hcurrentPos⟩⟩).val := hval.symm
      _ = (w.indexEquiv.symm (w.indexEquiv i)).val := hzeroInverse
      _ = i.val := by rw [hcurrent]
  have hindex : (⟨i.val - 1, by omega⟩ : Fin n) =
      w.indexEquiv.symm ⟨k, last⟩ := by
    apply Fin.ext
    change i.val - 1 = (w.indexEquiv.symm ⟨k, last⟩).val
    omega
  rw [hindex]
  exact w.order_inverse_indexEquiv _ _

/-- A global index lies strictly before the end of its weak component. -/
theorem index_val_lt_componentEnd
    {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W) (i : Fin n) :
    i.val <
      (∑ k ∈ Finset.Iio (w.indexEquiv i).1,
        finrank K (W.component k).carrier) +
      finrank K (W.component (w.indexEquiv i).1).carrier := by
  rw [w.index_val_eq_componentStart_add_local i]
  exact Nat.add_lt_add_left (w.indexEquiv i).2.isLt _

/-- The total component rank is the profiled BONG length. -/
theorem sum_componentRank_eq_length {b : BONG V q L n} {t : Nat}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W) :
    (∑ k, finrank K (W.component k).carrier) = n := by
  simpa only [Fintype.card_fin, Fintype.card_sigma] using
    (Fintype.card_congr w.indexEquiv).symm

end WeakJordanOrderProfileWitness

end BONG

end Bong
