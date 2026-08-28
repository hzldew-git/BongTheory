/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.JordanProfileMerge
import Bong.Bong.Beli2009JordanProfileGap

/-!
# Resolving weak Jordan-profile coordinates across an adjacent merge

These lemmas invert the canonical split profile produced by
`WeakJordanOrderProfileWitness.ofMerge`.  They allow later arguments to use
strict Jordan weight formulas while retaining the uniform unamalgamated
coordinates of a weak profile.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.WeakJordanOrderProfileWitness

/-- In the strict case the uniform weak profile and any strict profile have
identical dependent coordinates. -/
theorem indexEquiv_eq_ofStrict
    {n t : Nat} {b : BONG V q L n}
    {W : Lattice.WeakJordanDecomposition q L t}
    (x : WeakJordanOrderProfileWitness b W)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness b (W.toJordan hstrict))
    (i : Fin n) : x.indexEquiv i = P.indexEquiv i := by
  let y := WeakJordanOrderProfileWitness.ofStrict W hstrict P
  have h := x.indexEquiv_coordinates_eq_of_componentRank_eq y rfl i
  apply Sigma.ext
  · exact h.1
  · exact (Fin.heq_ext_iff
      (congrArg (fun p ↦ finrank K (W.component p).carrier) h.1)).2 h.2

/-- Any weak profile has the same split coordinates as the profile obtained
from a specified strict amalgamation. -/
theorem indexEquiv_eq_mergeIndexEquiv
    {n t : Nat} {b : BONG V q L n}
    {W : Lattice.WeakJordanDecomposition q L (t + 1)}
    (x : WeakJordanOrderProfileWitness b W)
    (hW : W.HasImproperEvenRank) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hstrict : StrictMono (fun i ↦
      ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator i)))
    (P : JordanOrderProfileWitness b
      ((W.mergeAdjacentAt k heq).toJordan hstrict))
    (i : Fin n) :
    x.indexEquiv i = W.mergeIndexEquiv k heq (P.indexEquiv i) := by
  let y := WeakJordanOrderProfileWitness.ofMerge W hW k heq hstrict P
  have h := x.indexEquiv_coordinates_eq_of_componentRank_eq y rfl i
  have hxy : x.indexEquiv i = y.indexEquiv i := by
    apply Sigma.ext
    · exact h.1
    · exact (Fin.heq_ext_iff
        (congrArg (fun p ↦ finrank K (W.component p).carrier) h.1)).2 h.2
  exact hxy

/-- A coordinate in the old left member of the equal-scale pair is the
same local coordinate in the merged strict component. -/
theorem strict_coordinates_of_left
    {n t : Nat} {b : BONG V q L n}
    {W : Lattice.WeakJordanDecomposition q L (t + 1)}
    (x : WeakJordanOrderProfileWitness b W)
    (hW : W.HasImproperEvenRank) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hstrict : StrictMono (fun i ↦
      ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator i)))
    (P : JordanOrderProfileWitness b
      ((W.mergeAdjacentAt k heq).toJordan hstrict))
    (i : Fin n) (hleft : (x.indexEquiv i).1 = k.castSucc) :
    (P.indexEquiv i).1 = k ∧
      (P.indexEquiv i).2.val = (x.indexEquiv i).2.val := by
  let oldLocal : Fin (finrank K (W.component k.castSucc).carrier) :=
    ⟨(x.indexEquiv i).2.val, by
      have hlocal := (x.indexEquiv i).2.isLt
      exact (congrArg
        (fun p ↦ finrank K (W.component p).carrier) hleft) ▸ hlocal⟩
  let mergedLocal : Fin
      (finrank K ((W.mergeAdjacentAt k heq).component k).carrier) :=
    ⟨oldLocal.val, by
      rw [W.mergeAdjacentAt_componentRank_self k heq]
      exact Nat.lt_add_right _ oldLocal.isLt⟩
  have hx : x.indexEquiv i = ⟨k.castSucc, oldLocal⟩ := by
    apply Sigma.ext
    · exact hleft
    · exact (Fin.heq_ext_iff
        (congrArg (fun p ↦ finrank K (W.component p).carrier) hleft)).2 rfl
  have hmap : W.mergeIndexEquiv k heq (P.indexEquiv i) =
      ⟨k.castSucc, oldLocal⟩ :=
    (x.indexEquiv_eq_mergeIndexEquiv hW k heq hstrict P i).symm.trans hx
  have hcanonical : W.mergeIndexEquiv k heq ⟨k, mergedLocal⟩ =
      ⟨k.castSucc, oldLocal⟩ := by
    simpa only [mergedLocal, oldLocal, Fin.val_mk] using
      W.mergeIndexEquiv_left k heq oldLocal
  have hstrictCoordinate : P.indexEquiv i = ⟨k, mergedLocal⟩ :=
    (W.mergeIndexEquiv k heq).injective (hmap.trans hcanonical.symm)
  constructor
  · exact congrArg Sigma.fst hstrictCoordinate
  · have hlocal := congrArg (fun z ↦ z.2.val) hstrictCoordinate
    simpa only [mergedLocal, oldLocal, Fin.val_mk] using hlocal

/-- A coordinate in the old right member is shifted by the rank of the old
left member inside the merged strict component. -/
theorem strict_coordinates_of_right
    {n t : Nat} {b : BONG V q L n}
    {W : Lattice.WeakJordanDecomposition q L (t + 1)}
    (x : WeakJordanOrderProfileWitness b W)
    (hW : W.HasImproperEvenRank) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hstrict : StrictMono (fun i ↦
      ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator i)))
    (P : JordanOrderProfileWitness b
      ((W.mergeAdjacentAt k heq).toJordan hstrict))
    (i : Fin n) (hright : (x.indexEquiv i).1 = k.succ) :
    (P.indexEquiv i).1 = k ∧
      (P.indexEquiv i).2.val =
        finrank K (W.component k.castSucc).carrier +
          (x.indexEquiv i).2.val := by
  let oldLocal : Fin (finrank K (W.component k.succ).carrier) :=
    ⟨(x.indexEquiv i).2.val, by
      have hlocal := (x.indexEquiv i).2.isLt
      exact (congrArg
        (fun p ↦ finrank K (W.component p).carrier) hright) ▸ hlocal⟩
  let mergedLocal : Fin
      (finrank K ((W.mergeAdjacentAt k heq).component k).carrier) :=
    ⟨finrank K (W.component k.castSucc).carrier + oldLocal.val, by
      rw [W.mergeAdjacentAt_componentRank_self k heq]
      exact Nat.add_lt_add_left oldLocal.isLt _⟩
  have hx : x.indexEquiv i = ⟨k.succ, oldLocal⟩ := by
    apply Sigma.ext
    · exact hright
    · exact (Fin.heq_ext_iff
        (congrArg (fun p ↦ finrank K (W.component p).carrier) hright)).2 rfl
  have hmap : W.mergeIndexEquiv k heq (P.indexEquiv i) =
      ⟨k.succ, oldLocal⟩ :=
    (x.indexEquiv_eq_mergeIndexEquiv hW k heq hstrict P i).symm.trans hx
  have hcanonical : W.mergeIndexEquiv k heq ⟨k, mergedLocal⟩ =
      ⟨k.succ, oldLocal⟩ := by
    simpa only [mergedLocal, oldLocal, Fin.val_mk] using
      W.mergeIndexEquiv_right k heq oldLocal
  have hstrictCoordinate : P.indexEquiv i = ⟨k, mergedLocal⟩ :=
    (W.mergeIndexEquiv k heq).injective (hmap.trans hcanonical.symm)
  constructor
  · exact congrArg Sigma.fst hstrictCoordinate
  · have hlocal := congrArg (fun z ↦ z.2.val) hstrictCoordinate
    simpa only [mergedLocal, oldLocal, Fin.val_mk] using hlocal

/-- A coordinate strictly before the old left member is unchanged by the
merge, up to the definitional cast from `Fin (t+1)` to `Fin t`. -/
theorem strict_coordinates_of_before
    {n t : Nat} {b : BONG V q L n}
    {W : Lattice.WeakJordanDecomposition q L (t + 1)}
    (x : WeakJordanOrderProfileWitness b W)
    (hW : W.HasImproperEvenRank) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hstrict : StrictMono (fun i ↦
      ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator i)))
    (P : JordanOrderProfileWitness b
      ((W.mergeAdjacentAt k heq).toJordan hstrict))
    (i : Fin n) (hbefore : (x.indexEquiv i).1 < k.castSucc) :
    ∃ p : Fin t, p < k ∧ p.castSucc = (x.indexEquiv i).1 ∧
      (P.indexEquiv i).1 = p ∧
      (P.indexEquiv i).2.val = (x.indexEquiv i).2.val := by
  let p : Fin t := ⟨(x.indexEquiv i).1.val, by
    have hk := k.isLt
    change (x.indexEquiv i).1.val < k.val at hbefore
    omega⟩
  have hp : p < k := by
    change (x.indexEquiv i).1.val < k.val
    exact hbefore
  have hpOld : p.castSucc = (x.indexEquiv i).1 := by
    apply Fin.ext
    rfl
  let mergedLocal : Fin
      (finrank K ((W.mergeAdjacentAt k heq).component p).carrier) :=
    ⟨(x.indexEquiv i).2.val, by
      rw [W.mergeAdjacentAt_component_of_ne k heq p (Fin.ne_of_lt hp)]
      rw [Fin.succAbove_of_castSucc_lt]
      · have hlocal := (x.indexEquiv i).2.isLt
        have hrankEq := congrArg
          (fun z ↦ finrank K (W.component z).carrier) hpOld
        rw [hrankEq]
        exact hlocal
      · exact Fin.castSucc_lt_succ_iff.mpr hp.le⟩
  let oldLocal : Fin (finrank K (W.component p.castSucc).carrier) :=
    ⟨(x.indexEquiv i).2.val, by
      have hlocal := (x.indexEquiv i).2.isLt
      have hrankEq := congrArg
        (fun z ↦ finrank K (W.component z).carrier) hpOld
      rw [hrankEq]
      exact hlocal⟩
  have hx : x.indexEquiv i = ⟨p.castSucc, oldLocal⟩ := by
    apply Sigma.ext
    · exact hpOld.symm
    · exact (Fin.heq_ext_iff
        (congrArg (fun z ↦ finrank K (W.component z).carrier)
          hpOld.symm)).2 rfl
  have hmap : W.mergeIndexEquiv k heq (P.indexEquiv i) =
      ⟨p.castSucc, oldLocal⟩ :=
    (x.indexEquiv_eq_mergeIndexEquiv hW k heq hstrict P i).symm.trans hx
  have hcanonical : W.mergeIndexEquiv k heq ⟨p, mergedLocal⟩ =
      ⟨p.castSucc, oldLocal⟩ := by
    simpa only [mergedLocal, oldLocal, Fin.val_mk] using
      W.mergeIndexEquiv_of_lt k heq p hp mergedLocal
  have hstrictCoordinate : P.indexEquiv i = ⟨p, mergedLocal⟩ :=
    (W.mergeIndexEquiv k heq).injective (hmap.trans hcanonical.symm)
  refine ⟨p, hp, hpOld, congrArg Sigma.fst hstrictCoordinate, ?_⟩
  have hlocal := congrArg (fun z ↦ z.2.val) hstrictCoordinate
  simpa only [mergedLocal, Fin.val_mk] using hlocal

/-- A coordinate strictly after the old right member of an equal-scale pair
is unchanged locally in the merged strict component.  Its strict component
index is the predecessor of the old weak component index. -/
theorem strict_coordinates_of_after
    {n t : Nat} {b : BONG V q L n}
    {W : Lattice.WeakJordanDecomposition q L (t + 1)}
    (x : WeakJordanOrderProfileWitness b W)
    (hW : W.HasImproperEvenRank) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hstrict : StrictMono (fun i ↦
      ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator i)))
    (P : JordanOrderProfileWitness b
      ((W.mergeAdjacentAt k heq).toJordan hstrict))
    (i : Fin n) (hafter : k.succ < (x.indexEquiv i).1) :
    ∃ p : Fin t, k < p ∧ p.succ = (x.indexEquiv i).1 ∧
      (P.indexEquiv i).1 = p ∧
      (P.indexEquiv i).2.val = (x.indexEquiv i).2.val := by
  let p : Fin t := ⟨(x.indexEquiv i).1.val - 1, by
    have hold := (x.indexEquiv i).1.isLt
    omega⟩
  have hkp : k < p := by
    change k.val < (x.indexEquiv i).1.val - 1
    change k.val + 1 < (x.indexEquiv i).1.val at hafter
    omega
  have hpOld : p.succ = (x.indexEquiv i).1 := by
    apply Fin.ext
    change (x.indexEquiv i).1.val - 1 + 1 = (x.indexEquiv i).1.val
    have hpos : 0 < (x.indexEquiv i).1.val := by
      change k.val + 1 < (x.indexEquiv i).1.val at hafter
      omega
    omega
  let mergedLocal : Fin
      (finrank K ((W.mergeAdjacentAt k heq).component p).carrier) :=
    ⟨(x.indexEquiv i).2.val, by
      rw [W.mergeAdjacentAt_component_of_ne k heq p
        (Fin.ne_of_gt hkp)]
      rw [Fin.succAbove_of_le_castSucc]
      · have hlocal := (x.indexEquiv i).2.isLt
        have hrankEq := congrArg
          (fun z ↦ finrank K (W.component z).carrier) hpOld
        rw [hrankEq]
        exact hlocal
      · exact Fin.succ_le_castSucc_iff.mpr hkp⟩
  let oldLocal : Fin
      (finrank K (W.component p.succ).carrier) :=
    ⟨(x.indexEquiv i).2.val, by
      have hlocal := (x.indexEquiv i).2.isLt
      have hrankEq := congrArg
        (fun z ↦ finrank K (W.component z).carrier) hpOld
      rw [hrankEq]
      exact hlocal⟩
  have hx : x.indexEquiv i = ⟨p.succ, oldLocal⟩ := by
    apply Sigma.ext
    · exact hpOld.symm
    · exact (Fin.heq_ext_iff
        (congrArg (fun z ↦ finrank K (W.component z).carrier)
          hpOld.symm)).2 rfl
  have hmap : W.mergeIndexEquiv k heq (P.indexEquiv i) =
      ⟨p.succ, oldLocal⟩ :=
    (x.indexEquiv_eq_mergeIndexEquiv hW k heq hstrict P i).symm.trans hx
  have hcanonical : W.mergeIndexEquiv k heq ⟨p, mergedLocal⟩ =
      ⟨p.succ, oldLocal⟩ := by
    simpa only [mergedLocal, oldLocal, Fin.val_mk] using
      W.mergeIndexEquiv_of_gt k heq p hkp mergedLocal
  have hstrictCoordinate : P.indexEquiv i = ⟨p, mergedLocal⟩ :=
    (W.mergeIndexEquiv k heq).injective (hmap.trans hcanonical.symm)
  refine ⟨p, hkp, hpOld, congrArg Sigma.fst hstrictCoordinate, ?_⟩
  have hlocal := congrArg (fun z ↦ z.2.val) hstrictCoordinate
  simpa only [mergedLocal, Fin.val_mk] using hlocal

/-- A terminal weak coordinate is the same strict Jordan boundary when the
weak family is already strict.  Both adjacent strict scales are identified
with the current and next weak scales. -/
theorem exists_boundary_resolution_ofStrict
    {m t : Nat} {a : GoodBONG q L (m + 1)}
    {W : Lattice.WeakJordanDecomposition q L (t + 1)}
    (x : WeakJordanOrderProfileWitness a.toBONG W)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (g : Fin m)
    (hlast : (x.indexEquiv g.castSucc).2.val + 1 =
      finrank K (W.component (x.indexEquiv g.castSucc).1).carrier)
    (hnext : (x.indexEquiv g.castSucc).1.val < t) :
    ∃ z : Fin t,
      P.boundaryIndex z = g ∧
      z.val = (x.indexEquiv g.castSucc).1.val ∧
      (W.toJordan hstrict).fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z) =
        ordUnit K (W.scaleGenerator (x.indexEquiv g.castSucc).1) ∧
      (W.toJordan hstrict).fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryRightIndex z) =
        ordUnit K (W.scaleGenerator
          ⟨(x.indexEquiv g.castSucc).1.val + 1, by omega⟩) := by
  let z : Fin t := ⟨(x.indexEquiv g.castSucc).1.val, hnext⟩
  have hcoordinates := x.indexEquiv_eq_ofStrict hstrict P g.castSucc
  have hcomponent : (P.indexEquiv g.castSucc).1 =
      Lattice.JordanDecomposition.boundaryLeftIndex z := by
    apply Fin.ext
    have hfirst := congrArg Sigma.fst hcoordinates
    change (P.indexEquiv g.castSucc).1.val =
      (x.indexEquiv g.castSucc).1.val
    exact congrArg Fin.val hfirst.symm
  have hlastStrict : (P.indexEquiv g.castSucc).2.val + 1 =
      (W.toJordan hstrict).componentRank (P.indexEquiv g.castSucc).1 := by
    have hfirst := congrArg Sigma.fst hcoordinates
    have hlocal := congrArg (fun z ↦ z.2.val) hcoordinates
    change (P.indexEquiv g.castSucc).2.val + 1 =
      finrank K (W.component (P.indexEquiv g.castSucc).1).carrier
    have hrank := congrArg
      (fun p ↦ finrank K (W.component p).carrier) hfirst
    omega
  refine ⟨z, P.boundaryIndex_eq_of_indexEquiv_last g z hcomponent
    hlastStrict, rfl, ?_, ?_⟩
  · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
    rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator]
    apply congrArg (fun p ↦ ordUnit K (W.scaleGenerator p))
    apply Fin.ext
    dsimp only [z, Lattice.JordanDecomposition.boundaryLeftIndex, Fin.val_mk]
    rfl
  · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
    rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator]
    apply congrArg (fun p ↦ ordUnit K (W.scaleGenerator p))
    apply Fin.ext
    dsimp only [z, Lattice.JordanDecomposition.boundaryRightIndex, Fin.val_mk]
    rfl

/-- A terminal weak coordinate strictly before an amalgamated pair remains
a strict boundary after the merge.  Its right strict scale is the next old
weak scale, including the case where that next component is the merged
pair itself. -/
theorem exists_boundary_resolution_ofMerge_before
    {m t : Nat} {a : GoodBONG q L (m + 1)}
    {W : Lattice.WeakJordanDecomposition q L (t + 1)}
    (x : WeakJordanOrderProfileWitness a.toBONG W)
    (hW : W.HasImproperEvenRank) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hstrict : StrictMono (fun i ↦
      ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG
      ((W.mergeAdjacentAt k heq).toJordan hstrict))
    (g : Fin m)
    (hbefore : (x.indexEquiv g.castSucc).1 < k.castSucc)
    (hlast : (x.indexEquiv g.castSucc).2.val + 1 =
      finrank K (W.component (x.indexEquiv g.castSucc).1).carrier) :
    ∃ s : Nat, ∃ hcount : t = s + 1,
      let J := (W.mergeAdjacentAt k heq).toJordan hstrict
      let J' := J.castComponentCount hcount
      let P' := P.castComponentCount hcount
      ∃ z : Fin s,
        P'.boundaryIndex z = g ∧
        z.val = (x.indexEquiv g.castSucc).1.val ∧
        J'.fundamentalScaleOrder
            (Lattice.JordanDecomposition.boundaryLeftIndex z) =
          ordUnit K (W.scaleGenerator (x.indexEquiv g.castSucc).1) ∧
        J'.fundamentalScaleOrder
            (Lattice.JordanDecomposition.boundaryRightIndex z) =
          ordUnit K (W.scaleGenerator
            ⟨(x.indexEquiv g.castSucc).1.val + 1, by
              have hk := k.isLt
              change (x.indexEquiv g.castSucc).1.val < k.val at hbefore
              omega⟩) := by
  have htPos : 0 < t := Nat.zero_lt_of_lt k.isLt
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htPos)
  refine ⟨s, rfl, ?_⟩
  let J := (W.mergeAdjacentAt k heq).toJordan hstrict
  let J' := J.castComponentCount rfl
  let P' := P.castComponentCount rfl
  have hcoordinates := x.strict_coordinates_of_before hW k heq hstrict P
    g.castSucc hbefore
  rcases hcoordinates with ⟨p, hp, hpOld, hpCoordinate, hlocal⟩
  have hpBound : p.val < s := by
    have hkBound := k.isLt
    omega
  let z : Fin s := ⟨p.val, hpBound⟩
  have hcomponent : (P'.indexEquiv g.castSucc).1 =
      Lattice.JordanDecomposition.boundaryLeftIndex z := by
    apply Fin.ext
    change (P.indexEquiv g.castSucc).1.val = p.val
    exact congrArg Fin.val hpCoordinate
  have hlastStrict : (P'.indexEquiv g.castSucc).2.val + 1 =
      J'.componentRank (P'.indexEquiv g.castSucc).1 := by
    change (P.indexEquiv g.castSucc).2.val + 1 =
      finrank K ((W.mergeAdjacentAt k heq).component
        (P.indexEquiv g.castSucc).1).carrier
    have hskip : k.succ.succAbove p = p.castSucc := by
      rw [Fin.succAbove_of_castSucc_lt]
      exact Fin.castSucc_lt_succ_iff.mpr hp.le
    have hrank : finrank K ((W.mergeAdjacentAt k heq).component
          (P.indexEquiv g.castSucc).1).carrier =
        finrank K (W.component (x.indexEquiv g.castSucc).1).carrier := by
      rw [hpCoordinate, W.mergeAdjacentAt_component_of_ne k heq p
        (Fin.ne_of_lt hp), hskip, hpOld]
    omega
  let right : Fin (s + 1) := ⟨p.val + 1, by omega⟩
  let weakNext : Fin (s + 2) :=
    ⟨(x.indexEquiv g.castSucc).1.val + 1, by
      change (x.indexEquiv g.castSucc).1.val < k.val at hbefore
      have hk := k.isLt
      omega⟩
  have hrightLe : right ≤ k := by
    change p.val + 1 ≤ k.val
    omega
  have hskipRight : k.succ.succAbove right = weakNext := by
    by_cases hrightLt : right < k
    · rw [Fin.succAbove_of_castSucc_lt]
      · apply Fin.ext
        have hpVal := congrArg Fin.val hpOld
        change p.val = (x.indexEquiv g.castSucc).1.val at hpVal
        change p.val + 1 = (x.indexEquiv g.castSucc).1.val + 1
        exact congrArg (fun z ↦ z + 1) hpVal
      · exact Fin.castSucc_lt_succ_iff.mpr hrightLt.le
    · have hrightEq : right = k := le_antisymm hrightLe (le_of_not_gt hrightLt)
      rw [hrightEq]
      have hskipSelf : k.succ.succAbove k = k.castSucc := by
        rw [Fin.succAbove_of_castSucc_lt]
        exact Fin.castSucc_lt_succ_iff.mpr (Fin.le_refl k)
      rw [hskipSelf]
      apply Fin.ext
      have hpVal := congrArg Fin.val hpOld
      change p.val = (x.indexEquiv g.castSucc).1.val at hpVal
      have hrightVal := congrArg Fin.val hrightEq
      change p.val + 1 = k.val at hrightVal
      change k.val = (x.indexEquiv g.castSucc).1.val + 1
      calc
        k.val = p.val + 1 := hrightVal.symm
        _ = (x.indexEquiv g.castSucc).1.val + 1 :=
          congrArg (fun z ↦ z + 1) hpVal
  refine ⟨z, P'.boundaryIndex_eq_of_indexEquiv_last g z hcomponent
    hlastStrict, ?_, ?_, ?_⟩
  · exact congrArg Fin.val hpOld
  · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
    change ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator
        (Lattice.JordanDecomposition.boundaryLeftIndex z)) = _
    rw [W.mergeAdjacentAt_scaleGenerator]
    have hleft : Lattice.JordanDecomposition.boundaryLeftIndex z = p := by
      apply Fin.ext
      rfl
    rw [hleft]
    have hskip : k.succ.succAbove p = p.castSucc := by
      rw [Fin.succAbove_of_castSucc_lt]
      exact Fin.castSucc_lt_succ_iff.mpr hp.le
    rw [hskip, hpOld]
  · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
    change ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator
        (Lattice.JordanDecomposition.boundaryRightIndex z)) = _
    rw [W.mergeAdjacentAt_scaleGenerator]
    have hright : Lattice.JordanDecomposition.boundaryRightIndex z = right := by
      apply Fin.ext
      rfl
    rw [hright, hskipRight]

/-- A terminal weak coordinate at or after the old right member of an
amalgamated pair remains a strict boundary after the merge.  The strict
boundary number is shifted down by one, and its adjacent scales are the
current and next old weak scales. -/
theorem exists_boundary_resolution_ofMerge_after_pair
    {m t : Nat} {a : GoodBONG q L (m + 1)}
    {W : Lattice.WeakJordanDecomposition q L (t + 1)}
    (x : WeakJordanOrderProfileWitness a.toBONG W)
    (hW : W.HasImproperEvenRank) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hstrict : StrictMono (fun i ↦
      ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG
      ((W.mergeAdjacentAt k heq).toJordan hstrict))
    (g : Fin m)
    (hpairLe : k.succ ≤ (x.indexEquiv g.castSucc).1)
    (hlast : (x.indexEquiv g.castSucc).2.val + 1 =
      finrank K (W.component (x.indexEquiv g.castSucc).1).carrier)
    (hnext : (x.indexEquiv g.castSucc).1.val < t) :
    ∃ s : Nat, ∃ hcount : t = s + 1,
      let J := (W.mergeAdjacentAt k heq).toJordan hstrict
      let J' := J.castComponentCount hcount
      let P' := P.castComponentCount hcount
      ∃ z : Fin s,
        P'.boundaryIndex z = g ∧
        z.val + 1 = (x.indexEquiv g.castSucc).1.val ∧
        J'.fundamentalScaleOrder
            (Lattice.JordanDecomposition.boundaryLeftIndex z) =
          ordUnit K (W.scaleGenerator (x.indexEquiv g.castSucc).1) ∧
        J'.fundamentalScaleOrder
            (Lattice.JordanDecomposition.boundaryRightIndex z) =
          ordUnit K (W.scaleGenerator
            ⟨(x.indexEquiv g.castSucc).1.val + 1, by omega⟩) := by
  have htTwo : 2 ≤ t := by
    have hk := k.isLt
    change k.val + 1 ≤ (x.indexEquiv g.castSucc).1.val at hpairLe
    omega
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  refine ⟨s, rfl, ?_⟩
  let J := (W.mergeAdjacentAt k heq).toJordan hstrict
  let J' := J.castComponentCount rfl
  let P' := P.castComponentCount rfl
  by_cases hrightEq : (x.indexEquiv g.castSucc).1 = k.succ
  · have hcoordinates := x.strict_coordinates_of_right hW k heq hstrict P
      g.castSucc hrightEq
    let z : Fin s := ⟨k.val, by
      have hp := congrArg Fin.val hrightEq
      change (x.indexEquiv g.castSucc).1.val = k.val + 1 at hp
      omega⟩
    have hcomponent : (P'.indexEquiv g.castSucc).1 =
        Lattice.JordanDecomposition.boundaryLeftIndex z := by
      apply Fin.ext
      change (P.indexEquiv g.castSucc).1.val = k.val
      exact congrArg Fin.val hcoordinates.1
    have hlastStrict : (P'.indexEquiv g.castSucc).2.val + 1 =
        J'.componentRank (P'.indexEquiv g.castSucc).1 := by
      change (P.indexEquiv g.castSucc).2.val + 1 =
        finrank K ((W.mergeAdjacentAt k heq).component
          (P.indexEquiv g.castSucc).1).carrier
      have hrightRank := congrArg
        (fun p ↦ finrank K (W.component p).carrier) hrightEq
      have hmergedRank :
          finrank K ((W.mergeAdjacentAt k heq).component
            (P.indexEquiv g.castSucc).1).carrier =
          finrank K (W.component k.castSucc).carrier +
            finrank K (W.component k.succ).carrier := by
        rw [hcoordinates.1, W.mergeAdjacentAt_componentRank_self]
      omega
    let right : Fin (s + 1) := ⟨k.val + 1, by
      have hp := congrArg Fin.val hrightEq
      change (x.indexEquiv g.castSucc).1.val = k.val + 1 at hp
      omega⟩
    let weakNext : Fin (s + 2) :=
      ⟨(x.indexEquiv g.castSucc).1.val + 1, by omega⟩
    have hskipLeft : k.succ.succAbove k = k.castSucc := by
      rw [Fin.succAbove_of_castSucc_lt]
      exact Fin.castSucc_lt_succ_iff.mpr (Fin.le_refl k)
    have hskipRight : k.succ.succAbove right = weakNext := by
      rw [Fin.succAbove_of_le_castSucc]
      · apply Fin.ext
        change k.val + 1 + 1 =
          (x.indexEquiv g.castSucc).1.val + 1
        have hp := congrArg Fin.val hrightEq
        change (x.indexEquiv g.castSucc).1.val = k.val + 1 at hp
        omega
      · change k.val + 1 ≤ k.val + 1
        exact le_rfl
    refine ⟨z, P'.boundaryIndex_eq_of_indexEquiv_last g z hcomponent
      hlastStrict, ?_, ?_, ?_⟩
    · have hp := congrArg Fin.val hrightEq
      change k.val + 1 = (x.indexEquiv g.castSucc).1.val
      exact hp.symm
    · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
      change ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator
          (Lattice.JordanDecomposition.boundaryLeftIndex z)) = _
      rw [W.mergeAdjacentAt_scaleGenerator]
      have hleft : Lattice.JordanDecomposition.boundaryLeftIndex z = k := by
        apply Fin.ext
        rfl
      rw [hleft, hskipLeft, hrightEq]
      exact heq
    · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
      change ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator
          (Lattice.JordanDecomposition.boundaryRightIndex z)) = _
      rw [W.mergeAdjacentAt_scaleGenerator]
      have hright :
          Lattice.JordanDecomposition.boundaryRightIndex z = right := by
        apply Fin.ext
        rfl
      rw [hright, hskipRight]
  · have hafter : k.succ < (x.indexEquiv g.castSucc).1 :=
      lt_of_le_of_ne hpairLe (Ne.symm hrightEq)
    obtain ⟨p, hkp, hpOld, hpCoordinate, hlocal⟩ :=
      x.strict_coordinates_of_after hW k heq hstrict P g.castSucc hafter
    have hpBound : p.val < s := by
      have hpVal := congrArg Fin.val hpOld
      change p.val + 1 = (x.indexEquiv g.castSucc).1.val at hpVal
      omega
    let z : Fin s := ⟨p.val, hpBound⟩
    have hcomponent : (P'.indexEquiv g.castSucc).1 =
        Lattice.JordanDecomposition.boundaryLeftIndex z := by
      apply Fin.ext
      change (P.indexEquiv g.castSucc).1.val = p.val
      exact congrArg Fin.val hpCoordinate
    have hskip : k.succ.succAbove p = p.succ := by
      rw [Fin.succAbove_of_le_castSucc]
      exact Fin.succ_le_castSucc_iff.mpr hkp
    have hlastStrict : (P'.indexEquiv g.castSucc).2.val + 1 =
        J'.componentRank (P'.indexEquiv g.castSucc).1 := by
      change (P.indexEquiv g.castSucc).2.val + 1 =
        finrank K ((W.mergeAdjacentAt k heq).component
          (P.indexEquiv g.castSucc).1).carrier
      have hrank : finrank K ((W.mergeAdjacentAt k heq).component
            (P.indexEquiv g.castSucc).1).carrier =
          finrank K (W.component (x.indexEquiv g.castSucc).1).carrier := by
        rw [hpCoordinate, W.mergeAdjacentAt_component_of_ne k heq p
          (Fin.ne_of_gt hkp), hskip, hpOld]
      omega
    let right : Fin (s + 1) := ⟨p.val + 1, by omega⟩
    let weakNext : Fin (s + 2) :=
      ⟨(x.indexEquiv g.castSucc).1.val + 1, by omega⟩
    have hrightLe : k.succ ≤ right.castSucc := by
      change k.val + 1 ≤ p.val + 1
      exact Nat.succ_le_succ hkp.le
    have hskipRight : k.succ.succAbove right = weakNext := by
      rw [Fin.succAbove_of_le_castSucc k.succ right hrightLe]
      apply Fin.ext
      have hpVal := congrArg Fin.val hpOld
      change p.val + 1 = (x.indexEquiv g.castSucc).1.val at hpVal
      change p.val + 1 + 1 = (x.indexEquiv g.castSucc).1.val + 1
      omega
    refine ⟨z, P'.boundaryIndex_eq_of_indexEquiv_last g z hcomponent
      hlastStrict, ?_, ?_, ?_⟩
    · exact congrArg Fin.val hpOld
    · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
      change ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator
          (Lattice.JordanDecomposition.boundaryLeftIndex z)) = _
      rw [W.mergeAdjacentAt_scaleGenerator]
      have hleft : Lattice.JordanDecomposition.boundaryLeftIndex z = p := by
        apply Fin.ext
        rfl
      rw [hleft, hskip, hpOld]
    · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
      change ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator
          (Lattice.JordanDecomposition.boundaryRightIndex z)) = _
      rw [W.mergeAdjacentAt_scaleGenerator]
      have hright :
          Lattice.JordanDecomposition.boundaryRightIndex z = right := by
        apply Fin.ext
        rfl
      rw [hright, hskipRight]

end BONG.WeakJordanOrderProfileWitness

end Bong
