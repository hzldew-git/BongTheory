/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanFundamentalSplitOrder
import Bong.Bong.Beli2009JordanDualPrefixWeight
import Bong.Bong.Beli2009NeighborAlphaMinimum
import Bong.Bong.Beli2009JordanBoundaryEvenNonunary

/-!
# Beli (2009), Lemmas 2.15--2.16: unary and mixed-rank even boundaries

This file proves the weight-ideal formula for a unary Jordan component from
the concrete prefix/suffix split and Beli's Lemma 2.14.  It then closes the
unary endpoint and mixed-rank branches of Lemma 2.16(ii), showing that the
even O'Meara boundary candidate has order equal to the corresponding BONG
alpha invariant in every adjacent-component rank.
-/

namespace Bong

open Dyadic Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace BONG.GoodBONG

/-- A global alpha immediately preceding a prefix cut is bounded by the
alpha at the last site of the canonical prefix segment. -/
theorem predecessorAlphaValue_le_prefixLocalAlpha
    {n : Nat} (b : GoodBONG q L (n + 2))
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    b.alphaValue ⟨i.val - 1, by omega⟩ ≤
      ((b.prefixAlphaSegmentWitness i hi).toGoodBONG b.good).alphaValue
        (prefixAlphaLocalizationIndex i hi).localPivot := by
  let s := prefixAlphaLocalizationIndex i hi
  let c := b.prefixAlphaSegmentWitness i hi
  have h := b.beli2009Lemma21_le_segmentAlpha s c
  have hpivot : s.pivotFin = ⟨i.val - 1, by omega⟩ := by
    apply Fin.ext
    rfl
  rw [hpivot, ← b.coe_alphaValue,
    ← (c.toGoodBONG b.good).coe_alphaValue] at h
  exact WithTop.coe_le_coe.mp h

end BONG.GoodBONG

namespace BONG.StrictJordanAdaptedAlignment

variable {m : Nat} {a : GoodBONG q L (m + 1)}
  {b : GoodBONG r M (m + 1)}

/-- The last alpha of the actual Jordan prefix is the localized alpha in
the canonical prefix segment at the boundary immediately before `k`. -/
theorem sourcePrefixAlphaLast_eq_boundaryPrefixLocalAlpha
    {n : Nat} {a : GoodBONG q L (n + 2)}
    {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (htwo : 2 ≤ S.componentStart k) :
    let j : Fin (n + 1) := ⟨S.componentStart k - 1, by
      have hbound := (S.componentStart_lt_componentStop k).trans_le
        (S.componentStop_le k)
      omega⟩
    let loc := GoodBONG.prefixAlphaLocalizationIndex j (by
      dsimp only [j]
      omega)
    let ell := S.componentStart k - 1
    let hell : ell + 1 = S.componentStart k := by
      dsimp only [ell]
      omega
    let pre := (S.sourcePrefixGoodBONG k hk T).castLength hell.symm
    pre.alphaValue ⟨ell - 1, by
      dsimp only [ell]
      omega⟩ =
      ((a.prefixAlphaSegmentWitness j (by
        dsimp only [j]
        omega)).toGoodBONG a.good).alphaValue
        loc.localPivot := by
  dsimp only
  have hprefix : 0 < S.componentStart k := by
    unfold componentStart
    let p : Fin S.componentCount := ⟨k.val - 1, by omega⟩
    have hp : p ∈ Finset.Iio k := by
      simp only [Finset.mem_Iio]
      change k.val - 1 < k.val
      omega
    have hle := Finset.single_le_sum
      (s := Finset.Iio k)
      (f := fun z ↦
        S.sourceJordan.toOrthogonalDecomposition.componentRank z)
      (fun _ _ ↦ Nat.zero_le _) hp
    exact (S.sourceJordan.component_finrank_pos p).trans_le hle
  let j : Fin (n + 1) := ⟨S.componentStart k - 1, by
    have hbound := (S.componentStart_lt_componentStop k).trans_le
      (S.componentStop_le k)
    omega⟩
  let loc := GoodBONG.prefixAlphaLocalizationIndex j (by
    dsimp only [j]
    omega)
  let segment := (a.prefixAlphaSegmentWitness j (by
    dsimp only [j]
    omega)).toGoodBONG a.good
  let ell := S.componentStart k - 1
  let hell : ell + 1 = S.componentStart k := by
    dsimp only [ell]
    omega
  let pre := (S.sourcePrefixGoodBONG k hk T).castLength hell.symm
  have hlen : loc.length = ell + 1 := by
    dsimp [loc, j, GoodBONG.prefixAlphaLocalizationIndex,
      AlphaLocalizationIndex.length, ell]
  let segment' := segment.castLength hlen
  have hvalues : ∀ z, segment'.valueUnit z = pre.valueUnit z := by
    intro z
    rw [show segment' = segment.castLength hlen by rfl,
      GoodBONG.valueUnit_castLength_fundamental]
    change (a.prefixAlphaSegmentWitness j _).bong.valueUnit _ =
      ((S.sourcePrefixGoodBONG k hk T).castLength hell.symm).valueUnit z
    rw [(a.prefixAlphaSegmentWitness j _).valueUnit_eq,
      GoodBONG.valueUnit_castLength_fundamental,
      S.sourcePrefixGoodBONG_valueUnit]
    apply congrArg a.valueUnit
    apply Fin.ext
    simp [BONG.SegmentWitness.sourceIndex, j,
      GoodBONG.prefixAlphaLocalizationIndex]
  have halpha := segment'.alphaValue_eq_of_valueUnits_eq pre hvalues
    ⟨ell - 1, by dsimp only [ell]; omega⟩
  have halphaLen : loc.stop - loc.start = ell := by
    dsimp [loc, j, ell, GoodBONG.prefixAlphaLocalizationIndex]
  have hlocal : Fin.cast halphaLen.symm
      ⟨ell - 1, by dsimp only [ell]; omega⟩ =
      loc.localPivot := by
    apply Fin.ext
    dsimp [loc, j, GoodBONG.prefixAlphaLocalizationIndex,
      AlphaLocalizationIndex.localPivot]
  have hcast := GoodBONG.alphaValue_castLength_fundamental
    segment halphaLen
      ⟨ell - 1, by dsimp only [ell]; omega⟩
  rw [hlocal] at hcast
  exact halpha.symm.trans hcast

/-- The first alpha of the actual Jordan suffix is the localized alpha in
the canonical suffix segment at the boundary immediately before `k`. -/
theorem sourceSuffixAlphaZero_eq_boundarySuffixLocalAlpha
    {n : Nat} {a : GoodBONG q L (n + 2)}
    {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (hright : S.componentStart k < n + 1) :
    let j : Fin (n + 1) := ⟨S.componentStart k - 1, by omega⟩
    let loc := GoodBONG.suffixAlphaLocalizationIndex j (by
      dsimp only [j]
      have hprefix : 0 < S.componentStart k := by
        unfold componentStart
        let p : Fin S.componentCount := ⟨k.val - 1, by omega⟩
        have hp : p ∈ Finset.Iio k := by
          simp only [Finset.mem_Iio]
          change k.val - 1 < k.val
          omega
        have hle := Finset.single_le_sum
          (s := Finset.Iio k)
          (f := fun z ↦
            S.sourceJordan.toOrthogonalDecomposition.componentRank z)
          (fun _ _ ↦ Nat.zero_le _) hp
        exact (S.sourceJordan.component_finrank_pos p).trans_le hle
      omega)
    let tail := n + 1 - S.componentStart k
    let htail : tail + 1 = n + 2 - S.componentStart k := by
      dsimp only [tail]
      omega
    let suf := (S.sourceSuffixGoodBONG k hk T).castLength htail.symm
    suf.alphaValue ⟨0, by dsimp only [tail]; omega⟩ =
      ((a.suffixAlphaSegmentWitness j (by
        dsimp only [j]
        have hprefix : 0 < S.componentStart k := by
          unfold componentStart
          let p : Fin S.componentCount := ⟨k.val - 1, by omega⟩
          have hp : p ∈ Finset.Iio k := by
            simp only [Finset.mem_Iio]
            change k.val - 1 < k.val
            omega
          have hle := Finset.single_le_sum
            (s := Finset.Iio k)
            (f := fun z ↦
              S.sourceJordan.toOrthogonalDecomposition.componentRank z)
            (fun _ _ ↦ Nat.zero_le _) hp
          exact (S.sourceJordan.component_finrank_pos p).trans_le hle
        omega)).toGoodBONG a.good).alphaValue
        loc.localPivot := by
  dsimp only
  have hprefixSuffix : 0 < S.componentStart k := by
    unfold componentStart
    let p : Fin S.componentCount := ⟨k.val - 1, by omega⟩
    have hp : p ∈ Finset.Iio k := by
      simp only [Finset.mem_Iio]
      change k.val - 1 < k.val
      omega
    have hle := Finset.single_le_sum
      (s := Finset.Iio k)
      (f := fun z ↦
        S.sourceJordan.toOrthogonalDecomposition.componentRank z)
      (fun _ _ ↦ Nat.zero_le _) hp
    exact (S.sourceJordan.component_finrank_pos p).trans_le hle
  let j : Fin (n + 1) := ⟨S.componentStart k - 1, by
    have hstart := S.componentStart_lt_componentStop k
    have hstop := S.componentStop_le k
    omega⟩
  let loc := GoodBONG.suffixAlphaLocalizationIndex j (by
    dsimp only [j]
    have hprefix : 0 < S.componentStart k := by
      unfold componentStart
      let p : Fin S.componentCount := ⟨k.val - 1, by omega⟩
      have hp : p ∈ Finset.Iio k := by
        simp only [Finset.mem_Iio]
        change k.val - 1 < k.val
        omega
      have hle := Finset.single_le_sum
        (s := Finset.Iio k)
        (f := fun z ↦
          S.sourceJordan.toOrthogonalDecomposition.componentRank z)
        (fun _ _ ↦ Nat.zero_le _) hp
      exact (S.sourceJordan.component_finrank_pos p).trans_le hle
    omega)
  let segment := (a.suffixAlphaSegmentWitness j (by
    dsimp only [j]
    have hprefix : 0 < S.componentStart k := by
      unfold componentStart
      let p : Fin S.componentCount := ⟨k.val - 1, by omega⟩
      have hp : p ∈ Finset.Iio k := by
        simp only [Finset.mem_Iio]
        change k.val - 1 < k.val
        omega
      have hle := Finset.single_le_sum
        (s := Finset.Iio k)
        (f := fun z ↦
          S.sourceJordan.toOrthogonalDecomposition.componentRank z)
        (fun _ _ ↦ Nat.zero_le _) hp
      exact (S.sourceJordan.component_finrank_pos p).trans_le hle
    omega)).toGoodBONG a.good
  let tail := n + 1 - S.componentStart k
  let htail : tail + 1 = n + 2 - S.componentStart k := by
    dsimp only [tail]
    omega
  let suf := (S.sourceSuffixGoodBONG k hk T).castLength htail.symm
  have hlen : loc.length = tail + 1 := by
    dsimp [loc, j, GoodBONG.suffixAlphaLocalizationIndex,
      AlphaLocalizationIndex.length, tail]
    omega
  let segment' := segment.castLength hlen
  have hvalues : ∀ z, segment'.valueUnit z = suf.valueUnit z := by
    intro z
    rw [show segment' = segment.castLength hlen by rfl,
      GoodBONG.valueUnit_castLength_fundamental]
    change (a.suffixAlphaSegmentWitness j _).bong.valueUnit _ =
      ((S.sourceSuffixGoodBONG k hk T).castLength htail.symm).valueUnit z
    rw [(a.suffixAlphaSegmentWitness j _).valueUnit_eq,
      GoodBONG.valueUnit_castLength_fundamental,
      S.sourceSuffixGoodBONG_valueUnit]
    apply congrArg a.valueUnit
    apply Fin.ext
    simp [BONG.SegmentWitness.sourceIndex, j,
      GoodBONG.suffixAlphaLocalizationIndex]
    all_goals omega
  have halpha := segment'.alphaValue_eq_of_valueUnits_eq suf hvalues
    ⟨0, by omega⟩
  have halphaLen : loc.stop - loc.start = tail := by
    dsimp [loc, j, tail, GoodBONG.suffixAlphaLocalizationIndex]
    omega
  have hlocal : Fin.cast halphaLen.symm
      (⟨0, by dsimp only [tail]; omega⟩ : Fin tail) =
      loc.localPivot := by
    apply Fin.ext
    dsimp [loc, j, GoodBONG.suffixAlphaLocalizationIndex,
      AlphaLocalizationIndex.localPivot]
    omega
  have hcast := GoodBONG.alphaValue_castLength_fundamental
    segment halphaLen ⟨0, by omega⟩
  rw [hlocal] at hcast
  exact halpha.symm.trans hcast

/-- On a unary Jordan component the BONG order at the unique coordinate is
the scale order of that component. -/
theorem sourceOrder_componentStart_eq_scaleOrder_of_unary
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount)
    (hrank : S.sourceJordan.toOrthogonalDecomposition.componentRank k = 1) :
    a.order ⟨S.componentStart k, by
        exact (S.componentStart_lt_componentStop k).trans_le
          (S.componentStop_le k)⟩ =
      ordUnit K (S.sourceJordan.scaleGenerator k) := by
  let C := S.sourceComponentCoordinates k
  have hdiff : C.stop - C.start = 1 := by
    dsimp only [C, sourceComponentCoordinates]
    unfold componentStop
    rw [Nat.add_sub_cancel_left, hrank]
  have hproper : C.normOrder = C.scaleOrder := by
    rcases C.proper_or_even with hproper | heven
    · exact hproper
    · rcases heven with ⟨z, hz⟩
      rw [hdiff] at hz
      omega
  have hord := (C.beli2009Lemma213_i C.start le_rfl C.start_lt_stop).1
    (by omega)
  rw [hproper] at hord
  simpa only [C, sourceComponentCoordinates,
    GoodBONG.JordanBlockCoordinates.index] using hord

/-- The adjacent order gap immediately before a noninitial Jordan component
is nonnegative, in concrete global BONG coordinates. -/
theorem source_order_before_component_le_start
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val) :
    a.order ⟨S.componentStart k - 1, by
        have hstart := S.componentStart_lt_componentStop k
        have hstop := S.componentStop_le k
        omega⟩ ≤
      a.order ⟨S.componentStart k, by
        exact (S.componentStart_lt_componentStop k).trans_le
          (S.componentStop_le k)⟩ := by
  let previous : Fin S.componentCount := ⟨k.val - 1, by omega⟩
  let last : Fin
      (S.sourceJordan.toOrthogonalDecomposition.componentRank previous) :=
    ⟨S.sourceJordan.toOrthogonalDecomposition.componentRank previous - 1,
      by
        simp only [Lattice.OrthogonalDecomposition.componentRank]
        exact Nat.sub_lt (S.sourceJordan.component_finrank_pos previous)
          Nat.zero_lt_one⟩
  let first : Fin
      (S.sourceJordan.toOrthogonalDecomposition.componentRank k) :=
    ⟨0, S.sourceJordan.component_finrank_pos k⟩
  let leftGlobal : Fin (m + 1) :=
    S.sourceProfile.indexEquiv.symm ⟨previous, last⟩
  let rightGlobal : Fin (m + 1) :=
    S.sourceProfile.indexEquiv.symm ⟨k, first⟩
  have hpreviousSucc : k.val = previous.val + 1 := by
    dsimp only [previous]
    omega
  have hlast : last.val + 1 =
      S.sourceJordan.toOrthogonalDecomposition.componentRank previous := by
    dsimp only [last]
    have hpos : 0 <
        S.sourceJordan.toOrthogonalDecomposition.componentRank previous := by
      simpa only [Lattice.OrthogonalDecomposition.componentRank] using
        S.sourceJordan.component_finrank_pos previous
    omega
  have hnext : rightGlobal.val = leftGlobal.val + 1 := by
    exact S.sourceProfile.inverse_index_val_next_component
      previous k hpreviousSucc last hlast
        (S.sourceJordan.component_finrank_pos k)
  have hrightVal : rightGlobal.val = S.componentStart k := by
    have hv := S.sourceProfile.inverse_index_val k first
    change rightGlobal.val =
      (∑ i ∈ Finset.Iio k,
        S.sourceJordan.toOrthogonalDecomposition.componentRank i) +
          first.val at hv
    change rightGlobal.val = S.componentStart k
    dsimp only [first, componentStart] at hv ⊢
    omega
  have hleftVal : leftGlobal.val = S.componentStart k - 1 := by
    omega
  have horder : a.order leftGlobal ≤ a.order rightGlobal := by
    simpa only [leftGlobal, rightGlobal, previous, last, first] using
      S.source_boundary_order_le k hk
  have hleftIndex : leftGlobal =
      ⟨S.componentStart k - 1, by
        have hstart := S.componentStart_lt_componentStop k
        have hstop := S.componentStop_le k
        omega⟩ := by
    apply Fin.ext
    exact hleftVal
  have hrightIndex : rightGlobal =
      ⟨S.componentStart k, by
        exact (S.componentStart_lt_componentStop k).trans_le
          (S.componentStop_le k)⟩ := by
    apply Fin.ext
    exact hrightVal
  rw [hleftIndex, hrightIndex] at horder
  exact horder

theorem source_component_has_successor_of_stop_lt
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount)
    (hstop : S.componentStop k < m + 1) :
    k.val + 1 < S.componentCount := by
  by_contra hnot
  have hlast : k.val + 1 = S.componentCount := by
    have hklt := k.isLt
    omega
  have huniv : insert k (Finset.Iio k) = Finset.univ := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_Iio, Finset.mem_univ,
      iff_true]
    have hxlt := x.isLt
    by_cases hx : x.val = k.val
    · exact Or.inl (Fin.ext hx)
    · exact Or.inr (by omega)
  have hsum := S.sourceProfile.sum_componentRank_eq_length
  have hstopEq : S.componentStop k = m + 1 := by
    calc
      S.componentStop k =
          ∑ z ∈ insert k (Finset.Iio k),
            S.sourceJordan.toOrthogonalDecomposition.componentRank z := by
        unfold componentStop componentStart
        rw [Finset.sum_insert (by simp)]
        omega
      _ = ∑ z,
          S.sourceJordan.toOrthogonalDecomposition.componentRank z := by
        rw [huniv]
      _ = m + 1 := hsum
  omega

theorem source_order_componentStart_le_after_of_unary_nonterminal
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount)
    (hrank : S.sourceJordan.toOrthogonalDecomposition.componentRank k = 1)
    (hstop : S.componentStop k < m + 1) :
    a.order ⟨S.componentStart k, by
        exact (S.componentStart_lt_componentStop k).trans_le
          (S.componentStop_le k)⟩ ≤
      a.order ⟨S.componentStart k + 1, by
        have h := hstop
        unfold componentStop at h
        rw [hrank] at h
        omega⟩ := by
  have hsucc := S.source_component_has_successor_of_stop_lt k hstop
  let l : Fin S.componentCount := ⟨k.val + 1, hsucc⟩
  have hlpos : 0 < l.val := by
    dsimp only [l]
    omega
  have hstopStart := S.componentStop_eq_componentStart_of_val_succ
    k l (by rfl)
  have hcomponentStop : S.componentStop k = S.componentStart k + 1 := by
    unfold componentStop
    rw [hrank]
  have hlStart : S.componentStart l = S.componentStart k + 1 := by
    omega
  have horder := S.source_order_before_component_le_start l hlpos
  have hleft :
      (⟨S.componentStart l - 1, by
        have hbegin := S.componentStart_lt_componentStop l
        have hend := S.componentStop_le l
        omega⟩ : Fin (m + 1)) =
      ⟨S.componentStart k, by
        exact (S.componentStart_lt_componentStop k).trans_le
          (S.componentStop_le k)⟩ := by
    apply Fin.ext
    dsimp only
    omega
  have hright :
      (⟨S.componentStart l, by
        exact (S.componentStart_lt_componentStop l).trans_le
          (S.componentStop_le l)⟩ : Fin (m + 1)) =
      ⟨S.componentStart k + 1, by omega⟩ := by
    apply Fin.ext
    exact hlStart
  rw [hleft, hright] at horder
  exact horder

/-- The order-theoretic minimum calculation behind the unary branch of
Lemma 2.15.  Missing endpoint terms can be represented by setting the
corresponding local alpha equal to `e`. -/
private theorem unaryNormalizedSplitMinimum_eq
    (g e alphaPrefix alphaSuffix alpha : ℚ) (delta : WithTop ℚ)
    (hgap : 0 ≤ g)
    (halpha : (alpha : WithTop ℚ) =
      min (((g / 2 + e : ℚ) : WithTop ℚ))
        (min (((g : ℚ) : WithTop ℚ) + delta)
          (min (((g + alphaPrefix : ℚ) : WithTop ℚ))
            (((g + alphaSuffix : ℚ) : WithTop ℚ))))) :
    min
        (min (alphaSuffix : WithTop ℚ) (e : WithTop ℚ))
        (min
          (min (((g + alphaPrefix : ℚ) : WithTop ℚ))
            (((g + e : ℚ) : WithTop ℚ)))
          (((g : ℚ) : WithTop ℚ) + delta)) =
      min (alpha : WithTop ℚ)
        (min (alphaSuffix : WithTop ℚ) (e : WithTop ℚ)) := by
  let x : WithTop ℚ :=
    min
      (min (alphaSuffix : WithTop ℚ) (e : WithTop ℚ))
      (min
        (min (((g + alphaPrefix : ℚ) : WithTop ℚ))
          (((g + e : ℚ) : WithTop ℚ)))
        (((g : ℚ) : WithTop ℚ) + delta))
  have hxSuffix : x ≤ (alphaSuffix : WithTop ℚ) :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hxE : x ≤ (e : WithTop ℚ) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hxPrefix : x ≤ ((g + alphaPrefix : ℚ) : WithTop ℚ) :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hxGapE : x ≤ ((g + e : ℚ) : WithTop ℚ) :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hxDelta : x ≤ ((g : ℚ) : WithTop ℚ) + delta :=
    (min_le_right _ _).trans (min_le_right _ _)
  have heHalf : (e : WithTop ℚ) ≤ ((g / 2 + e : ℚ) : WithTop ℚ) := by
    exact_mod_cast (by linarith : e ≤ g / 2 + e)
  have hsGap : (alphaSuffix : WithTop ℚ) ≤
      ((g + alphaSuffix : ℚ) : WithTop ℚ) := by
    exact_mod_cast (by linarith : alphaSuffix ≤ g + alphaSuffix)
  have heGap : (e : WithTop ℚ) ≤ ((g + e : ℚ) : WithTop ℚ) := by
    exact_mod_cast (by linarith : e ≤ g + e)
  have hxAlpha : x ≤ (alpha : WithTop ℚ) := by
    rw [halpha]
    exact le_min (hxE.trans heHalf)
      (le_min hxDelta (le_min hxPrefix (hxSuffix.trans hsGap)))
  apply le_antisymm
  · change x ≤ _
    exact le_min hxAlpha (min_le_left _ _)
  · have hyAlpha : min (alpha : WithTop ℚ)
        (min (alphaSuffix : WithTop ℚ) (e : WithTop ℚ)) ≤
        (alpha : WithTop ℚ) := min_le_left _ _
    have hyPair : min (alpha : WithTop ℚ)
        (min (alphaSuffix : WithTop ℚ) (e : WithTop ℚ)) ≤
        min (alphaSuffix : WithTop ℚ) (e : WithTop ℚ) :=
      min_le_right _ _
    have halphaPrefix : (alpha : WithTop ℚ) ≤
        ((g + alphaPrefix : ℚ) : WithTop ℚ) := by
      rw [halpha]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))
    have halphaDelta : (alpha : WithTop ℚ) ≤
        ((g : ℚ) : WithTop ℚ) + delta := by
      rw [halpha]
      exact (min_le_right _ _).trans (min_le_left _ _)
    change _ ≤ x
    apply le_min hyPair
    apply le_min
    · apply le_min
      · exact hyAlpha.trans halphaPrefix
      · exact (hyPair.trans (min_le_right _ _)).trans heGap
    · exact hyAlpha.trans halphaDelta

private theorem unarySplitMinimum_eq
    (B g e alphaPrefix alphaSuffix alpha : ℚ) (delta : WithTop ℚ)
    (hgap : 0 ≤ g)
    (halpha : (alpha : WithTop ℚ) =
      min (((g / 2 + e : ℚ) : WithTop ℚ))
        (min (((g : ℚ) : WithTop ℚ) + delta)
          (min (((g + alphaPrefix : ℚ) : WithTop ℚ))
            (((g + alphaSuffix : ℚ) : WithTop ℚ))))) :
    min
        (min (((B + alphaSuffix : ℚ) : WithTop ℚ))
          (((B + e : ℚ) : WithTop ℚ)))
        (min
          (min (((B + g + alphaPrefix : ℚ) : WithTop ℚ))
            (((B + g + e : ℚ) : WithTop ℚ)))
          (((B + g : ℚ) : WithTop ℚ) + delta)) =
      ((B + min alpha (min alphaSuffix e) : ℚ) : WithTop ℚ) := by
  have hnormalized := unaryNormalizedSplitMinimum_eq
    g e alphaPrefix alphaSuffix alpha delta hgap halpha
  calc
    min
        (min (((B + alphaSuffix : ℚ) : WithTop ℚ))
          (((B + e : ℚ) : WithTop ℚ)))
        (min
          (min (((B + g + alphaPrefix : ℚ) : WithTop ℚ))
            (((B + g + e : ℚ) : WithTop ℚ)))
          (((B + g : ℚ) : WithTop ℚ) + delta)) =
        (B : WithTop ℚ) +
          min
            (min (alphaSuffix : WithTop ℚ) (e : WithTop ℚ))
            (min
              (min (((g + alphaPrefix : ℚ) : WithTop ℚ))
                (((g + e : ℚ) : WithTop ℚ)))
              (((g : ℚ) : WithTop ℚ) + delta)) := by
      rw [GoodBONG.lemma214_withTop_add_min,
        GoodBONG.lemma214_withTop_add_min,
        GoodBONG.lemma214_withTop_add_min,
        GoodBONG.lemma214_withTop_add_min]
      norm_cast
      congr 1
      ac_rfl
    _ = (B : WithTop ℚ) +
        min (alpha : WithTop ℚ)
          (min (alphaSuffix : WithTop ℚ) (e : WithTop ℚ)) := by
      rw [hnormalized]
    _ = ((B + min alpha (min alphaSuffix e) : ℚ) : WithTop ℚ) := by
      norm_cast

/-- Lemma 2.14 for an actual Jordan suffix consisting of one coordinate. -/
theorem sourceSuffix_weightIdealOrder_unary
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (hlen : m + 1 - S.componentStart k = 1) :
    let D := S.sourceJordan.toOrthogonalDecomposition
    let U := D.suffixQuadraticSublattice k.val
    Lattice.weightIdealOrder U.space U.lattice =
      a.order ⟨S.componentStart k, by
        exact (S.componentStart_lt_componentStop k).trans_le
          (S.componentStop_le k)⟩ + ramificationIndex K := by
  let D := S.sourceJordan.toOrthogonalDecomposition
  let U := D.suffixQuadraticSublattice k.val
  let suffix := (S.sourceSuffixGoodBONG k hk T).castLength hlen
  have hweight := suffix.weightIdealOrder_unary_proof
  have horder : suffix.order 0 =
      a.order ⟨S.componentStart k, by
        exact (S.componentStart_lt_componentStop k).trans_le
          (S.componentStop_le k)⟩ := by
    rw [show suffix = (S.sourceSuffixGoodBONG k hk T).castLength hlen by rfl,
      GoodBONG.order_castLength]
    simpa using S.sourceSuffixGoodBONG_order k hk T
      ⟨0, by omega⟩
  rw [horder] at hweight
  simpa only [D, U, suffix] using hweight

theorem sourcePrefix_rescaleDual_weightIdealOrder_unary
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (hstart : S.componentStart k = 1) (c : Kˣ) :
    let D := S.sourceJordan.toOrthogonalDecomposition
    let P := D.prefixQuadraticSublattice k.val
    Lattice.weightIdealOrder P.space
        (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)) =
      2 * ordUnit K c -
        a.order ⟨S.componentStart k - 1, by
          have hbound := (S.componentStart_lt_componentStop k).trans_le
            (S.componentStop_le k)
          omega⟩ + ramificationIndex K := by
  let D := S.sourceJordan.toOrthogonalDecomposition
  let P := D.prefixQuadraticSublattice k.val
  let pre := (S.sourcePrefixGoodBONG k hk T).castLength hstart
  have hweight := pre.weightIdealOrder_rescale_dual_unary c
  have horder : pre.order 0 =
      a.order ⟨S.componentStart k - 1, by
        have hbound := (S.componentStart_lt_componentStop k).trans_le
          (S.componentStop_le k)
        omega⟩ := by
    rw [show pre = (S.sourcePrefixGoodBONG k hk T).castLength hstart by rfl,
      GoodBONG.order_castLength]
    have h := S.sourcePrefixGoodBONG_order k hk T ⟨0, by omega⟩
    calc
      (S.sourcePrefixGoodBONG k hk T).order ⟨0, by omega⟩ =
          a.order ⟨0, by
            have hstop := S.componentStop_le k
            have hbegin := S.componentStart_lt_componentStop k
            omega⟩ := h
      _ = a.order ⟨S.componentStart k - 1, by
          have hbound := (S.componentStart_lt_componentStop k).trans_le
            (S.componentStop_le k)
          omega⟩ := by
        apply congrArg a.order
        apply Fin.ext
        dsimp only
        omega
  rw [horder] at hweight
  simpa only [D, P, pre] using hweight

theorem sourcePrefix_rescaleDual_weightIdealOrder_nonunary
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (htwo : 2 ≤ S.componentStart k) (c : Kˣ) :
    let D := S.sourceJordan.toOrthogonalDecomposition
    let P := D.prefixQuadraticSublattice k.val
    let ell := S.componentStart k - 1
    let hell : ell + 1 = S.componentStart k := by
      dsimp only [ell]
      omega
    let pre := (S.sourcePrefixGoodBONG k hk T).castLength hell.symm
    (Lattice.weightIdealOrder P.space
        (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)) : ℚ) =
      min
        (((2 * ordUnit K c -
            a.order ⟨S.componentStart k - 1, by
              have hbound := (S.componentStart_lt_componentStop k).trans_le
                (S.componentStop_le k)
              omega⟩ : Int) : ℚ) +
          pre.alphaValue ⟨ell - 1, by omega⟩)
        (((2 * ordUnit K c -
            a.order ⟨S.componentStart k - 1, by
              have hbound := (S.componentStart_lt_componentStop k).trans_le
                (S.componentStop_le k)
              omega⟩ : Int) : ℚ) +
          (ramificationIndex K : ℚ)) := by
  dsimp only
  let D := S.sourceJordan.toOrthogonalDecomposition
  let P := D.prefixQuadraticSublattice k.val
  let ell := S.componentStart k - 1
  let hell : ell + 1 = S.componentStart k := by
    dsimp only [ell]
    omega
  let pre := (S.sourcePrefixGoodBONG k hk T).castLength hell.symm
  have hellPos : 0 < ell := by
    dsimp only [ell]
    omega
  obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hellPos)
  have hlen : ell + 1 = p + 2 := by omega
  let pre' := pre.castLength hlen
  have hweight := pre'.weightIdealOrder_rescale_dual c
  have hlastOrder : pre'.order ⟨p + 1, by omega⟩ =
      a.order ⟨S.componentStart k - 1, by
        have hbound := (S.componentStart_lt_componentStop k).trans_le
          (S.componentStop_le k)
        omega⟩ := by
    rw [show pre' = pre.castLength hlen by rfl,
      GoodBONG.order_castLength,
      show pre = (S.sourcePrefixGoodBONG k hk T).castLength hell.symm by rfl,
      GoodBONG.order_castLength]
    have h := S.sourcePrefixGoodBONG_order k hk T
      ⟨p + 1, by omega⟩
    calc
      (S.sourcePrefixGoodBONG k hk T).order ⟨p + 1, by omega⟩ =
          a.order ⟨p + 1, by
            have hstop := S.componentStop_le k
            have hbegin := S.componentStart_lt_componentStop k
            omega⟩ := h
      _ = a.order ⟨S.componentStart k - 1, by
          have hbound := (S.componentStart_lt_componentStop k).trans_le
            (S.componentStop_le k)
          omega⟩ := by
        apply congrArg a.order
        apply Fin.ext
        dsimp only
        omega
  have halpha : pre'.alphaValue ⟨p, by omega⟩ =
      pre.alphaValue ⟨ell - 1, by omega⟩ := by
    let halphaLen : ell = p + 1 := by omega
    have hproof : hlen = congrArg (fun z ↦ z + 1) halphaLen :=
      Subsingleton.elim _ _
    have hbase := GoodBONG.alphaValue_castLength_fundamental
      pre halphaLen ⟨p, by omega⟩
    have hpre' : pre' =
        pre.castLength (congrArg (fun z ↦ z + 1) halphaLen) := by
      dsimp only [pre']
    rw [hpre']
    calc
      (pre.castLength (congrArg (fun z ↦ z + 1) halphaLen)).alphaValue
          ⟨p, by omega⟩ =
          pre.alphaValue (Fin.cast halphaLen.symm ⟨p, by omega⟩) := hbase
      _ = pre.alphaValue ⟨ell - 1, by omega⟩ := by
        apply congrArg pre.alphaValue
        apply Fin.ext
        change p = ell - 1
        omega
  rw [hlastOrder, halpha] at hweight
  simpa only [D, P, ell, hell, pre, pre'] using hweight

/-- Corollary 2.5(ii) at the boundary before a noninitial component, when
both the actual prefix and suffix carry an alpha. -/
theorem sourcePredecessorAlpha_eq_min_four_local
    {n : Nat} {a : GoodBONG q L (n + 2)}
    {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (htwo : 2 ≤ S.componentStart k)
    (hright : S.componentStart k < n + 1) :
    let j : Fin (n + 1) := ⟨S.componentStart k - 1, by omega⟩
    let ell := S.componentStart k - 1
    let hell : ell + 1 = S.componentStart k := by
      dsimp only [ell]
      omega
    let pre := (S.sourcePrefixGoodBONG k hk T).castLength hell.symm
    let tail := n + 1 - S.componentStart k
    let htail : tail + 1 = n + 2 - S.componentStart k := by
      dsimp only [tail]
      omega
    let suf := (S.sourceSuffixGoodBONG k hk T).castLength htail.symm
    let g : ℚ := a.orderGap j
    let e : ℚ := ramificationIndex K
    let delta : WithTop ℚ := a.adjacentDefect j
    (a.alphaValue j : WithTop ℚ) =
      min (((g / 2 + e : ℚ) : WithTop ℚ))
        (min (((g : ℚ) : WithTop ℚ) + delta)
          (min (((g + pre.alphaValue ⟨ell - 1, by omega⟩ : ℚ) :
              WithTop ℚ))
            (((g + suf.alphaValue ⟨0, by omega⟩ : ℚ) :
              WithTop ℚ)))) := by
  dsimp only
  let j : Fin (n + 1) := ⟨S.componentStart k - 1, by omega⟩
  let ell := S.componentStart k - 1
  let hell : ell + 1 = S.componentStart k := by
    dsimp only [ell]
    omega
  let pre := (S.sourcePrefixGoodBONG k hk T).castLength hell.symm
  let tail := n + 1 - S.componentStart k
  let htail : tail + 1 = n + 2 - S.componentStart k := by
    dsimp only [tail]
    omega
  let suf := (S.sourceSuffixGoodBONG k hk T).castLength htail.symm
  let g : ℚ := a.orderGap j
  let e : ℚ := ramificationIndex K
  let delta : WithTop ℚ := a.adjacentDefect j
  have hleft : 0 < j.val := by
    dsimp only [j]
    omega
  have hrightJ : j.val + 1 < n + 1 := by
    dsimp only [j]
    have hstartPos : 0 < S.componentStart k := by omega
    omega
  have hglobal := a.alphaValue_eq_min_four_segmentCandidates
    j hleft hrightJ
  have hhalf : a.halfGapCandidate j =
      (((g / 2 + e : ℚ) : WithTop ℚ)) := by
    rfl
  have hdefect : a.leftDefectCandidate j j =
      ((g : WithTop ℚ) + delta) := by
    rfl
  have hprefixLocal :=
    S.sourcePrefixAlphaLast_eq_boundaryPrefixLocalAlpha k hk T htwo
  dsimp only at hprefixLocal
  have hprefix := a.prefixSegmentAlphaCandidate_eq_gap_add_alpha j hleft
  rw [← hprefixLocal] at hprefix
  have hprefix' : a.prefixSegmentAlphaCandidate j hleft =
      (((g + pre.alphaValue ⟨ell - 1, by omega⟩ : ℚ) :
        WithTop ℚ)) := by
    simpa only [g, pre, ell, WithTop.coe_eq_coe] using hprefix
  have hsuffixLocal :=
    S.sourceSuffixAlphaZero_eq_boundarySuffixLocalAlpha k hk T hright
  dsimp only at hsuffixLocal
  have hsuffix := a.suffixSegmentAlphaCandidate_eq_gap_add_alpha j hrightJ
  rw [← hsuffixLocal] at hsuffix
  have hsuffix' : a.suffixSegmentAlphaCandidate j hrightJ =
      (((g + suf.alphaValue ⟨0, by omega⟩ : ℚ) :
        WithTop ℚ)) := by
    simpa only [g, suf, WithTop.coe_eq_coe] using hsuffix
  rw [hglobal, hhalf, hdefect, hprefix', hsuffix']

private theorem alphaValue_eq_min_three_suffix_at_zero
    {n : Nat} (c : GoodBONG q L (n + 2))
    (i : Fin (n + 1)) (hzero : i.val = 0)
    (hright : i.val + 1 < n + 1) :
    (c.alphaValue i : WithTop ℚ) =
      min (c.halfGapCandidate i)
        (min (c.leftDefectCandidate i i)
          (c.suffixSegmentAlphaCandidate i hright)) := by
  have hn : 0 < n := by omega
  rw [c.coe_alphaValue, c.beli2009Corollary25_ii i]
  simp [GoodBONG.segmentRecursiveAlphaCandidates,
    GoodBONG.prefixSegmentAlphaCandidates,
    GoodBONG.suffixSegmentAlphaCandidates, hzero, hn]

private theorem alphaValue_eq_min_three_prefix_at_last
    {n : Nat} (c : GoodBONG q L (n + 2))
    (i : Fin (n + 1)) (hlast : i.val = n)
    (hleft : 0 < i.val) :
    (c.alphaValue i : WithTop ℚ) =
      min (c.halfGapCandidate i)
        (min (c.leftDefectCandidate i i)
          (c.prefixSegmentAlphaCandidate i hleft)) := by
  have hnotright : ¬ i.val + 1 < n + 1 := by omega
  rw [c.coe_alphaValue, c.beli2009Corollary25_ii i]
  simp [GoodBONG.segmentRecursiveAlphaCandidates,
    GoodBONG.prefixSegmentAlphaCandidates,
    GoodBONG.suffixSegmentAlphaCandidates, hleft, hnotright]

private theorem alphaValue_eq_min_two_at_only_boundary
    {n : Nat} (c : GoodBONG q L (n + 2))
    (i : Fin (n + 1)) (hzero : i.val = 0) (hlast : i.val = n) :
    (c.alphaValue i : WithTop ℚ) =
      min (c.halfGapCandidate i) (c.leftDefectCandidate i i) := by
  have hnotleft : ¬ 0 < i.val := by omega
  have hnotright : ¬ i.val + 1 < n + 1 := by omega
  rw [c.coe_alphaValue, c.beli2009Corollary25_ii i]
  simp [GoodBONG.segmentRecursiveAlphaCandidates,
    GoodBONG.prefixSegmentAlphaCandidates,
    GoodBONG.suffixSegmentAlphaCandidates, hnotleft, hnotright]

theorem sourcePredecessorAlpha_eq_min_four_local_prefix_unary
    {n : Nat} {a : GoodBONG q L (n + 2)}
    {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (hstart : S.componentStart k = 1)
    (hright : S.componentStart k < n + 1) :
    let j : Fin (n + 1) := ⟨S.componentStart k - 1, by omega⟩
    let tail := n + 1 - S.componentStart k
    let htail : tail + 1 = n + 2 - S.componentStart k := by
      dsimp only [tail]
      omega
    let suf := (S.sourceSuffixGoodBONG k hk T).castLength htail.symm
    let g : ℚ := a.orderGap j
    let e : ℚ := ramificationIndex K
    let delta : WithTop ℚ := a.adjacentDefect j
    (a.alphaValue j : WithTop ℚ) =
      min (((g / 2 + e : ℚ) : WithTop ℚ))
        (min (((g : ℚ) : WithTop ℚ) + delta)
          (min (((g + e : ℚ) : WithTop ℚ))
            (((g + suf.alphaValue ⟨0, by omega⟩ : ℚ) :
              WithTop ℚ)))) := by
  dsimp only
  let j : Fin (n + 1) := ⟨S.componentStart k - 1, by omega⟩
  let tail := n + 1 - S.componentStart k
  let htail : tail + 1 = n + 2 - S.componentStart k := by
    dsimp only [tail]
    omega
  let suf := (S.sourceSuffixGoodBONG k hk T).castLength htail.symm
  let g : ℚ := a.orderGap j
  let e : ℚ := ramificationIndex K
  let delta : WithTop ℚ := a.adjacentDefect j
  have hrightJ : j.val + 1 < n + 1 := by
    dsimp only [j]
    omega
  have hglobal := alphaValue_eq_min_three_suffix_at_zero
    a j (by dsimp only [j]; omega) hrightJ
  have hhalf : a.halfGapCandidate j =
      (((g / 2 + e : ℚ) : WithTop ℚ)) := by
    rfl
  have hdefect : a.leftDefectCandidate j j =
      ((g : WithTop ℚ) + delta) := by
    rfl
  have hsuffixLocal :=
    S.sourceSuffixAlphaZero_eq_boundarySuffixLocalAlpha k hk T hright
  dsimp only at hsuffixLocal
  have hsuffix := a.suffixSegmentAlphaCandidate_eq_gap_add_alpha j hrightJ
  rw [← hsuffixLocal] at hsuffix
  have hsuffix' : a.suffixSegmentAlphaCandidate j hrightJ =
      (((g + suf.alphaValue ⟨0, by omega⟩ : ℚ) :
        WithTop ℚ)) := by
    simpa only [g, suf, WithTop.coe_eq_coe] using hsuffix
  rw [hglobal, hhalf, hdefect, hsuffix']
  have horder := S.source_order_before_component_le_start k hk
  have hgap : 0 ≤ g := by
    have horder' : a.order j.castSucc ≤ a.order j.succ := by
      have hjcast : j.castSucc =
          ⟨S.componentStart k - 1, by omega⟩ := by
        apply Fin.ext
        rfl
      have hjsucc : j.succ =
          ⟨S.componentStart k, by
            exact (S.componentStart_lt_componentStop k).trans_le
              (S.componentStop_le k)⟩ := by
        apply Fin.ext
        change S.componentStart k - 1 + 1 = S.componentStart k
        omega
      rw [hjcast, hjsucc]
      exact horder
    dsimp only [g, GoodBONG.orderGap]
    exact_mod_cast sub_nonneg.mpr horder'
  have hdom : (((g / 2 + e : ℚ) : WithTop ℚ)) ≤
      (((g + e : ℚ) : WithTop ℚ)) := by
    exact_mod_cast (by linarith : g / 2 + e ≤ g + e)
  change
    min (((g / 2 + e : ℚ) : WithTop ℚ))
        (min (((g : ℚ) : WithTop ℚ) + delta)
          (((g + suf.alphaValue ⟨0, by omega⟩ : ℚ) : WithTop ℚ))) =
      min (((g / 2 + e : ℚ) : WithTop ℚ))
        (min (((g : ℚ) : WithTop ℚ) + delta)
          (min (((g + e : ℚ) : WithTop ℚ))
            (((g + suf.alphaValue ⟨0, by omega⟩ : ℚ) :
              WithTop ℚ))))
  calc
    min (((g / 2 + e : ℚ) : WithTop ℚ))
        (min (((g : ℚ) : WithTop ℚ) + delta)
          (((g + suf.alphaValue ⟨0, by omega⟩ : ℚ) : WithTop ℚ))) =
        min
          (min (((g / 2 + e : ℚ) : WithTop ℚ))
            (((g + e : ℚ) : WithTop ℚ)))
          (min (((g : ℚ) : WithTop ℚ) + delta)
            (((g + suf.alphaValue ⟨0, by omega⟩ : ℚ) :
              WithTop ℚ))) := by
      rw [min_eq_left hdom]
    _ = _ := by ac_rfl

theorem sourcePredecessorAlpha_eq_min_four_local_suffix_terminal
    {n : Nat} {a : GoodBONG q L (n + 2)}
    {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (htwo : 2 ≤ S.componentStart k)
    (hterminal : n + 2 - S.componentStart k = 1) :
    let j : Fin (n + 1) := ⟨S.componentStart k - 1, by omega⟩
    let ell := S.componentStart k - 1
    let hell : ell + 1 = S.componentStart k := by
      dsimp only [ell]
      omega
    let pre := (S.sourcePrefixGoodBONG k hk T).castLength hell.symm
    let g : ℚ := a.orderGap j
    let e : ℚ := ramificationIndex K
    let delta : WithTop ℚ := a.adjacentDefect j
    (a.alphaValue j : WithTop ℚ) =
      min (((g / 2 + e : ℚ) : WithTop ℚ))
        (min (((g : ℚ) : WithTop ℚ) + delta)
          (min (((g + pre.alphaValue ⟨ell - 1, by omega⟩ : ℚ) :
              WithTop ℚ))
            (((g + e : ℚ) : WithTop ℚ)))) := by
  dsimp only
  let j : Fin (n + 1) := ⟨S.componentStart k - 1, by omega⟩
  let ell := S.componentStart k - 1
  let hell : ell + 1 = S.componentStart k := by
    dsimp only [ell]
    omega
  let pre := (S.sourcePrefixGoodBONG k hk T).castLength hell.symm
  let g : ℚ := a.orderGap j
  let e : ℚ := ramificationIndex K
  let delta : WithTop ℚ := a.adjacentDefect j
  have hlast : j.val = n := by
    dsimp only [j]
    have hbound := (S.componentStart_lt_componentStop k).trans_le
      (S.componentStop_le k)
    omega
  have hleft : 0 < j.val := by
    dsimp only [j]
    omega
  have hglobal := alphaValue_eq_min_three_prefix_at_last
    a j hlast hleft
  have hhalf : a.halfGapCandidate j =
      (((g / 2 + e : ℚ) : WithTop ℚ)) := by
    rfl
  have hdefect : a.leftDefectCandidate j j =
      ((g : WithTop ℚ) + delta) := by
    rfl
  have hprefixLocal :=
    S.sourcePrefixAlphaLast_eq_boundaryPrefixLocalAlpha k hk T htwo
  dsimp only at hprefixLocal
  have hprefix := a.prefixSegmentAlphaCandidate_eq_gap_add_alpha j hleft
  rw [← hprefixLocal] at hprefix
  have hprefix' : a.prefixSegmentAlphaCandidate j hleft =
      (((g + pre.alphaValue ⟨ell - 1, by omega⟩ : ℚ) :
        WithTop ℚ)) := by
    simpa only [g, pre, ell, WithTop.coe_eq_coe] using hprefix
  rw [hglobal, hhalf, hdefect, hprefix']
  have horder := S.source_order_before_component_le_start k hk
  have hgap : 0 ≤ g := by
    have horder' : a.order j.castSucc ≤ a.order j.succ := by
      have hjcast : j.castSucc =
          ⟨S.componentStart k - 1, by omega⟩ := by
        apply Fin.ext
        rfl
      have hjsucc : j.succ =
          ⟨S.componentStart k, by
            exact (S.componentStart_lt_componentStop k).trans_le
              (S.componentStop_le k)⟩ := by
        apply Fin.ext
        change S.componentStart k - 1 + 1 = S.componentStart k
        omega
      rw [hjcast, hjsucc]
      exact horder
    dsimp only [g, GoodBONG.orderGap]
    exact_mod_cast sub_nonneg.mpr horder'
  have hdom : (((g / 2 + e : ℚ) : WithTop ℚ)) ≤
      (((g + e : ℚ) : WithTop ℚ)) := by
    exact_mod_cast (by linarith : g / 2 + e ≤ g + e)
  change
    min (((g / 2 + e : ℚ) : WithTop ℚ))
        (min (((g : ℚ) : WithTop ℚ) + delta)
          (((g + pre.alphaValue ⟨ell - 1, by omega⟩ : ℚ) :
            WithTop ℚ))) =
      min (((g / 2 + e : ℚ) : WithTop ℚ))
        (min (((g : ℚ) : WithTop ℚ) + delta)
          (min (((g + pre.alphaValue ⟨ell - 1, by omega⟩ : ℚ) :
              WithTop ℚ))
            (((g + e : ℚ) : WithTop ℚ))))
  calc
    min (((g / 2 + e : ℚ) : WithTop ℚ))
        (min (((g : ℚ) : WithTop ℚ) + delta)
          (((g + pre.alphaValue ⟨ell - 1, by omega⟩ : ℚ) :
            WithTop ℚ))) =
        min
          (min (((g / 2 + e : ℚ) : WithTop ℚ))
            (((g + e : ℚ) : WithTop ℚ)))
          (min (((g : ℚ) : WithTop ℚ) + delta)
            (((g + pre.alphaValue ⟨ell - 1, by omega⟩ : ℚ) :
              WithTop ℚ))) := by
      rw [min_eq_left hdom]
    _ = _ := by ac_rfl

theorem sourcePredecessorAlpha_eq_min_four_local_both_unary
    {n : Nat} {a : GoodBONG q L (n + 2)}
    {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (hstart : S.componentStart k = 1)
    (hterminal : n + 2 - S.componentStart k = 1) :
    let j : Fin (n + 1) := ⟨S.componentStart k - 1, by omega⟩
    let g : ℚ := a.orderGap j
    let e : ℚ := ramificationIndex K
    let delta : WithTop ℚ := a.adjacentDefect j
    (a.alphaValue j : WithTop ℚ) =
      min (((g / 2 + e : ℚ) : WithTop ℚ))
        (min (((g : ℚ) : WithTop ℚ) + delta)
          (min (((g + e : ℚ) : WithTop ℚ))
            (((g + e : ℚ) : WithTop ℚ)))) := by
  dsimp only
  let j : Fin (n + 1) := ⟨S.componentStart k - 1, by omega⟩
  let g : ℚ := a.orderGap j
  let e : ℚ := ramificationIndex K
  let delta : WithTop ℚ := a.adjacentDefect j
  have hlast : j.val = n := by
    dsimp only [j]
    have hbound := (S.componentStart_lt_componentStop k).trans_le
      (S.componentStop_le k)
    omega
  have hglobal := alphaValue_eq_min_two_at_only_boundary
    a j (by dsimp only [j]; omega) hlast
  have hhalf : a.halfGapCandidate j =
      (((g / 2 + e : ℚ) : WithTop ℚ)) := by
    rfl
  have hdefect : a.leftDefectCandidate j j =
      ((g : WithTop ℚ) + delta) := by
    rfl
  rw [hglobal, hhalf, hdefect]
  have horder := S.source_order_before_component_le_start k hk
  have hgap : 0 ≤ g := by
    have horder' : a.order j.castSucc ≤ a.order j.succ := by
      have hjcast : j.castSucc =
          ⟨S.componentStart k - 1, by omega⟩ := by
        apply Fin.ext
        rfl
      have hjsucc : j.succ =
          ⟨S.componentStart k, by
            exact (S.componentStart_lt_componentStop k).trans_le
              (S.componentStop_le k)⟩ := by
        apply Fin.ext
        change S.componentStart k - 1 + 1 = S.componentStart k
        omega
      rw [hjcast, hjsucc]
      exact horder
    dsimp only [g, GoodBONG.orderGap]
    exact_mod_cast sub_nonneg.mpr horder'
  have hdom : (((g / 2 + e : ℚ) : WithTop ℚ)) ≤
      (((g + e : ℚ) : WithTop ℚ)) := by
    exact_mod_cast (by linarith : g / 2 + e ≤ g + e)
  change
    min (((g / 2 + e : ℚ) : WithTop ℚ))
        (((g : ℚ) : WithTop ℚ) + delta) =
      min (((g / 2 + e : ℚ) : WithTop ℚ))
        (min (((g : ℚ) : WithTop ℚ) + delta)
          (min (((g + e : ℚ) : WithTop ℚ))
            (((g + e : ℚ) : WithTop ℚ))))
  calc
    min (((g / 2 + e : ℚ) : WithTop ℚ))
        (((g : ℚ) : WithTop ℚ) + delta) =
        min
          (min (((g / 2 + e : ℚ) : WithTop ℚ))
            (((g + e : ℚ) : WithTop ℚ)))
          (min (((g : ℚ) : WithTop ℚ) + delta)
            (((g + e : ℚ) : WithTop ℚ))) := by
      rw [min_eq_left hdom, ← min_assoc,
        min_eq_left ((min_le_left _ _).trans hdom)]
    _ = _ := by ac_rfl

/-- Beli's Lemma 2.15 in order form for a terminal unary Jordan component. -/
theorem sourceFundamentalWeightOrder_eq_order_add_min_alpha_e_of_unary_terminal
    {n : Nat} {a : GoodBONG q L (n + 2)}
    {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (hrank : S.sourceJordan.toOrthogonalDecomposition.componentRank k = 1)
    (hterminal : n + 2 - S.componentStart k = 1) :
    let i : Fin (n + 2) := ⟨S.componentStart k, by
      exact (S.componentStart_lt_componentStop k).trans_le
        (S.componentStop_le k)⟩
    let j : Fin (n + 1) := ⟨S.componentStart k - 1, by
      have hbound := (S.componentStart_lt_componentStop k).trans_le
        (S.componentStop_le k)
      omega⟩
    ((Lattice.weightIdealOrder q
        (S.sourceJordan.fundamentalLattice k) : Int) : ℚ) =
      (a.order i : ℚ) +
        min (a.alphaValue j) (ramificationIndex K : ℚ) := by
  dsimp only
  have hstartPos : 0 < S.componentStart k := by
    unfold componentStart
    let p : Fin S.componentCount := ⟨k.val - 1, by omega⟩
    have hp : p ∈ Finset.Iio k := by
      simp only [Finset.mem_Iio]
      change k.val - 1 < k.val
      omega
    have hle := Finset.single_le_sum
      (s := Finset.Iio k)
      (f := fun z ↦
        S.sourceJordan.toOrthogonalDecomposition.componentRank z)
      (fun _ _ ↦ Nat.zero_le _) hp
    exact (S.sourceJordan.component_finrank_pos p).trans_le hle
  let i : Fin (n + 2) := ⟨S.componentStart k, by
    exact (S.componentStart_lt_componentStop k).trans_le
      (S.componentStop_le k)⟩
  let j : Fin (n + 1) := ⟨S.componentStart k - 1, by
    have hbound := (S.componentStart_lt_componentStop k).trans_le
      (S.componentStop_le k)
    omega⟩
  let A : ℚ := a.order j.castSucc
  let B : ℚ := a.order i
  let g : ℚ := a.orderGap j
  let e : ℚ := ramificationIndex K
  let delta : WithTop ℚ := a.adjacentDefect j
  let D := S.sourceJordan.toOrthogonalDecomposition
  let P := D.prefixQuadraticSublattice k.val
  let U := D.suffixQuadraticSublattice k.val
  let c := Lattice.scaleTruncationUnit (K := K)
    (ordUnit K (S.sourceJordan.scaleGenerator k))
  have hjsucc : j.succ = i := by
    apply Fin.ext
    change S.componentStart k - 1 + 1 = S.componentStart k
    omega
  have hjcast : j.castSucc =
      ⟨S.componentStart k - 1, by
        have hbound := (S.componentStart_lt_componentStop k).trans_le
          (S.componentStop_le k)
        omega⟩ := by
    apply Fin.ext
    rfl
  have hscaleBase :=
    S.sourceOrder_componentStart_eq_scaleOrder_of_unary k hrank
  have hscale : a.order i = ordUnit K (S.sourceJordan.scaleGenerator k) := by
    simpa only [i] using hscaleBase
  have hc : ordUnit K c = a.order i := by
    dsimp only [c]
    rw [Lattice.scaleTruncationUnit, ordUnit_uniformizerPowerUnit]
    exact hscale.symm
  have hgapEq : g = B - A := by
    dsimp only [g, GoodBONG.orderGap]
    rw [hjsucc]
    dsimp only [B, A]
    push_cast
    ring
  have horder := S.source_order_before_component_le_start k hk
  have hgap : 0 ≤ g := by
    have horder' : a.order j.castSucc ≤ a.order i := by
      have hjcast : j.castSucc =
          ⟨S.componentStart k - 1, by omega⟩ := by
        apply Fin.ext
        rfl
      rw [hjcast]
      simpa only [i] using horder
    dsimp only [g, GoodBONG.orderGap]
    have hji : j.succ = i := by
      exact hjsucc
    rw [hji]
    exact_mod_cast sub_nonneg.mpr horder'
  have hsuffixInt :=
    S.sourceSuffix_weightIdealOrder_unary k hk T hterminal
  have hsuffixQ : (Lattice.weightIdealOrder U.space U.lattice : ℚ) =
      B + e := by
    have hcast := congrArg (fun z : Int ↦ (z : ℚ)) hsuffixInt
    push_cast at hcast
    simpa only [D, U, B, e, i] using hcast
  have hsuffixTop :
      ((((Lattice.weightIdealOrder U.space U.lattice : Int) : ℚ) :
        WithTop ℚ)) = (((B + e : ℚ) : WithTop ℚ)) :=
    congrArg (fun z : ℚ ↦ (z : WithTop ℚ)) hsuffixQ
  have hsplit := S.sourceFundamentalWeightOrder_eq_min_split k hk T
  have hcross :
      (((((2 * ordUnit K (S.sourceJordan.scaleGenerator k) -
          a.order j.castSucc : Int) : ℚ) : WithTop ℚ)) + delta) =
        (((B + g : ℚ) : WithTop ℚ) + delta) := by
    congr 1
    norm_cast
    push_cast
    have hscaleQ : (ordUnit K (S.sourceJordan.scaleGenerator k) : ℚ) = B := by
      dsimp only [B]
      exact_mod_cast hscale.symm
    rw [hscaleQ]
    change 2 * B - A = B + g
    linarith [hgapEq]
  by_cases hprefixUnary : S.componentStart k = 1
  · have hprefixInt :=
      S.sourcePrefix_rescaleDual_weightIdealOrder_unary
        k hk T hprefixUnary c
    have hprefixQ :
        (Lattice.weightIdealOrder P.space
          (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)) : ℚ) =
          B + g + e := by
      have hcast := congrArg (fun z : Int ↦ (z : ℚ)) hprefixInt
      push_cast at hcast
      rw [hc] at hcast
      rw [← hjcast] at hcast
      dsimp only [D, P, B, e, A] at hcast ⊢
      linarith [hgapEq]
    have hprefixTop :
        ((((Lattice.weightIdealOrder P.space
          (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)) :
            Int) : ℚ) : WithTop ℚ)) =
          (((B + g + e : ℚ) : WithTop ℚ)) :=
      congrArg (fun z : ℚ ↦ (z : WithTop ℚ)) hprefixQ
    have halpha :=
      S.sourcePredecessorAlpha_eq_min_four_local_both_unary
        k hk hprefixUnary hterminal
    dsimp only at halpha
    have hminimum := unarySplitMinimum_eq
      B g e e e (a.alphaValue j) delta hgap halpha
    have hsplit' := hsplit
    dsimp only [D, P, U, c, j, delta] at hsplit'
    rw [hsuffixTop, hprefixTop, hcross] at hsplit'
    have hfinalTop :
        ((((Lattice.weightIdealOrder q
          (S.sourceJordan.fundamentalLattice k) : Int) : ℚ) :
            WithTop ℚ)) =
          (((B + min (a.alphaValue j) e : ℚ) : WithTop ℚ)) := by
      calc
        ((((Lattice.weightIdealOrder q
            (S.sourceJordan.fundamentalLattice k) : Int) : ℚ) :
              WithTop ℚ)) =
            min
              (min (((B + e : ℚ) : WithTop ℚ))
                (((B + g + e : ℚ) : WithTop ℚ)))
              (((B + g : ℚ) : WithTop ℚ) + delta) := hsplit'
        _ = (((B + min (a.alphaValue j) e : ℚ) : WithTop ℚ)) := by
          simpa only [min_self, min_assoc] using hminimum
    exact WithTop.coe_eq_coe.mp hfinalTop
  · have htwo : 2 ≤ S.componentStart k := by omega
    let ell := S.componentStart k - 1
    let hell : ell + 1 = S.componentStart k := by
      dsimp only [ell]
      omega
    let pre := (S.sourcePrefixGoodBONG k hk T).castLength hell.symm
    let alphaPrefix : ℚ := pre.alphaValue ⟨ell - 1, by omega⟩
    have hprefixBase :=
      S.sourcePrefix_rescaleDual_weightIdealOrder_nonunary
        k hk T htwo c
    dsimp only at hprefixBase
    have hprefixQ :
        (Lattice.weightIdealOrder P.space
          (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)) : ℚ) =
          min (B + g + alphaPrefix) (B + g + e) := by
      rw [hc] at hprefixBase
      push_cast at hprefixBase
      rw [← hjcast] at hprefixBase
      dsimp only [D, P, B, e, A, alphaPrefix, pre, ell, hell]
        at hprefixBase ⊢
      rw [hprefixBase]
      congr 1 <;> linarith [hgapEq]
    have hprefixTop :
        ((((Lattice.weightIdealOrder P.space
          (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)) :
            Int) : ℚ) : WithTop ℚ)) =
          min (((B + g + alphaPrefix : ℚ) : WithTop ℚ))
            (((B + g + e : ℚ) : WithTop ℚ)) := by
      have hcast := congrArg (fun z : ℚ ↦ (z : WithTop ℚ)) hprefixQ
      simpa only [WithTop.coe_min] using hcast
    have halphaBase :=
      S.sourcePredecessorAlpha_eq_min_four_local_suffix_terminal
        k hk T htwo hterminal
    dsimp only at halphaBase
    have halpha : (a.alphaValue j : WithTop ℚ) =
        min (((g / 2 + e : ℚ) : WithTop ℚ))
          (min (((g : ℚ) : WithTop ℚ) + delta)
            (min (((g + alphaPrefix : ℚ) : WithTop ℚ))
              (((g + e : ℚ) : WithTop ℚ)))) := by
      simpa only [j, g, e, delta, alphaPrefix, pre, ell, hell] using halphaBase
    have hminimum := unarySplitMinimum_eq
      B g e alphaPrefix e (a.alphaValue j) delta hgap halpha
    have hsplit' := hsplit
    dsimp only [D, P, U, c, j, delta] at hsplit'
    rw [hsuffixTop, hprefixTop, hcross] at hsplit'
    have hfinalTop :
        ((((Lattice.weightIdealOrder q
          (S.sourceJordan.fundamentalLattice k) : Int) : ℚ) :
            WithTop ℚ)) =
          (((B + min (a.alphaValue j) e : ℚ) : WithTop ℚ)) := by
      calc
        ((((Lattice.weightIdealOrder q
            (S.sourceJordan.fundamentalLattice k) : Int) : ℚ) :
              WithTop ℚ)) =
            min
              (min (((B + e : ℚ) : WithTop ℚ))
                (min (((B + g + alphaPrefix : ℚ) : WithTop ℚ))
                  (((B + g + e : ℚ) : WithTop ℚ))))
              (((B + g : ℚ) : WithTop ℚ) + delta) := hsplit'
        _ = (((B + min (a.alphaValue j) e : ℚ) : WithTop ℚ)) := by
          simpa only [min_self, min_assoc] using hminimum
    exact WithTop.coe_eq_coe.mp hfinalTop

/-- At a nonterminal unary component, capping the actual suffix alpha by
the predecessor alpha is the same as capping the next global alpha. -/
theorem source_min_predecessor_suffixAlpha_eq_min_neighborAlphas
    {n : Nat} {a : GoodBONG q L (n + 2)}
    {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (hrank : S.sourceJordan.toOrthogonalDecomposition.componentRank k = 1)
    (hright : S.componentStart k < n + 1) :
    let i : Fin (n + 1) := ⟨S.componentStart k, hright⟩
    let j : Fin (n + 1) := ⟨S.componentStart k - 1, by omega⟩
    let p := n - S.componentStart k
    let hp : p + 2 = n + 2 - S.componentStart k := by
      dsimp only [p]
      omega
    let suffix := (S.sourceSuffixGoodBONG k hk T).castLength hp.symm
    min (a.alphaValue j) (suffix.alphaValue ⟨0, by omega⟩) =
      min (a.alphaValue j) (a.alphaValue i) := by
  dsimp only
  let i : Fin (n + 1) := ⟨S.componentStart k, hright⟩
  let j : Fin (n + 1) := ⟨S.componentStart k - 1, by omega⟩
  let p := n - S.componentStart k
  let hp : p + 2 = n + 2 - S.componentStart k := by
    dsimp only [p]
    omega
  let suffix := (S.sourceSuffixGoodBONG k hk T).castLength hp.symm
  have hleft : 0 < i.val := by
    dsimp only [i]
    unfold componentStart
    let previous : Fin S.componentCount := ⟨k.val - 1, by omega⟩
    have hprevious : previous ∈ Finset.Iio k := by
      simp only [Finset.mem_Iio]
      change k.val - 1 < k.val
      omega
    have hle := Finset.single_le_sum
      (s := Finset.Iio k)
      (f := fun z ↦
        S.sourceJordan.toOrthogonalDecomposition.componentRank z)
      (fun _ _ ↦ Nat.zero_le _) hprevious
    exact (S.sourceJordan.component_finrank_pos previous).trans_le hle
  have hvalues : ∀ z, suffix.valueUnit z =
      a.valueUnit ⟨i.val + z.val, by
        dsimp only [i, p]
        have hz := z.isLt
        omega⟩ := by
    intro z
    rw [show suffix = (S.sourceSuffixGoodBONG k hk T).castLength hp.symm by rfl,
      GoodBONG.valueUnit_castLength_fundamental,
      S.sourceSuffixGoodBONG_valueUnit]
  have hnextAlpha := a.alphaValue_eq_min_prefix_suffix
    i hleft suffix hp hvalues
  have hpredecessorLocal :=
    a.predecessorAlphaValue_le_prefixLocalAlpha i hleft
  let loc := GoodBONG.prefixAlphaLocalizationIndex i hleft
  let localAlpha : ℚ :=
    ((a.prefixAlphaSegmentWitness i hleft).toGoodBONG a.good).alphaValue
      loc.localPivot
  have hjpred :
      (⟨i.val - 1, by omega⟩ : Fin (n + 1)) = j := by
    apply Fin.ext
    dsimp only [i, j]
  have hlocalLe : a.alphaValue j ≤ localAlpha := by
    rw [← hjpred]
    simpa only [loc, localAlpha] using hpredecessorLocal
  have hstop : S.componentStop k < n + 2 := by
    unfold componentStop
    rw [hrank]
    omega
  have hnextOrder :=
    S.source_order_componentStart_le_after_of_unary_nonterminal
      k hrank hstop
  have hgapNext : 0 ≤ (a.orderGap i : ℚ) := by
    unfold GoodBONG.orderGap
    have hiCast : i.castSucc =
        ⟨S.componentStart k, by
          exact (S.componentStart_lt_componentStop k).trans_le
            (S.componentStop_le k)⟩ := by
      apply Fin.ext
      rfl
    have hiSucc : i.succ =
        ⟨S.componentStart k + 1, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hiCast, hiSucc]
    exact_mod_cast sub_nonneg.mpr hnextOrder
  have hprefixFormula :=
    a.prefixSegmentAlphaCandidate_eq_gap_add_alpha i hleft
  have hprefixLeQ : a.alphaValue j ≤
      (a.orderGap i : ℚ) + localAlpha := by
    linarith
  have hprefixLe : (a.alphaValue j : WithTop ℚ) ≤
      a.prefixSegmentAlphaCandidate i hleft := by
    rw [hprefixFormula]
    exact_mod_cast hprefixLeQ
  have htop :
      min (a.alphaValue j : WithTop ℚ)
          (suffix.alphaValue ⟨0, by omega⟩ : WithTop ℚ) =
        min (a.alphaValue j : WithTop ℚ)
          (a.alphaValue i : WithTop ℚ) := by
    calc
      min (a.alphaValue j : WithTop ℚ)
          (suffix.alphaValue ⟨0, by omega⟩ : WithTop ℚ) =
          min
            (min (a.alphaValue j : WithTop ℚ)
              (a.prefixSegmentAlphaCandidate i hleft))
            (suffix.alphaValue ⟨0, by omega⟩ : WithTop ℚ) := by
        rw [min_eq_left hprefixLe]
      _ = min (a.alphaValue j : WithTop ℚ)
          (min (a.prefixSegmentAlphaCandidate i hleft)
            (suffix.alphaValue ⟨0, by omega⟩ : WithTop ℚ)) := by
        rw [min_assoc]
      _ = min (a.alphaValue j : WithTop ℚ)
          (a.alphaValue i : WithTop ℚ) := by
        rw [← hnextAlpha]
  exact WithTop.coe_eq_coe.mp (by simpa only [WithTop.coe_min] using htop)

/-- Beli's Lemma 2.15 in order form for a nonterminal unary Jordan
component, with both neighboring global alpha invariants displayed. -/
theorem sourceFundamentalWeightOrder_eq_order_add_min_neighborAlphas_e_of_unary
    {n : Nat} {a : GoodBONG q L (n + 2)}
    {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (hrank : S.sourceJordan.toOrthogonalDecomposition.componentRank k = 1)
    (hright : S.componentStart k < n + 1) :
    let i : Fin (n + 1) := ⟨S.componentStart k, hright⟩
    let j : Fin (n + 1) := ⟨S.componentStart k - 1, by omega⟩
    ((Lattice.weightIdealOrder q
        (S.sourceJordan.fundamentalLattice k) : Int) : ℚ) =
      (a.order i.castSucc : ℚ) +
        min (a.alphaValue j)
          (min (a.alphaValue i) (ramificationIndex K : ℚ)) := by
  dsimp only
  have hstartPos : 0 < S.componentStart k := by
    unfold componentStart
    let previous : Fin S.componentCount := ⟨k.val - 1, by omega⟩
    have hprevious : previous ∈ Finset.Iio k := by
      simp only [Finset.mem_Iio]
      change k.val - 1 < k.val
      omega
    have hle := Finset.single_le_sum
      (s := Finset.Iio k)
      (f := fun z ↦
        S.sourceJordan.toOrthogonalDecomposition.componentRank z)
      (fun _ _ ↦ Nat.zero_le _) hprevious
    exact (S.sourceJordan.component_finrank_pos previous).trans_le hle
  let i : Fin (n + 1) := ⟨S.componentStart k, hright⟩
  let j : Fin (n + 1) := ⟨S.componentStart k - 1, by omega⟩
  let iB : Fin (n + 2) := i.castSucc
  let A : ℚ := a.order j.castSucc
  let B : ℚ := a.order iB
  let g : ℚ := a.orderGap j
  let e : ℚ := ramificationIndex K
  let delta : WithTop ℚ := a.adjacentDefect j
  let p := n - S.componentStart k
  let hp : p + 2 = n + 2 - S.componentStart k := by
    dsimp only [p]
    omega
  let suffix := (S.sourceSuffixGoodBONG k hk T).castLength hp.symm
  let alphaSuffix : ℚ := suffix.alphaValue ⟨0, by omega⟩
  let tail := n + 1 - S.componentStart k
  let htail : tail + 1 = n + 2 - S.componentStart k := by
    dsimp only [tail]
    omega
  let suffixLocal :=
    (S.sourceSuffixGoodBONG k hk T).castLength htail.symm
  have htailAlpha : tail = p + 1 := by
    dsimp only [tail, p]
    omega
  have hsuffixValues : ∀ z, suffixLocal.valueUnit z =
      suffix.valueUnit
        (Fin.cast (congrArg (fun x ↦ x + 1) htailAlpha) z) := by
    intro z
    rw [show suffixLocal =
        (S.sourceSuffixGoodBONG k hk T).castLength htail.symm by rfl,
      show suffix =
        (S.sourceSuffixGoodBONG k hk T).castLength hp.symm by rfl,
      GoodBONG.valueUnit_castLength_fundamental,
      GoodBONG.valueUnit_castLength_fundamental]
    apply congrArg (S.sourceSuffixGoodBONG k hk T).valueUnit
    apply Fin.ext
    rfl
  have hsuffixAlphaCast := GoodBONG.alphaValue_eq_of_valueUnits_eq_cast
    suffixLocal suffix htailAlpha hsuffixValues
      (⟨0, by dsimp only [tail]; omega⟩ : Fin tail)
  have hsuffixAlphaLocal : suffixLocal.alphaValue
        ⟨0, by dsimp only [tail]; omega⟩ = alphaSuffix := by
    dsimp only [alphaSuffix]
    calc
      suffixLocal.alphaValue ⟨0, by dsimp only [tail]; omega⟩ =
          suffix.alphaValue
            (Fin.cast htailAlpha
              (⟨0, by dsimp only [tail]; omega⟩ : Fin tail)) :=
        hsuffixAlphaCast
      _ = suffix.alphaValue ⟨0, by omega⟩ := by
        apply congrArg suffix.alphaValue
        apply Fin.ext
        rfl
  let D := S.sourceJordan.toOrthogonalDecomposition
  let P := D.prefixQuadraticSublattice k.val
  let U := D.suffixQuadraticSublattice k.val
  let c := Lattice.scaleTruncationUnit (K := K)
    (ordUnit K (S.sourceJordan.scaleGenerator k))
  have hiBGlobal : iB =
      ⟨S.componentStart k, by
        exact (S.componentStart_lt_componentStop k).trans_le
          (S.componentStop_le k)⟩ := by
    apply Fin.ext
    rfl
  have hjsucc : j.succ = iB := by
    apply Fin.ext
    change S.componentStart k - 1 + 1 = S.componentStart k
    omega
  have hjcast : j.castSucc =
      ⟨S.componentStart k - 1, by
        have hbound := (S.componentStart_lt_componentStop k).trans_le
          (S.componentStop_le k)
        omega⟩ := by
    apply Fin.ext
    rfl
  have hscaleBase :=
    S.sourceOrder_componentStart_eq_scaleOrder_of_unary k hrank
  have hscale : a.order iB = ordUnit K (S.sourceJordan.scaleGenerator k) := by
    rw [hiBGlobal]
    exact hscaleBase
  have hc : ordUnit K c = a.order iB := by
    dsimp only [c]
    rw [Lattice.scaleTruncationUnit, ordUnit_uniformizerPowerUnit]
    exact hscale.symm
  have hgapEq : g = B - A := by
    dsimp only [g, GoodBONG.orderGap]
    rw [hjsucc]
    dsimp only [B, A]
    push_cast
    ring
  have horder := S.source_order_before_component_le_start k hk
  have hgap : 0 ≤ g := by
    have horder' : a.order j.castSucc ≤ a.order iB := by
      rw [hjcast, hiBGlobal]
      exact horder
    dsimp only [g, GoodBONG.orderGap]
    rw [hjsucc]
    exact_mod_cast sub_nonneg.mpr horder'
  have hsuffixBase :=
    S.sourceSuffix_weightIdealOrder_general k hk T p hp
  dsimp only at hsuffixBase
  have hsuffixQ : (Lattice.weightIdealOrder U.space U.lattice : ℚ) =
      min (B + alphaSuffix) (B + e) := by
    have hBGlobal :
        (a.order ⟨S.componentStart k, by
          exact (S.componentStart_lt_componentStop k).trans_le
            (S.componentStop_le k)⟩ : ℚ) = B := by
      dsimp only [B]
      rw [hiBGlobal]
    rw [hBGlobal] at hsuffixBase
    dsimp only [D, U, e, alphaSuffix, suffix, p, hp] at hsuffixBase ⊢
    convert hsuffixBase using 1
    apply congrArg₂ min
    · apply congrArg (fun z : ℚ ↦ B + z)
      apply congrArg
      apply Fin.ext
      rfl
    · rfl
  have hsuffixTop :
      ((((Lattice.weightIdealOrder U.space U.lattice : Int) : ℚ) :
        WithTop ℚ)) =
        min (((B + alphaSuffix : ℚ) : WithTop ℚ))
          (((B + e : ℚ) : WithTop ℚ)) := by
    have hcast := congrArg (fun z : ℚ ↦ (z : WithTop ℚ)) hsuffixQ
    simpa only [WithTop.coe_min] using hcast
  have hsplit := S.sourceFundamentalWeightOrder_eq_min_split k hk T
  have hcross :
      (((((2 * ordUnit K (S.sourceJordan.scaleGenerator k) -
          a.order j.castSucc : Int) : ℚ) : WithTop ℚ)) + delta) =
        (((B + g : ℚ) : WithTop ℚ) + delta) := by
    congr 1
    norm_cast
    push_cast
    have hscaleQ : (ordUnit K (S.sourceJordan.scaleGenerator k) : ℚ) = B := by
      dsimp only [B]
      exact_mod_cast hscale.symm
    rw [hscaleQ]
    change 2 * B - A = B + g
    linarith [hgapEq]
  have hneighborBase :=
    S.source_min_predecessor_suffixAlpha_eq_min_neighborAlphas
      k hk T hrank hright
  dsimp only at hneighborBase
  have hneighbor : min (a.alphaValue j) alphaSuffix =
      min (a.alphaValue j) (a.alphaValue i) := by
    simpa only [j, i, p, hp, suffix, alphaSuffix] using hneighborBase
  have hcap : min (a.alphaValue j) (min alphaSuffix e) =
      min (a.alphaValue j) (min (a.alphaValue i) e) := by
    calc
      min (a.alphaValue j) (min alphaSuffix e) =
          min (min (a.alphaValue j) alphaSuffix) e := by ac_rfl
      _ = min (min (a.alphaValue j) (a.alphaValue i)) e := by
        rw [hneighbor]
      _ = min (a.alphaValue j) (min (a.alphaValue i) e) := by ac_rfl
  by_cases hprefixUnary : S.componentStart k = 1
  · have hprefixInt :=
      S.sourcePrefix_rescaleDual_weightIdealOrder_unary
        k hk T hprefixUnary c
    have hprefixQ :
        (Lattice.weightIdealOrder P.space
          (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)) : ℚ) =
          B + g + e := by
      have hcast := congrArg (fun z : Int ↦ (z : ℚ)) hprefixInt
      push_cast at hcast
      rw [hc] at hcast
      rw [← hjcast] at hcast
      dsimp only [D, P, B, e, A] at hcast ⊢
      linarith [hgapEq]
    have hprefixTop :
        ((((Lattice.weightIdealOrder P.space
          (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)) :
            Int) : ℚ) : WithTop ℚ)) =
          (((B + g + e : ℚ) : WithTop ℚ)) :=
      congrArg (fun z : ℚ ↦ (z : WithTop ℚ)) hprefixQ
    have halphaBase :=
      S.sourcePredecessorAlpha_eq_min_four_local_prefix_unary
        k hk T hprefixUnary hright
    dsimp only at halphaBase
    rw [hsuffixAlphaLocal] at halphaBase
    have halpha : (a.alphaValue j : WithTop ℚ) =
        min (((g / 2 + e : ℚ) : WithTop ℚ))
          (min (((g : ℚ) : WithTop ℚ) + delta)
            (min (((g + e : ℚ) : WithTop ℚ))
              (((g + alphaSuffix : ℚ) : WithTop ℚ)))) := by
      simpa only [j, g, e, delta, p, hp, suffix, alphaSuffix,
        tail, htail, suffixLocal]
        using halphaBase
    have hminimumBase := unarySplitMinimum_eq
      B g e e alphaSuffix (a.alphaValue j) delta hgap halpha
    have hminimum :
        min
            (min (((B + alphaSuffix : ℚ) : WithTop ℚ))
              (((B + e : ℚ) : WithTop ℚ)))
            (min
              (min (((B + g + e : ℚ) : WithTop ℚ))
                (((B + g + e : ℚ) : WithTop ℚ)))
              (((B + g : ℚ) : WithTop ℚ) + delta)) =
          (((B + min (a.alphaValue j)
            (min (a.alphaValue i) e) : ℚ) : WithTop ℚ)) := by
      rw [← hcap]
      exact hminimumBase
    have hsplit' := hsplit
    dsimp only [D, P, U, c, j, delta] at hsplit'
    rw [hsuffixTop, hprefixTop, hcross] at hsplit'
    have hfinalTop :
        ((((Lattice.weightIdealOrder q
          (S.sourceJordan.fundamentalLattice k) : Int) : ℚ) :
            WithTop ℚ)) =
          (((B + min (a.alphaValue j)
            (min (a.alphaValue i) e) : ℚ) : WithTop ℚ)) := by
      calc
        ((((Lattice.weightIdealOrder q
            (S.sourceJordan.fundamentalLattice k) : Int) : ℚ) :
              WithTop ℚ)) =
            min
              (min
                (min (((B + alphaSuffix : ℚ) : WithTop ℚ))
                  (((B + e : ℚ) : WithTop ℚ)))
                (((B + g + e : ℚ) : WithTop ℚ)))
              (((B + g : ℚ) : WithTop ℚ) + delta) := hsplit'
        _ = _ := by simpa only [min_self, min_assoc] using hminimum
    exact WithTop.coe_eq_coe.mp hfinalTop
  · have htwo : 2 ≤ S.componentStart k := by omega
    let ell := S.componentStart k - 1
    let hell : ell + 1 = S.componentStart k := by
      dsimp only [ell]
      omega
    let pre := (S.sourcePrefixGoodBONG k hk T).castLength hell.symm
    let alphaPrefix : ℚ := pre.alphaValue ⟨ell - 1, by omega⟩
    have hprefixBase :=
      S.sourcePrefix_rescaleDual_weightIdealOrder_nonunary
        k hk T htwo c
    dsimp only at hprefixBase
    have hprefixQ :
        (Lattice.weightIdealOrder P.space
          (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)) : ℚ) =
          min (B + g + alphaPrefix) (B + g + e) := by
      rw [hc] at hprefixBase
      push_cast at hprefixBase
      rw [← hjcast] at hprefixBase
      dsimp only [D, P, B, e, A, alphaPrefix, pre, ell, hell]
        at hprefixBase ⊢
      rw [hprefixBase]
      congr 1 <;> linarith [hgapEq]
    have hprefixTop :
        ((((Lattice.weightIdealOrder P.space
          (Lattice.rescale c (Lattice.dualLattice P.space P.lattice)) :
            Int) : ℚ) : WithTop ℚ)) =
          min (((B + g + alphaPrefix : ℚ) : WithTop ℚ))
            (((B + g + e : ℚ) : WithTop ℚ)) := by
      have hcast := congrArg (fun z : ℚ ↦ (z : WithTop ℚ)) hprefixQ
      simpa only [WithTop.coe_min] using hcast
    have halphaBase :=
      S.sourcePredecessorAlpha_eq_min_four_local
        k hk T htwo hright
    dsimp only at halphaBase
    rw [hsuffixAlphaLocal] at halphaBase
    have halpha : (a.alphaValue j : WithTop ℚ) =
        min (((g / 2 + e : ℚ) : WithTop ℚ))
          (min (((g : ℚ) : WithTop ℚ) + delta)
            (min (((g + alphaPrefix : ℚ) : WithTop ℚ))
              (((g + alphaSuffix : ℚ) : WithTop ℚ)))) := by
      simpa only [j, g, e, delta, p, hp, suffix, alphaSuffix,
        tail, htail, suffixLocal, alphaPrefix, pre, ell, hell]
        using halphaBase
    have hminimumBase := unarySplitMinimum_eq
      B g e alphaPrefix alphaSuffix (a.alphaValue j) delta hgap halpha
    have hminimum :
        min
            (min (((B + alphaSuffix : ℚ) : WithTop ℚ))
              (((B + e : ℚ) : WithTop ℚ)))
            (min
              (min (((B + g + alphaPrefix : ℚ) : WithTop ℚ))
                (((B + g + e : ℚ) : WithTop ℚ)))
              (((B + g : ℚ) : WithTop ℚ) + delta)) =
          (((B + min (a.alphaValue j)
            (min (a.alphaValue i) e) : ℚ) : WithTop ℚ)) := by
      rw [← hcap]
      exact hminimumBase
    have hsplit' := hsplit
    dsimp only [D, P, U, c, j, delta] at hsplit'
    rw [hsuffixTop, hprefixTop, hcross] at hsplit'
    have hfinalTop :
        ((((Lattice.weightIdealOrder q
          (S.sourceJordan.fundamentalLattice k) : Int) : ℚ) :
            WithTop ℚ)) =
          (((B + min (a.alphaValue j)
            (min (a.alphaValue i) e) : ℚ) : WithTop ℚ)) := by
      calc
        ((((Lattice.weightIdealOrder q
            (S.sourceJordan.fundamentalLattice k) : Int) : ℚ) :
              WithTop ℚ)) =
            min
              (min
                (min (((B + alphaSuffix : ℚ) : WithTop ℚ))
                  (((B + e : ℚ) : WithTop ℚ)))
                (min (((B + g + alphaPrefix : ℚ) : WithTop ℚ))
                  (((B + g + e : ℚ) : WithTop ℚ))))
              (((B + g : ℚ) : WithTop ℚ) + delta) := hsplit'
        _ = _ := by simpa only [min_assoc] using hminimum
    exact WithTop.coe_eq_coe.mp hfinalTop

/-- At an even Jordan boundary with a unary right component, the right
weight term is bounded below by the boundary alpha and, when present,
above by the successor-neighbor candidate. -/
theorem sourceEvenBoundaryRightTerm_bounds_of_unary
    {n : Nat} {a : GoodBONG q L (n + 2)}
    {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (z : Fin t)
    (hrank : S.sourceJordan.componentRank
      (Fin.cast h.symm
        (Lattice.JordanDecomposition.boundaryRightIndex z)) = 1) :
    let P := S.sourceProfileSucc h
    let J := S.sourceJordanSucc h
    let j := P.boundaryIndex z
    let term : WithTop ℚ :=
      (((ordUnit K (P.boundaryLeftValue z) -
        2 * J.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z) +
        J.fundamentalWeightOrder
          (Lattice.JordanDecomposition.boundaryRightIndex z) : Int) : ℚ) :
        WithTop ℚ)
    (a.alphaValue j : WithTop ℚ) ≤ term ∧
      ∀ sidx : Fin (n + 1),
        sidx.val = j.val + 1 →
        term ≤ a.neighborAlphaCandidate j sidx := by
  dsimp only
  let P := S.sourceProfileSucc h
  let J := S.sourceJordanSucc h
  let li : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex z
  let ri : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex z
  let k : Fin S.componentCount := Fin.cast h.symm ri
  let j : Fin (n + 1) := P.boundaryIndex z
  let term : WithTop ℚ :=
    (((ordUnit K (P.boundaryLeftValue z) -
      2 * J.fundamentalScaleOrder li +
      J.fundamentalWeightOrder ri : Int) : ℚ) : WithTop ℚ)
  have hk : 0 < k.val := by
    dsimp only [k, ri, Lattice.JordanDecomposition.boundaryRightIndex]
    change 0 < z.val + 1
    omega
  rcases S.source_hasTwoBlockSplit_componentStart k hk with ⟨T⟩
  have hstart : j.val + 1 = S.componentStart k := by
    dsimp only [j, P, k, ri]
    exact S.sourceBoundaryIndex_succ_val_eq_componentStart h z
  have hpred :
      (⟨S.componentStart k - 1, by omega⟩ : Fin (n + 1)) = j := by
    apply Fin.ext
    dsimp only [j]
    omega
  have hleftGen := S.sourceBoundaryLeftValue_isNormGeneratorValue h z
  have hterminal := S.sourceTerminalValue_isNormGeneratorValue h li
  have hnorm := S.sourceNormGenerator_order_eq_fundamental h li
  have hu : ordUnit K (P.boundaryLeftValue z) =
      ordUnit K (J.fundamentalNormGenerator li) := by
    apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact hleftGen.2.symm.trans (J.fundamentalNormGenerator_spec li).2
  have horderLeft : a.order j.castSucc =
      2 * J.fundamentalScaleOrder li -
        ordUnit K (P.boundaryLeftValue z) := by
    rw [P.order_boundaryIndex z hterminal hnorm, hu]
  let g : ℚ := a.orderGap j
  let e : ℚ := ramificationIndex K
  have hboundaryOrder := S.source_order_before_component_le_start k hk
  have hgap : 0 ≤ g := by
    unfold g GoodBONG.orderGap
    have hleftIndex : j.castSucc =
        ⟨S.componentStart k - 1, by
          have hbound := (S.componentStart_lt_componentStop k).trans_le
            (S.componentStop_le k)
          omega⟩ := by
      apply Fin.ext
      change j.val = S.componentStart k - 1
      omega
    have hrightIndex : j.succ =
        ⟨S.componentStart k, by
          exact (S.componentStart_lt_componentStop k).trans_le
            (S.componentStop_le k)⟩ := by
      apply Fin.ext
      exact hstart
    rw [hleftIndex, hrightIndex]
    exact_mod_cast sub_nonneg.mpr hboundaryOrder
  have hhalf : a.alphaValue j ≤ g + e := by
    have hbase := a.alphaValue_le_halfGapValue j
    unfold GoodBONG.halfGapValue at hbase
    dsimp only [g, e]
    linarith
  by_cases hright : S.componentStart k < n + 1
  · let next : Fin (n + 1) := ⟨S.componentStart k, hright⟩
    have hweightRaw :=
      S.sourceFundamentalWeightOrder_eq_order_add_min_neighborAlphas_e_of_unary
        k hk T hrank hright
    dsimp only at hweightRaw
    have hnextIndex : next = ⟨S.componentStart k, hright⟩ := rfl
    have hweight : ((J.fundamentalWeightOrder ri : Int) : ℚ) =
        (a.order j.succ : ℚ) +
          min (a.alphaValue j) (min (a.alphaValue next) e) := by
      dsimp only [J, sourceJordanSucc]
      rw [Lattice.JordanDecomposition.castComponentCount_fundamentalWeightOrder]
      change ((S.sourceJordan.fundamentalWeightOrder k : Int) : ℚ) = _
      change ((Lattice.weightIdealOrder q
        (S.sourceJordan.fundamentalLattice k) : Int) : ℚ) = _
      have hstartIndex :
          (⟨S.componentStart k, hright⟩ : Fin (n + 1)).castSucc =
            j.succ := by
        apply Fin.ext
        exact hstart.symm
      rw [hstartIndex] at hweightRaw
      rw [hpred] at hweightRaw
      simpa only [next, hnextIndex] using hweightRaw
    have horderLeftQ : (a.order j.castSucc : ℚ) =
        2 * (J.fundamentalScaleOrder li : ℚ) -
          (ordUnit K (P.boundaryLeftValue z) : ℚ) := by
      exact_mod_cast horderLeft
    have htermQ :
        ((ordUnit K (P.boundaryLeftValue z) -
          2 * J.fundamentalScaleOrder li +
          J.fundamentalWeightOrder ri : Int) : ℚ) =
        g + min (a.alphaValue j) (min (a.alphaValue next) e) := by
      push_cast
      rw [hweight]
      unfold g GoodBONG.orderGap
      push_cast
      linarith [horderLeftQ]
    have hneighbor : a.alphaValue j ≤ g + a.alphaValue next := by
      have htop := a.alpha_le_neighborAlphaCandidate j next (Or.inr (by
        dsimp only [next]
        exact hstart))
      rw [← a.coe_alphaValue] at htop
      unfold GoodBONG.neighborAlphaCandidate GoodBONG.alphaGapValue at htop
      have htop' : (a.alphaValue j : WithTop ℚ) ≤
          (((g + a.alphaValue next : ℚ) : WithTop ℚ)) := by
        simpa only [g, GoodBONG.orderGap, WithTop.coe_add] using htop
      exact WithTop.coe_le_coe.mp htop'
    have hlowerQ : a.alphaValue j ≤
        g + min (a.alphaValue j) (min (a.alphaValue next) e) := by
      rw [GoodBONG.lemma214_add_min, GoodBONG.lemma214_add_min]
      apply le_min
      · linarith
      · apply le_min hneighbor
        exact hhalf
    constructor
    · rw [htermQ]
      exact_mod_cast hlowerQ
    · intro sidx hsidx
      have hsnext : sidx = next := by
        apply Fin.ext
        change sidx.val = S.componentStart k
        change sidx.val = j.val + 1 at hsidx
        omega
      subst sidx
      rw [htermQ]
      unfold GoodBONG.neighborAlphaCandidate GoodBONG.alphaGapValue
      change ((g + min (a.alphaValue j)
          (min (a.alphaValue next) e) : ℚ) : WithTop ℚ) ≤
        ((g + a.alphaValue next : ℚ) : WithTop ℚ)
      exact_mod_cast (by
        have hmin : min (a.alphaValue j)
            (min (a.alphaValue next) e) ≤ a.alphaValue next :=
          (min_le_right _ _).trans (min_le_left _ _)
        linarith)
  · have hterminalLength : n + 2 - S.componentStart k = 1 := by
      have hbound := (S.componentStart_lt_componentStop k).trans_le
        (S.componentStop_le k)
      omega
    have hweightRaw :=
      S.sourceFundamentalWeightOrder_eq_order_add_min_alpha_e_of_unary_terminal
        k hk T hrank hterminalLength
    dsimp only at hweightRaw
    have hweight : ((J.fundamentalWeightOrder ri : Int) : ℚ) =
        (a.order j.succ : ℚ) + min (a.alphaValue j) e := by
      dsimp only [J, sourceJordanSucc]
      rw [Lattice.JordanDecomposition.castComponentCount_fundamentalWeightOrder]
      change ((S.sourceJordan.fundamentalWeightOrder k : Int) : ℚ) = _
      change ((Lattice.weightIdealOrder q
        (S.sourceJordan.fundamentalLattice k) : Int) : ℚ) = _
      have hstartIndex :
          (⟨S.componentStart k, by
            have hbound := (S.componentStart_lt_componentStop k).trans_le
              (S.componentStop_le k)
            omega⟩ : Fin (n + 2)) = j.succ := by
        apply Fin.ext
        exact hstart.symm
      rw [hstartIndex] at hweightRaw
      rw [hpred] at hweightRaw
      simpa using hweightRaw
    have horderLeftQ : (a.order j.castSucc : ℚ) =
        2 * (J.fundamentalScaleOrder li : ℚ) -
          (ordUnit K (P.boundaryLeftValue z) : ℚ) := by
      exact_mod_cast horderLeft
    have htermQ :
        ((ordUnit K (P.boundaryLeftValue z) -
          2 * J.fundamentalScaleOrder li +
          J.fundamentalWeightOrder ri : Int) : ℚ) =
        g + min (a.alphaValue j) e := by
      push_cast
      rw [hweight]
      unfold g GoodBONG.orderGap
      push_cast
      linarith [horderLeftQ]
    have hlowerQ : a.alphaValue j ≤
        g + min (a.alphaValue j) e := by
      rw [GoodBONG.lemma214_add_min]
      exact le_min (by linarith) hhalf
    constructor
    · rw [htermQ]
      exact_mod_cast hlowerQ
    · intro sidx hsidx
      have hslt := sidx.isLt
      change sidx.val = j.val + 1 at hsidx
      have hsstart : sidx.val = S.componentStart k := by omega
      have hstartBound : S.componentStart k < n + 1 := by omega
      exact (hright hstartBound).elim

/-- At an even Jordan boundary with a unary left component, the left
weight term is bounded below by the boundary alpha and, when present,
above by the predecessor-neighbor candidate. -/
theorem sourceEvenBoundaryLeftTerm_bounds_of_unary
    {n : Nat} {a : GoodBONG q L (n + 2)}
    {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (z : Fin t)
    (hrank : S.sourceJordan.componentRank
      (Fin.cast h.symm
        (Lattice.JordanDecomposition.boundaryLeftIndex z)) = 1) :
    let P := S.sourceProfileSucc h
    let J := S.sourceJordanSucc h
    let j := P.boundaryIndex z
    let term : WithTop ℚ :=
      (((ordUnit K (P.boundaryRightValue z) -
        2 * J.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z) +
        J.fundamentalWeightOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z) : Int) : ℚ) :
        WithTop ℚ)
    (a.alphaValue j : WithTop ℚ) ≤ term ∧
      ∀ pidx : Fin (n + 1),
        pidx.val + 1 = j.val →
        term ≤ a.neighborAlphaCandidate j pidx := by
  dsimp only
  let P := S.sourceProfileSucc h
  let J := S.sourceJordanSucc h
  let li : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex z
  let ri : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex z
  let kL : Fin S.componentCount := Fin.cast h.symm li
  let kR : Fin S.componentCount := Fin.cast h.symm ri
  let j : Fin (n + 1) := P.boundaryIndex z
  let term : WithTop ℚ :=
    (((ordUnit K (P.boundaryRightValue z) -
      2 * J.fundamentalScaleOrder li +
      J.fundamentalWeightOrder li : Int) : ℚ) : WithTop ℚ)
  have hkval : kR.val = kL.val + 1 := by
    dsimp only [kR, kL, ri, li,
      Lattice.JordanDecomposition.boundaryRightIndex,
      Lattice.JordanDecomposition.boundaryLeftIndex]
    rfl
  have hstopStart : S.componentStop kL = S.componentStart kR :=
    S.componentStop_eq_componentStart_of_val_succ kL kR hkval
  have hstartRight : j.val + 1 = S.componentStart kR := by
    dsimp only [j, P, kR, ri]
    exact S.sourceBoundaryIndex_succ_val_eq_componentStart h z
  have hstopLeft : S.componentStop kL = j.val + 1 := by omega
  have hrankL :
      S.sourceJordan.toOrthogonalDecomposition.componentRank kL = 1 := by
    change S.sourceJordan.componentRank kL = 1
    simpa only [kL, li] using hrank
  have hstartLeft : S.componentStart kL = j.val := by
    unfold componentStop at hstopLeft
    rw [hrankL] at hstopLeft
    omega
  have hright : S.componentStart kL < n + 1 := by
    rw [hstartLeft]
    exact j.isLt
  have hstartIndex :
      (⟨S.componentStart kL, by
        exact (S.componentStart_lt_componentStop kL).trans_le
          (S.componentStop_le kL)⟩ : Fin (n + 2)) = j.castSucc := by
    apply Fin.ext
    exact hstartLeft
  have hafterIndex :
      (⟨S.componentStart kL + 1, by
        rw [hstartLeft]
        omega⟩ : Fin (n + 2)) = j.succ := by
    apply Fin.ext
    exact congrArg (fun x ↦ x + 1) hstartLeft
  have hscaleRaw :=
    S.sourceOrder_componentStart_eq_scaleOrder_of_unary kL hrankL
  have hscaleCast : J.fundamentalScaleOrder li =
      S.sourceJordan.fundamentalScaleOrder kL := by
    dsimp only [J, sourceJordanSucc]
    rw [Lattice.JordanDecomposition.castComponentCount_fundamentalScaleOrder]
  have hscale : a.order j.castSucc = J.fundamentalScaleOrder li := by
    rw [hscaleCast]
    change a.order j.castSucc =
      ordUnit K (S.sourceJordan.scaleGenerator kL)
    rw [← hstartIndex]
    exact hscaleRaw
  have hrightGen := S.sourceBoundaryRightValue_isNormGeneratorValue h z
  have hv : ordUnit K (P.boundaryRightValue z) =
      ordUnit K (J.fundamentalNormGenerator ri) := by
    apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact hrightGen.2.symm.trans (J.fundamentalNormGenerator_spec ri).2
  have horderRight : a.order j.succ =
      ordUnit K (P.boundaryRightValue z) := by
    rw [P.order_boundaryIndex_succ z, hv]
  have hstopComponent : S.componentStop kL < n + 2 := by
    rw [hstopLeft]
    exact Nat.succ_lt_succ j.isLt
  have horderNext :=
    S.source_order_componentStart_le_after_of_unary_nonterminal
      kL hrankL hstopComponent
  rw [hstartIndex, hafterIndex] at horderNext
  let g : ℚ := a.orderGap j
  let e : ℚ := ramificationIndex K
  have hgap : 0 ≤ g := by
    unfold g GoodBONG.orderGap
    exact_mod_cast sub_nonneg.mpr horderNext
  have hhalf : a.alphaValue j ≤ g + e := by
    have hbase := a.alphaValue_le_halfGapValue j
    unfold GoodBONG.halfGapValue at hbase
    dsimp only [g, e]
    linarith
  by_cases hk : 0 < kL.val
  · rcases S.source_hasTwoBlockSplit_componentStart kL hk with ⟨T⟩
    have hstartPos : 0 < S.componentStart kL := by
      unfold componentStart
      let p : Fin S.componentCount := ⟨kL.val - 1, by omega⟩
      have hp : p ∈ Finset.Iio kL := by
        simp only [Finset.mem_Iio]
        change kL.val - 1 < kL.val
        omega
      have hle := Finset.single_le_sum
        (s := Finset.Iio kL)
        (f := fun x ↦
          S.sourceJordan.toOrthogonalDecomposition.componentRank x)
        (fun _ _ ↦ Nat.zero_le _) hp
      exact (S.sourceJordan.component_finrank_pos p).trans_le hle
    have hjpos : 0 < j.val := by omega
    let prev : Fin (n + 1) := ⟨S.componentStart kL - 1, by
      rw [hstartLeft]
      omega⟩
    have hprev : prev.val + 1 = j.val := by
      dsimp only [prev]
      rw [hstartLeft]
      omega
    have hweightRaw :=
      S.sourceFundamentalWeightOrder_eq_order_add_min_neighborAlphas_e_of_unary
        kL hk T hrankL hright
    dsimp only at hweightRaw
    have hi : (⟨S.componentStart kL, hright⟩ : Fin (n + 1)) = j := by
      apply Fin.ext
      exact hstartLeft
    have hp :
        (⟨S.componentStart kL - 1, by
          have hbound := (S.componentStart_lt_componentStop kL).trans_le
            (S.componentStop_le kL)
          omega⟩ : Fin (n + 1)) = prev := by
      apply Fin.ext
      rfl
    have hweight : ((J.fundamentalWeightOrder li : Int) : ℚ) =
        (a.order j.castSucc : ℚ) +
          min (a.alphaValue prev) (min (a.alphaValue j) e) := by
      dsimp only [J, sourceJordanSucc]
      rw [Lattice.JordanDecomposition.castComponentCount_fundamentalWeightOrder]
      change ((S.sourceJordan.fundamentalWeightOrder kL : Int) : ℚ) = _
      change ((Lattice.weightIdealOrder q
        (S.sourceJordan.fundamentalLattice kL) : Int) : ℚ) = _
      rw [hi] at hweightRaw
      rw [hp] at hweightRaw
      simpa only [e] using hweightRaw
    have hscaleQ : (a.order j.castSucc : ℚ) =
        (J.fundamentalScaleOrder li : ℚ) := by
      exact_mod_cast hscale
    have horderRightQ : (a.order j.succ : ℚ) =
        (ordUnit K (P.boundaryRightValue z) : ℚ) := by
      exact_mod_cast horderRight
    have htermQ :
        ((ordUnit K (P.boundaryRightValue z) -
          2 * J.fundamentalScaleOrder li +
          J.fundamentalWeightOrder li : Int) : ℚ) =
        g + min (a.alphaValue prev) (min (a.alphaValue j) e) := by
      push_cast
      rw [hweight]
      unfold g GoodBONG.orderGap
      push_cast
      linarith [hscaleQ, horderRightQ]
    have hneighbor : a.alphaValue j ≤ g + a.alphaValue prev := by
      have htop := a.alpha_le_neighborAlphaCandidate j prev (Or.inl hprev)
      rw [← a.coe_alphaValue] at htop
      unfold GoodBONG.neighborAlphaCandidate GoodBONG.alphaGapValue at htop
      have htop' : (a.alphaValue j : WithTop ℚ) ≤
          (((g + a.alphaValue prev : ℚ) : WithTop ℚ)) := by
        simpa only [g, GoodBONG.orderGap, WithTop.coe_add] using htop
      exact WithTop.coe_le_coe.mp htop'
    have hlowerQ : a.alphaValue j ≤
        g + min (a.alphaValue prev) (min (a.alphaValue j) e) := by
      rw [GoodBONG.lemma214_add_min, GoodBONG.lemma214_add_min]
      exact le_min hneighbor (le_min (by linarith) hhalf)
    constructor
    · rw [htermQ]
      exact_mod_cast hlowerQ
    · intro pidx hpidx
      have hpprev : pidx = prev := by
        apply Fin.ext
        change pidx.val = S.componentStart kL - 1
        change pidx.val + 1 = j.val at hpidx
        omega
      subst pidx
      rw [htermQ]
      unfold GoodBONG.neighborAlphaCandidate GoodBONG.alphaGapValue
      change ((g + min (a.alphaValue prev)
          (min (a.alphaValue j) e) : ℚ) : WithTop ℚ) ≤
        ((g + a.alphaValue prev : ℚ) : WithTop ℚ)
      exact_mod_cast (by
        have hmin : min (a.alphaValue prev)
            (min (a.alphaValue j) e) ≤ a.alphaValue prev := min_le_left _ _
        linarith)
  · have hkzero : kL.val = 0 := by omega
    have hkfirst : kL = S.sourceFirstComponent := by
      apply Fin.ext
      exact hkzero
    have hstartZero : S.componentStart kL = 0 := by
      rw [hkfirst]
      unfold componentStart
      rw [S.Iio_sourceFirstComponent_eq_empty]
      simp
    have hjzero : j = 0 := by
      apply Fin.ext
      change j.val = 0
      omega
    have hweightGlobal := a.lemma214_weightIdealOrder_all
    have hweightGlobalQ : (Lattice.weightIdealOrder q L : ℚ) =
        (a.order j.castSucc : ℚ) + min (a.alphaValue j) e := by
      calc
        (Lattice.weightIdealOrder q L : ℚ) =
            min ((a.order 0 : ℚ) + a.alphaValue 0)
              ((a.order 0 : ℚ) + (ramificationIndex K : ℚ)) :=
          hweightGlobal
        _ = (a.order 0 : ℚ) +
            min (a.alphaValue 0) (ramificationIndex K : ℚ) := by
          rw [GoodBONG.lemma214_add_min]
        _ = (a.order j.castSucc : ℚ) + min (a.alphaValue j) e := by
          simp only [hjzero, e, Fin.castSucc_zero]
    have hweightZero :=
      S.sourceJordan.fundamentalWeightOrder_zero S.componentCount_pos
    have hzeroIndex :
        (⟨0, S.componentCount_pos⟩ : Fin S.componentCount) = kL := by
      apply Fin.ext
      exact hkzero.symm
    rw [hzeroIndex] at hweightZero
    have hweight : ((J.fundamentalWeightOrder li : Int) : ℚ) =
        (a.order j.castSucc : ℚ) + min (a.alphaValue j) e := by
      dsimp only [J, sourceJordanSucc]
      rw [Lattice.JordanDecomposition.castComponentCount_fundamentalWeightOrder]
      change ((S.sourceJordan.fundamentalWeightOrder kL : Int) : ℚ) = _
      rw [hweightZero]
      exact hweightGlobalQ
    have hscaleQ : (a.order j.castSucc : ℚ) =
        (J.fundamentalScaleOrder li : ℚ) := by
      exact_mod_cast hscale
    have horderRightQ : (a.order j.succ : ℚ) =
        (ordUnit K (P.boundaryRightValue z) : ℚ) := by
      exact_mod_cast horderRight
    have htermQ :
        ((ordUnit K (P.boundaryRightValue z) -
          2 * J.fundamentalScaleOrder li +
          J.fundamentalWeightOrder li : Int) : ℚ) =
        g + min (a.alphaValue j) e := by
      push_cast
      rw [hweight]
      unfold g GoodBONG.orderGap
      push_cast
      linarith [hscaleQ, horderRightQ]
    have hlowerQ : a.alphaValue j ≤ g + min (a.alphaValue j) e := by
      rw [GoodBONG.lemma214_add_min]
      exact le_min (by linarith) hhalf
    constructor
    · rw [htermQ]
      exact_mod_cast hlowerQ
    · intro pidx hpidx
      change pidx.val + 1 = j.val at hpidx
      have hpidxLt := pidx.isLt
      have hjzeroVal : j.val = 0 := by simp [hjzero]
      omega

/-- The right weight term at an even Jordan boundary has the two estimates
needed for the Corollary 2.5 minimum argument, in every component rank. -/
theorem sourceEvenBoundaryRightTerm_bounds
    {n : Nat} {a : GoodBONG q L (n + 2)}
    {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (z : Fin t) :
    let P := S.sourceProfileSucc h
    let J := S.sourceJordanSucc h
    let j := P.boundaryIndex z
    let term : WithTop ℚ :=
      (((ordUnit K (P.boundaryLeftValue z) -
        2 * J.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z) +
        J.fundamentalWeightOrder
          (Lattice.JordanDecomposition.boundaryRightIndex z) : Int) : ℚ) :
        WithTop ℚ)
    (a.alphaValue j : WithTop ℚ) ≤ term ∧
      ∀ sidx : Fin (n + 1),
        sidx.val = j.val + 1 →
        term ≤ a.neighborAlphaCandidate j sidx := by
  dsimp only
  let P := S.sourceProfileSucc h
  let ri : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex z
  let k : Fin S.componentCount := Fin.cast h.symm ri
  let j : Fin (n + 1) := P.boundaryIndex z
  have hrankPos : 0 < S.sourceJordan.componentRank k :=
    S.sourceJordan.component_finrank_pos k
  by_cases hrank : S.sourceJordan.componentRank k = 1
  · exact S.sourceEvenBoundaryRightTerm_bounds_of_unary h z
      (by simpa only [k, ri] using hrank)
  · have hrankTwo : 2 ≤ S.sourceJordan.componentRank k := by omega
    have hrankTwo' : 2 ≤
        S.sourceJordan.toOrthogonalDecomposition.componentRank k := by
      change 2 ≤ S.sourceJordan.componentRank k at hrankTwo
      exact hrankTwo
    have hstart : j.val + 1 = S.componentStart k := by
      dsimp only [j, P, k, ri]
      exact S.sourceBoundaryIndex_succ_val_eq_componentStart h z
    have hstartLt : S.componentStart k < n + 1 := by
      have hstop := S.componentStop_le k
      unfold componentStop at hstop
      omega
    let sidx : Fin (n + 1) := ⟨S.componentStart k, hstartLt⟩
    have hsidx : sidx.val = j.val + 1 := by
      dsimp only [sidx]
      exact hstart.symm
    have heq := S.sourceEvenBoundaryRightTerm_eq_neighborAlphaCandidate
      h z sidx hsidx (by simpa only [k, ri] using hrankTwo)
    constructor
    · rw [heq]
      simpa only [a.coe_alphaValue] using
        a.alpha_le_neighborAlphaCandidate j sidx (Or.inr hsidx.symm)
    · intro sidx' hsidx'
      exact le_of_eq (S.sourceEvenBoundaryRightTerm_eq_neighborAlphaCandidate
        h z sidx' hsidx' (by simpa only [k, ri] using hrankTwo))

/-- The left weight term at an even Jordan boundary has the two estimates
needed for the Corollary 2.5 minimum argument, in every component rank. -/
theorem sourceEvenBoundaryLeftTerm_bounds
    {n : Nat} {a : GoodBONG q L (n + 2)}
    {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (z : Fin t) :
    let P := S.sourceProfileSucc h
    let J := S.sourceJordanSucc h
    let j := P.boundaryIndex z
    let term : WithTop ℚ :=
      (((ordUnit K (P.boundaryRightValue z) -
        2 * J.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z) +
        J.fundamentalWeightOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z) : Int) : ℚ) :
        WithTop ℚ)
    (a.alphaValue j : WithTop ℚ) ≤ term ∧
      ∀ pidx : Fin (n + 1),
        pidx.val + 1 = j.val →
        term ≤ a.neighborAlphaCandidate j pidx := by
  dsimp only
  let P := S.sourceProfileSucc h
  let li : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex z
  let ri : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex z
  let kL : Fin S.componentCount := Fin.cast h.symm li
  let kR : Fin S.componentCount := Fin.cast h.symm ri
  let j : Fin (n + 1) := P.boundaryIndex z
  have hrankPos : 0 < S.sourceJordan.componentRank kL :=
    S.sourceJordan.component_finrank_pos kL
  by_cases hrank : S.sourceJordan.componentRank kL = 1
  · exact S.sourceEvenBoundaryLeftTerm_bounds_of_unary h z
      (by simpa only [kL, li] using hrank)
  · have hrankTwo : 2 ≤ S.sourceJordan.componentRank kL := by omega
    have hrankTwo' : 2 ≤
        S.sourceJordan.toOrthogonalDecomposition.componentRank kL := by
      change 2 ≤ S.sourceJordan.componentRank kL at hrankTwo
      exact hrankTwo
    have hkval : kR.val = kL.val + 1 := by
      dsimp only [kR, kL, ri, li,
        Lattice.JordanDecomposition.boundaryRightIndex,
        Lattice.JordanDecomposition.boundaryLeftIndex]
      rfl
    have hstopStart : S.componentStop kL = S.componentStart kR :=
      S.componentStop_eq_componentStart_of_val_succ kL kR hkval
    have hstartRight : j.val + 1 = S.componentStart kR := by
      dsimp only [j, P, kR, ri]
      exact S.sourceBoundaryIndex_succ_val_eq_componentStart h z
    have hstopLeft : S.componentStop kL = j.val + 1 := by omega
    have hjpos : 0 < j.val := by
      unfold componentStop at hstopLeft
      omega
    let pidx : Fin (n + 1) := ⟨j.val - 1, by omega⟩
    have hpidx : pidx.val + 1 = j.val := by
      dsimp only [pidx]
      omega
    have heq := S.sourceEvenBoundaryLeftTerm_eq_neighborAlphaCandidate
      h z pidx hpidx (by simpa only [kL, li] using hrankTwo)
    constructor
    · rw [heq]
      simpa only [a.coe_alphaValue] using
        a.alpha_le_neighborAlphaCandidate j pidx (Or.inl hpidx)
    · intro pidx' hpidx'
      exact le_of_eq (S.sourceEvenBoundaryLeftTerm_eq_neighborAlphaCandidate
        h z pidx' hpidx' (by simpa only [kL, li] using hrankTwo))

/-- Beli (2009), Lemma 2.16(ii), even case, with no restriction on the
ranks of the two Jordan components adjacent to the boundary. -/
theorem sourceEvenBoundaryCandidateMinimum_eq_alpha
    {n : Nat}
    {a : GoodBONG q L (n + 2)} {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (z : Fin t)
    (heven : Even ((S.sourceJordanSucc h).boundaryNormOrderSum z)) :
    let P := S.sourceProfileSucc h
    let J := S.sourceJordanSucc h
    let j := P.boundaryIndex z
    J.evenBoundaryCandidateMinimum z
        (P.boundaryLeftValue z) (P.boundaryRightValue z) =
      (a.alphaValue j : WithTop ℚ) := by
  dsimp only
  let P := S.sourceProfileSucc h
  let J := S.sourceJordanSucc h
  let li : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex z
  let ri : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex z
  let j : Fin (n + 1) := P.boundaryIndex z
  let rightTerm : WithTop ℚ :=
    (((ordUnit K (P.boundaryLeftValue z) -
      2 * J.fundamentalScaleOrder li +
      J.fundamentalWeightOrder ri : Int) : ℚ) : WithTop ℚ)
  let leftTerm : WithTop ℚ :=
    (((ordUnit K (P.boundaryRightValue z) -
      2 * J.fundamentalScaleOrder li +
      J.fundamentalWeightOrder li : Int) : ℚ) : WithTop ℚ)
  let half := a.halfGapCandidate j
  let defect := a.leftDefectCandidate j j
  have hleftGen := S.sourceBoundaryLeftValue_isNormGeneratorValue h z
  have hrightGen := S.sourceBoundaryRightValue_isNormGeneratorValue h z
  have hterminal := S.sourceTerminalValue_isNormGeneratorValue h li
  have hnorm := S.sourceNormGenerator_order_eq_fundamental h li
  have hprofile := P.evenBoundaryCandidateMinimum_eq_profileMinimum z
    hleftGen hrightGen hterminal hnorm heven
  dsimp only at hprofile
  change J.evenBoundaryCandidateMinimum z
      (P.boundaryLeftValue z) (P.boundaryRightValue z) =
    min half (min defect (min rightTerm leftTerm)) at hprofile
  have hrightBounds := S.sourceEvenBoundaryRightTerm_bounds h z
  dsimp only at hrightBounds
  change (a.alphaValue j : WithTop ℚ) ≤ rightTerm ∧
    ∀ sidx : Fin (n + 1), sidx.val = j.val + 1 →
      rightTerm ≤ a.neighborAlphaCandidate j sidx at hrightBounds
  have hleftBounds := S.sourceEvenBoundaryLeftTerm_bounds h z
  dsimp only at hleftBounds
  change (a.alphaValue j : WithTop ℚ) ≤ leftTerm ∧
    ∀ pidx : Fin (n + 1), pidx.val + 1 = j.val →
      leftTerm ≤ a.neighborAlphaCandidate j pidx at hleftBounds
  have halphaHalf : (a.alphaValue j : WithTop ℚ) ≤ half := by
    dsimp only [half]
    simpa only [a.coe_alphaValue] using a.alpha_le_halfGapCandidate j
  have halphaDefect : (a.alphaValue j : WithTop ℚ) ≤ defect := by
    dsimp only [defect]
    simpa only [a.coe_alphaValue] using
      a.alpha_le_leftDefectCandidate (i := j) (j := j) le_rfl
  rw [hprofile]
  apply le_antisymm
  · have hminHalf : min half (min defect (min rightTerm leftTerm)) ≤ half :=
      min_le_left _ _
    have hminDefect : min half (min defect (min rightTerm leftTerm)) ≤ defect :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hminRight : min half (min defect (min rightTerm leftTerm)) ≤
        rightTerm :=
      (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))
    have hminLeft : min half (min defect (min rightTerm leftTerm)) ≤
        leftTerm :=
      (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))
    by_cases hjzero : j.val = 0
    · by_cases hright : j.val + 1 < n + 1
      · cases n with
        | zero => omega
        | succ n' =>
          let sidx : Fin (n' + 2) := ⟨j.val + 1, by omega⟩
          have hsidx : sidx.val = j.val + 1 := rfl
          have hj : j = (0 : Fin (n' + 2)) := by
            apply Fin.ext
            exact hjzero
          have hs : sidx = (1 : Fin (n' + 2)) := by
            apply Fin.ext
            change sidx.val = 1
            dsimp only [sidx]
            omega
          have hglobal := a.alphaValue_zero_eq_min_neighborSuccessor
          dsimp only at hglobal
          have hglobal' : (a.alphaValue j : WithTop ℚ) =
              min half (min defect (a.neighborAlphaCandidate j sidx)) := by
            simpa only [hj, hs, half, defect] using hglobal
          rw [hglobal']
          exact le_min hminHalf
            (le_min hminDefect
              (hminRight.trans (hrightBounds.2 sidx hsidx)))
      · have hjlast : j.val = n := by omega
        have hglobal := alphaValue_eq_min_two_at_only_boundary
          a j hjzero hjlast
        change (a.alphaValue j : WithTop ℚ) = min half defect at hglobal
        rw [hglobal]
        exact le_min hminHalf hminDefect
    · have hjpos : 0 < j.val := by omega
      by_cases hright : j.val + 1 < n + 1
      · let pidx : Fin (n + 1) := ⟨j.val - 1, by omega⟩
        let sidx : Fin (n + 1) := ⟨j.val + 1, hright⟩
        have hpidx : pidx.val + 1 = j.val := by
          dsimp only [pidx]
          omega
        have hsidx : sidx.val = j.val + 1 := rfl
        have hglobal :=
          a.alphaValue_eq_min_four_neighborCandidates j hjpos hright
        dsimp only at hglobal
        change (a.alphaValue j : WithTop ℚ) =
          min half (min defect
            (min (a.neighborAlphaCandidate j pidx)
              (a.neighborAlphaCandidate j sidx))) at hglobal
        rw [hglobal]
        exact le_min hminHalf (le_min hminDefect (le_min
          (hminLeft.trans (hleftBounds.2 pidx hpidx))
          (hminRight.trans (hrightBounds.2 sidx hsidx))))
      · have hjlast : j.val = n := by omega
        cases n with
        | zero => omega
        | succ n' =>
          let pidx : Fin (n' + 2) := ⟨j.val - 1, by omega⟩
          have hpidx : pidx.val + 1 = j.val := by
            dsimp only [pidx]
            omega
          have hj : j = Fin.last (n' + 1) := by
            apply Fin.ext
            change j.val = n' + 1
            exact hjlast
          have hp : pidx = (⟨n', by omega⟩ : Fin (n' + 2)) := by
            apply Fin.ext
            dsimp only [pidx]
            omega
          have hglobal := a.alphaValue_last_eq_min_neighborPredecessor
          dsimp only at hglobal
          have hglobal' : (a.alphaValue j : WithTop ℚ) =
              min half (min defect (a.neighborAlphaCandidate j pidx)) := by
            simpa only [hj, hp, half, defect] using hglobal
          rw [hglobal']
          exact le_min hminHalf
            (le_min hminDefect
              (hminLeft.trans (hleftBounds.2 pidx hpidx)))
  · exact le_min halphaHalf
      (le_min halphaDefect (le_min hrightBounds.1 hleftBounds.1))

/-- Beli (2009), Lemma 2.16(ii), even fundamental-ideal order, including
all unary endpoint and mixed-rank cases. -/
theorem sourceEvenBoundaryFundamentalOrder_eq_alpha
    {n : Nat}
    {a : GoodBONG q L (n + 2)} {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (z : Fin t)
    (heven : Even ((S.sourceJordanSucc h).boundaryNormOrderSum z)) :
    let P := S.sourceProfileSucc h
    let J := S.sourceJordanSucc h
    let hleft := S.sourceBoundaryLeftValue_isNormGeneratorValue h z
    let hright := S.sourceBoundaryRightValue_isNormGeneratorValue h z
    (((J.evenOrderedFundamentalIdeal z
        (P.boundaryLeftValue z) (P.boundaryRightValue z)
        hleft hright heven).order : Int) : ℚ) =
      a.alphaValue (P.boundaryIndex z) := by
  dsimp only
  apply (S.sourceJordanSucc h).evenOrderedFundamentalIdeal_order_eq_alpha_of_candidateMinimum
  exact S.sourceEvenBoundaryCandidateMinimum_eq_alpha h z heven

end BONG.StrictJordanAdaptedAlignment

end Bong
