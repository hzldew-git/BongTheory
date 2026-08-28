/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019JordanApproximation
import Bong.Bong.JordanProfileMerge

/-!
# Jordan approximation intervals from weak profiles

A weak Jordan profile already identifies the exact global half-open interval
occupied by each component.  This file turns that information into the
`JordanBlockCoordinates` consumed by Beli (2019), Lemma 3.2.  In particular,
the alternating order formula and the improper-even-rank endpoint condition
are proved from the profile witness; they are not additional seed data.
-/

open scoped BigOperators

namespace Bong

open Dyadic
open Module

universe u v

namespace BONG.WeakJordanOrderProfileWitness

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N t : Nat}

/-- The global start of a component in a weak Jordan profile. -/
noncomputable def componentStart
    {b : BONG V q L N}
    {W : Lattice.WeakJordanDecomposition q L t}
    (_w : WeakJordanOrderProfileWitness b W)
    (p : Fin t) : Nat :=
  ∑ k ∈ Finset.Iio p, finrank K (W.component k).carrier

/-- The endpoint of a component in a weak Jordan profile. -/
noncomputable def componentStop
    {b : BONG V q L N}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W)
    (p : Fin t) : Nat :=
  w.componentStart p + finrank K (W.component p).carrier

/-- If a global coordinate occurs no later than the start of a prescribed
weak Jordan component, then its own weak component is no later than the
prescribed one.  This is the prefix-rank monotonicity needed to turn the
numerical reduced ranges in Section 5 into hypotheses for collision-safe
strict resolutions. -/
theorem component_le_of_index_val_le_componentStart
    {b : BONG V q L N}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W)
    (I : Fin N) (p : Fin t)
    (hI : I.val ≤ w.componentStart p) :
    (w.indexEquiv I).1 ≤ p := by
  classical
  by_contra hnot
  have hpCurrent : p < (w.indexEquiv I).1 := lt_of_not_ge hnot
  have hsubset : Finset.Iic p ⊆ Finset.Iio (w.indexEquiv I).1 := by
    intro k hk
    exact Finset.mem_Iio.mpr
      ((Finset.mem_Iic.mp hk).trans_lt hpCurrent)
  have hsumLe :
      (∑ k ∈ Finset.Iic p, finrank K (W.component k).carrier) ≤
        ∑ k ∈ Finset.Iio (w.indexEquiv I).1,
          finrank K (W.component k).carrier :=
    Finset.sum_le_sum_of_subset hsubset
  have hclosed : Finset.Iic p = insert p (Finset.Iio p) := by
    ext k
    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Iio]
    constructor
    · intro hk
      exact hk.eq_or_lt
    · rintro (rfl | hk)
      · exact le_rfl
      · exact hk.le
  rw [hclosed, Finset.sum_insert (by simp)] at hsumLe
  have hpositive : 0 < finrank K (W.component p).carrier :=
    W.component_finrank_pos p
  have hglobal := w.index_val_eq_componentStart_add_local I
  unfold componentStart at hI
  omega

/-- Every component of a weak Jordan profile gives the checked alternating
global interval required by Lemma 3.2. -/
noncomputable def jordanBlockCoordinates
    {a : BONG.GoodBONG q L N}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness a.toBONG W)
    (hW : W.HasImproperEvenRank) (p : Fin t) :
    a.JordanBlockCoordinates := by
  let start := w.componentStart p
  let stop := w.componentStop p
  let scale := ordUnit K (W.scaleGenerator p)
  let effective := W.effectiveNormOrderAt p scale
  have hstartStop : start < stop := by
    dsimp only [start, stop, componentStop]
    exact Nat.lt_add_of_pos_right (W.component_finrank_pos p)
  have hstopLe : stop ≤ N := by
    let last : Fin (finrank K (W.component p).carrier) :=
      ⟨finrank K (W.component p).carrier - 1, by
        have := W.component_finrank_pos p
        omega⟩
    have hvalue := w.inverse_index_val p last
    have hlt := (w.indexEquiv.symm ⟨p, last⟩).isLt
    dsimp only [last, Fin.val_mk] at hvalue
    dsimp only [stop, componentStop, start, componentStart]
    omega
  refine {
    start := start
    stop := stop
    start_lt_stop := hstartStop
    stop_le := hstopLe
    scaleOrder := scale
    normOrder := effective
    order_eq := ?_
    proper_or_even := ?_ }
  · intro j hleft hright
    let localIndex : Fin (finrank K (W.component p).carrier) :=
      ⟨j - start, by
        dsimp only [stop, componentStop] at hright
        omega⟩
    let global : Fin N := w.indexEquiv.symm ⟨p, localIndex⟩
    have hglobalVal : global.val = j := by
      change (w.indexEquiv.symm ⟨p, localIndex⟩).val = j
      rw [w.inverse_index_val]
      change
        (∑ h ∈ Finset.Iio p, finrank K (W.component h).carrier) +
            (j - start) = j
      have hstart : start =
          ∑ h ∈ Finset.Iio p, finrank K (W.component h).carrier := rfl
      omega
    have hindex : (⟨j, hright.trans_le hstopLe⟩ : Fin N) = global := by
      apply Fin.ext
      exact hglobalVal.symm
    rw [hindex]
    change a.toBONG.order (w.indexEquiv.symm ⟨p, localIndex⟩) = _
    rw [w.order_inverse_indexEquiv]
    change JordanProfileOrder.localOrder scale effective (j - start) = _
    by_cases hproper : scale = effective
    · simp only [JordanProfileOrder.localOrder, hproper, if_pos]
      split <;> omega
    · by_cases heven : Even (j - start)
      · have hmod : (j - start) % 2 = 0 := by
          rcases heven with ⟨k, hk⟩
          omega
        rw [JordanProfileOrder.localOrder_of_even hproper heven]
        simp only [hmod, if_pos]
      · have hmod : (j - start) % 2 ≠ 0 := by
          intro hzero
          apply heven
          exact Nat.even_iff.mpr hzero
        rw [JordanProfileOrder.localOrder_of_odd hproper heven]
        simp only [hmod, if_false]
  · by_cases hproper : effective = scale
    · exact Or.inl hproper
    · right
      have hstop : stop = start +
          finrank K (W.component p).carrier := rfl
      rw [hstop, Nat.add_sub_cancel_left]
      apply hW.componentRank_even_of_lt_effectiveNormOrderAt W p p
      change scale < effective
      have hne : scale ≠ effective := by
        intro h
        exact hproper h.symm
      exact lt_of_le_of_ne
        (W.targetScale_le_effectiveNormOrderAt p scale) hne

end BONG.WeakJordanOrderProfileWitness

end Bong
