/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma715Prefix
import Bong.Bong.Beli2009AlphaLocalizationProof
import Bong.Bong.Beli2009AlphaArithmetic
import Bong.Bong.Beli2009TwoAdic
import Bong.Bong.AlphaValueExt
import Bong.Bong.DefectArithmetic

/-!
# Beli (2019), Lemma 7.15: common alpha machinery

At the boundary used in Lemma 7.15, Corollary 2.5(ii) of Beli
(2009/2010) expresses `alpha` as the minimum of four kinds of terms: the
half gap, the adjacent defect, a prefix alpha, and (when present) a suffix
alpha.  This module packages the two elementary minimum reductions used in
both branches of the proof.  It also records comparison lemmas for the
canonical prefix and suffix segments.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {qV : QuadraticSpace K V}
  {LV LW : Lattice K V} {n : Nat}

/-- The boundary candidate set after deleting only the prefix term. -/
noncomputable def boundaryAlphaCoreCandidates
    (b : GoodBONG qV LV (n + 2)) (i : Fin (n + 1)) :
    Finset (WithTop ℚ) :=
  insert (b.halfGapCandidate i)
    (insert (b.leftDefectCandidate i i)
      (b.suffixSegmentAlphaCandidates i))

theorem boundaryAlphaCoreCandidates_nonempty
    (b : GoodBONG qV LV (n + 2)) (i : Fin (n + 1)) :
    (b.boundaryAlphaCoreCandidates i).Nonempty :=
  ⟨b.halfGapCandidate i, Finset.mem_insert_self _ _⟩

/-- The boundary candidate set after deleting both the prefix term and the
adjacent-defect term. -/
noncomputable def boundaryAlphaTailCandidates
    (b : GoodBONG qV LV (n + 2)) (i : Fin (n + 1)) :
    Finset (WithTop ℚ) :=
  insert (b.halfGapCandidate i) (b.suffixSegmentAlphaCandidates i)

theorem boundaryAlphaTailCandidates_nonempty
    (b : GoodBONG qV LV (n + 2)) (i : Fin (n + 1)) :
    (b.boundaryAlphaTailCandidates i).Nonempty :=
  ⟨b.halfGapCandidate i, Finset.mem_insert_self _ _⟩

/-- The optional suffix term is determined by the order at the current
coefficient and by the exact coefficient values strictly to its right. -/
theorem suffixSegmentAlphaCandidates_eq_of_order_eq_of_tail_valueUnits_eq
    (a : GoodBONG qV LV (n + 2)) (b : GoodBONG qV LW (n + 2))
    (i : Fin (n + 1))
    (hcurrent : a.order i.castSucc = b.order i.castSucc)
    (htail : ∀ j : Fin (n + 2), i.val < j.val →
      a.valueUnit j = b.valueUnit j) :
    a.suffixSegmentAlphaCandidates i =
      b.suffixSegmentAlphaCandidates i := by
  classical
  unfold suffixSegmentAlphaCandidates
  split
  next hi =>
    congr 1
    unfold suffixSegmentAlphaCandidate rightCompressionValue
    let sa := a.suffixAlphaSegmentWitness i hi
    let sb := b.suffixAlphaSegmentWitness i hi
    have hsegmentValues : ∀ j,
        (sa.toGoodBONG a.good).valueUnit j =
          (sb.toGoodBONG b.good).valueUnit j := by
      intro j
      change sa.bong.valueUnit j = sb.bong.valueUnit j
      rw [sa.valueUnit_eq, sb.valueUnit_eq]
      apply htail
      simp only [BONG.SegmentWitness.sourceIndex_val, sa, sb,
        suffixAlphaSegmentWitness, suffixAlphaLocalizationIndex]
      omega
    have hsegmentAlpha :
        (sa.toGoodBONG a.good).alphaValue
            (suffixAlphaLocalizationIndex i hi).localPivot =
          (sb.toGoodBONG b.good).alphaValue
            (suffixAlphaLocalizationIndex i hi).localPivot :=
      (sa.toGoodBONG a.good).alphaValue_eq_of_valueUnits_eq
        (sb.toGoodBONG b.good) hsegmentValues _
    have hpivotOrder :
        a.order
            (suffixAlphaLocalizationIndex i hi).pivotFin.castSucc =
          b.order
            (suffixAlphaLocalizationIndex i hi).pivotFin.castSucc := by
      change a.toBONG.order _ = b.toBONG.order _
      rw [a.toBONG.order_eq_ordUnit, b.toBONG.order_eq_ordUnit]
      congr 1
      apply htail
      change i.val <
        (suffixAlphaLocalizationIndex i hi).pivotFin.castSucc.val
      simp [suffixAlphaLocalizationIndex,
        AlphaLocalizationIndex.pivotFin]
    rw [hpivotOrder, hcurrent, hsegmentAlpha]
  next hi =>
    rfl

/-- The half-gap term is determined by the current order and the first
coefficient in the exact common tail. -/
theorem halfGapCandidate_eq_of_order_eq_of_tail_valueUnits_eq
    (a : GoodBONG qV LV (n + 2)) (b : GoodBONG qV LW (n + 2))
    (i : Fin (n + 1))
    (hcurrent : a.order i.castSucc = b.order i.castSucc)
    (htail : ∀ j : Fin (n + 2), i.val < j.val →
      a.valueUnit j = b.valueUnit j) :
    a.halfGapCandidate i = b.halfGapCandidate i := by
  have hnext : a.order i.succ = b.order i.succ := by
    change a.toBONG.order i.succ = b.toBONG.order i.succ
    rw [a.toBONG.order_eq_ordUnit, b.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) (htail i.succ (by simp))
  unfold halfGapCandidate
  rw [hcurrent, hnext]

/-- The local defect candidate is determined by the two coefficient values
of its adjacent pair. -/
theorem leftDefectCandidate_self_eq_of_pair_valueUnits_eq
    (a : GoodBONG qV LV (n + 2)) (b : GoodBONG qV LW (n + 2))
    (i : Fin (n + 1))
    (hleft : a.valueUnit i.castSucc = b.valueUnit i.castSucc)
    (hright : a.valueUnit i.succ = b.valueUnit i.succ) :
    a.leftDefectCandidate i i = b.leftDefectCandidate i i := by
  have hleftOrder : a.order i.castSucc = b.order i.castSucc := by
    calc
      a.order i.castSucc = ordUnit K (a.valueUnit i.castSucc) :=
        a.toBONG.order_eq_ordUnit i.castSucc
      _ = ordUnit K (b.valueUnit i.castSucc) := congrArg (ordUnit K) hleft
      _ = b.order i.castSucc :=
        (b.toBONG.order_eq_ordUnit i.castSucc).symm
  have hrightOrder : a.order i.succ = b.order i.succ := by
    calc
      a.order i.succ = ordUnit K (a.valueUnit i.succ) :=
        a.toBONG.order_eq_ordUnit i.succ
      _ = ordUnit K (b.valueUnit i.succ) := congrArg (ordUnit K) hright
      _ = b.order i.succ := (b.toBONG.order_eq_ordUnit i.succ).symm
  unfold leftDefectCandidate adjacentDefect adjacentProduct
  rw [hleftOrder, hrightOrder, hleft, hright]

/-- Equality of the three-term boundary cores follows from equality of the
half gap, local defect, and exact suffix data. -/
theorem boundaryAlphaCoreCandidates_eq
    (a : GoodBONG qV LV (n + 2)) (b : GoodBONG qV LW (n + 2))
    (i : Fin (n + 1))
    (hcurrent : a.order i.castSucc = b.order i.castSucc)
    (htail : ∀ j : Fin (n + 2), i.val < j.val →
      a.valueUnit j = b.valueUnit j)
    (hlocal : a.leftDefectCandidate i i =
      b.leftDefectCandidate i i) :
    a.boundaryAlphaCoreCandidates i =
      b.boundaryAlphaCoreCandidates i := by
  unfold boundaryAlphaCoreCandidates
  rw [a.halfGapCandidate_eq_of_order_eq_of_tail_valueUnits_eq
      b i hcurrent htail,
    hlocal,
    a.suffixSegmentAlphaCandidates_eq_of_order_eq_of_tail_valueUnits_eq
      b i hcurrent htail]

/-- Equality of the two-term boundary tails follows from equality of the
half gap and exact suffix data. -/
theorem boundaryAlphaTailCandidates_eq
    (a : GoodBONG qV LV (n + 2)) (b : GoodBONG qV LW (n + 2))
    (i : Fin (n + 1))
    (hcurrent : a.order i.castSucc = b.order i.castSucc)
    (htail : ∀ j : Fin (n + 2), i.val < j.val →
      a.valueUnit j = b.valueUnit j) :
    a.boundaryAlphaTailCandidates i =
      b.boundaryAlphaTailCandidates i := by
  unfold boundaryAlphaTailCandidates
  rw [a.halfGapCandidate_eq_of_order_eq_of_tail_valueUnits_eq
      b i hcurrent htail,
    a.suffixSegmentAlphaCandidates_eq_of_order_eq_of_tail_valueUnits_eq
      b i hcurrent htail]

/-- A preceding prefix alpha of at least `2e` dominates the half gap at the
next boundary.  The universal lower bound `orderGap ≥ -2e` supplies the
remaining arithmetic inequality. -/
theorem halfGapCandidate_le_prefixSegmentAlphaCandidate_of_alpha_ge_twoE
    (b : GoodBONG qV LV (n + 2)) (i : Fin (n + 1))
    (hi : 0 < i.val)
    (halpha : 2 * (ramificationIndex K : ℚ) ≤
      ((b.prefixAlphaSegmentWitness i hi).toGoodBONG b.good).alphaValue
        (prefixAlphaLocalizationIndex i hi).localPivot) :
    b.halfGapCandidate i ≤ b.prefixSegmentAlphaCandidate i hi := by
  rw [← b.coe_halfGapValue,
    b.prefixSegmentAlphaCandidate_eq_gap_add_alpha i hi]
  norm_cast
  have hgap : -(2 * (ramificationIndex K : Int)) ≤ b.orderGap i :=
    b.orderGap_ge_neg_two_mul_e i
  have hgapQ : -(2 * (ramificationIndex K : ℚ)) ≤
      (b.orderGap i : ℚ) := by
    exact_mod_cast hgap
  unfold halfGapValue
  linarith

/-- The type-II target has preceding alpha `2e-1`; the sharper current-gap
bound `2-2e` still makes its prefix term dominate the half gap. -/
theorem halfGapCandidate_le_prefixSegmentAlphaCandidate_of_alpha_ge_twoE_sub_one
    (b : GoodBONG qV LV (n + 2)) (i : Fin (n + 1))
    (hi : 0 < i.val)
    (hgap : 2 - 2 * (ramificationIndex K : Int) ≤ b.orderGap i)
    (halpha : 2 * (ramificationIndex K : ℚ) - 1 ≤
      ((b.prefixAlphaSegmentWitness i hi).toGoodBONG b.good).alphaValue
        (prefixAlphaLocalizationIndex i hi).localPivot) :
    b.halfGapCandidate i ≤ b.prefixSegmentAlphaCandidate i hi := by
  rw [← b.coe_halfGapValue,
    b.prefixSegmentAlphaCandidate_eq_gap_add_alpha i hi]
  norm_cast
  have hgapQ : 2 - 2 * (ramificationIndex K : ℚ) ≤
      (b.orderGap i : ℚ) := by
    exact_mod_cast hgap
  unfold halfGapValue
  linarith

/-- If the current gap is at least `2-2e` and the adjacent defect is at
least `2e-1`, the local defect term is dominated by the half gap. -/
theorem halfGapCandidate_le_leftDefectCandidate_self_of_typeII_bounds
    (b : GoodBONG qV LV (n + 2)) (i : Fin (n + 1))
    (hgap : 2 - 2 * (ramificationIndex K : Int) ≤ b.orderGap i)
    (hdefect :
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) ≤
        b.adjacentDefect i) :
    b.halfGapCandidate i ≤ b.leftDefectCandidate i i := by
  have hgapQ : 2 - 2 * (ramificationIndex K : ℚ) ≤
      (b.orderGap i : ℚ) := by
    exact_mod_cast hgap
  calc
    b.halfGapCandidate i = (b.halfGapValue i : WithTop ℚ) :=
      (b.coe_halfGapValue i).symm
    _ ≤ (((b.orderGap i : ℚ) +
          (2 * (ramificationIndex K : ℚ) - 1) : ℚ) : WithTop ℚ) := by
      apply WithTop.coe_le_coe.mpr
      unfold halfGapValue
      linarith
    _ = ((b.orderGap i : ℚ) : WithTop ℚ) +
        (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) := by
      norm_num
    _ ≤ ((b.orderGap i : ℚ) : WithTop ℚ) + b.adjacentDefect i :=
      by
        simpa only [add_comm] using
          (add_le_add_left hdefect ((b.orderGap i : ℚ) : WithTop ℚ))
    _ = b.leftDefectCandidate i i := by
      unfold leftDefectCandidate orderGap
      rfl

variable [Beli2006AlphaLaws.{u, v} K]

/-- If the prefix term is dominated by the half gap, Corollary 2.5(ii)
reduces to the half gap, the local defect, and the optional suffix term. -/
theorem alpha_eq_boundaryAlphaCoreMin
    (b : GoodBONG qV LV (n + 2)) (i : Fin (n + 1))
    (hprefix : ∀ x ∈ b.prefixSegmentAlphaCandidates i,
      b.halfGapCandidate i ≤ x) :
    b.alpha i =
      (b.boundaryAlphaCoreCandidates i).min'
        (b.boundaryAlphaCoreCandidates_nonempty i) := by
  rw [b.beli2009Corollary25_ii]
  apply le_antisymm
  · apply Finset.le_min'
    intro x hx
    simp only [boundaryAlphaCoreCandidates, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact Finset.min'_le _ _ (by
        simp [segmentRecursiveAlphaCandidates])
    · exact Finset.min'_le _ _ (by
        simp [segmentRecursiveAlphaCandidates])
    · exact Finset.min'_le _ _ (by
        simp [segmentRecursiveAlphaCandidates, hx])
  · apply Finset.le_min'
    intro x hx
    simp only [segmentRecursiveAlphaCandidates, Finset.mem_insert,
      Finset.mem_union] at hx
    rcases hx with rfl | rfl | hx | hx
    · exact Finset.min'_le _ _ (by
        simp [boundaryAlphaCoreCandidates])
    · exact Finset.min'_le _ _ (by
        simp [boundaryAlphaCoreCandidates])
    · exact (Finset.min'_le _ _ (by
        simp [boundaryAlphaCoreCandidates])).trans (hprefix x hx)
    · exact Finset.min'_le _ _ (by
        simp [boundaryAlphaCoreCandidates, hx])

/-- If the local defect is also dominated by the half gap, only the common
half-gap and suffix terms can contribute to the boundary alpha. -/
theorem alpha_eq_boundaryAlphaTailMin
    (b : GoodBONG qV LV (n + 2)) (i : Fin (n + 1))
    (hprefix : ∀ x ∈ b.prefixSegmentAlphaCandidates i,
      b.halfGapCandidate i ≤ x)
    (hlocal : b.halfGapCandidate i ≤ b.leftDefectCandidate i i) :
    b.alpha i =
      (b.boundaryAlphaTailCandidates i).min'
        (b.boundaryAlphaTailCandidates_nonempty i) := by
  rw [b.alpha_eq_boundaryAlphaCoreMin i hprefix]
  apply le_antisymm
  · apply Finset.le_min'
    intro x hx
    simp only [boundaryAlphaTailCandidates, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact Finset.min'_le _ _ (by
        simp [boundaryAlphaCoreCandidates])
    · exact Finset.min'_le _ _ (by
        simp [boundaryAlphaCoreCandidates, hx])
  · apply Finset.le_min'
    intro x hx
    simp only [boundaryAlphaCoreCandidates, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact Finset.min'_le _ _ (by
        simp [boundaryAlphaTailCandidates])
    · exact (Finset.min'_le _ _ (by
        simp [boundaryAlphaTailCandidates])).trans hlocal
    · exact Finset.min'_le _ _ (by
        simp [boundaryAlphaTailCandidates, hx])

/-- Boundary alpha equality when the two local defects agree. -/
theorem alpha_eq_of_boundary_local_eq
    (a : GoodBONG qV LV (n + 2)) (b : GoodBONG qV LW (n + 2))
    (i : Fin (n + 1))
    (hcurrent : a.order i.castSucc = b.order i.castSucc)
    (htail : ∀ j : Fin (n + 2), i.val < j.val →
      a.valueUnit j = b.valueUnit j)
    (hprefixA : ∀ x ∈ a.prefixSegmentAlphaCandidates i,
      a.halfGapCandidate i ≤ x)
    (hprefixB : ∀ x ∈ b.prefixSegmentAlphaCandidates i,
      b.halfGapCandidate i ≤ x)
    (hlocal : a.leftDefectCandidate i i =
      b.leftDefectCandidate i i) :
    a.alpha i = b.alpha i := by
  rw [a.alpha_eq_boundaryAlphaCoreMin i hprefixA,
    b.alpha_eq_boundaryAlphaCoreMin i hprefixB]
  have hcandidates := a.boundaryAlphaCoreCandidates_eq
    b i hcurrent htail hlocal
  simpa only [hcandidates]

/-- Boundary alpha equality when both local defects are dominated by their
respective (equal) half-gap terms. -/
theorem alpha_eq_of_boundary_local_dominated
    (a : GoodBONG qV LV (n + 2)) (b : GoodBONG qV LW (n + 2))
    (i : Fin (n + 1))
    (hcurrent : a.order i.castSucc = b.order i.castSucc)
    (htail : ∀ j : Fin (n + 2), i.val < j.val →
      a.valueUnit j = b.valueUnit j)
    (hprefixA : ∀ x ∈ a.prefixSegmentAlphaCandidates i,
      a.halfGapCandidate i ≤ x)
    (hprefixB : ∀ x ∈ b.prefixSegmentAlphaCandidates i,
      b.halfGapCandidate i ≤ x)
    (hlocalA : a.halfGapCandidate i ≤ a.leftDefectCandidate i i)
    (hlocalB : b.halfGapCandidate i ≤ b.leftDefectCandidate i i) :
    a.alpha i = b.alpha i := by
  rw [a.alpha_eq_boundaryAlphaTailMin i hprefixA hlocalA,
    b.alpha_eq_boundaryAlphaTailMin i hprefixB hlocalB]
  have hcandidates := a.boundaryAlphaTailCandidates_eq
    b i hcurrent htail
  simpa only [hcandidates]

variable [Beli2009AlphaParityLaws.{u, v} K]

/-- If the preceding coefficient gap is at least `2e`, the last alpha of
the canonical prefix segment is at least `2e`. -/
theorem prefixSegmentAlphaValue_ge_twoE_of_predecessor_gap
    (b : GoodBONG qV LV (n + 2)) (i : Fin (n + 1))
    (hi : 0 < i.val)
    (hprev : 2 * (ramificationIndex K : Int) ≤
      b.order i.castSucc - b.order ⟨i.val - 1, by omega⟩) :
    2 * (ramificationIndex K : ℚ) ≤
      ((b.prefixAlphaSegmentWitness i hi).toGoodBONG b.good).alphaValue
        (prefixAlphaLocalizationIndex i hi).localPivot := by
  let p := prefixAlphaLocalizationIndex i hi
  let w := b.prefixAlphaSegmentWitness i hi
  let c := w.toGoodBONG b.good
  have hgap : 2 * (ramificationIndex K : Int) ≤
      c.orderGap p.localPivot := by
    unfold orderGap
    change 2 * (ramificationIndex K : Int) ≤
      w.bong.order p.localPivot.succ -
        w.bong.order p.localPivot.castSucc
    rw [w.order_eq, w.order_eq]
    have hsucc : w.sourceIndex p.localPivot.succ = i.castSucc := by
      apply Fin.ext
      simp [p, prefixAlphaLocalizationIndex,
        AlphaLocalizationIndex.localPivot,
        BONG.SegmentWitness.sourceIndex]
      omega
    have hcast : w.sourceIndex p.localPivot.castSucc =
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      simp [p, prefixAlphaLocalizationIndex,
        AlphaLocalizationIndex.localPivot,
        BONG.SegmentWitness.sourceIndex]
    rw [hsucc, hcast]
    exact hprev
  have halpha := c.beli2009Lemma27_ii p.localPivot hgap
  rw [halpha]
  unfold halfGapValue
  have hgapQ : 2 * (ramificationIndex K : ℚ) ≤
      (c.orderGap p.localPivot : ℚ) := by
    exact_mod_cast hgap
  linarith

/-- If the preceding coefficient gap is exactly `2e-2`, Corollary 2.9(i)
gives the exact last prefix alpha `2e-1`. -/
theorem prefixSegmentAlphaValue_eq_twoE_sub_one_of_predecessor_gap_eq
    (b : GoodBONG qV LV (n + 2)) (i : Fin (n + 1))
    (hi : 0 < i.val)
    (hprev : b.order i.castSucc -
        b.order ⟨i.val - 1, by omega⟩ =
      2 * (ramificationIndex K : Int) - 2) :
    ((b.prefixAlphaSegmentWitness i hi).toGoodBONG b.good).alphaValue
        (prefixAlphaLocalizationIndex i hi).localPivot =
      2 * (ramificationIndex K : ℚ) - 1 := by
  let p := prefixAlphaLocalizationIndex i hi
  let w := b.prefixAlphaSegmentWitness i hi
  let c := w.toGoodBONG b.good
  have hgap : c.orderGap p.localPivot =
      2 * (ramificationIndex K : Int) - 2 := by
    unfold orderGap
    change w.bong.order p.localPivot.succ -
        w.bong.order p.localPivot.castSucc = _
    rw [w.order_eq, w.order_eq]
    have hsucc : w.sourceIndex p.localPivot.succ = i.castSucc := by
      apply Fin.ext
      simp [p, prefixAlphaLocalizationIndex,
        AlphaLocalizationIndex.localPivot,
        BONG.SegmentWitness.sourceIndex]
      omega
    have hcast : w.sourceIndex p.localPivot.castSucc =
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      simp [p, prefixAlphaLocalizationIndex,
        AlphaLocalizationIndex.localPivot,
        BONG.SegmentWitness.sourceIndex]
    rw [hsucc, hcast]
    exact hprev
  have halpha := c.beli2009Corollary29_i p.localPivot
    (Or.inr (Or.inr (Or.inr hgap)))
  rw [halpha]
  unfold halfGapValue
  rw [hgap]
  push_cast
  ring

end BONG.GoodBONG

end Bong
