/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma517Complete
import Bong.Bong.Beli2019PrefixExtensionFull
import Bong.Bong.Beli2019PrefixChange
import Bong.Bong.Beli2019Reflexivity
import Bong.Bong.Beli2009AlphaMonotonicity

/-!
# Beli (2019), Section 5, condition (ii): the equal-order branch

After Lemma 5.17, the source and target order sequences agree through the
current boundary.  Corollary 5.10 then changes the source good BONG so that
its first `i` ambient vectors agree with the target.  This file carries
out the remaining finite-candidate comparison

`A_i(M,N) <= alpha_i(M)`.

The proof follows the four alternatives in the definition of `alpha_i`:
the half gap, the current adjacent defect, a preceding adjacent defect, and
a following adjacent defect.  It is deliberately stated independently of
the concrete almost-Jordan profile so it can be reused after reverse duality.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- A sequence-prefix agreement gives equality of the actual good-BONG
orders at every coordinate in that prefix. -/
theorem order_eq_of_orderSequence_prefixAgreement
    {a : GoodBONG q M (n + 1)} {b : GoodBONG q N (n + 1)}
    {p j : Nat}
    (h : a.orderSequence.PrefixAgreement b.orderSequence p)
    (hj : j < p) :
    a.order ⟨j, hj.trans_le h.leftBound⟩ =
      b.order ⟨j, hj.trans_le h.rightBound⟩ := by
  have heq := h.entry_eq j hj
  rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
      (hj.trans_le h.leftBound),
    BeliOrderSequence.entryOrZero_of_lt b.orderSequence
      (hj.trans_le h.rightBound)] at heq
  exact heq

/-- If the target prefix through `i - 1` is literally the source prefix,
the primary comparison defect is bounded by the source adjacent defect at
the current boundary. -/
theorem truncatedPrefixDefect_neg_succ_pred_le_adjacent_of_prefixProduct_eq
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hprefix : a.prefixProduct (i.val - 1) =
      b.prefixProduct (i.val - 1)) :
    a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) ≤
      a.adjacentDefect (representationAlphaIndex i) := by
  apply (a.truncatedPrefixDefect_le_defect b (-1)
    (i.val + 1) (i.val - 1)).trans_eq
  unfold adjacentDefect
  have hi : (i.val - 1) + 1 < n + 1 := by
    have := i.pos
    have := i.lt_large
    omega
  have hproduct := a.prefixProduct_add_two (i.val - 1) hi
  have hindex : i.val + 1 = (i.val - 1) + 2 := by
    have := i.pos
    omega
  rw [hindex, hproduct, hprefix]
  have hzero :
      (⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Fin (n + 1)) =
        (representationAlphaIndex i).castSucc := by
    apply Fin.ext
    rfl
  have hone :
      (⟨i.val - 1 + 1, hi⟩ : Fin (n + 1)) =
        (representationAlphaIndex i).succ := by
    apply Fin.ext
    simp only [representationAlphaIndex, Fin.succ]
  rw [hzero, hone]
  rw [show (-1 : Kˣ) *
      (b.prefixProduct (i.val - 1) *
        a.valueUnit (representationAlphaIndex i).castSucc *
        a.valueUnit (representationAlphaIndex i).succ) *
      b.prefixProduct (i.val - 1) =
      a.adjacentProduct (representationAlphaIndex i) *
        b.prefixProduct (i.val - 1) ^ 2 by
    unfold adjacentProduct representationAlphaIndex
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_one, pow_two]
    ring]
  exact defectOrder_mul_square _ _

/-- Current-order agreement and literal equality of the preceding scalar
prefix bound the primary `A_i` candidate by the current source
left-defect candidate. -/
theorem representationPrimaryDefect_le_current_leftDefect
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hcurrent : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩)
    (hprefix : a.prefixProduct (i.val - 1) =
      b.prefixProduct (i.val - 1)) :
    a.representationPrimaryDefect b i ≤
      a.leftDefectCandidate (representationAlphaIndex i)
        (representationAlphaIndex i) := by
  have hsub : i.val - 1 + 1 = i.val := by
    have := i.pos
    omega
  have hsucc : (representationAlphaIndex i).succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [representationAlphaIndex, Fin.succ]
    exact hsub
  have hcast : (representationAlphaIndex i).castSucc =
      (⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ :
        Fin (n + 1)) := by
    apply Fin.ext
    rfl
  unfold representationPrimaryDefect leftDefectCandidate
  rw [hsucc, hcast, ← hcurrent]
  gcongr
  exact a.truncatedPrefixDefect_neg_succ_pred_le_adjacent_of_prefixProduct_eq
    b i hprefix

/-- Current-order equality identifies the half-gap candidate of `A_i` with
the half-gap candidate defining the source `alpha_i`. -/
theorem representationAlpha_le_sourceHalfGap_of_currentOrder
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hcurrent : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩) :
    a.representationAlpha b i ≤
      a.halfGapCandidate (representationAlphaIndex i) := by
  have hsub : i.val - 1 + 1 = i.val := by
    have := i.pos
    omega
  have hsucc : (representationAlphaIndex i).succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [representationAlphaIndex, Fin.succ]
    exact hsub
  have hcast : (representationAlphaIndex i).castSucc =
      (⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ :
        Fin (n + 1)) := by
    apply Fin.ext
    rfl
  calc
    a.representationAlpha b i ≤ a.representationHalfGap b i :=
      a.representationAlpha_le_halfGap b i
    _ = a.halfGapCandidate (representationAlphaIndex i) := by
      unfold representationHalfGap halfGapCandidate
      rw [hsucc, hcast, ← hcurrent]

/-- If the next source alpha exists, the left cap in the primary
representation candidate gives the estimate

`A_i(M,N) ≤ R_(i+1) - R_i + alpha_(i+1)(M)`.

Only equality of the current orders is used.  This is the estimate needed
in the two-step equality branch below; it avoids asking Corollary 5.10 to
prescribe one vector more than its hypotheses justify. -/
theorem representationAlpha_le_orderGap_add_nextAlpha_of_currentOrder
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hnext : i.val + 1 < n + 1)
    (hcurrent : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩) :
    a.representationAlpha b i ≤
      (((((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ)) :
            WithTop ℚ) +
        (a.alphaValue ⟨i.val, by omega⟩ : WithTop ℚ)) := by
  have hcap := a.truncatedPrefixDefect_le_leftCap b (-1)
    (i.val + 1) (i.val - 1)
  rw [a.prefixAlphaCap_of_internal (by omega) hnext] at hcap
  have hindex :
      (⟨i.val + 1 - 1, by omega⟩ : Fin n) =
        (⟨i.val, by omega⟩ : Fin n) := by
    apply Fin.ext
    simp only [Fin.val_mk, Nat.add_sub_cancel]
  rw [hindex] at hcap
  calc
    a.representationAlpha b i ≤
        a.representationPrimaryDefect b i :=
      a.representationAlpha_le_primary b i
    _ ≤
        (((((a.order ⟨i.val, i.lt_large⟩ -
          a.order ⟨i.val - 1,
            (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ)) :
              WithTop ℚ) +
          (a.alphaValue ⟨i.val, by omega⟩ : WithTop ℚ)) := by
      unfold representationPrimaryDefect
      rw [← hcurrent]
      gcongr

/-- Beli (2009), Corollary 2.3(i), in the adjacent form used after the
equal-order branch of Lemma 5.17.  If the two source orders two places apart
are equal, then

`R_(i+1) - R_i + alpha_(i+1) = alpha_i`.
-/
theorem orderGap_add_nextAlpha_eq_alpha_of_twoStep_eq
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hnext : i.val + 1 < n + 1)
    (houter : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      a.order ⟨i.val + 1, hnext⟩) :
    (((((a.order ⟨i.val, i.lt_large⟩ -
      a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ)) :
          WithTop ℚ) +
      (a.alphaValue ⟨i.val, by omega⟩ : WithTop ℚ)) =
        (a.alphaValue (representationAlphaIndex i) : WithTop ℚ) := by
  cases n with
  | zero => omega
  | succ N =>
      let current : Fin (N + 1) := representationAlphaIndex i
      let next : Fin (N + 1) := ⟨i.val, by omega⟩
      have hle : current ≤ next := by
        change i.val - 1 ≤ i.val
        omega
      have hcurrentCast : current.castSucc =
          (⟨i.val - 1, by omega⟩ : Fin (N + 2)) := by
        apply Fin.ext
        rfl
      have hcurrentSucc : current.succ =
          (⟨i.val, by omega⟩ : Fin (N + 2)) := by
        apply Fin.ext
        simpa only [current, representationAlphaIndex, Fin.val_succ,
          Fin.val_mk] using
            (Nat.sub_add_cancel
              (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt i.pos)))
      have hnextCast : next.castSucc =
          (⟨i.val, by omega⟩ : Fin (N + 2)) := by
        apply Fin.ext
        rfl
      have hnextSucc : next.succ =
          (⟨i.val + 1, by omega⟩ : Fin (N + 2)) := by
        apply Fin.ext
        rfl
      have hsum : a.adjacentOrderSum current =
          a.adjacentOrderSum next := by
        unfold adjacentOrderSum
        rw [hcurrentCast, hcurrentSucc, hnextCast, hnextSucc]
        rw [← houter]
        omega
      have hend :=
        (a.beli2009Corollary23 current next hle hsum).leftEndpoint_eq
          next hle le_rfl
      unfold alphaLeftEndpoint at hend
      rw [hnextCast, hcurrentCast] at hend
      have hrat :
          ((a.order ⟨i.val, i.lt_large⟩ -
            a.order ⟨i.val - 1,
              (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ) +
              a.alphaValue ⟨i.val, by omega⟩ =
            a.alphaValue (representationAlphaIndex i) := by
        change
          ((a.order ⟨i.val, by omega⟩ -
            a.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) +
              a.alphaValue next = a.alphaValue current
        push_cast at hend ⊢
        linarith
      exact_mod_cast hrat

/-- Every source left-defect candidate bounds `A_i` once Corollary 5.10 has
aligned the source and target through the current coordinate. -/
theorem representationAlpha_le_sourceLeftDefect_of_alignedPrefix
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (horders : a.orderSequence.PrefixAgreement b.orderSequence i.val)
    (hambient : BONG.AmbientPrefixAgreement a.toBONG b.toBONG i.val)
    (j : Fin n) (hjle : j ≤ representationAlphaIndex i) :
    a.representationAlpha b i ≤
      a.leftDefectCandidate (representationAlphaIndex i) j := by
  have hcurrent : a.order
      ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      b.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ :=
    order_eq_of_orderSequence_prefixAgreement horders (by
      have := i.pos
      omega)
  have hprefix : a.prefixProduct (i.val - 1) =
      b.prefixProduct (i.val - 1) :=
    hambient.prefixProduct_eq (i.val - 1) (by omega)
  by_cases hjeq : j = representationAlphaIndex i
  · subst j
    exact (a.representationAlpha_le_primary b i).trans
      (a.representationPrimaryDefect_le_current_leftDefect
        b i hcurrent hprefix)
  · have hjlt : j < representationAlphaIndex i :=
      lt_of_le_of_ne hjle hjeq
    have hjltNat : j.val < i.val - 1 := hjlt
    have hiTwo : 2 ≤ i.val := by omega
    let p : Fin n :=
      ⟨(representationAlphaIndex i).val - 1, by omega⟩
    have hjp : j ≤ p := by
      change j.val ≤ p.val
      dsimp only [p]
      omega
    have hiPredInternal : i.val - 1 < n + 1 := by
      have := i.lt_large
      omega
    have hcap := a.truncatedPrefixDefect_le_rightCap b (-1)
      (i.val + 1) (i.val - 1)
    rw [b.prefixAlphaCap_of_internal (by omega) hiPredInternal] at hcap
    have hpIndex : p = ⟨(i.val - 1) - 1, by omega⟩ := by
      apply Fin.ext
      dsimp only [p, representationAlphaIndex]
    rw [← hpIndex] at hcap
    have htargetAlpha : (b.alphaValue p : WithTop ℚ) ≤
        b.leftDefectCandidate p j := by
      rw [b.coe_alphaValue]
      exact b.alpha_le_leftDefectCandidate hjp
    have hjOrderBound : j.val < n + 1 := j.isLt.trans_le (by omega)
    have hsourceJ : a.order ⟨j.val, hjOrderBound⟩ =
        b.order ⟨j.val, hjOrderBound⟩ :=
      order_eq_of_orderSequence_prefixAgreement horders (by omega)
    let gap : WithTop ℚ :=
      (((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ) :
            WithTop ℚ)
    have hprimary : a.representationPrimaryDefect b i ≤
        gap + (b.alphaValue p : WithTop ℚ) := by
      unfold representationPrimaryDefect gap
      exact add_le_add_right hcap gap
    have hpSucc : p.succ =
        (⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ :
          Fin (n + 1)) := by
      apply Fin.ext
      dsimp only [p, representationAlphaIndex, Fin.succ]
      omega
    have hsourceJ' : a.order j.castSucc = b.order j.castSucc := by
      have hjCast : j.castSucc = (⟨j.val, hjOrderBound⟩ : Fin (n + 1)) := by
        apply Fin.ext
        rfl
      rw [hjCast]
      exact hsourceJ
    have hrepSucc : (representationAlphaIndex i).succ =
        (⟨i.val, i.lt_large⟩ : Fin (n + 1)) := by
      apply Fin.ext
      change (i.val - 1) + 1 = i.val
      have := i.pos
      omega
    have hadjacent : b.adjacentDefect j = a.adjacentDefect j := by
      unfold adjacentDefect adjacentProduct
      have hja : a.valueUnit j.castSucc = b.valueUnit j.castSucc :=
        hambient.valueUnit_eq j.val (by omega)
      have hjb : a.valueUnit j.succ = b.valueUnit j.succ :=
        hambient.valueUnit_eq (j.val + 1) (by omega)
      rw [← hja, ← hjb]
    have hcandidate : gap + b.leftDefectCandidate p j =
        a.leftDefectCandidate (representationAlphaIndex i) j := by
      unfold gap leftDefectCandidate
      rw [hpSucc, ← hcurrent, ← hsourceJ', hrepSucc, hadjacent,
        ← add_assoc, ← WithTop.coe_add]
      congr 1
      norm_cast
      omega
    calc
      a.representationAlpha b i ≤ a.representationPrimaryDefect b i :=
        a.representationAlpha_le_primary b i
      _ ≤ gap + (b.alphaValue p : WithTop ℚ) := hprimary
      _ ≤ gap + b.leftDefectCandidate p j :=
        by simpa only [add_comm] using add_le_add_left htargetAlpha gap
      _ = a.leftDefectCandidate (representationAlphaIndex i) j := hcandidate

/-- Every source right-defect candidate bounds `A_i`; here the left cap of
the primary comparison defect supplies the next source alpha. -/
theorem representationAlpha_le_sourceRightDefect_of_currentOrder
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hcurrent : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩)
    (hprefix : a.prefixProduct (i.val - 1) =
      b.prefixProduct (i.val - 1))
    (j : Fin n) (hle : representationAlphaIndex i ≤ j) :
    a.representationAlpha b i ≤
      a.rightDefectCandidate (representationAlphaIndex i) j := by
  by_cases hjeq : j = representationAlphaIndex i
  · subst j
    exact (a.representationAlpha_le_primary b i).trans
      (a.representationPrimaryDefect_le_current_leftDefect
        b i hcurrent hprefix)
  · have hlt : representationAlphaIndex i < j :=
      lt_of_le_of_ne hle (Ne.symm hjeq)
    let s : Fin n :=
      ⟨(representationAlphaIndex i).val + 1, by omega⟩
    have hsj : s ≤ j := by
      change s.val ≤ j.val
      dsimp only [s]
      omega
    have hiSuccInternal : i.val + 1 < n + 1 := by
      have := j.isLt
      change i.val - 1 < j.val at hlt
      omega
    have hcap := a.truncatedPrefixDefect_le_leftCap b (-1)
      (i.val + 1) (i.val - 1)
    rw [a.prefixAlphaCap_of_internal (by omega) hiSuccInternal] at hcap
    have hsIndex : s = ⟨(i.val + 1) - 1, by omega⟩ := by
      apply Fin.ext
      dsimp only [s, representationAlphaIndex]
      have := i.pos
      omega
    rw [← hsIndex] at hcap
    have hsourceAlpha : (a.alphaValue s : WithTop ℚ) ≤
        a.rightDefectCandidate s j := by
      rw [a.coe_alphaValue]
      exact a.alpha_le_rightDefectCandidate hsj
    let gap : WithTop ℚ :=
      (((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ) :
            WithTop ℚ)
    have hprimary : a.representationPrimaryDefect b i ≤
        gap + (a.alphaValue s : WithTop ℚ) := by
      unfold representationPrimaryDefect gap
      exact add_le_add_right hcap gap
    have hsCast : s.castSucc =
        (⟨i.val, i.lt_large⟩ : Fin (n + 1)) := by
      apply Fin.ext
      change (i.val - 1) + 1 = i.val
      have := i.pos
      omega
    have hcurrentCast : (representationAlphaIndex i).castSucc =
        (⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ :
          Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hcandidate : gap + a.rightDefectCandidate s j =
        a.rightDefectCandidate (representationAlphaIndex i) j := by
      unfold gap rightDefectCandidate
      rw [← hcurrent, hsCast, hcurrentCast]
      rw [← add_assoc, ← WithTop.coe_add]
      congr 1
      norm_cast
      omega
    calc
      a.representationAlpha b i ≤ a.representationPrimaryDefect b i :=
        a.representationAlpha_le_primary b i
      _ ≤ gap + (a.alphaValue s : WithTop ℚ) := hprimary
      _ ≤ gap + a.rightDefectCandidate s j :=
        by simpa only [add_comm] using add_le_add_left hsourceAlpha gap
      _ = a.rightDefectCandidate (representationAlphaIndex i) j := hcandidate

/-- The finite-candidate calculation following Lemma 5.17.  The source and
target orders and actual scalar prefixes agree through the current entry. -/
theorem representationAlpha_le_sourceAlpha_of_aligned_currentPrefix
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (horders : a.orderSequence.PrefixAgreement b.orderSequence i.val)
    (hambient : BONG.AmbientPrefixAgreement
      a.toBONG b.toBONG i.val) :
    a.representationAlpha b i ≤
      a.alpha (representationAlphaIndex i) := by
  have hprefix : a.prefixProduct (i.val - 1) =
      b.prefixProduct (i.val - 1) :=
    hambient.prefixProduct_eq (i.val - 1) (by omega)
  have hcurrent : a.order
      ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      b.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ :=
    order_eq_of_orderSequence_prefixAgreement horders (by
      have := i.pos
      omega)
  unfold alpha
  apply Finset.le_min'
  intro x hx
  simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union] at hx
  rcases hx with rfl | hx | hx
  · exact a.representationAlpha_le_sourceHalfGap_of_currentOrder
      b i hcurrent
  · rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    exact a.representationAlpha_le_sourceLeftDefect_of_alignedPrefix
      b i horders hambient j (Finset.mem_filter.mp hj).2
  · rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    exact a.representationAlpha_le_sourceRightDefect_of_currentOrder
      b i hcurrent hprefix j (Finset.mem_filter.mp hj).2

/-- The paper-faithful equal-order branch following Lemma 5.17.  Corollary
5.10 is first used at prefix length `i - 1`, which is automatic from the
current-order equality.  At the next step there are only two possibilities:

* a strict two-step rise (or the terminal boundary), where Corollary 5.10
  legitimately extends the literal prefix through the current vector;
* equality of the two source orders two places apart, where Beli (2009),
  Corollary 2.3(i), identifies
  `R_(i+1) - R_i + alpha_(i+1)` with `alpha_i` and no extra vector alignment
  is needed.

Thus the omitted Corollary 5.10 trigger in the printed proof is not made an
assumption. -/
theorem Beli2019Lemma517Data.commonBound_of_twoStep_split
    [BONGStructuralLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q L (n + 1))
    (hLM : L ≤ M)
    {InReducedRange : RepresentationIndex (n + 1) (n + 1) → Prop}
    (D : Beli2019Lemma517Data a b InReducedRange)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : InReducedRange i)
    (hcurrent : a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1)) :
    a.representationAlpha b i ≤
      min (a.prefixAlphaCap i.val) (b.prefixAlphaCap i.val) := by
  letI : Beli2006PrefixChangeLaws.{u, v} K :=
    prefixChangeLawsOfClassification
  rcases a.exists_goodBONG_with_previousAmbientPrefix_of_lemma517
      b hLM D i hi hcurrent with ⟨c, hcPrevious⟩
  have hcOrders :
      c.orderSequence.PrefixAgreement b.orderSequence i.val := by
    rw [c.orderSequence_eq_of_same_lattice a]
    exact D.prefixAgreement i hi hcurrent
  have hcCurrent : c.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ :=
    order_eq_of_orderSequence_prefixAgreement hcOrders (by
      have := i.pos
      omega)
  have halignedBound
      (htrigger : BeliPrefixExtensionTrigger
        (ramificationIndex K : Int)
          c.orderSequence b.orderSequence i.val) :
      c.representationAlpha b i ≤
        c.alpha (representationAlphaIndex i) := by
    rcases c.exists_goodBONG_with_ambientPrefix b hLM
        { agreement := hcOrders, trigger := htrigger } with ⟨d, hdPrefix⟩
    have hdOrders :
        d.orderSequence.PrefixAgreement b.orderSequence i.val := by
      rw [d.orderSequence_eq_of_same_lattice c]
      exact hcOrders
    have hdBound :=
      d.representationAlpha_le_sourceAlpha_of_aligned_currentPrefix
        b i hdOrders hdPrefix
    have hrepresentation :
        c.representationAlpha b i = d.representationAlpha b i :=
      representationAlpha_invariant c d b b i
    have halphaValue :
        d.alphaValue (representationAlphaIndex i) =
          c.alphaValue (representationAlphaIndex i) :=
      d.alpha_invariant c (representationAlphaIndex i)
    calc
      c.representationAlpha b i = d.representationAlpha b i :=
        hrepresentation
      _ ≤ d.alpha (representationAlphaIndex i) := hdBound
      _ = c.alpha (representationAlphaIndex i) := by
        rw [← d.coe_alphaValue, ← c.coe_alphaValue, halphaValue]
  have hcBound : c.representationAlpha b i ≤
      c.alpha (representationAlphaIndex i) := by
    by_cases hnext : i.val + 1 < n + 1
    · let current : Fin (n + 1) :=
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩
      let twoAhead : Fin (n + 1) := ⟨i.val + 1, hnext⟩
      have htwoStep : c.order current ≤ c.order twoAhead := by
        have hraw := c.good current (by
          dsimp only [current, Fin.val_mk]
          have := i.pos
          omega)
        have hindex :
            (⟨current.val + 2, by
              dsimp only [current, Fin.val_mk]
              have := i.pos
              omega⟩ : Fin (n + 1)) = twoAhead := by
          apply Fin.ext
          dsimp only [current, twoAhead, Fin.val_mk]
          have := i.pos
          omega
        rw [hindex] at hraw
        exact hraw
      by_cases houter : c.order current = c.order twoAhead
      · have hnextAlpha :=
          c.representationAlpha_le_orderGap_add_nextAlpha_of_currentOrder
            b i hnext hcCurrent
        have hrecurrence :=
          c.orderGap_add_nextAlpha_eq_alpha_of_twoStep_eq i hnext houter
        rw [← c.coe_alphaValue]
        exact hnextAlpha.trans_eq hrecurrence
      · have hstrict : c.order current < c.order twoAhead :=
          lt_of_le_of_ne htwoStep houter
        apply halignedBound
        apply BeliPrefixExtensionTrigger.strictTwoStep hnext
        rw [BeliOrderSequence.entryOrZero_of_lt c.orderSequence
              (by have := i.lt_large; omega),
          BeliOrderSequence.entryOrZero_of_lt c.orderSequence hnext]
        simpa only [current, twoAhead, BONG.GoodBONG.orderSequence_at]
          using hstrict
    · apply halignedBound
      apply BeliPrefixExtensionTrigger.terminal
      omega
  have hrepresentation :
      a.representationAlpha b i = c.representationAlpha b i :=
    representationAlpha_invariant a c b b i
  have halphaValue :
      c.alphaValue (representationAlphaIndex i) =
        a.alphaValue (representationAlphaIndex i) :=
    c.alpha_invariant a (representationAlphaIndex i)
  apply D.commonBound_of_leftCap i hi hcurrent
  rw [a.prefixAlphaCap_of_internal i.pos i.lt_large]
  rw [hrepresentation]
  change c.representationAlpha b i ≤
    (a.alphaValue (representationAlphaIndex i) : WithTop ℚ)
  rw [← halphaValue, c.coe_alphaValue]
  exact hcBound

/-- Lemma 5.17 together with its Corollary 5.10 trigger proves the complete
common-cap inequality in the equal-order branch.  The temporary source BONG
chosen by Corollary 5.10 is transported back to the original source BONG by
the already proved Beli (2009) classification invariance. -/
theorem Beli2019Lemma517PrefixData.commonBound
    [BONGStructuralLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q L (n + 1))
    (hLM : L ≤ M)
    {InReducedRange : RepresentationIndex (n + 1) (n + 1) → Prop}
    (D : Beli2019Lemma517PrefixData a b InReducedRange)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : InReducedRange i)
    (hcurrent : a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1)) :
    a.representationAlpha b i ≤
      min (a.prefixAlphaCap i.val) (b.prefixAlphaCap i.val) := by
  letI : Beli2006PrefixChangeLaws.{u, v} K :=
    prefixChangeLawsOfClassification
  rcases a.exists_goodBONG_with_ambientPrefix_of_lemma517 b hLM D i hi
      hcurrent with ⟨c, hcPrefix⟩
  have hcOrders :
      c.orderSequence.PrefixAgreement b.orderSequence i.val := by
    rw [c.orderSequence_eq_of_same_lattice a]
    exact D.prefixAgreement i hi hcurrent
  have hcBound :=
    c.representationAlpha_le_sourceAlpha_of_aligned_currentPrefix
      b i hcOrders hcPrefix
  have hrepresentation :
      a.representationAlpha b i = c.representationAlpha b i :=
    representationAlpha_invariant a c b b i
  have halphaValue :
      c.alphaValue (representationAlphaIndex i) =
        a.alphaValue (representationAlphaIndex i) :=
    c.alpha_invariant a (representationAlphaIndex i)
  apply D.toBeli2019Lemma517Data.commonBound_of_leftCap i hi hcurrent
  rw [a.prefixAlphaCap_of_internal i.pos i.lt_large]
  rw [hrepresentation]
  change c.representationAlpha b i ≤
    (a.alphaValue (representationAlphaIndex i) : WithTop ℚ)
  rw [← halphaValue, c.coe_alphaValue]
  exact hcBound

end BONG.GoodBONG

end Bong
