/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Proposition62EqualRank
import Bong.Bong.Beli2019SuffixMaximum
import Bong.Bong.Beli2019WeightSegmentSum

/-!
# Beli (2019), Lemma 6.9(iv): the right-tail minimum formula

On an unchanged order suffix, equality of adjacent order sums gives equality
of the corresponding suffix sums of the two `W`-sequences.  Proposition 6.2
orders those sequences, so Lemma 5.6(ii) identifies every odd coordinate on
the suffix as a maximum.  Rewriting the odd coordinates gives exactly
`beta_i = min alpha_i (S_(i+1) - S_(u+1) + beta_u)`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Lemma 6.9(iv) with the order relation between the two `W`-sequences
supplied explicitly. -/
theorem beli2019Lemma69_iv_beta_eq_min_of_weightOrder
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (hW : BeliOrderLE a.weightSequence b.weightSequence)
    (first j : Fin (n + 1)) (hfirst : first <= j)
    (hsuffix : forall k, first.val + 1 <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k) :
    b.alphaValue j =
      min (a.alphaValue j)
        (((b.order j.succ - b.order first.succ : Int) : Rat) +
          b.alphaValue first) := by
  have hsegment := weightSegmentSum_eq_of_adjacentOrderSums
    a b (first.val + 1) (n + 1) (by omega) (by omega) (by
      intro k hkLeft hkRight
      have hk := hsuffix k hkLeft (by omega)
      have hkNext := hsuffix (k + 1) (by omega) (by omega)
      have hkA := a.orderSequence_entryOrZero_eq_order
        ⟨k, by omega⟩
      have hkB := b.orderSequence_entryOrZero_eq_order
        ⟨k, by omega⟩
      have hkNextA := a.orderSequence_entryOrZero_eq_order
        ⟨k + 1, by omega⟩
      have hkNextB := b.orderSequence_entryOrZero_eq_order
        ⟨k + 1, by omega⟩
      rw [hkA, hkB] at hk
      rw [hkNextA, hkNextB] at hkNext
      rw [hk, hkNext])
  have hweightSuffix :
      a.weightSequence.suffixSum (2 * (first.val + 1)) =
        b.weightSequence.suffixSum (2 * (first.val + 1)) := by
    rw [a.weightSequence.suffixSum_eq_total_sub_prefix
        (2 * (first.val + 1)) (by omega),
      b.weightSequence.suffixSum_eq_total_sub_prefix
        (2 * (first.val + 1)) (by omega)]
    simpa only [BeliOrderSequence.segmentSum] using hsegment
  have hmax := hW.entryOrZero_eq_max_of_suffixSum_eq_of_evenGap
    (2 * (first.val + 1)) (2 * j.val + 1) (by omega) (by omega)
    (by omega) (by
      refine ⟨j.val - first.val, ?_⟩
      omega) hweightSuffix
  have haEntry :
      a.weightSequence.entryOrZero (2 * j.val + 1) =
        (a.order j.succ : Rat) - a.alphaValue j := by
    rw [BeliOrderSequence.entryOrZero_of_lt _ (by omega)]
    change a.weightSequence.value ⟨2 * j.val + 1, by omega⟩ = _
    simpa only using a.weightSequence_odd j
  have hbEntry :
      b.weightSequence.entryOrZero (2 * j.val + 1) =
        (b.order j.succ : Rat) - b.alphaValue j := by
    rw [BeliOrderSequence.entryOrZero_of_lt _ (by omega)]
    change b.weightSequence.value ⟨2 * j.val + 1, by omega⟩ = _
    simpa only using b.weightSequence_odd j
  have hfirstEntry :
      b.weightSequence.entryOrZero (2 * (first.val + 1) - 1) =
        (b.order first.succ : Rat) - b.alphaValue first := by
    rw [show 2 * (first.val + 1) - 1 = 2 * first.val + 1 by omega]
    rw [BeliOrderSequence.entryOrZero_of_lt _ (by omega)]
    change b.weightSequence.value ⟨2 * first.val + 1, by omega⟩ = _
    simpa only using b.weightSequence_odd first
  rw [haEntry, hbEntry, hfirstEntry] at hmax
  have horderJ := hsuffix (j.val + 1) (by omega) (by omega)
  have horderJA := a.orderSequence_entryOrZero_eq_order
    ⟨j.val + 1, by omega⟩
  have horderJB := b.orderSequence_entryOrZero_eq_order
    ⟨j.val + 1, by omega⟩
  rw [horderJA, horderJB] at horderJ
  have hnextIndex :
      (⟨j.val + 1, by omega⟩ : Fin (n + 2)) = j.succ := by
    apply Fin.ext
    rfl
  have horderJSucc : a.order j.succ = b.order j.succ := by
    simpa only [hnextIndex] using horderJ
  rw [horderJSucc] at hmax
  by_cases hcase :
      (b.order j.succ : Rat) - a.alphaValue j <=
        (b.order first.succ : Rat) - b.alphaValue first
  · rw [max_eq_right hcase] at hmax
    rw [min_eq_right (by push_cast; linarith)]
    push_cast
    linarith
  · have hreverse :
        (b.order first.succ : Rat) - b.alphaValue first <=
          (b.order j.succ : Rat) - a.alphaValue j :=
      le_of_not_ge hcase
    rw [max_eq_left hreverse] at hmax
    rw [min_eq_left (by push_cast; linarith)]
    linarith

/-- Lemma 6.9(iv) derived directly from conditions 2.1(i) and (ii). -/
theorem beli2019Lemma69_iv_beta_eq_min
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (first j : Fin (n + 1)) (hfirst : first <= j)
    (hsuffix : forall k, first.val + 1 <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k) :
    b.alphaValue j =
      min (a.alphaValue j)
        (((b.order j.succ - b.order first.succ : Int) : Rat) +
          b.alphaValue first) :=
  beli2019Lemma69_iv_beta_eq_min_of_weightOrder a b
    (a.weightSequence_le_of_representationConditions b horder hdefect)
    first j hfirst hsuffix

/-- In the strict branch of Lemma 6.9(iv), the shifted endpoint candidate
is the active minimum. -/
theorem beli2019Lemma69_iv_beta_shift_of_lt_sourceAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (first j : Fin (n + 1)) (hfirst : first <= j)
    (hsuffix : forall k, first.val + 1 <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k)
    (hstrict : b.alphaValue j < a.alphaValue j) :
    b.alphaValue j =
      ((b.order j.succ - b.order first.succ : Int) : Rat) +
        b.alphaValue first := by
  have hformula := beli2019Lemma69_iv_beta_eq_min
    a b horder hdefect first j hfirst hsuffix
  by_cases hleft :
      a.alphaValue j <=
        ((b.order j.succ - b.order first.succ : Int) : Rat) +
          b.alphaValue first
  · have heq := hformula.trans (min_eq_left hleft)
    exact (ne_of_lt hstrict heq).elim
  · exact hformula.trans (min_eq_right (le_of_not_ge hleft))

end BONG.GoodBONG

end Bong
