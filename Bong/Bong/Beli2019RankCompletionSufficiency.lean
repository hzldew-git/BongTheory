/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019RankCompletion

/-!
# Beli (2019), Lemma 2.20 in the sufficiency direction

A lower-rank source BONG is completed by adjoining a uniformly deep
orthogonal tail.  This file proves the numerical part of Lemma 2.20 in the
direction needed for sufficiency: the revised four conditions for the short
pair imply the same conditions for the completed equal-rank pair.
-/

namespace Bong

open Dyadic

universe u v w x

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type x} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {C : Lattice K U}
  {m n : Nat}
  {a : GoodBONG q L (m + 1)} {b : GoodBONG r M (n + 1)}
  {c : GoodBONG s C (m + 1)} {hRank : n ≤ m}

/-- A uniform integral depth dominating every target order by `2e`. -/
noncomputable def rankCompletionTailOrderBound
    (a : GoodBONG q L (m + 1)) : Int :=
  Finset.univ.sup' Finset.univ_nonempty a.order +
    2 * (ramificationIndex K : Int)

/-- Every target order, with the `2e` margin used in conditions (ii) and
(iv), lies below the chosen uniform tail bound. -/
theorem order_add_twoE_le_rankCompletionTailOrderBound
    (a : GoodBONG q L (m + 1)) (i : Fin (m + 1)) :
    a.order i + 2 * (ramificationIndex K : Int) ≤
      a.rankCompletionTailOrderBound := by
  unfold rankCompletionTailOrderBound
  simpa only [add_comm] using add_le_add_right
    (Finset.le_sup' a.order (Finset.mem_univ i))
      (2 * (ramificationIndex K : Int))

/-- In particular, every target order lies below the uniform tail bound. -/
theorem order_le_rankCompletionTailOrderBound
    (a : GoodBONG q L (m + 1)) (i : Fin (m + 1)) :
    a.order i ≤ a.rankCompletionTailOrderBound := by
  exact (a.order_add_twoE_le_rankCompletionTailOrderBound i).trans' (by
    have he : 0 ≤ (ramificationIndex K : Int) := Int.natCast_nonneg _
    omega)

/-- Condition (i) lifts to a same-rank completion once all new source orders
are uniformly deep. -/
theorem representationOrderCondition_toSameRank_of_prefixAgreement
    (h : PrefixAgreement c b hRank)
    (hTail : ∀ (i : Fin (m + 1)), n + 1 ≤ i.val →
      a.rankCompletionTailOrderBound ≤ c.order i)
    (hb : a.RepresentationOrderCondition b hRank) :
    a.RepresentationOrderCondition c (Nat.le_refl m) := by
  intro i
  by_cases hi : i.val < n + 1
  · let j : Fin (n + 1) := ⟨i.val, hi⟩
    have horder : c.order i = b.order j := by
      simpa only [j] using h.order_eq j
    rcases hb j with hfirst | ⟨hj0, hjLarge, hpair⟩
    · left
      simpa only [j, horder] using hfirst
    · right
      refine ⟨hj0, hjLarge, ?_⟩
      have hprevious :
          c.order ⟨i.val - 1, by omega⟩ =
            b.order ⟨j.val - 1, by omega⟩ := by
        exact h.order_eq_nat (by omega)
      simpa only [j, horder, hprevious] using hpair
  · left
    exact (a.order_le_rankCompletionTailOrderBound i).trans
      (hTail i (by omega))

/-- The last ordinary index of the lower-rank comparison. -/
def rankCompletionBoundaryIndex (hStrict : n < m) :
    RepresentationIndex (m + 1) (n + 1) where
  val := n + 1
  pos := by omega
  lt_large := by omega
  le_small := le_rfl

/-- Condition (ii) lifts to a same-rank completion.  Before the new boundary
the invariant is unchanged; at the boundary the prescribed large alpha cap
protects the old inequality; after it, the half-gap is nonpositive while
capped defects are nonnegative. -/
theorem representationDefectCondition_toSameRank_of_prefixAgreement
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaU : Beli2006AlphaLaws.{u, x} K]
    (h : PrefixAgreement c b hRank) (hStrict : n < m)
    (hTail : ∀ (i : Fin (m + 1)), n + 1 ≤ i.val →
      a.rankCompletionTailOrderBound ≤ c.order i)
    (hAlpha :
      a.representationAlphaValue b (rankCompletionBoundaryIndex hStrict) ≤
        c.alphaValue ⟨n, hStrict⟩)
    (hb : a.RepresentationDefectCondition b) :
    a.RepresentationDefectCondition c := by
  intro i
  by_cases hold : i.val ≤ n + 1
  · by_cases hinterior : i.val ≤ n
    · let j : RepresentationIndex (m + 1) (n + 1) :=
        { val := i.val
          pos := i.pos
          lt_large := i.lt_large
          le_small := hinterior.trans (Nat.le_succ n) }
      have hji : j.toSameRank = i := by
        cases i
        rfl
      rw [← hji, a.representationAlphaValue_eq_of_prefixAgreement h j]
      simp only [RepresentationIndex.toSameRank]
      rw [a.truncatedPrefixDefect_eq_of_prefixAgreement h 1
        j.val j.val (by simpa only [j] using hinterior)]
      exact hb j
    · have hival : i.val = n + 1 := by omega
      have hiBoundary :
          i = (rankCompletionBoundaryIndex hStrict).toSameRank := by
        cases i with
        | mk val pos lt_large le_small =>
            dsimp only at hival
            subst val
            rfl
      rw [hiBoundary,
        a.representationAlphaValue_eq_of_prefixAgreement h
          (rankCompletionBoundaryIndex hStrict)]
      simp only [RepresentationIndex.toSameRank]
      change
        (a.representationAlphaValue b
            (rankCompletionBoundaryIndex hStrict) : WithTop ℚ) ≤
          a.truncatedPrefixDefect c 1 (n + 1) (n + 1)
      rw [a.truncatedPrefixDefect_boundary_eq_min h hStrict 1 (n + 1)]
      exact le_min (hb (rankCompletionBoundaryIndex hStrict))
        (WithTop.coe_le_coe.mpr hAlpha)
  · have hilower : n + 2 ≤ i.val := by omega
    have hsourceIndex : n + 1 ≤ i.val - 1 :=
      Nat.le_sub_of_add_le (by omega)
    have hpreviousLt : i.val - 1 < m + 1 :=
      (Nat.sub_le i.val 1).trans_lt i.lt_large
    have hdepth :
        a.order ⟨i.val, i.lt_large⟩ +
            2 * (ramificationIndex K : Int) ≤
          c.order ⟨i.val - 1, hpreviousLt⟩ :=
      (a.order_add_twoE_le_rankCompletionTailOrderBound
        ⟨i.val, i.lt_large⟩).trans
        (hTail ⟨i.val - 1, hpreviousLt⟩ hsourceIndex)
    have hdepthQ :
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) +
            2 * (ramificationIndex K : ℚ) ≤
          (c.order ⟨i.val - 1, hpreviousLt⟩ : ℚ) := by
      exact_mod_cast hdepth
    have hhalf : a.representationHalfGap c i ≤ (0 : WithTop ℚ) := by
      unfold representationHalfGap
      apply WithTop.coe_le_coe.mpr
      push_cast
      linarith [hdepthQ]
    calc
      (a.representationAlphaValue c i : WithTop ℚ) =
          a.representationAlpha c i := a.coe_representationAlphaValue c i
      _ ≤ a.representationHalfGap c i :=
        a.representationAlpha_le_halfGap c i
      _ ≤ 0 := hhalf
      _ ≤ a.truncatedPrefixDefect c 1 i.val i.val :=
        a.truncatedPrefixDefect_nonneg
          (alphaV := alphaV) (alphaW := alphaU) c 1 i.val i.val

/-- At the exceptional last central index, the completed v2 trigger implies
the original lower-rank trigger.  The completed current defect is a minimum
with one additional cap, so it can only be smaller. -/
theorem centralDefectTrigger_of_toSameRank_terminal
    (h : PrefixAgreement c b hRank) (hStrict : n < m)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hi : i.val = n + 2)
    (hc : a.centralDefectTrigger c i.toSameRank) :
    a.centralDefectTrigger b i := by
  have hsource : i.val - 2 < n + 1 := by omega
  have horder := h.order_eq_nat hsource
  have hprevious := a.centralPreviousDefect_eq_of_prefixAgreement h i
  have hcurrent := a.centralCurrentDefect_eq_min_of_terminal
    h hStrict i hi
  unfold centralDefectTrigger at hc ⊢
  simp only [CentralRepresentationIndex.toSameRank] at hc hprevious hcurrent
  rw [horder, hprevious, hcurrent] at hc
  have hmin := add_le_add_right
    (min_le_left (a.centralCurrentDefect b i)
      (c.alphaValue ⟨n, hStrict⟩ : WithTop ℚ))
    (a.centralPreviousDefect b i)
  exact ⟨hc.1, hc.2.trans_le (by simpa only [add_comm] using hmin)⟩

/-- Revised condition (iii') lifts to the completed equal-rank pair.  Old
indices are unchanged, the exceptional boundary uses monotonicity of the new
cap, and all later triggers are killed by the deep tail orders. -/
theorem centralRepresentationConditionsPrime_toSameRank_of_prefixAgreement
    (h : PrefixAgreement c b hRank) (hStrict : n < m)
    (hTail : ∀ (i : Fin (m + 1)), n + 1 ≤ i.val →
      a.rankCompletionTailOrderBound ≤ c.order i)
    (hb : a.CentralRepresentationConditionsPrime b) :
    a.CentralRepresentationConditionsPrime c := by
  intro i htrigger
  by_cases hold : i.val ≤ n + 2
  · let j : CentralRepresentationIndex (m + 1) (n + 1) :=
      { val := i.val
        one_lt := i.one_lt
        lt_large := i.lt_large
        le_small_succ := hold }
    have hji : j.toSameRank = i := by
      cases i
      rfl
    rw [← hji] at htrigger ⊢
    simp only [CentralRepresentationIndex.toSameRank] at htrigger ⊢
    have hjTrigger : a.centralDefectTrigger b j := by
      by_cases hinterior : j.val ≤ n + 1
      · exact (a.centralDefectTrigger_iff_of_prefixAgreement
          h j hinterior).mp htrigger
      · have hjval : j.val = n + 2 := by
          have hjiVal : j.val = i.val := rfl
          omega
        exact a.centralDefectTrigger_of_toSameRank_terminal
          h hStrict j hjval htrigger
    have hrep := hb j hjTrigger
    have hpref := h.prefixValues_eq (j.val - 1) (by
      have := j.le_small_succ
      omega)
    rw [hpref]
    exact hrep
  · have hilower : n + 3 ≤ i.val := by omega
    have htailIndex : n + 1 ≤ i.val - 2 :=
      Nat.le_sub_of_add_le (by omega)
    have hearlierLt : i.val - 2 < m + 1 :=
      (Nat.sub_le i.val 2).trans_lt i.lt_large
    have hnotlt :
        a.order ⟨i.val, i.lt_large⟩ ≤
          c.order ⟨i.val - 2, hearlierLt⟩ :=
      (a.order_le_rankCompletionTailOrderBound
        ⟨i.val, i.lt_large⟩).trans
        (hTail ⟨i.val - 2, hearlierLt⟩ htailIndex)
    exact (not_lt_of_ge hnotlt htrigger.1).elim

/-- Condition (iv) lifts to the completed equal-rank pair.  The indices whose
prefix still lies in the original lattice are transported verbatim.  Beyond
that prefix, the strict trigger is incompatible with the uniformly deep
adjoined tail. -/
theorem longRepresentationConditions_toSameRank_of_prefixAgreement
    (h : PrefixAgreement c b hRank)
    (hTail : ∀ (i : Fin (m + 1)), n + 1 ≤ i.val →
      a.rankCompletionTailOrderBound ≤ c.order i)
    (hb : a.LongRepresentationConditions b) :
    a.LongRepresentationConditions c := by
  unfold LongRepresentationConditions at hb ⊢
  intro i htrigger
  by_cases hold : i.val ≤ n + 2
  · let j : LongRepresentationIndex (m + 1) (n + 1) :=
      { val := i.val
        one_lt := i.one_lt
        succ_lt_large := i.succ_lt_large
        le_small_succ := hold }
    have hji : j.toSameRank = i := by
      cases i
      rfl
    rw [← hji] at htrigger ⊢
    simp only [LongRepresentationIndex.toSameRank] at htrigger ⊢
    have hiComplete : j.val ≤ m + 1 := by
      have := j.succ_lt_large
      omega
    have hfirstCompleted := htrigger.1
    rw [dif_pos hiComplete] at hfirstCompleted
    have hjTrigger :
        ((if hi : j.val ≤ n + 1 then
            a.order ⟨j.val + 1, j.succ_lt_large⟩ ≤
              b.order ⟨j.val - 1, by
                have := j.one_lt
                have := hi
                omega⟩
          else True) ∧
          b.order ⟨j.val - 2, by
              have := j.one_lt
              have := j.le_small_succ
              omega⟩ + 2 * (ramificationIndex K : Int) <
            a.order ⟨j.val + 1, j.succ_lt_large⟩ ∧
          a.order ⟨j.val, by
              have := j.succ_lt_large
              omega⟩ + 2 * (ramificationIndex K : Int) ≤
            b.order ⟨j.val - 2, by
              have := j.one_lt
              have := j.le_small_succ
              omega⟩ + 2 * (ramificationIndex K : Int)) := by
      refine ⟨?_, ?_, ?_⟩
      · by_cases hjold : j.val ≤ n + 1
        · rw [dif_pos hjold]
          have hprevious := h.order_eq_nat (i := j.val - 1) (by omega)
          rw [hprevious] at hfirstCompleted
          exact hfirstCompleted
        · rw [dif_neg hjold]
          trivial
      · have hearlier := h.order_eq_nat (i := j.val - 2) (by
          have := j.le_small_succ
          omega)
        rw [hearlier] at htrigger
        exact htrigger.2.1
      · have hearlier := h.order_eq_nat (i := j.val - 2) (by
          have := j.le_small_succ
          omega)
        rw [hearlier] at htrigger
        exact htrigger.2.2
    have hrep := hb j hjTrigger
    have hpref := h.prefixValues_eq (j.val - 1) (by
      have := j.le_small_succ
      omega)
    rw [hpref]
    exact hrep
  · have hilower : n + 3 ≤ i.val := by omega
    have hearlierLt : i.val - 2 < m + 1 := by
      have := i.succ_lt_large
      omega
    have hfutureLt : i.val + 1 < m + 1 := i.succ_lt_large
    have htailIndex : n + 1 ≤ i.val - 2 :=
      Nat.le_sub_of_add_le (by omega)
    have hfuture :
        a.order ⟨i.val + 1, hfutureLt⟩ +
            2 * (ramificationIndex K : Int) ≤
          c.order ⟨i.val - 2, hearlierLt⟩ :=
      (a.order_add_twoE_le_rankCompletionTailOrderBound
        ⟨i.val + 1, hfutureLt⟩).trans
        (hTail ⟨i.val - 2, hearlierLt⟩ htailIndex)
    have he := ramificationIndex_pos (K := K)
    omega

/-- The complete revised v2 four-condition package lifts from a shorter BONG
to a uniformly deep same-rank completion. -/
theorem representationConditionsPrime_toSameRank_of_prefixAgreement
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaU : Beli2006AlphaLaws.{u, x} K]
    (h : PrefixAgreement c b hRank) (hStrict : n < m)
    (hTail : ∀ (i : Fin (m + 1)), n + 1 ≤ i.val →
      a.rankCompletionTailOrderBound ≤ c.order i)
    (hAlpha :
      a.representationAlphaValue b (rankCompletionBoundaryIndex hStrict) ≤
        c.alphaValue ⟨n, hStrict⟩)
    (hb : RepresentationConditionsPrime a b hRank) :
    RepresentationConditionsPrime a c (Nat.le_refl m) := by
  exact
    ⟨a.representationOrderCondition_toSameRank_of_prefixAgreement
        h hTail hb.orderCondition,
      a.representationDefectCondition_toSameRank_of_prefixAgreement
        (alphaV := alphaV) (alphaU := alphaU)
        h hStrict hTail hAlpha hb.defectCondition,
      a.centralRepresentationConditionsPrime_toSameRank_of_prefixAgreement
        h hStrict hTail hb.centralRepresentations,
      a.longRepresentationConditions_toSameRank_of_prefixAgreement
        h hTail hb.longRepresentations⟩

/-- Original Theorem 2.1 conditions lift as well: Lemma 2.16 converts to the
revised package before completion and converts back afterwards. -/
theorem representationConditions_toSameRank_of_prefixAgreement
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [alphaU : Beli2006AlphaLaws.{u, x} K]
    (h : PrefixAgreement c b hRank) (hStrict : n < m)
    (hTail : ∀ (i : Fin (m + 1)), n + 1 ≤ i.val →
      a.rankCompletionTailOrderBound ≤ c.order i)
    (hAlpha :
      a.representationAlphaValue b (rankCompletionBoundaryIndex hStrict) ≤
        c.alphaValue ⟨n, hStrict⟩)
    (hb : RepresentationConditions a b hRank) :
    RepresentationConditions a c (Nat.le_refl m) := by
  have hbPrime : RepresentationConditionsPrime a b hRank :=
    RepresentationConditions.toPrime
      (sourceLaws := alphaV) (targetLaws := alphaW) hb
  have hcPrime : RepresentationConditionsPrime a c (Nat.le_refl m) :=
    a.representationConditionsPrime_toSameRank_of_prefixAgreement
      (alphaV := alphaV) (alphaU := alphaU)
      h hStrict hTail hAlpha hbPrime
  have htrigger : a.CentralTriggerEquivalence c :=
    a.beli2019Lemma216 (sourceLaws := alphaV) (targetLaws := alphaU)
      c (Nat.le_refl m) hcPrime.orderCondition hcPrime.defectCondition
  exact (representationConditions_iff_prime
    a c (Nat.le_refl m) htrigger).mpr hcPrime

end BONG.GoodBONG

end Bong
