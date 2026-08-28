/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Necessity
import Bong.Bong.GoodBONGDeepIntegralExtension

/-!
# Beli (2019), Lemmas 2.20--2.21

This file proves the numerical part of the reduction to equal rank.  A deep
integral extension supplies an exact initial BONG segment and large boundary
invariants.  We prove in Lean that conditions (i), (ii), (iii'), and (iv) for
the completed lattice imply the corresponding conditions for the original
lower-rank lattice.
-/

namespace Bong

open Dyadic

universe u v w x

namespace RepresentationIndex

/-- Regard an ordinary index as an index for the equal-rank comparison. -/
def toSameRank {largeRank smallRank : Nat}
    (i : RepresentationIndex largeRank smallRank) :
    RepresentationIndex largeRank largeRank where
  val := i.val
  pos := i.pos
  lt_large := i.lt_large
  le_small := i.lt_large.le

end RepresentationIndex

namespace CentralRepresentationIndex

/-- Regard a central index as an index for the equal-rank comparison. -/
def toSameRank {largeRank smallRank : Nat}
    (i : CentralRepresentationIndex largeRank smallRank) :
    CentralRepresentationIndex largeRank largeRank where
  val := i.val
  one_lt := i.one_lt
  lt_large := i.lt_large
  le_small_succ := i.lt_large.le.trans (Nat.le_succ _)

end CentralRepresentationIndex

namespace LongRepresentationIndex

/-- Regard a long index as an index for the equal-rank comparison. -/
def toSameRank {largeRank smallRank : Nat}
    (i : LongRepresentationIndex largeRank smallRank) :
    LongRepresentationIndex largeRank largeRank where
  val := i.val
  one_lt := i.one_lt
  succ_lt_large := i.succ_lt_large
  le_small_succ :=
    (Nat.lt_of_succ_lt i.succ_lt_large).le.trans (Nat.le_succ _)

end LongRepresentationIndex

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type x} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {C : Lattice K U} {m n : Nat}
  {a : GoodBONG q L (m + 1)} {c : GoodBONG s C (m + 1)}
  {b : GoodBONG r M (n + 1)} {hRank : n ≤ m}

/-- A capped prefix defect is unchanged before the new boundary. -/
theorem truncatedPrefixDefect_eq_of_prefixAgreement
    (h : PrefixAgreement c b hRank) (epsilon : Kˣ) (i j : Nat)
    (hj : j ≤ n) :
    a.truncatedPrefixDefect c epsilon i j =
      a.truncatedPrefixDefect b epsilon i j := by
  unfold truncatedPrefixDefect
  rw [h.prefixProduct_eq j (by omega), h.prefixAlphaCap_eq j hj]

/-- At the first new boundary, the completed capped defect can only decrease. -/
theorem truncatedPrefixDefect_le_of_prefixAgreement_boundary
    (h : PrefixAgreement c b hRank) (epsilon : Kˣ) (i : Nat) :
    a.truncatedPrefixDefect c epsilon i (n + 1) ≤
      a.truncatedPrefixDefect b epsilon i (n + 1) := by
  unfold truncatedPrefixDefect
  rw [h.prefixProduct_eq (n + 1) le_rfl, b.prefixAlphaCap_last]
  rw [min_eq_left le_top]
  exact min_le_min le_rfl (min_le_left _ _)

/-- The half-gap candidate is unchanged at every old ordinary index. -/
theorem representationHalfGap_eq_of_prefixAgreement
    (h : PrefixAgreement c b hRank)
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationHalfGap c i.toSameRank =
      a.representationHalfGap b i := by
  unfold representationHalfGap
  simp only [RepresentationIndex.toSameRank]
  have hi : i.val - 1 < n + 1 := by
    have := i.le_small
    omega
  rw [h.order_eq_nat hi]

/-- The primary defect candidate is unchanged at every old ordinary index. -/
theorem representationPrimaryDefect_eq_of_prefixAgreement
    (h : PrefixAgreement c b hRank)
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationPrimaryDefect c i.toSameRank =
      a.representationPrimaryDefect b i := by
  unfold representationPrimaryDefect
  simp only [RepresentationIndex.toSameRank]
  have hi : i.val - 1 < n + 1 := by
    have := i.le_small
    omega
  rw [h.order_eq_nat hi]
  rw [a.truncatedPrefixDefect_eq_of_prefixAgreement h (-1)
    (i.val + 1) (i.val - 1) (by omega)]

/-- The optional secondary candidate is unchanged at every old ordinary
index. -/
theorem representationSecondaryDefect_eq_of_prefixAgreement
    (h : PrefixAgreement c b hRank)
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) :
    a.representationSecondaryDefect c i.toSameRank hi =
      a.representationSecondaryDefect b i hi := by
  unfold representationSecondaryDefect
  simp only [RepresentationIndex.toSameRank]
  have hi₁ : i.val - 2 < n + 1 := by
    have := i.le_small
    omega
  have hi₂ : i.val - 1 < n + 1 := by
    have := i.le_small
    omega
  rw [h.order_eq_nat hi₁, h.order_eq_nat hi₂]
  rw [a.truncatedPrefixDefect_eq_of_prefixAgreement h 1
    (i.val + 2) (i.val - 2) (by omega)]

/-- The candidate set defining `A_i` is unchanged at every old index. -/
theorem representationAlphaCandidates_eq_of_prefixAgreement
    (h : PrefixAgreement c b hRank)
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlphaCandidates c i.toSameRank =
      a.representationAlphaCandidates b i := by
  unfold representationAlphaCandidates
  rw [a.representationHalfGap_eq_of_prefixAgreement h i,
    a.representationPrimaryDefect_eq_of_prefixAgreement h i]
  change insert (a.representationHalfGap b i)
      (insert (a.representationPrimaryDefect b i)
        (if hi : 1 < i.val ∧ i.val + 1 < m + 1 then
          {a.representationSecondaryDefect c i.toSameRank hi}
        else ∅)) =
    insert (a.representationHalfGap b i)
      (insert (a.representationPrimaryDefect b i)
        (if hi : 1 < i.val ∧ i.val + 1 < m + 1 then
          {a.representationSecondaryDefect b i hi}
        else ∅))
  split_ifs with hi
  · rw [a.representationSecondaryDefect_eq_of_prefixAgreement h i hi]
  · rfl

/-- Beli's invariant `A_i` is unchanged at every old ordinary index. -/
theorem representationAlpha_eq_of_prefixAgreement
    (h : PrefixAgreement c b hRank)
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlpha c i.toSameRank =
      a.representationAlpha b i := by
  unfold representationAlpha
  apply le_antisymm
  · apply Finset.le_min'
    intro x hx
    apply Finset.min'_le
    simpa only [a.representationAlphaCandidates_eq_of_prefixAgreement h i]
      using hx
  · apply Finset.le_min'
    intro x hx
    apply Finset.min'_le
    simpa only [a.representationAlphaCandidates_eq_of_prefixAgreement h i]
      using hx

/-- The rational value of `A_i` is unchanged at every old ordinary index. -/
theorem representationAlphaValue_eq_of_prefixAgreement
    (h : PrefixAgreement c b hRank)
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlphaValue c i.toSameRank =
      a.representationAlphaValue b i := by
  apply WithTop.coe_injective
  rw [coe_representationAlphaValue, coe_representationAlphaValue,
    a.representationAlpha_eq_of_prefixAgreement h i]

/-- Condition (i) for a completed same-rank pair implies condition (i) for
the original lower-rank pair. -/
theorem representationOrderCondition_of_prefixAgreement
    (h : PrefixAgreement c b hRank)
    (hc : a.RepresentationOrderCondition c (Nat.le_refl m)) :
    a.RepresentationOrderCondition b hRank := by
  intro i
  let j : Fin (m + 1) := ⟨i.val, by
    have := i.isLt
    omega⟩
  have hj := hc j
  rcases hj with hfirst | ⟨hi0, hiLarge, htwo⟩
  · left
    have horder : c.order j = b.order i := by
      simpa only [j] using h.order_eq i
    simpa only [j, horder] using hfirst
  · right
    refine ⟨hi0, hiLarge, ?_⟩
    have hcurrent : c.order j = b.order i := by
      simpa only [j] using h.order_eq i
    have hpreviousIndex : i.val - 1 < n + 1 := by
      have := i.isLt
      omega
    have hprevious : c.order ⟨i.val - 1, by omega⟩ =
        b.order ⟨i.val - 1, hpreviousIndex⟩ :=
      h.order_eq_nat hpreviousIndex
    simpa only [j, hcurrent, hprevious] using htwo

/-- Condition (ii) descends from a completed same-rank pair.  At the last
old boundary the completed cap may be smaller, which is the favorable
inequality direction. -/
theorem representationDefectCondition_of_prefixAgreement
    (h : PrefixAgreement c b hRank)
    (hc : a.RepresentationDefectCondition c) :
    a.RepresentationDefectCondition b := by
  intro i
  have hcompleted := hc i.toSameRank
  rw [a.representationAlphaValue_eq_of_prefixAgreement h i] at hcompleted
  simp only [RepresentationIndex.toSameRank] at hcompleted
  by_cases hi : i.val ≤ n
  · rw [a.truncatedPrefixDefect_eq_of_prefixAgreement h 1
      i.val i.val hi] at hcompleted
    exact hcompleted
  · have hilast : i.val = n + 1 := by
      have := i.le_small
      omega
    rw [hilast] at hcompleted ⊢
    exact hcompleted.trans
      (a.truncatedPrefixDefect_le_of_prefixAgreement_boundary h 1 (n + 1))

/-- A single rational bound which is relevant exactly when condition (iii')
has an exceptional last index. -/
noncomputable def rankCompletionAlphaBound
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1)) : ℚ :=
  if hgap : n + 2 < m + 1 then
    2 * (ramificationIndex K : ℚ) +
      (b.order ⟨n, by omega⟩ : ℚ) -
        (a.order ⟨n + 2, hgap⟩ : ℚ)
  else 0

/-- A single integral order bound which is relevant exactly when condition
(iv) has an exceptional last index. -/
noncomputable def rankCompletionOrderBound
    (a : GoodBONG q L (m + 1)) : Int :=
  if hgap : n + 3 < m + 1 then a.order ⟨n + 3, hgap⟩ else 0

/-- The new alpha cap is the only extra term in the completed defect at the
first new boundary. -/
theorem truncatedPrefixDefect_boundary_eq_min
    (h : PrefixAgreement c b hRank) (hStrict : n < m)
    (epsilon : Kˣ) (i : Nat) :
    a.truncatedPrefixDefect c epsilon i (n + 1) =
      min (a.truncatedPrefixDefect b epsilon i (n + 1))
        (c.alphaValue ⟨n, hStrict⟩ : WithTop ℚ) := by
  unfold truncatedPrefixDefect
  rw [h.prefixProduct_eq (n + 1) le_rfl,
    c.prefixAlphaCap_of_internal (Nat.succ_pos n) (by omega),
    b.prefixAlphaCap_last]
  have hindex : (⟨n + 1 - 1, by omega⟩ : Fin m) = ⟨n, hStrict⟩ := by
    apply Fin.ext
    simp
  rw [hindex]
  rw [min_eq_left le_top]
  simp only [min_assoc]

/-- Before the exceptional last index, the revised condition (iii') trigger
is literally unchanged. -/
theorem centralDefectTrigger_iff_of_prefixAgreement
    (h : PrefixAgreement c b hRank)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hi : i.val ≤ n + 1) :
    a.centralDefectTrigger c i.toSameRank ↔
      a.centralDefectTrigger b i := by
  unfold centralDefectTrigger centralPreviousDefect centralCurrentDefect
  simp only [CentralRepresentationIndex.toSameRank]
  have hiOrder : i.val - 2 < n + 1 := by
    have := i.one_lt
    have := i.le_small_succ
    omega
  rw [h.order_eq_nat hiOrder]
  rw [a.truncatedPrefixDefect_eq_of_prefixAgreement h (-1)
    i.val (i.val - 2) (by omega)]
  rw [a.truncatedPrefixDefect_eq_of_prefixAgreement h (-1)
    (i.val + 1) (i.val - 1) (by omega)]

/-- At the exceptional last central index, the completed current defect is
the minimum of the old current defect and the first new alpha. -/
theorem centralCurrentDefect_eq_min_of_terminal
    (h : PrefixAgreement c b hRank) (hStrict : n < m)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hi : i.val = n + 2) :
    a.centralCurrentDefect c i.toSameRank =
      min (a.centralCurrentDefect b i)
        (c.alphaValue ⟨n, hStrict⟩ : WithTop ℚ) := by
  unfold centralCurrentDefect
  simp only [CentralRepresentationIndex.toSameRank]
  rw [hi]
  have hplus : n + 2 + 1 = n + 3 := by omega
  have hminus : n + 2 - 1 = n + 1 := by omega
  rw [hplus, hminus]
  exact a.truncatedPrefixDefect_boundary_eq_min h hStrict (-1) (n + 3)

/-- The preceding central defect is unchanged, including at the exceptional
last index. -/
theorem centralPreviousDefect_eq_of_prefixAgreement
    (h : PrefixAgreement c b hRank)
    (i : CentralRepresentationIndex (m + 1) (n + 1)) :
    a.centralPreviousDefect c i.toSameRank =
      a.centralPreviousDefect b i := by
  unfold centralPreviousDefect
  simp only [CentralRepresentationIndex.toSameRank]
  apply a.truncatedPrefixDefect_eq_of_prefixAgreement h
  have := i.le_small_succ
  omega

/-- A boundary alpha above `rankCompletionAlphaBound` preserves the revised
condition (iii') trigger at its unique exceptional last index. -/
theorem centralDefectTrigger_toSameRank_of_terminal
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (h : PrefixAgreement c b hRank) (hStrict : n < m)
    (hAlpha : a.rankCompletionAlphaBound b <
      c.alphaValue ⟨n, hStrict⟩)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hi : i.val = n + 2) (htrigger : a.centralDefectTrigger b i) :
    a.centralDefectTrigger c i.toSameRank := by
  have hgap : n + 2 < m + 1 := by
    rw [← hi]
    exact i.lt_large
  let T : ℚ := 2 * (ramificationIndex K : ℚ) +
    (b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ : ℚ) -
      (a.order ⟨i.val, i.lt_large⟩ : ℚ)
  have hAlphaQ : T < c.alphaValue ⟨n, hStrict⟩ := by
    have hAlpha' : 2 * (ramificationIndex K : ℚ) +
        (b.order ⟨n, by omega⟩ : ℚ) -
          (a.order ⟨n + 2, hgap⟩ : ℚ) <
        c.alphaValue ⟨n, hStrict⟩ := by
      simpa only [rankCompletionAlphaBound, dif_pos hgap] using hAlpha
    have hbIndex : (⟨i.val - 2, by omega⟩ : Fin (n + 1)) =
        ⟨n, by omega⟩ := by
      apply Fin.ext
      change i.val - 2 = n
      omega
    have haIndex : (⟨i.val, i.lt_large⟩ : Fin (m + 1)) =
        ⟨n + 2, hgap⟩ := by
      apply Fin.ext
      exact hi
    dsimp only [T]
    rw [hbIndex, haIndex]
    exact hAlpha'
  have hAlphaTop : (T : WithTop ℚ) <
      (c.alphaValue ⟨n, hStrict⟩ : WithTop ℚ) := by
    exact_mod_cast hAlphaQ
  have hpreviousNonneg : (0 : WithTop ℚ) ≤
      a.centralPreviousDefect b i := by
    unfold centralPreviousDefect
    exact a.truncatedPrefixDefect_nonneg
      (alphaV := alphaV) (alphaW := alphaW) b (-1) i.val (i.val - 2)
  have hAlphaShifted : (T : WithTop ℚ) <
      a.centralPreviousDefect b i +
        (c.alphaValue ⟨n, hStrict⟩ : WithTop ℚ) := by
    calc
      (T : WithTop ℚ) < 0 +
          (c.alphaValue ⟨n, hStrict⟩ : WithTop ℚ) := by
        simpa only [zero_add] using hAlphaTop
      _ ≤ a.centralPreviousDefect b i +
          (c.alphaValue ⟨n, hStrict⟩ : WithTop ℚ) := by
        have hadd := add_le_add_right hpreviousNonneg
          (c.alphaValue ⟨n, hStrict⟩ : WithTop ℚ)
        simpa only [zero_add, add_comm] using hadd
  have hprevious := a.centralPreviousDefect_eq_of_prefixAgreement h i
  have hcurrent :=
    a.centralCurrentDefect_eq_min_of_terminal h hStrict i hi
  simp only [CentralRepresentationIndex.toSameRank] at hprevious hcurrent
  have hiOrder : i.val - 2 < n + 1 := by
    have := i.one_lt
    have := i.le_small_succ
    omega
  have horder := h.order_eq_nat hiOrder
  change b.order ⟨i.val - 2, by omega⟩ <
      a.order ⟨i.val, i.lt_large⟩ ∧
    (T : WithTop ℚ) <
      a.centralPreviousDefect b i + a.centralCurrentDefect b i at htrigger
  unfold centralDefectTrigger
  simp only [CentralRepresentationIndex.toSameRank]
  constructor
  · rw [horder]
    exact htrigger.1
  · rw [horder, hprevious, hcurrent, add_min]
    exact lt_min htrigger.2 hAlphaShifted

/-- Revised condition (iii') descends from the completed same-rank pair. -/
theorem centralRepresentationConditionsPrime_of_prefixAgreement
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (h : PrefixAgreement c b hRank) (hStrict : n < m)
    (hAlpha : a.rankCompletionAlphaBound b <
      c.alphaValue ⟨n, hStrict⟩)
    (hc : a.CentralRepresentationConditionsPrime c) :
    a.CentralRepresentationConditionsPrime b := by
  intro i htrigger
  have hcompletedTrigger : a.centralDefectTrigger c i.toSameRank := by
    by_cases hi : i.val ≤ n + 1
    · exact (a.centralDefectTrigger_iff_of_prefixAgreement h i hi).2 htrigger
    · have hiterminal : i.val = n + 2 := by
        have := i.le_small_succ
        omega
      exact a.centralDefectTrigger_toSameRank_of_terminal
        (alphaV := alphaV) (alphaW := alphaW)
        h hStrict hAlpha i hiterminal htrigger
  have hrepresentation := hc i.toSameRank hcompletedTrigger
  simp only [CentralRepresentationIndex.toSameRank] at hrepresentation
  have hiPrefix : i.val - 1 ≤ n + 1 := by
    have := i.le_small_succ
    omega
  have hpref := h.prefixValues_eq (i.val - 1) hiPrefix
  rw [hpref] at hrepresentation
  exact hrepresentation

/-- Condition (iv) descends from the completed same-rank pair.  Its sole new
terminal premise is supplied by `rankCompletionOrderBound`. -/
theorem longRepresentationConditions_of_prefixAgreement
    (h : PrefixAgreement c b hRank) (hStrict : n < m)
    (hOrder : a.rankCompletionOrderBound (n := n) ≤
      c.order ⟨n + 1, by omega⟩)
    (hc : a.LongRepresentationConditions c) :
    a.LongRepresentationConditions b := by
  unfold LongRepresentationConditions at hc ⊢
  intro i htrigger
  have hiComplete : i.val ≤ m + 1 := by
    have := i.succ_lt_large
    omega
  have hiCompletePrevious : i.val - 1 < m + 1 := by
    have := i.succ_lt_large
    omega
  have hiCompleteEarlier : i.val - 2 < m + 1 := by
    have := i.succ_lt_large
    omega
  have hiSourceCurrent : i.val < m + 1 := by
    have := i.succ_lt_large
    omega
  have hiOldEarlier : i.val - 2 < n + 1 := by
    have := i.one_lt
    have := i.le_small_succ
    omega
  have hearlier := h.order_eq_nat hiOldEarlier
  have hfirst : a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
      c.order ⟨i.val - 1, hiCompletePrevious⟩ := by
    by_cases hiOld : i.val ≤ n + 1
    · have hiOldPrevious : i.val - 1 < n + 1 := by
        have := i.one_lt
        omega
      have hprevious := h.order_eq_nat hiOldPrevious
      have hfirstOld := htrigger.1
      rw [dif_pos hiOld] at hfirstOld
      rw [hprevious]
      exact hfirstOld
    · have hiterminal : i.val = n + 2 := by
        have := i.le_small_succ
        omega
      have hgap : n + 3 < m + 1 := by
        have := i.succ_lt_large
        omega
      have hbound : a.order ⟨n + 3, hgap⟩ ≤
          c.order ⟨n + 1, by omega⟩ := by
        simpa only [rankCompletionOrderBound, dif_pos hgap] using hOrder
      have haIndex : (⟨i.val + 1, i.succ_lt_large⟩ : Fin (m + 1)) =
          ⟨n + 3, hgap⟩ := by
        apply Fin.ext
        change i.val + 1 = n + 3
        omega
      have hcIndex : (⟨i.val - 1, by omega⟩ : Fin (m + 1)) =
          ⟨n + 1, by omega⟩ := by
        apply Fin.ext
        change i.val - 1 = n + 1
        omega
      rw [haIndex, hcIndex]
      exact hbound
  have hcompletedTrigger :
      ((if hi : i.val ≤ m + 1 then
          a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
            c.order ⟨i.val - 1, hiCompletePrevious⟩
        else True) ∧
        c.order ⟨i.val - 2, hiCompleteEarlier⟩ +
            2 * (ramificationIndex K : Int) <
          a.order ⟨i.val + 1, i.succ_lt_large⟩ ∧
        a.order ⟨i.val, hiSourceCurrent⟩ +
            2 * (ramificationIndex K : Int) ≤
          c.order ⟨i.val - 2, hiCompleteEarlier⟩ +
            2 * (ramificationIndex K : Int)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [dif_pos hiComplete]
      exact hfirst
    · rw [hearlier]
      exact htrigger.2.1
    · rw [hearlier]
      exact htrigger.2.2
  have hrepresentation := hc i.toSameRank (by
    simpa only [LongRepresentationIndex.toSameRank] using hcompletedTrigger)
  simp only [LongRepresentationIndex.toSameRank] at hrepresentation
  have hiPrefix : i.val - 1 ≤ n + 1 := by
    have := i.le_small_succ
    omega
  have hpref := h.prefixValues_eq (i.val - 1) hiPrefix
  rw [hpref] at hrepresentation
  exact hrepresentation

/-- Revised condition (iii') is invariant under full scalar agreement in the
same-rank case. -/
theorem centralRepresentationConditionsPrime_of_scalarAgreement
    {L' C' : Lattice K V} {M' : Lattice K W}
    {a' : GoodBONG q L' (n + 1)} {c' : GoodBONG q C' (n + 1)}
    {b' : GoodBONG r M' (n + 1)}
    (h : ScalarAgreement c' b')
    (hc : a'.CentralRepresentationConditionsPrime c') :
    a'.CentralRepresentationConditionsPrime b' := by
  let hp : PrefixAgreement c' b' (Nat.le_refl n) := h.toPrefixAgreement
  intro i htrigger
  have hi : i.val ≤ n + 1 := by
    have := i.lt_large
    omega
  have hcompletedTrigger :
      a'.centralDefectTrigger c' i.toSameRank :=
    (a'.centralDefectTrigger_iff_of_prefixAgreement hp i hi).2 htrigger
  have hrepresentation := hc i.toSameRank hcompletedTrigger
  simp only [CentralRepresentationIndex.toSameRank] at hrepresentation
  have hiPrefix : i.val - 1 ≤ n + 1 := by
    have := i.lt_large
    omega
  rw [h.prefixValues_eq (i.val - 1) hiPrefix] at hrepresentation
  exact hrepresentation

/-- Condition (iv) is invariant under full scalar agreement in the same-rank
case. -/
theorem longRepresentationConditions_of_scalarAgreement
    {L' C' : Lattice K V} {M' : Lattice K W}
    {a' : GoodBONG q L' (n + 1)} {c' : GoodBONG q C' (n + 1)}
    {b' : GoodBONG r M' (n + 1)}
    (h : ScalarAgreement c' b')
    (hc : a'.LongRepresentationConditions c') :
    a'.LongRepresentationConditions b' := by
  unfold LongRepresentationConditions at hc ⊢
  intro i htrigger
  have hiPrevious : i.val - 1 < n + 1 := by
    have := i.one_lt
    have := i.succ_lt_large
    omega
  have hiEarlier : i.val - 2 < n + 1 := by
    have := i.one_lt
    have := i.succ_lt_large
    omega
  have hprevious := h.order_eq ⟨i.val - 1, hiPrevious⟩
  have hearlier := h.order_eq ⟨i.val - 2, hiEarlier⟩
  have hi : i.val ≤ n + 1 := by
    have := i.succ_lt_large
    omega
  have hiCurrent : i.val < n + 1 := by
    have := i.succ_lt_large
    omega
  have hfirst : a'.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
      c'.order ⟨i.val - 1, hiPrevious⟩ := by
    have hfirstB := htrigger.1
    rw [dif_pos hi] at hfirstB
    rw [hprevious]
    exact hfirstB
  have hsecond : c'.order ⟨i.val - 2, hiEarlier⟩ +
        2 * (ramificationIndex K : Int) <
      a'.order ⟨i.val + 1, i.succ_lt_large⟩ := by
    rw [hearlier]
    exact htrigger.2.1
  have hthird : a'.order ⟨i.val, hiCurrent⟩ +
        2 * (ramificationIndex K : Int) ≤
      c'.order ⟨i.val - 2, hiEarlier⟩ +
        2 * (ramificationIndex K : Int) := by
    rw [hearlier]
    exact htrigger.2.2
  have hrepresentation := hc i (by
    rw [dif_pos hi]
    exact ⟨hfirst, hsecond, hthird⟩)
  have hiPrefix : i.val - 1 ≤ n + 1 := by omega
  rw [h.prefixValues_eq (i.val - 1) hiPrefix] at hrepresentation
  exact hrepresentation

/-- All four revised conditions are invariant under scalar agreement in the
same-rank case. -/
theorem representationConditionsPrime_of_scalarAgreement
    {L' C' : Lattice K V} {M' : Lattice K W}
    {a' : GoodBONG q L' (n + 1)} {c' : GoodBONG q C' (n + 1)}
    {b' : GoodBONG r M' (n + 1)}
    (h : ScalarAgreement c' b')
    (hc : RepresentationConditionsPrime a' c' (Nat.le_refl n)) :
    RepresentationConditionsPrime a' b' (Nat.le_refl n) := by
  let hp : PrefixAgreement c' b' (Nat.le_refl n) := h.toPrefixAgreement
  exact
    ⟨a'.representationOrderCondition_of_prefixAgreement hp hc.orderCondition,
      a'.representationDefectCondition_of_prefixAgreement hp hc.defectCondition,
      a'.centralRepresentationConditionsPrime_of_scalarAgreement
        h hc.centralRepresentations,
      a'.longRepresentationConditions_of_scalarAgreement
        h hc.longRepresentations⟩

/-- All four revised conditions descend from a sufficiently deep same-rank
completion.  This is the numerical content of Beli (2019), Lemma 2.20. -/
theorem representationConditionsPrime_of_prefixAgreement
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (h : PrefixAgreement c b hRank) (hStrict : n < m)
    (hOrder : a.rankCompletionOrderBound (n := n) ≤
      c.order ⟨n + 1, by omega⟩)
    (hAlpha : a.rankCompletionAlphaBound b <
      c.alphaValue ⟨n, hStrict⟩)
    (hc : RepresentationConditionsPrime a c (Nat.le_refl m)) :
    RepresentationConditionsPrime a b hRank :=
  ⟨a.representationOrderCondition_of_prefixAgreement h hc.orderCondition,
    a.representationDefectCondition_of_prefixAgreement h hc.defectCondition,
    a.centralRepresentationConditionsPrime_of_prefixAgreement
      (alphaV := alphaV) (alphaW := alphaW) h hStrict hAlpha
      hc.centralRepresentations,
    a.longRepresentationConditions_of_prefixAgreement
      h hStrict hOrder hc.longRepresentations⟩

end BONG.GoodBONG

end Bong
