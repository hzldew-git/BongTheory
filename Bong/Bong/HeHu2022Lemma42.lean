/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022SectionFour
import Bong.Bong.HeHu2022Lemma311
import Bong.Bong.Beli2019Lemma213Nonessential
import Bong.Bong.Beli2019RankCompletion
import Bong.Bong.Beli2019RankCompletionSufficiency
import Bong.Bong.Beli2019Corollary210
import Bong.Bong.GoodBONGDeepIntegralExtensionProof

/-!
# He--Hu 2022, Lemma 4.2

This file formalizes the implication `I1^E(n) -> (i),(ii)` in Lemma 4.2.
For an arbitrary integral target, its ambient embedding is first completed
by a sufficiently deep orthogonal tail.  The resulting good BONG has the
same rank as the source and agrees with the target on its initial segment.
The middle defect inequalities are then exactly Beli's nonessential-index
lemma; the two endpoint inequalities are the estimates displayed in the
published proof.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- Under `I1^E`, condition (i) of Theorem 2.8 holds for every integral
target of the prescribed even rank.  The two parity branches are precisely
Proposition 2.7(i)'s lower bounds `S_i >= 0` and `S_i >= -2e`. -/
theorem heHuI1E_representationOrderCondition {m t : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (t + 2))
    (hm : t + 2 ≤ m) (hI1 : a.HeHuI1E (t + 2) (by omega))
    (hBIntegral : Lattice.IsIntegral r M) :
    a.RepresentationOrderCondition b (by omega) := by
  intro i
  left
  let targetOrders := b.heHu2022Proposition27i hBIntegral
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · have hsource : a.order ⟨i.val, by omega⟩ = 0 :=
      hI1.oddOrder ⟨i.val, by omega⟩ (Even.add_one hiEven)
    have htarget : 0 ≤ b.order i :=
      (targetOrders.oddIndexed i i le_rfl hiEven hiEven).1
    rw [hsource]
    exact htarget
  · have hsource : a.order ⟨i.val, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) :=
      hI1.evenOrder i (Odd.add_one hiOdd)
    have htarget : -(2 * (ramificationIndex K : Int)) ≤ b.order i :=
      (targetOrders.evenIndexed i i le_rfl hiOdd hiOdd).1
    rw [hsource]
    exact htarget

/-- Equation (4.1) in the published proof.  Here `i` is a one-based paper
index: the conclusion is `R_(i+1) <= S_(i-1)`. -/
theorem heHuI1E_sourceNext_le_targetPrevious {m t i : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (t + 2))
    (hm : t + 2 ≤ m) (hnEven : Even (t + 2))
    (hI1 : a.HeHuI1E (t + 2) (by omega))
    (hBIntegral : Lattice.IsIntegral r M)
    (hiTwo : 2 ≤ i) (hiLast : i ≤ t + 2) :
    a.order ⟨i, by omega⟩ ≤ b.order ⟨i - 2, by omega⟩ := by
  let targetOrders := b.heHu2022Proposition27i hBIntegral
  rcases Nat.even_or_odd i with hiEven | hiOdd
  · have hpreviousEven : Even (i - 2) := by
      rcases hiEven with ⟨pairs, hpairs⟩
      refine ⟨pairs - 1, ?_⟩
      omega
    have hsource : a.order ⟨i, by omega⟩ = 0 :=
      hI1.oddOrder ⟨i, by omega⟩ (Even.add_one hiEven)
    have htarget : 0 ≤ b.order ⟨i - 2, by omega⟩ :=
      (targetOrders.oddIndexed ⟨i - 2, by omega⟩
        ⟨i - 2, by omega⟩ le_rfl hpreviousEven hpreviousEven).1
    rw [hsource]
    exact htarget
  · have hiStrict : i < t + 2 := by
      by_contra hnot
      have hiEq : i = t + 2 := by omega
      rw [hiEq] at hiOdd
      exact (Nat.not_odd_iff_even.mpr hnEven hiOdd).elim
    have hpreviousOdd : Odd (i - 2) := by
      rcases hiOdd with ⟨pairs, hpairs⟩
      refine ⟨pairs - 1, ?_⟩
      omega
    have hsource : a.order ⟨i, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) :=
      hI1.evenOrder ⟨i, hiStrict⟩ (Odd.add_one hiOdd)
    have htarget : -(2 * (ramificationIndex K : Int)) ≤
        b.order ⟨i - 2, by omega⟩ :=
      (targetOrders.evenIndexed ⟨i - 2, by omega⟩
        ⟨i - 2, by omega⟩ le_rfl hpreviousOdd hpreviousOdd).1
    rw [hsource]
    exact htarget

/-- The pair-sum inequality of Beli's Lemma 1.6 (cited as [3, Lemma
4.6(i)] in He--Hu) forces the source's first `n` orders to equal the
alternating target profile. -/
theorem alternatingInitialOrders_of_representationOrderCondition
    {m t : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (t + 2))
    (hm : t + 2 ≤ m) (hnEven : Even (t + 2))
    (hAIntegral : Lattice.IsIntegral q L)
    (horder : a.RepresentationOrderCondition b (by omega))
    (hTargetOdd : ∀ i : Fin (t + 2), Even i.val → b.order i = 0)
    (hTargetEven : ∀ i : Fin (t + 2), Odd i.val →
      b.order i = -(2 * (ramificationIndex K : Int))) :
    (∀ i : Fin (t + 2), Even i.val →
        a.order ⟨i.val, by omega⟩ = 0) ∧
      (∀ i : Fin (t + 2), Odd i.val →
        a.order ⟨i.val, by omega⟩ =
          -(2 * (ramificationIndex K : Int))) := by
  let O := (a.representationOrderCondition_iff b (by omega)).mp horder
  let sourceOrders := a.heHu2022Proposition27i hAIntegral
  constructor
  · intro i hiEven
    have hiNext : i.val + 1 < t + 2 := by
      by_contra hnot
      have hiEq : i.val + 1 = t + 2 := by omega
      rcases hnEven with ⟨pairs, hpairs⟩
      rcases hiEven with ⟨sourcePairs, hsourcePairs⟩
      omega
    let next : Fin (t + 2) := ⟨i.val + 1, hiNext⟩
    have hnextOdd : Odd next.val := by
      simpa only [next] using Even.add_one hiEven
    have hpairRaw := O.pairSum_le i.val hiNext
    have hpair :
        a.order ⟨i.val, by omega⟩ +
            a.order ⟨i.val + 1, by omega⟩ ≤
          b.order i + b.order next := by
      simpa only [orderSequence_at, next] using hpairRaw
    have hsourceOddLower : 0 ≤ a.order ⟨i.val, by omega⟩ :=
      (sourceOrders.oddIndexed ⟨i.val, by omega⟩ ⟨i.val, by omega⟩
        le_rfl hiEven hiEven).1
    have hsourceEvenLower :
        -(2 * (ramificationIndex K : Int)) ≤
          a.order ⟨i.val + 1, by omega⟩ :=
      (sourceOrders.evenIndexed ⟨i.val + 1, by omega⟩
        ⟨i.val + 1, by omega⟩ le_rfl hnextOdd hnextOdd).1
    rw [hTargetOdd i hiEven, hTargetEven next hnextOdd] at hpair
    omega
  · intro i hiOdd
    have hiPos : 0 < i.val := by
      rcases hiOdd with ⟨pairs, hpairs⟩
      omega
    have hpreviousEven : Even (i.val - 1) := by
      rcases hiOdd with ⟨pairs, hpairs⟩
      exact ⟨pairs, by omega⟩
    let previous : Fin (t + 2) := ⟨i.val - 1, by omega⟩
    have hpairRaw := O.pairSum_le (i.val - 1) (by omega)
    have hpair :
        a.order ⟨i.val - 1, by omega⟩ +
            a.order ⟨i.val, by omega⟩ ≤
          b.order previous + b.order i := by
      simpa only [orderSequence_at, previous,
        Nat.sub_add_cancel hiPos] using hpairRaw
    have hsourceOddLower : 0 ≤
        a.order ⟨i.val - 1, by omega⟩ :=
      (sourceOrders.oddIndexed ⟨i.val - 1, by omega⟩
        ⟨i.val - 1, by omega⟩ le_rfl hpreviousEven hpreviousEven).1
    have hsourceEvenLower :
        -(2 * (ramificationIndex K : Int)) ≤
          a.order ⟨i.val, by omega⟩ :=
      (sourceOrders.evenIndexed ⟨i.val, by omega⟩
        ⟨i.val, by omega⟩ le_rfl hiOdd hiOdd).1
    rw [hTargetOdd previous hpreviousEven, hTargetEven i hiOdd] at hpair
    omega

/-- Equation (4.1) makes the left endpoint of every middle representation
boundary nonessential after completing the target to the source rank. -/
theorem not_isCurrentEssential_of_heHuI1E {m t : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (t + 2))
    {C : Lattice K V} (c : GoodBONG q C (m + 2))
    (hm : t + 2 ≤ m)
    (hPrefix : PrefixAgreement c b (by omega : t + 1 ≤ m + 1))
    (hnEven : Even (t + 2))
    (hI1 : a.HeHuI1E (t + 2) (by omega))
    (hBIntegral : Lattice.IsIntegral r M)
    (i : RepresentationIndex (m + 2) (t + 2))
    (hiTwo : 2 ≤ i.val) :
    ¬a.IsCurrentEssential c i.toSameRank := by
  intro hessential
  unfold IsCurrentEssential currentEssentialIndex IsEssentialFor
    BeliOrderSequence.IsEssentialFor at hessential
  have hstrict := hessential.1
    (by
      simp only [RepresentationIndex.toSameRank]
      omega)
    (by
      simp only [RepresentationIndex.toSameRank]
      change i.val - 1 + 1 < m + 2
      have hiSmall := i.le_small
      omega)
  simp only [orderSequence_at, RepresentationIndex.toSameRank] at hstrict
  have hiSmall := i.le_small
  have hleftIndex :
      (⟨i.val - 1 - 1, by omega⟩ : Fin (m + 2)) =
        ⟨i.val - 2, by omega⟩ := by
    apply Fin.ext
    change i.val - 1 - 1 = i.val - 2
    omega
  have hrightIndex :
      (⟨i.val - 1 + 1, by omega⟩ : Fin (m + 2)) =
        ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  have hstrict' :
      c.order ⟨i.val - 2, by omega⟩ <
        a.order ⟨i.val, by omega⟩ := by
    rw [hleftIndex, hrightIndex] at hstrict
    exact hstrict
  have hPrefixOrder :
      c.order ⟨i.val - 2, by omega⟩ =
        b.order ⟨i.val - 2, by omega⟩ :=
    hPrefix.order_eq_nat (by omega)
  have hbound := a.heHuI1E_sourceNext_le_targetPrevious b hm hnEven hI1
    hBIntegral (i := i.val) hiTwo i.le_small
  rw [hPrefixOrder] at hstrict'
  exact (not_lt_of_ge hbound) hstrict'

/-- Equation (4.1) also makes the right endpoint nonessential before the
last boundary. -/
theorem not_isNextEssential_of_heHuI1E {m t : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (t + 2))
    {C : Lattice K V} (c : GoodBONG q C (m + 2))
    (hm : t + 2 ≤ m)
    (hPrefix : PrefixAgreement c b (by omega : t + 1 ≤ m + 1))
    (hnEven : Even (t + 2))
    (hI1 : a.HeHuI1E (t + 2) (by omega))
    (hBIntegral : Lattice.IsIntegral r M)
    (i : RepresentationIndex (m + 2) (t + 2))
    (hiLast : i.val < t + 2) :
    ¬a.IsNextEssential c i.toSameRank := by
  intro hessential
  unfold IsNextEssential nextEssentialIndex IsEssentialFor
    BeliOrderSequence.IsEssentialFor at hessential
  have hstrict := hessential.1
    (by
      simp only [RepresentationIndex.toSameRank]
      exact i.pos)
    (by
      simp only [RepresentationIndex.toSameRank]
      have hiSmall := i.le_small
      omega)
  simp only [orderSequence_at, RepresentationIndex.toSameRank] at hstrict
  have hiPos := i.pos
  have hPrefixOrder :
      c.order ⟨i.val - 1, by omega⟩ =
        b.order ⟨i.val - 1, by omega⟩ :=
    hPrefix.order_eq_nat (by omega)
  have hiTwo' : 2 ≤ i.val + 1 := by omega
  have hiLast' : i.val + 1 ≤ t + 2 := by omega
  have hbound := a.heHuI1E_sourceNext_le_targetPrevious b hm hnEven hI1
    hBIntegral (i := i.val + 1) hiTwo' hiLast'
  rw [hPrefixOrder] at hstrict
  exact (not_lt_of_ge hbound) hstrict

/-- The first defect inequality in Lemma 4.2: `A_1 <= 0 <= d[a_1b_1]`. -/
theorem heHuI1E_first_representationDefect {m t : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (t + 2))
    (hm : t + 2 ≤ m) (hI1 : a.HeHuI1E (t + 2) (by omega))
    (hBIntegral : Lattice.IsIntegral r M)
    (i : RepresentationIndex (m + 2) (t + 2)) (hi : i.val = 1) :
    (a.representationAlphaValue b i : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
  have hsource : a.order ⟨i.val, i.lt_large⟩ =
      -(2 * (ramificationIndex K : Int)) := by
    apply hI1.evenOrder ⟨i.val, by omega⟩
    change Even (i.val + 1)
    rw [hi]
    norm_num
  have htarget : 0 ≤ b.order ⟨i.val - 1, by omega⟩ := by
    let targetOrders := b.heHu2022Proposition27i hBIntegral
    have hzero : Even (i.val - 1) := by
      rw [hi]
      exact Even.zero
    exact (targetOrders.oddIndexed ⟨i.val - 1, by omega⟩
      ⟨i.val - 1, by omega⟩ le_rfl hzero hzero).1
  have hhalf : a.representationHalfGap b i ≤ 0 := by
    unfold representationHalfGap
    apply WithTop.coe_le_coe.mpr
    have horder : a.order ⟨i.val, i.lt_large⟩ +
        2 * (ramificationIndex K : Int) ≤
          b.order ⟨i.val - 1, by omega⟩ := by
      rw [hsource]
      simpa only [neg_add_cancel] using htarget
    have horderQ :
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) +
            2 * (ramificationIndex K : ℚ) ≤
          (b.order ⟨i.val - 1, by omega⟩ : ℚ) := by
      exact_mod_cast horder
    push_cast at horderQ ⊢
    linarith
  calc
    (a.representationAlphaValue b i : WithTop ℚ) =
        a.representationAlpha b i := a.coe_representationAlphaValue b i
    _ ≤ a.representationHalfGap b i :=
      a.representationAlpha_le_halfGap b i
    _ ≤ 0 := hhalf
    _ ≤ a.truncatedPrefixDefect b 1 i.val i.val :=
      a.truncatedPrefixDefect_nonneg b 1 i.val i.val

/-- The last defect inequality in Lemma 4.2 is exactly He--Hu Lemma 2.9. -/
theorem heHuI1E_last_representationDefect {m t : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (t + 2))
    (hm : t + 2 ≤ m) (hnEven : Even (t + 2))
    (hI1 : a.HeHuI1E (t + 2) (by omega))
    (hAIntegral : Lattice.IsIntegral q L)
    (hBIntegral : Lattice.IsIntegral r M)
    (i : RepresentationIndex (m + 2) (t + 2))
    (hi : i.val = t + 2) :
    (a.representationAlphaValue b i : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
  have hcurrent : a.order ⟨i.val - 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
    have hindex : i.val - 1 = t + 1 := by omega
    apply hI1.evenOrder ⟨i.val - 1, by omega⟩
    change Even ((i.val - 1) + 1)
    rw [hindex]
    simpa only [Nat.add_sub_cancel] using hnEven
  have hnext : a.order ⟨i.val, i.lt_large⟩ = 0 := by
    apply hI1.oddOrder ⟨i.val, by omega⟩
    change Odd (i.val + 1)
    simpa only [hi] using Even.add_one hnEven
  have hlemma := a.heHu2022Lemma29 b hAIntegral hBIntegral i
    (by simpa only [hi] using hnEven) hcurrent hnext
  simpa only [← a.coe_representationAlphaValue b i] using hlemma

/-- Pointwise form of the sufficiency half of Lemma 4.2, assuming a
same-rank completion with the required prefix agreement. -/
theorem heHuI1E_representationDefectCondition_of_prefixAgreement
    {m t : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (t + 2))
    {C : Lattice K V} (c : GoodBONG q C (m + 2))
    (hm : t + 2 ≤ m)
    (hPrefix : PrefixAgreement c b (by omega : t + 1 ≤ m + 1))
    (hnEven : Even (t + 2))
    (hI1 : a.HeHuI1E (t + 2) (by omega))
    (hAIntegral : Lattice.IsIntegral q L)
    (hBIntegral : Lattice.IsIntegral r M) :
    a.RepresentationDefectCondition b := by
  intro i
  by_cases hfirst : i.val = 1
  · exact a.heHuI1E_first_representationDefect b hm hI1 hBIntegral i hfirst
  by_cases hlast : i.val = t + 2
  · exact a.heHuI1E_last_representationDefect b hm hnEven hI1
      hAIntegral hBIntegral i hlast
  have hiPos := i.pos
  have hiSmall := i.le_small
  have hiTwo : 2 ≤ i.val := by omega
  have hiLast : i.val < t + 2 := by omega
  have hmiddle : a.RepresentationDefectAt c i.toSameRank :=
    a.representationDefectAt_of_not_essential c i.toSameRank
      (a.not_isCurrentEssential_of_heHuI1E b c hm hPrefix hnEven hI1
        hBIntegral i hiTwo)
      (a.not_isNextEssential_of_heHuI1E b c hm hPrefix hnEven hI1
        hBIntegral i hiLast)
  unfold RepresentationDefectAt at hmiddle
  rw [a.representationAlpha_eq_of_prefixAgreement hPrefix i] at hmiddle
  simp only [RepresentationIndex.toSameRank] at hmiddle
  rw [a.truncatedPrefixDefect_eq_of_prefixAgreement hPrefix 1
    i.val i.val (by omega)] at hmiddle
  rw [← a.coe_representationAlphaValue b i] at hmiddle
  exact hmiddle

/-- If the source order immediately after an even-rank target is positive,
Corollary 2.10 makes the source--target determinant-prefix product a square.
The target is first completed to the source rank; the prefix product then
descends through the exact prefix agreement.  This is the square-class step
in the implication `(ii) -> (iii)` of He--Hu, Lemma 4.2. -/
theorem comparisonPrefixProduct_isSquare_of_boundaryOrder_pos
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    {m t : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (t + 2))
    (hm : t + 2 ≤ m)
    (hAmbient : q.Represents r)
    (horder : a.RepresentationOrderCondition b (by omega))
    (hdefect : a.RepresentationDefectCondition b)
    (hTargetLast : b.order ⟨t + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hSourceBoundaryPos : 0 < a.order ⟨t + 2, by omega⟩) :
    IsSquare (a.prefixProduct (t + 2) * b.prefixProduct (t + 2)) := by
  rcases hAmbient with ⟨f⟩
  let E : Lattice K V := Lattice.representationEnvelope f L M
  let fE : Lattice.Representation r q M E :=
    Lattice.Representation.ofAmbientToEnvelope f L M
  rcases exists_good_bong q E with ⟨dRaw⟩
  let d : GoodBONG q E (m + 2) :=
    dRaw.castLength a.toBONG.length_eq_finrank.symm
  have hStrict : t + 1 < m + 1 := by omega
  obtain ⟨D⟩ := d.exists_deepIntegralExtension b hStrict fE
    a.rankCompletionTailOrderBound
    (a.representationAlphaValue b
      (rankCompletionBoundaryIndex hStrict))
  have horderCompleted :
      a.RepresentationOrderCondition D.completedBONG le_rfl :=
    a.representationOrderCondition_toSameRank_of_prefixAgreement
      D.prefixAgreement D.tailOrder horder
  have hdefectCompleted :
      a.RepresentationDefectCondition D.completedBONG :=
    a.representationDefectCondition_toSameRank_of_prefixAgreement
      (alphaV := sourceLaws) (alphaU := sourceLaws)
      D.prefixAgreement hStrict D.tailOrder D.boundaryAlpha.le hdefect
  let i : RepresentationIndex (m + 2) (m + 2) :=
    { val := t + 2
      pos := by omega
      lt_large := by omega
      le_small := by omega }
  have hCompletedLast :
      D.completedBONG.order ⟨t + 1, by omega⟩ =
        b.order ⟨t + 1, by omega⟩ :=
    D.prefixAgreement.order_eq_nat (by omega)
  have hstrictRaw :
      D.completedBONG.order ⟨t + 1, by omega⟩ +
          2 * (ramificationIndex K : Int) <
        a.order ⟨t + 2, by omega⟩ := by
    rw [hCompletedLast, hTargetLast]
    simpa only [neg_add_cancel] using hSourceBoundaryPos
  have hstrict :
      D.completedBONG.order
          ⟨i.val - 1, (Nat.sub_le i.val 1).trans_lt i.lt_large⟩ +
          2 * (ramificationIndex K : Int) <
        a.order ⟨i.val, i.lt_large⟩ := by
    simpa only [i, show t + 2 - 1 = t + 1 by omega] using hstrictRaw
  have hiOne : 1 < i.val := by
    dsimp only [i]
    omega
  have hsquareCompleted := a.beli2019Corollary210_complete
    (sourceLaws := sourceLaws) (targetLaws := sourceLaws)
    D.completedBONG horderCompleted hdefectCompleted i hiOne hstrict
  have hprefix : D.completedBONG.prefixProduct (t + 2) =
      b.prefixProduct (t + 2) :=
    D.prefixAgreement.prefixProduct_eq (t + 2) le_rfl
  simpa only [i, hprefix] using hsquareCompleted

/-- Cancelling a common source prefix from two square comparison products
shows that the product of the two target prefixes is itself a square. -/
theorem targetPrefixProduct_isSquare_of_common_source
    (A B C : Kˣ) (hAB : IsSquare (A * B)) (hAC : IsSquare (A * C)) :
    IsSquare (B * C) := by
  have hA2 : IsSquare (A ^ 2) := ⟨A, by simp only [pow_two]⟩
  have hquotient := (hAB.mul hAC).div hA2
  have hcancel : ((A * B) * (A * C)) / A ^ 2 = B * C := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero A]
  rw [hcancel] at hquotient
  exact hquotient

/-- The two determinant-square-class tests in Lemma 4.2 force the source
boundary order `R_(n+1)` to vanish.  This is the contradiction argument in
the published proof, isolated from the later choice of the concrete test
lattices `N_1^n(1)` and `N_1^n(Delta)`. -/
theorem boundaryOrder_eq_zero_of_two_squareClass_tests
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    {m t : Nat}
    {rOne rDelta : QuadraticSpace K W}
    {MOne MDelta : Lattice K W}
    (a : GoodBONG q L (m + 2))
    (bOne : GoodBONG rOne MOne (t + 2))
    (bDelta : GoodBONG rDelta MDelta (t + 2))
    (hm : t + 2 ≤ m) (hnEven : Even (t + 2))
    (hAIntegral : Lattice.IsIntegral q L)
    (hAmbientOne : q.Represents rOne)
    (hAmbientDelta : q.Represents rDelta)
    (horderOne : a.RepresentationOrderCondition bOne (by omega))
    (hdefectOne : a.RepresentationDefectCondition bOne)
    (horderDelta : a.RepresentationOrderCondition bDelta (by omega))
    (hdefectDelta : a.RepresentationDefectCondition bDelta)
    (hOneLast : bOne.order ⟨t + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hDeltaLast : bDelta.order ⟨t + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hTargetProductNotSquare :
      ¬IsSquare (bOne.prefixProduct (t + 2) *
        bDelta.prefixProduct (t + 2))) :
    a.order ⟨t + 2, by omega⟩ = 0 := by
  have hnonneg : 0 ≤ a.order ⟨t + 2, by omega⟩ := by
    let sourceOrders := a.heHu2022Proposition27i hAIntegral
    exact (sourceOrders.oddIndexed ⟨t + 2, by omega⟩
      ⟨t + 2, by omega⟩ le_rfl hnEven hnEven).1
  apply le_antisymm ?_ hnonneg
  by_contra hnotLe
  have hpos : 0 < a.order ⟨t + 2, by omega⟩ := lt_of_not_ge hnotLe
  have hsqOne := a.comparisonPrefixProduct_isSquare_of_boundaryOrder_pos
    bOne hm hAmbientOne horderOne hdefectOne hOneLast hpos
  have hsqDelta := a.comparisonPrefixProduct_isSquare_of_boundaryOrder_pos
    bDelta hm hAmbientDelta horderDelta hdefectDelta hDeltaLast hpos
  exact hTargetProductNotSquare
    (targetPrefixProduct_isSquare_of_common_source
      (a.prefixProduct (t + 2)) (bOne.prefixProduct (t + 2))
        (bDelta.prefixProduct (t + 2)) hsqOne hsqDelta)

/-- Abstract necessity half of Lemma 4.2.  One alternating test determines
the first `n` source orders; a second test in the discriminant square class
forces the additional odd-index boundary order to be zero. -/
theorem heHu2022Lemma42Necessity_of_two_squareClass_tests
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    {m t : Nat}
    {rOne rDelta : QuadraticSpace K W}
    {MOne MDelta : Lattice K W}
    (a : GoodBONG q L (m + 2))
    (bOne : GoodBONG rOne MOne (t + 2))
    (bDelta : GoodBONG rDelta MDelta (t + 2))
    (hm : t + 2 ≤ m) (hnEven : Even (t + 2))
    (hAIntegral : Lattice.IsIntegral q L)
    (hAmbientOne : q.Represents rOne)
    (hAmbientDelta : q.Represents rDelta)
    (horderOne : a.RepresentationOrderCondition bOne (by omega))
    (hdefectOne : a.RepresentationDefectCondition bOne)
    (horderDelta : a.RepresentationOrderCondition bDelta (by omega))
    (hdefectDelta : a.RepresentationDefectCondition bDelta)
    (hOneOdd : ∀ i : Fin (t + 2), Even i.val → bOne.order i = 0)
    (hOneEven : ∀ i : Fin (t + 2), Odd i.val →
      bOne.order i = -(2 * (ramificationIndex K : Int)))
    (hDeltaLast : bDelta.order ⟨t + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hTargetProductNotSquare :
      ¬IsSquare (bOne.prefixProduct (t + 2) *
        bDelta.prefixProduct (t + 2))) :
    a.HeHuI1E (t + 2) (by omega) := by
  have hInitial := a.alternatingInitialOrders_of_representationOrderCondition
    bOne hm hnEven hAIntegral horderOne hOneOdd hOneEven
  have hOneLast : bOne.order ⟨t + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
    apply hOneEven
    change Odd (t + 1)
    rcases hnEven with ⟨pairs, hpairs⟩
    refine ⟨pairs - 1, ?_⟩
    omega
  have hBoundary := a.boundaryOrder_eq_zero_of_two_squareClass_tests
    bOne bDelta hm hnEven hAIntegral hAmbientOne hAmbientDelta
      horderOne hdefectOne horderDelta hdefectDelta hOneLast hDeltaLast
      hTargetProductNotSquare
  constructor
  · intro i hiOddPaper
    by_cases hiInitial : i.val < t + 2
    · have hiEven : Even i.val := by
        rcases hiOddPaper with ⟨pairs, hpairs⟩
        exact ⟨pairs, by omega⟩
      exact hInitial.1 ⟨i.val, hiInitial⟩ hiEven
    · have hiBoundary : i.val = t + 2 := by omega
      simpa only [hiBoundary] using hBoundary
  · intro i hiEvenPaper
    have hiOdd : Odd i.val := by
      rcases hiEvenPaper with ⟨pairs, hpairs⟩
      refine ⟨pairs - 1, ?_⟩
      omega
    exact hInitial.2 i hiOdd

/-- He--Hu, Lemma 4.2, implication `(i) -> (iii)`.  The published test
lattices `N_1^n(1)` and `N_1^n(Delta)` are instantiated by the exact models
from Lemma 3.11; their determinant classes are separated by the preceding
explicit prefix-product calculation. -/
theorem heHu2022Lemma42Necessity
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DyadicDiscriminantClassLaws K]
    {m t : Nat}
    (a : GoodBONG q L (m + 2))
    (hm : t + 2 ≤ m) (hnEven : Even (t + 2))
    (hAIntegral : Lattice.IsIntegral q L)
    (hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q (t + 2))
    (hAll : HeHuAllOrderAndDefectConditions.{u, v, u}
      (n := t + 1) a (by omega)) :
    a.HeHuI1E (t + 2) (by omega) := by
  rcases hnEven with ⟨pairs, hpairs⟩
  have hpairsPos : 0 < pairs := by omega
  let k := pairs - 1
  have hRank : 2 + 2 * k = t + 2 := by
    dsimp only [k]
    omega
  let bOneRaw := heHuLemma311EvenFirstOneBONG (K := K) k
  let bDeltaRaw := heHuLemma311EvenFirstDeltaBONG (K := K) k
  let bOne := bOneRaw.castLength hRank
  let bDelta := bDeltaRaw.castLength hRank
  have hOneOdd : ∀ i : Fin (t + 2), Even i.val → bOne.order i = 0 := by
    intro i hiEven
    rcases hiEven with ⟨j, hj⟩
    have hjSmall : j < k + 1 := by omega
    let p : Fin (k + 1) := ⟨j, hjSmall⟩
    have hprofile := heHu2022Lemma311iFirstOne (K := K) k p
    dsimp only [bOne]
    rw [order_castLength]
    have hindex : (⟨i.val, by omega⟩ : Fin (2 + 2 * k)) =
        ⟨2 * p.val, by omega⟩ := by
      apply Fin.ext
      dsimp only [p]
      omega
    rw [hindex]
    exact hprofile.1
  have hOneEven : ∀ i : Fin (t + 2), Odd i.val →
      bOne.order i = -(2 * (ramificationIndex K : Int)) := by
    intro i hiOdd
    rcases hiOdd with ⟨j, hj⟩
    have hjSmall : j < k + 1 := by omega
    let p : Fin (k + 1) := ⟨j, hjSmall⟩
    have hprofile := heHu2022Lemma311iFirstOne (K := K) k p
    dsimp only [bOne]
    rw [order_castLength]
    have hindex : (⟨i.val, by omega⟩ : Fin (2 + 2 * k)) =
        ⟨2 * p.val + 1, by omega⟩ := by
      apply Fin.ext
      dsimp only [p]
      omega
    rw [hindex]
    exact hprofile.2
  have hDeltaLast : bDelta.order ⟨t + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
    let p : Fin (k + 1) := ⟨k, by omega⟩
    have hprofile := heHu2022Lemma311iFirstDelta (K := K) k p
    dsimp only [bDelta]
    rw [order_castLength]
    have hindex : (⟨t + 1, by omega⟩ : Fin (2 + 2 * k)) =
        ⟨2 * p.val + 1, by omega⟩ := by
      apply Fin.ext
      dsimp only [p]
      omega
    rw [hindex]
    exact hprofile.2
  have hOneNonneg : 0 ≤ bOne.order 0 := by
    have hzero := hOneOdd (0 : Fin (t + 2)) Even.zero
    rw [hzero]
  let hOneIntegral := heHuIntegral_of_firstOrder_nonneg bOne hOneNonneg
  have hDeltaNonneg : 0 ≤ bDelta.order 0 := by
    let p : Fin (k + 1) := ⟨0, by omega⟩
    have hprofile := heHu2022Lemma311iFirstDelta (K := K) k p
    dsimp only [bDelta]
    rw [order_castLength]
    have hindex : (⟨0, by omega⟩ : Fin (2 + 2 * k)) =
        ⟨2 * p.val, by omega⟩ := by
      apply Fin.ext
      rfl
    have hzero : bDeltaRaw.order ⟨0, by omega⟩ = 0 := by
      rw [hindex]
      exact hprofile.1
    change 0 ≤ bDeltaRaw.order ⟨0, by omega⟩
    rw [hzero]
  let hDeltaIntegral :=
    heHuIntegral_of_firstOrder_nonneg bDelta hDeltaNonneg
  have hNotSquare :
      ¬IsSquare (bOne.prefixProduct (t + 2) *
        bDelta.prefixProduct (t + 2)) := by
    have hraw := heHuLemma311EvenFirst_prefixProducts_not_isSquare
      (K := K) k
    dsimp only [bOne, bDelta]
    simpa only [prefixProduct_castLength_heHu, ← hRank] using hraw
  have hOneConditions := hAll bOne hOneIntegral
  have hDeltaConditions := hAll bDelta hDeltaIntegral
  exact a.heHu2022Lemma42Necessity_of_two_squareClass_tests
    bOne bDelta hm ⟨pairs, hpairs⟩ hAIntegral
      (hAmbient _ _ bOne.toBONG.length_eq_finrank.symm hOneIntegral)
      (hAmbient _ _ bDelta.toBONG.length_eq_finrank.symm hDeltaIntegral)
      hOneConditions.1 hOneConditions.2 hDeltaConditions.1
      hDeltaConditions.2 hOneOdd hOneEven hDeltaLast hNotSquare

/-- He--Hu, Lemma 4.2, implication `(iii) -> (i)`: under ambient
`n`-universality, `I1^E(n)` supplies conditions (i) and (ii) of Theorem 2.8
for every integral rank-`n` target. -/
theorem heHu2022Lemma42Sufficiency {m t : Nat}
    (a : GoodBONG q L (m + 2))
    (hm : t + 2 ≤ m) (hnEven : Even (t + 2))
    (hAIntegral : Lattice.IsIntegral q L)
    (hAmbient : Lattice.AmbientlyNUniversal.{u, v, w} q (t + 2))
    (hI1 : a.HeHuI1E (t + 2) (by omega)) :
    HeHuAllOrderAndDefectConditions.{u, v, w} (n := t + 1) a
      (by omega : t + 1 ≤ m + 1) := by
  intro W _ _ r M b hBIntegral
  have hfin : Module.finrank K W = t + 2 :=
    b.toBONG.length_eq_finrank.symm
  have hambient : q.Represents r := hAmbient r M hfin hBIntegral
  rcases hambient with ⟨f⟩
  let E : Lattice K V := Lattice.representationEnvelope f L M
  let fE : Lattice.Representation r q M E :=
    Lattice.Representation.ofAmbientToEnvelope f L M
  rcases exists_good_bong q E with ⟨dRaw⟩
  let d : GoodBONG q E (m + 2) :=
    dRaw.castLength a.toBONG.length_eq_finrank.symm
  have hStrict : t + 1 < m + 1 := by omega
  obtain ⟨D⟩ := d.exists_deepIntegralExtension b hStrict fE 0 0
  have hPrefix : PrefixAgreement D.completedBONG b (by omega) :=
    D.prefixAgreement
  exact
    ⟨a.heHuI1E_representationOrderCondition b hm hI1 hBIntegral,
      a.heHuI1E_representationDefectCondition_of_prefixAgreement
        b D.completedBONG hm hPrefix hnEven hI1 hAIntegral hBIntegral⟩

/-- He--Hu, Lemma 4.2, complete equivalence `(i) <-> (iii)` (with the
intermediate two-test statement `(ii)` realized by the explicit Lemma 3.11
models in the necessity proof). -/
theorem heHu2022Lemma42
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DyadicDiscriminantClassLaws K]
    {m t : Nat}
    (a : GoodBONG q L (m + 2))
    (hm : t + 2 ≤ m) (hnEven : Even (t + 2))
    (hAIntegral : Lattice.IsIntegral q L) :
    Lattice.AmbientlyNUniversal.{u, v, u} q (t + 2) →
      (HeHuAllOrderAndDefectConditions.{u, v, u}
          (n := t + 1) a (by omega) ↔
        a.HeHuI1E (t + 2) (by omega)) := by
  intro hAmbient
  constructor
  · intro hAll
    exact a.heHu2022Lemma42Necessity hm hnEven hAIntegral
      hAmbient hAll
  · intro hI1
    exact a.heHu2022Lemma42Sufficiency hm hnEven hAIntegral
      hAmbient hI1

end BONG.GoodBONG

end Bong
