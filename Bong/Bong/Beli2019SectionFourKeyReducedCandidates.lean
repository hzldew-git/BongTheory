/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma29ReducedEquality
import Bong.Bong.Beli2019SectionFourKeySecondaryTriangle

/-!
# Beli (2019), Lemma 4.2: the four reduced middle candidates

The secondary-source branch in the proof of Lemma 4.2(i) invokes Lemma 2.9
for the middle-to-target invariant `B_(i-1)`.  The direct order hypothesis
makes the secondary coefficient positive, while condition 2.1(ii) is exactly
the comparison hypothesis of Lemma 2.9.  This file records the resulting
four-candidate normal form and its exhaustive equality split.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U} {n : Nat}

/-- Lemma 2.9 gives the four-term reduced formula for `B_(i-1)` in the
interior direct branch of Lemma 4.2(i). -/
theorem middleTargetAlpha_eq_reduced_of_leftDirect
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    b.representationAlpha c j =
      b.representationAlphaReduced c j hi j.lt_large := by
  have hpair := a.keyLemmaLeftDirect_middlePair_lt b c hab j
    hi.1 hi.2 hessential hdirect
  have hshift : 0 <
      b.order ⟨j.val, j.lt_large⟩ + b.order ⟨j.val + 1, hi.2⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ := by
    omega
  have hcomparison : b.representationAlpha c j ≤
      b.truncatedPrefixDefect c 1 j.val j.val := by
    simpa only [← b.coe_representationAlphaValue c j] using hbcDefect j
  exact b.representationAlpha_eq_reduced_of_positiveShift
    (sourceLaws := middleLaws) (targetLaws := targetLaws)
    c j hi j.lt_large hshift hcomparison

/-- The four alternatives displayed for `B_(i-1)` in Lemma 4.2(i).
The terms are, in order, the half-gap, primary, middle-alpha, and
target-alpha candidates of Definition 6. -/
theorem middleTargetAlpha_reduced_four_candidates
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    b.representationAlpha c j = b.representationHalfGap c j ∨
      b.representationAlpha c j = b.representationPrimaryDefect c j ∨
      b.representationAlpha c j =
        b.representationSecondarySourceAlpha c j hi ∨
      b.representationAlpha c j =
        b.representationSecondaryTargetAlpha c j hi j.lt_large := by
  have hnormal := a.middleTargetAlpha_eq_reduced_of_leftDirect
    (middleLaws := middleLaws) (targetLaws := targetLaws)
    b c hab hbcDefect j hi hessential hdirect
  unfold representationAlphaReduced at hnormal
  rcases min_choice (b.representationHalfGap c j)
      (min (b.representationPrimaryDefect c j)
        (min (b.representationSecondarySourceAlpha c j hi)
          (b.representationSecondaryTargetAlpha c j hi j.lt_large))) with
    hhalf | hrest
  · exact Or.inl (hnormal.trans hhalf)
  · rcases min_choice (b.representationPrimaryDefect c j)
        (min (b.representationSecondarySourceAlpha c j hi)
          (b.representationSecondaryTargetAlpha c j hi j.lt_large)) with
      hprimary | hsecondary
    · exact Or.inr (Or.inl (hnormal.trans (hrest.trans hprimary)))
    · rcases min_choice (b.representationSecondarySourceAlpha c j hi)
          (b.representationSecondaryTargetAlpha c j hi j.lt_large) with
        hsource | htarget
      · exact Or.inr (Or.inr (Or.inl
          (hnormal.trans (hrest.trans (hsecondary.trans hsource)))))
      · exact Or.inr (Or.inr (Or.inr
          (hnormal.trans (hrest.trans (hsecondary.trans htarget)))))

/-- The half-gap alternative for `B_(i-1)` is incompatible with a strict
failure at the source secondary candidate.  This is the first exclusion in
the secondary branch of Lemma 4.2(i), lines 2147--2152. -/
theorem middleTargetHalfGap_impossible_of_sourceSecondaryFailure
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hsecondary : a.representationSecondaryCurrentDefect b j hi <
      a.representationAlpha c j)
    (hhalf : b.representationAlpha c j =
      b.representationHalfGap c j) : False := by
  have hlower := a.shift_middleTargetAlpha_le_secondaryCurrentSource
    b c hbcOrder hbcDefect j hi hessential hsecondary
  rw [hhalf] at hlower
  have hupper : a.representationAlpha c j ≤
      (((a.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        (c.halfGapValue ⟨j.val - 2, by omega⟩ : WithTop ℚ) :=
    (a.representationAlpha_le_prime c j).trans
      (a.representationAlphaPrime_le_primaryRightHalfGap c j hi.1)
  have hstrict := hlower.trans_lt hsecondary
  have hfinite := hstrict.trans_le hupper
  have hpairRaw :=
    ((b.representationOrderCondition_iff c le_rfl).mp hbcOrder).pairSum_le
      (j.val - 2) (by omega)
  have hpair :
      b.order ⟨j.val - 2, by omega⟩ + b.order ⟨j.val - 1, by omega⟩ ≤
        c.order ⟨j.val - 2, by omega⟩ +
          c.order ⟨j.val - 1, by omega⟩ := by
    simpa only [orderSequence_at, show j.val - 2 + 1 = j.val - 1 by omega]
      using hpairRaw
  have hdirectRaw := hdirect hi.1 hi.2
  simp only [nextEssentialIndex] at hdirectRaw
  have hessentialCross :
      c.order ⟨j.val - 1, by omega⟩ <
        a.order ⟨j.val + 1, hi.2⟩ := by
    unfold IsNextEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hessential
    have hraw := hessential.1 (by
      simp only [nextEssentialIndex]
      omega) (by simpa only [nextEssentialIndex] using hi.2)
    simpa only [orderSequence_at, nextEssentialIndex] using hraw
  unfold representationSecondaryCurrentDefect representationHalfGap at hfinite
  unfold halfGapValue orderGap at hfinite
  norm_cast at hfinite
  simp only [Rat.divInt_eq_div] at hfinite
  push_cast at hfinite
  have htargetSucc :
      (⟨j.val - 2, by omega⟩ : Fin n).succ =
        (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp
    omega
  have htargetCast :
      (⟨j.val - 2, by omega⟩ : Fin n).castSucc =
        (⟨j.val - 2, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  rw [htargetSucc, htargetCast] at hfinite
  have hpairQ :
      (b.order ⟨j.val - 2, by omega⟩ : ℚ) +
          b.order ⟨j.val - 1, by omega⟩ ≤
        c.order ⟨j.val - 2, by omega⟩ +
          c.order ⟨j.val - 1, by omega⟩ := by
    exact_mod_cast hpair
  have hdirectQ :
      (c.order ⟨j.val - 2, by omega⟩ : ℚ) +
          c.order ⟨j.val - 1, by omega⟩ <
        a.order ⟨j.val + 1, hi.2⟩ +
          b.order ⟨j.val, j.lt_large⟩ := by
    exact_mod_cast hdirectRaw
  have hessentialQ :
      (c.order ⟨j.val - 1, by omega⟩ : ℚ) <
        a.order ⟨j.val + 1, hi.2⟩ := by
    exact_mod_cast hessentialCross
  linarith

/-- A strict failure of the source bound chooses an actual defect candidate,
not merely a candidate below the target.  This retains the equality used in
the paper's contradiction argument. -/
theorem leftDirect_sourceFailure_candidate_eq
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hfailure : ¬a.representationAlpha c j ≤
      a.representationAlpha b j) :
    (a.representationAlpha b j = a.representationPrimaryDefect b j ∧
      a.representationPrimaryDefect b j < a.representationAlpha c j) ∨
    (a.representationAlpha b j =
        a.representationSecondaryCurrentDefect b j hi ∧
      a.representationSecondaryCurrentDefect b j hi <
        a.representationAlpha c j) := by
  have hnormal := by
    letI : Beli2006AlphaLaws.{u, w} K := middleLaws
    exact a.representationAlpha_eq_min_halfGap_primary_current_of_leftDirect
      b c hbc j hi hessential hdirect
  have hstrict : a.representationAlpha b j <
      a.representationAlpha c j := lt_of_not_ge hfailure
  have hhalfLe := by
    letI : Beli2006AlphaLaws.{u, z} K := targetLaws
    exact a.representationAlpha_le_leftDirect_sourceHalfGap_of_conditions
      b c hab hbc j hi.1 hi.2 hessential hdirect
  rcases min_choice (a.representationHalfGap b j)
      (min (a.representationPrimaryDefect b j)
        (a.representationSecondaryCurrentDefect b j hi)) with
    hhalf | hdefect
  · have heq := hnormal.trans hhalf
    exact False.elim ((not_lt_of_ge hhalfLe) (heq ▸ hstrict))
  · rcases min_choice (a.representationPrimaryDefect b j)
        (a.representationSecondaryCurrentDefect b j hi) with
      hprimary | hsecondary
    · have heq := hnormal.trans (hdefect.trans hprimary)
      exact Or.inl ⟨heq, heq ▸ hstrict⟩
    · have heq := hnormal.trans (hdefect.trans hsecondary)
      exact Or.inr ⟨heq, heq ▸ hstrict⟩

/-- The middle-alpha alternative
`2S_i-T_(i-2)-T_(i-1)+beta_i` cannot occur when the source invariant is
its secondary candidate.  Monotonicity of `S_k+beta_k` is Lemma 2.2. -/
theorem middleTargetSourceAlpha_impossible_of_sourceSecondary_eq
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hsourceEq : a.representationAlpha b j =
      a.representationSecondaryCurrentDefect b j hi)
    (hmiddleEq : b.representationAlpha c j =
      b.representationSecondarySourceAlpha c j hi)
    (hlower :
      (((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
        b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + b.representationAlpha c j ≤
        a.representationSecondaryCurrentDefect b j hi) : False := by
  let previous : Fin n := ⟨j.val - 2, by omega⟩
  let middle : Fin n := ⟨j.val - 1, by omega⟩
  let current : Fin n := ⟨j.val, by omega⟩
  have hpreviousVal : previous.val = j.val - 2 := rfl
  have hmiddleVal : middle.val = j.val - 1 := rfl
  have hcurrentVal : current.val = j.val := rfl
  have hprev := (b.alpha_p1 previous (by
    rw [hpreviousVal]
    omega)).1
  have hcurrent := (b.alpha_p1 middle (by
    rw [hmiddleVal]
    omega)).1
  have hmono : b.alphaLeftEndpoint previous ≤
      b.alphaLeftEndpoint current := by
    have hstep : (⟨previous.val + 1, by
        rw [hpreviousVal]
        omega⟩ : Fin n) = middle := by
      apply Fin.ext
      simp only [previous, middle]
      omega
    have hstep' : (⟨middle.val + 1, by
        rw [hmiddleVal]
        omega⟩ : Fin n) = current := by
      apply Fin.ext
      simp only [middle, current]
      omega
    rw [hstep] at hprev
    rw [hstep'] at hcurrent
    exact hprev.trans hcurrent
  have hmonoQ :
      (b.order ⟨j.val - 2, by omega⟩ : ℚ) + b.alphaValue previous ≤
        b.order ⟨j.val, j.lt_large⟩ + b.alphaValue current := by
    unfold alphaLeftEndpoint at hmono
    have hpreviousCast : previous.castSucc =
        (⟨j.val - 2, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hcurrentCast : current.castSucc =
        (⟨j.val, j.lt_large⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    rw [hpreviousCast, hcurrentCast] at hmono
    exact hmono
  have hcap : a.representationAlpha b j ≤
      (((a.order ⟨j.val, j.lt_large⟩ -
        b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + (b.alphaValue previous : WithTop ℚ) := by
    calc
      a.representationAlpha b j ≤ a.representationAlphaPrime b j :=
        a.representationAlpha_le_prime b j
      _ ≤ (((a.order ⟨j.val, j.lt_large⟩ -
          b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + b.prefixAlphaCap (j.val - 1) :=
        a.representationAlphaPrime_le_primaryRightCap b j
      _ = _ := by
        rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
        congr 1
  have hstrictStart :
      (((a.order ⟨j.val, j.lt_large⟩ -
        b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + (b.alphaValue previous : WithTop ℚ) <
        (((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
          b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
          b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + b.representationAlpha c j := by
    rw [hmiddleEq]
    unfold representationSecondarySourceAlpha
    norm_cast
    have hdirectRaw := hdirect hi.1 hi.2
    simp only [nextEssentialIndex] at hdirectRaw
    have hdirectQ :
        (c.order ⟨j.val - 2, by omega⟩ : ℚ) +
            c.order ⟨j.val - 1, by omega⟩ <
          a.order ⟨j.val + 1, hi.2⟩ +
            b.order ⟨j.val, j.lt_large⟩ := by
      exact_mod_cast hdirectRaw
    push_cast
    linarith
  have hstrict := hstrictStart.trans_le hlower
  exact (not_lt_of_ge (hsourceEq ▸ hcap)) hstrict

/-- The target-alpha alternative
`S_i+S_(i+1)-2T_(i-1)+gamma_(i-2)` is incompatible with the same strict
secondary failure.  This is the third exclusion in lines 2157--2160. -/
theorem middleTargetTargetAlpha_impossible_of_sourceSecondaryFailure
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hsecondary : a.representationSecondaryCurrentDefect b j hi <
      a.representationAlpha c j)
    (hmiddleEq : b.representationAlpha c j =
      b.representationSecondaryTargetAlpha c j hi j.lt_large)
    (hlower :
      (((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
        b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + b.representationAlpha c j ≤
        a.representationSecondaryCurrentDefect b j hi) : False := by
  let previous : Fin n := ⟨j.val - 2, by omega⟩
  let b0 : Fin (n + 1) := ⟨j.val - 2, by omega⟩
  let b1 : Fin (n + 1) := ⟨j.val - 1, by omega⟩
  have hb0 : b0.val = j.val - 2 := rfl
  have hb1 : b1.val = j.val - 1 := rfl
  have hgood0 := b.good b0 (by rw [hb0]; omega)
  have hgood1 := b.good b1 (by rw [hb1]; omega)
  have hpair :
      b.order ⟨j.val - 2, by omega⟩ + b.order ⟨j.val - 1, by omega⟩ ≤
        b.order ⟨j.val, j.lt_large⟩ + b.order ⟨j.val + 1, hi.2⟩ := by
    have hgood0' : b.order ⟨j.val - 2, by omega⟩ ≤
        b.order ⟨j.val, j.lt_large⟩ := by
      change b.toBONG.order ⟨j.val - 2, by omega⟩ ≤
        b.toBONG.order ⟨j.val, j.lt_large⟩
      simpa only [b0, show j.val - 2 + 2 = j.val by omega] using hgood0
    have hgood1' : b.order ⟨j.val - 1, by omega⟩ ≤
        b.order ⟨j.val + 1, hi.2⟩ := by
      change b.toBONG.order ⟨j.val - 1, by omega⟩ ≤
        b.toBONG.order ⟨j.val + 1, hi.2⟩
      simpa only [b1, show j.val - 1 + 2 = j.val + 1 by omega] using hgood1
    omega
  have hcross : c.order ⟨j.val - 1, by omega⟩ <
      a.order ⟨j.val + 1, hi.2⟩ := by
    unfold IsNextEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hessential
    have hraw := hessential.1 (by
      simp only [nextEssentialIndex]
      omega) (by simpa only [nextEssentialIndex] using hi.2)
    simpa only [orderSequence_at, nextEssentialIndex] using hraw
  have hupper : a.representationAlpha c j ≤
      (((a.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + (c.alphaValue previous : WithTop ℚ) := by
    calc
      a.representationAlpha c j ≤ a.representationAlphaPrime c j :=
        a.representationAlpha_le_prime c j
      _ ≤ (((a.order ⟨j.val, j.lt_large⟩ -
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + c.prefixAlphaCap (j.val - 1) :=
        a.representationAlphaPrime_le_primaryRightCap c j
      _ = _ := by
        rw [c.prefixAlphaCap_of_internal (by omega) (by omega)]
        congr 1
  have hstrictStart :
      (((a.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + (c.alphaValue previous : WithTop ℚ) <
        (((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
          b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
          b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + b.representationAlpha c j := by
    rw [hmiddleEq]
    unfold representationSecondaryTargetAlpha
    norm_cast
    have hpairQ :
        (b.order ⟨j.val - 2, by omega⟩ : ℚ) +
            b.order ⟨j.val - 1, by omega⟩ ≤
          b.order ⟨j.val, j.lt_large⟩ +
            b.order ⟨j.val + 1, hi.2⟩ := by
      exact_mod_cast hpair
    have hcrossQ :
        (c.order ⟨j.val - 1, by omega⟩ : ℚ) <
          a.order ⟨j.val + 1, hi.2⟩ := by
      exact_mod_cast hcross
    push_cast
    linarith
  have hcontradiction := (hstrictStart.trans_le hlower).trans hsecondary
  exact (not_lt_of_ge hupper) hcontradiction

/-- After the three exclusions, `B_(i-1)` is its primary defect candidate,
exactly as concluded at line 2162 of the paper. -/
theorem middleTargetAlpha_eq_primary_of_sourceSecondaryFailure
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hsourceEq : a.representationAlpha b j =
      a.representationSecondaryCurrentDefect b j hi)
    (hsecondary : a.representationSecondaryCurrentDefect b j hi <
      a.representationAlpha c j) :
    b.representationAlpha c j = b.representationPrimaryDefect c j := by
  have hlower := a.shift_middleTargetAlpha_le_secondaryCurrentSource
    b c hbcOrder hbcDefect j hi hessential hsecondary
  rcases a.middleTargetAlpha_reduced_four_candidates
      (middleLaws := middleLaws) (targetLaws := targetLaws)
      b c hab hbcDefect j hi hessential hdirect with
    hhalf | hprimary | hsource | htarget
  · exact False.elim
      (a.middleTargetHalfGap_impossible_of_sourceSecondaryFailure
        (middleLaws := middleLaws) (targetLaws := targetLaws)
        b c hab hbcOrder hbcDefect j hi hessential hdirect hsecondary hhalf)
  · exact hprimary
  · exact False.elim
      (a.middleTargetSourceAlpha_impossible_of_sourceSecondary_eq
        (middleLaws := middleLaws) b c j hi hdirect hsourceEq hsource hlower)
  · exact False.elim
      (a.middleTargetTargetAlpha_impossible_of_sourceSecondaryFailure
        b c j hi hessential hsecondary htarget hlower)

/-- With `B_(i-1)` now identified as its primary candidate, the strict
failure gives the triangle identity
`d[-b_(1,i)c_(1,i-2)] = d[a_(1,i)b_(1,i)]` from line 2170. -/
theorem middleTargetPrimaryDefect_eq_sourceMiddleCurrentDefect
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hmiddlePrimary : b.representationAlpha c j =
      b.representationPrimaryDefect c j)
    (hsecondary : a.representationSecondaryCurrentDefect b j hi <
      a.representationAlpha c j)
    (hlower :
      (((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
        b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + b.representationAlpha c j ≤
        a.representationSecondaryCurrentDefect b j hi) :
    b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) =
      a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) := by
  let sourceShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
      b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let middleShift : ℚ :=
    ((b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let targetShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let middleDefect :=
    b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
  let targetDefect :=
    a.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
  have htarget := a.representationAlpha_le_primary c j
  have hsourceStrict :
      (sourceShift : WithTop ℚ) + b.representationAlpha c j <
        a.representationAlpha c j := by
    calc
      (sourceShift : WithTop ℚ) + b.representationAlpha c j ≤
          a.representationSecondaryCurrentDefect b j hi := by
        simpa only [sourceShift] using hlower
      _ < a.representationAlpha c j := hsecondary
  have hstrictShifted : (sourceShift : WithTop ℚ) +
      ((middleShift : WithTop ℚ) + middleDefect) <
        (targetShift : WithTop ℚ) + targetDefect := by
    calc
      (sourceShift : WithTop ℚ) +
          ((middleShift : WithTop ℚ) + middleDefect) =
        (sourceShift : WithTop ℚ) + b.representationAlpha c j := by
          rw [hmiddlePrimary]
          rfl
      _ < a.representationAlpha c j := hsourceStrict
      _ ≤ (targetShift : WithTop ℚ) + targetDefect := by
        simpa only [targetShift, targetDefect,
          representationPrimaryDefect] using htarget
  have htwoStep :
      b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
        b.order ⟨j.val, j.lt_large⟩ := by
    have h := b.orderSequence.twoStep (j.val - 2) (by omega)
    change b.order ⟨j.val - 2, by omega⟩ ≤
      b.order ⟨j.val - 2 + 2, by omega⟩ at h
    simpa only [Nat.sub_add_cancel (show 2 ≤ j.val by omega)] using h
  have hcross := a.keyLemmaLeftDirect_middlePrevious_lt_sourceNext
    b c hbcOrder j hi.1 hi.2 hessential hdirect
  have hshiftLt : targetShift < sourceShift + middleShift := by
    dsimp only [sourceShift, middleShift, targetShift]
    push_cast
    have htwoStepQ :
        (b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : ℚ) ≤
          (b.order ⟨j.val, j.lt_large⟩ : ℚ) := by
      exact_mod_cast htwoStep
    have hcrossQ :
        (b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) <
          (a.order ⟨j.val + 1, hi.2⟩ : ℚ) := by
      exact_mod_cast hcross
    linarith
  have hmiddleNeTop : middleDefect ≠ ⊤ := by
    intro htop
    rw [htop, add_top, add_top] at hstrictShifted
    exact (not_lt_of_ge le_top) hstrictShifted
  have hstrict' : (targetShift : WithTop ℚ) + middleDefect <
      (targetShift : WithTop ℚ) + targetDefect := by
    calc
      (targetShift : WithTop ℚ) + middleDefect <
          ((sourceShift + middleShift : ℚ) : WithTop ℚ) + middleDefect :=
        (WithTop.add_lt_add_iff_right hmiddleNeTop).mpr
          (WithTop.coe_lt_coe.mpr hshiftLt)
      _ = (sourceShift : WithTop ℚ) +
          ((middleShift : WithTop ℚ) + middleDefect) := by
        simp only [WithTop.coe_add, add_assoc]
      _ < (targetShift : WithTop ℚ) + targetDefect := hstrictShifted
  have hdefect : middleDefect < targetDefect :=
    (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hstrict'
  have hdefect' :
      c.truncatedPrefixDefect b (-1) (j.val - 1) (j.val + 1) <
        c.truncatedPrefixDefect a (-1) (j.val - 1) (j.val + 1) := by
    simpa only [middleDefect, targetDefect,
      c.truncatedPrefixDefect_comm b (-1) (j.val - 1) (j.val + 1),
      c.truncatedPrefixDefect_comm a (-1) (j.val - 1) (j.val + 1)] using hdefect
  have htriangle := c.truncatedPrefixDefect_neg_eq_pos_of_lt_neg b a
    (j.val - 1) (j.val + 1) (j.val + 1) hdefect'
  calc
    b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) =
        c.truncatedPrefixDefect b (-1) (j.val - 1) (j.val + 1) :=
      (c.truncatedPrefixDefect_comm b (-1) (j.val - 1) (j.val + 1)).symm
    _ = b.truncatedPrefixDefect a 1 (j.val + 1) (j.val + 1) := htriangle
    _ = a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) :=
      b.truncatedPrefixDefect_comm a 1 (j.val + 1) (j.val + 1)

end BONG.GoodBONG

end Bong
