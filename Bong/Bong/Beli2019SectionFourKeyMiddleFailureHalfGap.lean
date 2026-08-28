/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyMiddleFailureReplacement

/-!
# Beli (2019), Lemma 4.2: excluding the next half-gap

The two lower terms obtained on lines 2312--2317 are both strictly greater
than `B_(i-1)` if `A_i` is its half-gap candidate.  Lines 2318--2324 use
the essential crossing for the first term and the direct trigger for the
second term.
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

/-- Lines 2318--2324: under a strict failure of the desired middle bound,
the next source invariant `A_i` cannot attain its half-gap candidate. -/
theorem nextSourceAlpha_ne_halfGap_of_middleTarget_failure
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hfailure : ¬a.representationAlpha c j ≤
      b.representationAlpha c j) :
    a.representationAlpha b (nextRepresentationIndex j hi.2) ≠
      a.representationHalfGap b (nextRepresentationIndex j hi.2) := by
  intro hhalf
  let next := nextRepresentationIndex j hi.2
  have hlower :=
    a.min_shifted_nextSourceAlpha_le_middleTargetAlpha_of_leftDirect_failure
      (middleLaws := middleLaws) (targetLaws := targetLaws)
      b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect hfailure
  have hessentialRaw := by
    unfold IsNextEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hessential
    exact hessential.1 j.pos hi.2
  simp only [orderSequence_at, nextEssentialIndex] at hessentialRaw
  have hessentialQ :
      (c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) <
        a.order ⟨j.val + 1, hi.2⟩ := by
    exact_mod_cast hessentialRaw
  have hfirst : b.representationAlpha c j <
      (((b.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.representationAlpha b next := by
    rw [hhalf]
    apply (b.representationAlpha_le_halfGap c j).trans_lt
    unfold representationHalfGap
    norm_cast
    simp only [next, nextRepresentationIndex, Rat.divInt_eq_div]
    push_cast
    linarith
  have hmiddleCap : b.representationAlpha c j ≤
      (((b.order ⟨j.val, j.lt_large⟩ : ℚ) -
        (c.order ⟨j.val - 2, by omega⟩ : ℚ) / 2 -
        (c.order ⟨j.val - 1, by omega⟩ : ℚ) / 2 +
        (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    let targetPair : Fin n := ⟨j.val - 2, by omega⟩
    have hraw := (b.representationAlpha_le_prime c j).trans
      (b.representationAlphaPrime_le_primaryRightHalfGap c j hi.1)
    have hcast : targetPair.castSucc =
        (⟨j.val - 2, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hsucc : targetPair.succ =
        (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [targetPair, Fin.val_succ]
      omega
    calc
      b.representationAlpha c j ≤
          (((b.order ⟨j.val, j.lt_large⟩ -
            c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
            (c.halfGapValue targetPair : WithTop ℚ) := hraw
      _ = _ := by
        unfold halfGapValue orderGap
        rw [hcast, hsucc]
        norm_cast
        simp only [Rat.divInt_eq_div]
        push_cast
        ring
  have hdirectRaw := hdirect hi.1 hi.2
  simp only [nextEssentialIndex] at hdirectRaw
  have hdirectQ :
      (c.order ⟨j.val - 2, by omega⟩ : ℚ) +
          c.order ⟨j.val - 1, by omega⟩ <
        a.order ⟨j.val + 1, hi.2⟩ +
          b.order ⟨j.val, j.lt_large⟩ := by
    exact_mod_cast hdirectRaw
  have hsecond : b.representationAlpha c j <
      (((2 * b.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.representationAlpha b next := by
    rw [hhalf]
    apply hmiddleCap.trans_lt
    unfold representationHalfGap
    norm_cast
    simp only [next, nextRepresentationIndex, Rat.divInt_eq_div]
    push_cast
    linarith
  have hstrict := lt_min hfirst hsecond
  have hlower' :
      min
          ((((b.order ⟨j.val, j.lt_large⟩ -
            c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.representationAlpha b next)
          ((((2 * b.order ⟨j.val, j.lt_large⟩ -
            c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
            c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.representationAlpha b next) ≤
        b.representationAlpha c j := by
    simpa only [next] using hlower
  exact (not_lt_of_ge hlower') hstrict

/-- The conclusion immediately following line 2324: deleting the half-gap
candidate identifies `A_i` with Definition 5's auxiliary invariant `A'_i`. -/
theorem nextSourceAlpha_eq_prime_of_middleTarget_failure
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hfailure : ¬a.representationAlpha c j ≤
      b.representationAlpha c j) :
    a.representationAlpha b (nextRepresentationIndex j hi.2) =
      a.representationAlphaPrime b (nextRepresentationIndex j hi.2) := by
  let next := nextRepresentationIndex j hi.2
  have hne := a.nextSourceAlpha_ne_halfGap_of_middleTarget_failure
    (middleLaws := middleLaws) (targetLaws := targetLaws)
    b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect hfailure
  have hnormal := a.representationAlpha_eq_min_halfGap_prime b next
  rcases min_choice (a.representationHalfGap b next)
      (a.representationAlphaPrime b next) with hhalf | hprime
  · exact False.elim (hne (by simpa only [next] using hnormal.trans hhalf))
  · simpa only [next] using hnormal.trans hprime

end BONG.GoodBONG

end Bong
