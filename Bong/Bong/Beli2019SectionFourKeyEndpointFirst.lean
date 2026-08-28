/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyMiddleComplete

/-!
# Beli (2019), Lemma 4.2: the first left endpoint

At `i = 2` the secondary candidate of `B_(i-1)` is absent.  This file
formalizes the resulting one-term version of lines 2299--2348.  The proof
keeps the paper's endpoint convention explicit instead of manufacturing a
candidate with a negative prefix index.
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

set_option maxHeartbeats 800000 in
-- The endpoint proof normalizes several nested WithTop minima and dependent indices.
/-- Lemma 4.2(i), second direct inequality at `i = 2`, when the following
ordinary boundary exists. -/
theorem leftDirect_middleBound_of_eq_one_of_not_last
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hj : j.val = 1) (hnext : j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j) :
    a.representationAlpha c j ≤ b.representationAlpha c j := by
  let next := nextRepresentationIndex j hnext
  let sourceDefect := a.truncatedPrefixDefect b (-1) (j.val + 2) j.val
  let base : ℚ := ((b.order ⟨j.val, j.lt_large⟩ -
    a.order ⟨j.val + 1, hnext⟩ : Int) : ℚ)
  let firstShift : ℚ := ((b.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let sourceShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let firstDefectShift : ℚ := ((a.order ⟨j.val + 1, hnext⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  have hsourceBound :=
    a.representationAlpha_le_leftDirect_sourceAlpha_of_eq_one
      b c hbcOrder j hj
  by_contra hfailure
  have hsourceCurrent :=
    a.keyLemmaLeftDirect_sourceCurrent_le_middleCurrent_of_eq_one
      b c hab hbcOrder j hj hnext hessential
  have hmiddleHalf :=
    a.representationAlpha_le_leftDirect_middleHalfGap_of_eq_one
      b c hab hbcOrder j hj hessential
  have hnormal : b.representationAlpha c j =
      min (b.representationHalfGap c j)
        (b.representationPrimaryDefect c j) := by
    rw [b.representationAlpha_eq_min_halfGap_prime c j,
      b.representationAlphaPrime_eq_primary_of_not_interior c j (by omega)]
  have hmiddlePrimary : b.representationAlpha c j =
      b.representationPrimaryDefect c j := by
    rcases min_choice (b.representationHalfGap c j)
        (b.representationPrimaryDefect c j) with hhalf | hprimary
    · have heq := hnormal.trans hhalf
      exact False.elim (hfailure (hmiddleHalf.trans_eq heq.symm))
    · exact hnormal.trans hprimary
  let middleDefect := b.truncatedPrefixDefect c (-1)
    (j.val + 1) (j.val - 1)
  let targetDefect := a.truncatedPrefixDefect c (-1)
    (j.val + 1) (j.val - 1)
  have htarget : a.representationAlpha c j ≤
      (sourceShift : WithTop ℚ) + targetDefect := by
    simpa only [sourceShift, targetDefect, representationPrimaryDefect]
      using a.representationAlpha_le_primary c j
  have hshift : sourceShift ≤ firstShift := by
    dsimp only [sourceShift, firstShift]
    exact_mod_cast sub_le_sub_right hsourceCurrent
      (c.order ⟨j.val - 1, by have := j.lt_large; omega⟩)
  have hstrictShifted : (firstShift : WithTop ℚ) + middleDefect <
      (firstShift : WithTop ℚ) + targetDefect := by
    calc
      (firstShift : WithTop ℚ) + middleDefect =
          b.representationAlpha c j := by
        rw [hmiddlePrimary]
        rfl
      _ < a.representationAlpha c j := lt_of_not_ge hfailure
      _ ≤ (sourceShift : WithTop ℚ) + targetDefect := htarget
      _ ≤ (firstShift : WithTop ℚ) + targetDefect :=
        add_le_add (by exact_mod_cast hshift) le_rfl
  have hdefectStrict : middleDefect < targetDefect :=
    (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hstrictShifted
  have hdefectStrict' :
      c.truncatedPrefixDefect b (-1) (j.val - 1) (j.val + 1) <
        c.truncatedPrefixDefect a (-1) (j.val - 1) (j.val + 1) := by
    simpa only [middleDefect, targetDefect,
      c.truncatedPrefixDefect_comm b (-1) (j.val - 1) (j.val + 1),
      c.truncatedPrefixDefect_comm a (-1) (j.val - 1) (j.val + 1)]
      using hdefectStrict
  have htriangle := c.truncatedPrefixDefect_neg_eq_pos_of_lt_neg
    b a (j.val - 1) (j.val + 1) (j.val + 1) hdefectStrict'
  have hreplace : middleDefect =
      a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) := by
    calc
      middleDefect =
          c.truncatedPrefixDefect b (-1) (j.val - 1) (j.val + 1) := by
        exact (c.truncatedPrefixDefect_comm b (-1)
          (j.val - 1) (j.val + 1)).symm
      _ = b.truncatedPrefixDefect a 1 (j.val + 1) (j.val + 1) := htriangle
      _ = a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) :=
        b.truncatedPrefixDefect_comm a 1 (j.val + 1) (j.val + 1)
  have hnextDefect : a.representationAlpha b next ≤
      a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) := by
    have hcondition := habDefect next
    rw [a.coe_representationAlphaValue b next] at hcondition
    simpa only [next, nextRepresentationIndex] using hcondition
  have hlower : (firstShift : WithTop ℚ) +
      a.representationAlpha b next ≤ b.representationAlpha c j := by
    rw [hmiddlePrimary]
    unfold representationPrimaryDefect
    change (firstShift : WithTop ℚ) + a.representationAlpha b next ≤
      (firstShift : WithTop ℚ) + middleDefect
    rw [hreplace]
    exact add_le_add le_rfl hnextDefect
  have hessentialRaw := by
    unfold IsNextEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hessential
    exact hessential.1 j.pos hnext
  simp only [orderSequence_at, nextEssentialIndex] at hessentialRaw
  have hbaseFirst : base < firstShift := by
    dsimp only [base, firstShift]
    push_cast
    have hessentialQ :
        (c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) <
          a.order ⟨j.val + 1, hnext⟩ := by
      exact_mod_cast hessentialRaw
    linarith
  have hnextFinite : a.representationAlpha b next ≠ ⊤ :=
    a.representationAlpha_ne_top b next
  have hsmall : (base : WithTop ℚ) + a.representationAlpha b next <
      b.representationAlpha c j :=
    (WithTop.add_lt_add_right hnextFinite
      (by exact_mod_cast hbaseFirst)).trans_le hlower
  have hnextNotHalf : a.representationAlpha b next ≠
      a.representationHalfGap b next := by
    intro hhalf
    have hmiddleUpper := b.representationAlpha_le_halfGap c j
    have hreverse : b.representationAlpha c j <
        (firstShift : WithTop ℚ) + a.representationAlpha b next := by
      rw [hhalf]
      apply hmiddleUpper.trans_lt
      unfold representationHalfGap
      dsimp only [firstShift]
      norm_cast
      simp only [next, nextRepresentationIndex, Rat.divInt_eq_div]
      push_cast
      have hessentialQ :
          (c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) <
            a.order ⟨j.val + 1, hnext⟩ := by
        exact_mod_cast hessentialRaw
      linarith
    exact (not_lt_of_ge hlower) hreverse
  have hnextPrime : a.representationAlpha b next =
      a.representationAlphaPrime b next := by
    have hform := a.representationAlpha_eq_min_halfGap_prime b next
    rcases min_choice (a.representationHalfGap b next)
        (a.representationAlphaPrime b next) with hhalf | hprime
    · exact False.elim (hnextNotHalf (hform.trans hhalf))
    · exact hform.trans hprime
  have hsmallPrime : (base : WithTop ℚ) +
      a.representationAlphaPrime b next < b.representationAlpha c j := by
    simpa only [hnextPrime] using hsmall
  have hcrossNext : b.order ⟨next.val - 2, by
      have := next.le_small
      omega⟩ ≤ a.order ⟨next.val, next.lt_large⟩ := by
    have hlt := a.keyLemmaLeftDirect_middleFirst_lt_sourceNext_of_eq_one
      b c hbcOrder j hj hnext hessential
    dsimp only [next, nextRepresentationIndex]
    simpa only [hj, Nat.reduceSubDiff] using hlt.le
  let opposite : ℚ := ((a.order ⟨j.val + 1, hnext⟩ -
    b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ)
  have hprimaryFormula : a.representationPrimaryDefect b next =
      (opposite : WithTop ℚ) + sourceDefect := by
    unfold representationPrimaryDefect
    simp only [next, nextRepresentationIndex, Nat.add_sub_cancel,
      opposite, sourceDefect]
  have hcancel : base + opposite = 0 := by
    dsimp only [base, opposite]
    push_cast
    ring
  have hprimaryShift : (base : WithTop ℚ) +
      a.representationPrimaryDefect b next = sourceDefect := by
    rw [hprimaryFormula, ← add_assoc, ← WithTop.coe_add, hcancel]
    simp
  have hshiftPrime : (base : WithTop ℚ) +
      a.representationAlphaPrime b next = sourceDefect := by
    by_cases hinterior : 1 < next.val ∧ next.val + 1 < n + 1
    · let secondTerm : WithTop ℚ := (base : WithTop ℚ) +
        a.representationSecondaryPreviousDefect b next hinterior
      have htwoStepRaw := a.orderSequence.twoStep j.val (by
        dsimp only [next, nextRepresentationIndex] at hinterior
        omega)
      have htwoStep : a.order ⟨j.val, j.lt_large⟩ ≤
          a.order ⟨j.val + 2, by
            dsimp only [next, nextRepresentationIndex] at hinterior
            omega⟩ := by
        change a.orderSequence.entry j.val j.lt_large ≤
          a.orderSequence.entry (j.val + 2) (by
            dsimp only [next, nextRepresentationIndex] at hinterior
            omega)
        exact htwoStepRaw
      let primaryShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
        b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
      let primaryDefect := a.truncatedPrefixDefect b (-1)
        (j.val + 1) (j.val - 1)
      let secondaryShift : ℚ := ((a.order
        ⟨next.val, next.lt_large⟩ +
        a.order ⟨next.val + 1, hinterior.2⟩ -
        b.order ⟨next.val - 2, by have := next.le_small; omega⟩ -
        b.order ⟨next.val - 1, by have := next.le_small; omega⟩ : Int) : ℚ)
      let secondaryDefect := a.truncatedPrefixDefect b (-1)
        next.val (next.val - 2)
      have hnextCurrent : (⟨next.val, next.lt_large⟩ : Fin (n + 1)) =
          ⟨j.val + 1, hnext⟩ := by
        apply Fin.ext
        simp only [next, nextRepresentationIndex]
      have hnextNext : (⟨next.val + 1, hinterior.2⟩ : Fin (n + 1)) =
          ⟨j.val + 2, by
            dsimp only [next, nextRepresentationIndex] at hinterior
            omega⟩ := by
        apply Fin.ext
        simp only [next, nextRepresentationIndex]
      have hmiddlePrevious :
          (⟨next.val - 2, by have := next.le_small; omega⟩ : Fin (n + 1)) =
            ⟨j.val - 1, by have := j.lt_large; omega⟩ := by
        apply Fin.ext
        simp only [next, nextRepresentationIndex]
        omega
      have hmiddleCurrent :
          (⟨next.val - 1, by have := next.le_small; omega⟩ : Fin (n + 1)) =
            ⟨j.val, j.lt_large⟩ := by
        apply Fin.ext
        simp only [next, nextRepresentationIndex, Nat.add_sub_cancel]
      have hdefect : secondaryDefect = primaryDefect := by
        dsimp only [secondaryDefect, primaryDefect]
        have hfirst : next.val = j.val + 1 := by
          simp only [next, nextRepresentationIndex]
        rw [hfirst]
        congr 1
      have hshift : primaryShift ≤ base + secondaryShift := by
        dsimp only [primaryShift, base, secondaryShift]
        rw [hnextCurrent, hnextNext, hmiddlePrevious, hmiddleCurrent]
        push_cast
        have htwoStepQ :
            (a.order ⟨j.val, j.lt_large⟩ : ℚ) ≤
              a.order ⟨j.val + 2, by
                dsimp only [next, nextRepresentationIndex] at hinterior
                omega⟩ := by
          exact_mod_cast htwoStep
        linarith
      have hprimarySecond : a.representationPrimaryDefect b j ≤
          secondTerm := by
        change (primaryShift : WithTop ℚ) + primaryDefect ≤
          (base : WithTop ℚ) +
            ((secondaryShift : WithTop ℚ) + secondaryDefect)
        rw [hdefect, ← add_assoc]
        have hshiftTop : (primaryShift : WithTop ℚ) ≤
            ((base + secondaryShift : ℚ) : WithTop ℚ) := by
          exact_mod_cast hshift
        exact add_le_add hshiftTop le_rfl
      have hsecondLarge : b.representationAlpha c j < secondTerm :=
        (lt_of_not_ge hfailure).trans_le
          (hsourceBound.trans
            ((a.representationAlpha_le_primary b j).trans hprimarySecond))
      letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
      have hnormalPrime := a.representationAlphaPrime_eq_min_primary_previous
        b next hinterior hcrossNext
      have hnormalPrime' : (base : WithTop ℚ) +
          a.representationAlphaPrime b next = min sourceDefect secondTerm := by
        rw [hnormalPrime, add_min, hprimaryShift]
      rcases min_choice sourceDefect secondTerm with hsource | hsecond
      · exact hnormalPrime'.trans hsource
      · have heq : (base : WithTop ℚ) +
            a.representationAlphaPrime b next = secondTerm :=
          hnormalPrime'.trans hsecond
        exact False.elim ((not_lt_of_ge hsecondLarge.le)
          (heq ▸ hsmallPrime))
    · have hnormalPrime := a.representationAlphaPrime_eq_primary_of_not_interior
        b next hinterior
      rw [hnormalPrime, hprimaryShift]
  have hdefectMiddle : sourceDefect < b.representationAlpha c j := by
    simpa only [hnextPrime, hshiftPrime] using hsmall
  have habPositive : a.representationAlpha b j ≤
      a.truncatedPrefixDefect b 1 j.val j.val := by
    simpa only [← a.coe_representationAlphaValue b j] using habDefect j
  have hsourceStrict : sourceDefect <
      a.truncatedPrefixDefect b 1 j.val j.val :=
    hdefectMiddle.trans
      ((lt_of_not_ge hfailure).trans_le (hsourceBound.trans habPositive))
  have hsourceStrict' :
      b.truncatedPrefixDefect a (-1) j.val (j.val + 2) <
        b.truncatedPrefixDefect a 1 j.val j.val := by
    simpa only [sourceDefect,
      a.truncatedPrefixDefect_comm b (-1) (j.val + 2) j.val,
      a.truncatedPrefixDefect_comm b 1 j.val j.val] using hsourceStrict
  have hselfTriangle := b.truncatedPrefixDefect_neg_eq_neg_of_lt_pos
    a a j.val (j.val + 2) j.val hsourceStrict'
  have hself : sourceDefect =
      a.truncatedPrefixDefect a (-1) (j.val + 2) j.val := by
    calc
      sourceDefect = b.truncatedPrefixDefect a (-1) j.val (j.val + 2) :=
        a.truncatedPrefixDefect_comm b (-1) (j.val + 2) j.val
      _ = a.truncatedPrefixDefect a (-1) (j.val + 2) j.val := hselfTriangle
  have hbcPositive : b.representationAlpha c j ≤
      b.truncatedPrefixDefect c 1 j.val j.val := by
    simpa only [← b.coe_representationAlphaValue c j] using hbcDefect j
  have htargetStrict : sourceDefect <
      b.truncatedPrefixDefect c 1 j.val j.val :=
    hdefectMiddle.trans_le hbcPositive
  have htargetStrict' :
      b.truncatedPrefixDefect a (-1) j.val (j.val + 2) <
        b.truncatedPrefixDefect c 1 j.val j.val := by
    rw [← a.truncatedPrefixDefect_comm b (-1) (j.val + 2) j.val]
    exact htargetStrict
  have htargetTriangle := b.truncatedPrefixDefect_neg_eq_neg_of_lt_pos
    a c j.val (j.val + 2) j.val htargetStrict'
  have htargetDefect : sourceDefect =
      a.truncatedPrefixDefect c (-1) (j.val + 2) j.val := by
    calc
      sourceDefect = b.truncatedPrefixDefect a (-1) j.val (j.val + 2) :=
        a.truncatedPrefixDefect_comm b (-1) (j.val + 2) j.val
      _ = a.truncatedPrefixDefect c (-1) (j.val + 2) j.val := htargetTriangle
  have hfirstIdentity : (firstShift : WithTop ℚ) +
      a.representationAlpha b next =
        (firstDefectShift : WithTop ℚ) + sourceDefect := by
    rw [hnextPrime, ← hshiftPrime, ← add_assoc, ← WithTop.coe_add]
    congr 1
    norm_cast
    dsimp only [firstShift, firstDefectShift, base]
    push_cast
    simp only [Nat.add_comm j.val 1]
    ring_nf
  let p : Fin n := ⟨j.val, by omega⟩
  let adjacentShift : ℚ := ((a.order ⟨j.val + 1, hnext⟩ -
    a.order ⟨j.val, j.lt_large⟩ : Int) : ℚ)
  have hprimaryCap : a.representationAlpha c j ≤
      (sourceShift : WithTop ℚ) + (a.alphaValue p : WithTop ℚ) := by
    have hraw := (a.representationAlpha_le_prime c j).trans
      (a.representationAlphaPrime_le_primaryLeftCap c j)
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hraw
    simpa only [sourceShift, p, Nat.add_sub_cancel] using hraw
  have hadjacent : (a.alphaValue p : WithTop ℚ) ≤
      (adjacentShift : WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) (j.val + 2) j.val := by
    letI : Beli2006AlphaLaws K := sourceLaws
    have hraw := a.alpha_le_orderGap_add_cappedAdjacent p
    rw [a.truncatedPrefixDefect_comm a (-1) p.val (p.val + 2)] at hraw
    have hpCast : p.castSucc =
        (⟨j.val, j.lt_large⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hpSucc : p.succ =
        (⟨j.val + 1, hnext⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [p, Fin.val_succ]
    rw [hpCast, hpSucc] at hraw
    simpa only [p, adjacentShift] using hraw
  have hfinalLower : a.representationAlpha c j ≤
      (firstShift : WithTop ℚ) + a.representationAlpha b next := by
    calc
      a.representationAlpha c j ≤
          (sourceShift : WithTop ℚ) + (a.alphaValue p : WithTop ℚ) :=
        hprimaryCap
      _ ≤ (sourceShift : WithTop ℚ) +
          ((adjacentShift : WithTop ℚ) +
            a.truncatedPrefixDefect a (-1) (j.val + 2) j.val) :=
        add_le_add le_rfl hadjacent
      _ = (firstDefectShift : WithTop ℚ) + sourceDefect := by
        rw [← add_assoc, ← hself]
        congr 1
        norm_cast
        dsimp only [sourceShift, adjacentShift, firstDefectShift]
        push_cast
        ring
      _ = (firstShift : WithTop ℚ) + a.representationAlpha b next :=
        hfirstIdentity.symm
  exact hfailure (hfinalLower.trans hlower)

end BONG.GoodBONG

end Bong
