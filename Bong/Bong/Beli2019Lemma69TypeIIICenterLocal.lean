/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIII
import Bong.Bong.Beli2019Lemma63
import Bong.Bong.Beli2019Lemma66
import Bong.Bong.Beli2019Lemma69TypeIRightEndpoint
import Bong.Bong.Beli2019Lemma79OrderRightAlternating

/-!
# Beli (2019), Lemma 6.9(i): the local type-III centre

The original Section 6 statement is not restricted to a first difference at
the first BONG entry.  The common prefix is handled by Lemma 6.3 at the first
unequal coordinate, after which the capped-defect argument propagates along
the alternating left profile.  This restores the general form needed after
reverse duality when the original pair has a proper common suffix.
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
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

set_option maxHeartbeats 12000000 in
/-- The type-III central source alpha is at most one without normalizing the
first unequal order to zero. -/
theorem beli2019Lemma69_i_typeIII_local
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeIII a b)
    (hdefect : a.RepresentationDefectCondition b) :
    a.alphaValue
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≤ 1 := by
  by_cases hfirstZero : D.outer.first = 0
  · exact a.beli2019Lemma69_i_typeIII
      (alphaV := alphaV) (alphaW := alphaW) b D hfirstZero hdefect
  let first := D.outer.first
  let left := D.outer.transition.lastZero
  let right := D.outer.transition.firstTwo - 1
  have hfirstPos : 0 < first := by
    simp only [first]
    omega
  have htransitionBound := D.outer.transition.firstTwo_le_rank
  have hleftBound : left < n + 1 := by
    simp only [left]
    rw [D.adjacent] at htransitionBound
    omega
  have hrightEq : right = left + 1 := by
    simp only [right, left]
    rw [D.adjacent]
    omega
  have hrightBound : right < n + 2 := by omega
  let p : Fin (n + 1) := ⟨left, hleftBound⟩
  change a.alphaValue p ≤ 1
  let idx : RepresentationIndex (n + 2) (n + 2) := {
    val := left + 1
    pos := by omega
    lt_large := by omega
    le_small := by omega }
  have hidxVal : idx.val = left + 1 := rfl
  have hidxPred : idx.val - 1 = left := by
    rw [hidxVal]
    omega
  have hidxRight : idx.val = right := by
    rw [hidxVal, hrightEq]
  have hfirstLeLeft : first ≤ left := by
    simpa only [first, left] using D.outer.first_le_left
  have hleftParity : Even (left - first) := by
    by_cases heq : first = left
    · rw [heq]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < D.outer.transition.lastZero := by
        simpa only [first, left] using lt_of_le_of_ne hfirstLeLeft heq
      simpa only [first, left] using (D.outer.leftProfile hlt).1
  have hsourceAt (k : Nat) (hkFirst : first ≤ k) (hkLeft : k ≤ left)
      (hkParity : Even (k - first)) :
      a.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero left := by
    by_cases hfirstLeft : first = left
    · have hk : k = left := by omega
      rw [hk]
    · have hprofile := D.outer.leftProfile (by
        change D.outer.first < D.outer.transition.lastZero
        simpa only [first, left] using
          lt_of_le_of_ne hfirstLeLeft hfirstLeft)
      have hkEq := hprofile.2.2 k (by simpa only [first] using hkFirst)
        (by simpa only [left] using hkLeft)
        (by simpa only [first] using hkParity)
      have hleftEq := hprofile.2.2 left D.outer.first_le_left le_rfl
        hprofile.1
      exact hkEq.trans hleftEq.symm
  have hsourceFirst : a.orderSequence.entryOrZero first =
      a.orderSequence.entryOrZero left :=
    hsourceAt first le_rfl hfirstLeLeft ⟨0, by omega⟩
  have hleftGap : b.orderSequence.entryOrZero left =
      a.orderSequence.entryOrZero left + 1 := by
    simpa only [left] using D.outer.transition.leftBoundary
  have hfirstGap : b.orderSequence.entryOrZero first =
      a.orderSequence.entryOrZero first + 1 := by
    by_cases heq : first = left
    · rw [heq]
      exact hleftGap
    · have hprofile := D.outer.leftProfile (by
        change D.outer.first < D.outer.transition.lastZero
        simpa only [first, left] using
          lt_of_le_of_ne hfirstLeLeft heq)
      have hstrict : a.orderSequence.entryOrZero first <
          b.orderSequence.entryOrZero first := by
        simpa only [first] using hprofile.2.1
      have hupper := D.no_gap_two first (by
        simp only [first]
        exact D.outer.firstDifference.bound)
      omega
  have htargetFirst : b.orderSequence.entryOrZero first =
      b.orderSequence.entryOrZero left := by omega
  have htargetAt (k : Nat) (hkFirst : first ≤ k) (hkLeft : k ≤ left)
      (hkParity : Even (k - first)) :
      b.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero left := by
    have hfirstK := b.orderSequence.entryOrZero_le_of_evenGap
      first k hkFirst (by omega) hkParity
    have hkLeftParity : Even (left - k) := by
      rcases hleftParity with ⟨d, hd⟩
      rcases hkParity with ⟨e, he⟩
      exact ⟨d - e, by omega⟩
    have hkLeftOrder := b.orderSequence.entryOrZero_le_of_evenGap
      k left hkLeft (by omega) hkLeftParity
    exact le_antisymm hkLeftOrder (htargetFirst.symm.trans_le hfirstK)
  have hprevious_le_next :
      b.orderSequence.entryOrZero (left - 1) ≤
        a.orderSequence.entryOrZero (left + 1) := by
    have hsourceMono := a.orderSequence.entryOrZero_le_of_evenGap
      (left - 1) (left + 1) (by omega) (by
        rw [← hrightEq]
        exact hrightBound) ⟨1, by omega⟩
    by_cases hfirstLeft : first = left
    · have hcommonPrevious := D.outer.firstDifference.before
        (left - 1) (by rw [← hfirstLeft]; omega)
      exact hcommonPrevious.symm.le.trans hsourceMono
    · have hfirstStrict : first < left :=
        lt_of_le_of_ne hfirstLeLeft hfirstLeft
      have hleftTwo : first + 2 ≤ left := by
        rcases hleftParity with ⟨d, hd⟩
        omega
      have hpair := D.outer.leftPairEq (left - 2) (by omega)
        ⟨1, by omega⟩
      have hsourcePrevious := hsourceAt (left - 2) (by omega)
        (by omega) (by
          rcases hleftParity with ⟨d, hd⟩
          exact ⟨d - 1, by omega⟩)
      have htargetPrevious := htargetAt (left - 2) (by omega)
        (by omega) (by
          rcases hleftParity with ⟨d, hd⟩
          exact ⟨d - 1, by omega⟩)
      have hone : left - 2 + 1 = left - 1 := by omega
      rw [hone] at hpair
      have htargetOdd : b.orderSequence.entryOrZero (left - 1) =
          a.orderSequence.entryOrZero (left - 1) - 1 := by omega
      omega
  have htailLe (hnextBound : left + 2 < n + 2) :
      b.orderSequence.entryOrZero left ≤
        a.orderSequence.entryOrZero (left + 2) := by
    have htargetMono := b.orderSequence.entryOrZero_le_of_evenGap
      left (left + 2) (by omega) hnextBound ⟨1, by omega⟩
    by_cases hthrough : left + 2 ≤ D.outer.last
    · have hsourceTarget := D.outer.source_rightOdd_eq_target_add_one
        D.no_gap_two (left + 2) (by
          simp only [left]
          rw [D.adjacent]
          omega) hthrough
          ⟨0, by simp only [left]; rw [D.adjacent]; omega⟩
      omega
    · have hcommonNext := D.outer.lastDifference.after
        (left + 2) (by omega) hnextBound
      omega
  by_cases hspecial : ∃ hnextBound : left + 2 < n + 2,
      a.orderSequence.entryOrZero (left + 2) =
        b.orderSequence.entryOrZero left
  · rcases hspecial with ⟨hnextBound, htailEq⟩
    refine ?_
    · have hlastBefore : D.outer.last < left + 2 := by
        by_contra hnot
        have hthrough : left + 2 ≤ D.outer.last := by omega
        have hsourceTarget := D.outer.source_rightOdd_eq_target_add_one
          D.no_gap_two (left + 2) (by
            simp only [left]
            rw [D.adjacent]
            omega) hthrough
            ⟨0, by simp only [left]; rw [D.adjacent]; omega⟩
        have htargetMono := b.orderSequence.entryOrZero_le_of_evenGap
          left (left + 2) (by omega) hnextBound ⟨1, by omega⟩
        omega
      have hcommonNext := D.outer.lastDifference.after
        (left + 2) hlastBefore hnextBound
      have htargetEndpoints : b.orderSequence.entryOrZero left =
          b.orderSequence.entryOrZero (left + 2) := by omega
      have hmod := b.entryOrZero_modEq_of_equal_even_endpoints
        (i := left) (j := left + 2) (k := left + 1)
        (by omega) hnextBound (by omega) (by omega) (by omega)
        ⟨1, by omega⟩ htargetEndpoints
      have hrightBoundary : b.orderSequence.entryOrZero (left + 1) =
          a.orderSequence.entryOrZero (left + 1) + 1 := by
        simpa only [left, right, hrightEq] using
          D.outer.transition.rightBoundary
      have houterMod : Int.ModEq 2
          (a.orderSequence.entryOrZero (left + 2))
          (a.orderSequence.entryOrZero (left + 1) + 1) := by
        rw [htailEq, ← hrightBoundary]
        exact hmod.symm
      have hoddOrders : Odd
          (a.orderSequence.entryOrZero (left + 1) +
            a.orderSequence.entryOrZero (left + 2)) := by
        have hodd := odd_add_of_modEq_add_one houterMod
        simpa only [add_comm] using hodd
      let adjacent : Fin (n + 1) := ⟨left + 1, by omega⟩
      have hoddOrdersFin : Odd
          (a.order adjacent.castSucc + a.order adjacent.succ) := by
        rw [← a.orderSequence_entryOrZero_eq_order adjacent.castSucc,
          ← a.orderSequence_entryOrZero_eq_order adjacent.succ]
        simpa only [adjacent, Fin.val_castSucc, Fin.val_succ] using hoddOrders
      have hzero : a.adjacentDefect adjacent = 0 :=
        a.adjacentDefect_eq_zero_of_order_sum_odd adjacent hoddOrdersFin
      have hcandidate := a.alpha_le_rightDefectCandidate
        (i := p) (j := adjacent) (by
          change left ≤ left + 1
          omega)
      have horderDifference :
          a.order adjacent.succ - a.order p.castSucc = 1 := by
        rw [← a.orderSequence_entryOrZero_eq_order adjacent.succ,
          ← a.orderSequence_entryOrZero_eq_order p.castSucc]
        change a.orderSequence.entryOrZero (left + 2) -
          a.orderSequence.entryOrZero left = 1
        omega
      have hupperTop : (a.alphaValue p : WithTop ℚ) ≤ 1 := by
        rw [a.coe_alphaValue p]
        calc
          a.alpha p ≤ a.rightDefectCandidate p adjacent := hcandidate
          _ = ((1 : ℚ) : WithTop ℚ) := by
            unfold rightDefectCandidate
            rw [hzero, horderDifference]
            norm_num
          _ = (1 : WithTop ℚ) := rfl
      exact_mod_cast hupperTop
  · refine ?_
    · have hsecondaryPos
          (hi : 1 < idx.val ∧ idx.val + 1 < n + 2) :
          (0 : WithTop ℚ) < a.representationSecondaryDefect b idx hi := by
        have hnextBound : left + 2 < n + 2 := by
          simpa only [idx] using hi.2
        have htailNe : a.orderSequence.entryOrZero (left + 2) ≠
            b.orderSequence.entryOrZero left := by
          intro htailEq
          exact hspecial ⟨hnextBound, htailEq⟩
        have htailStrict : b.orderSequence.entryOrZero left <
            a.orderSequence.entryOrZero (left + 2) :=
          lt_of_le_of_ne (htailLe hnextBound) (Ne.symm htailNe)
        have hcoefficient : 0 <
            a.orderSequence.entryOrZero (left + 1) +
              a.orderSequence.entryOrZero (left + 2) -
              b.orderSequence.entryOrZero (left - 1) -
              b.orderSequence.entryOrZero left := by omega
        have hcoefficientOrder : 0 <
            a.order ⟨idx.val, idx.lt_large⟩ +
              a.order ⟨idx.val + 1, hi.2⟩ -
              b.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ -
              b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ := by
          have haCurrent : a.order ⟨idx.val, idx.lt_large⟩ =
              a.orderSequence.entryOrZero idx.val :=
            (BeliOrderSequence.entryOrZero_of_lt a.orderSequence
              idx.lt_large).symm
          have haNext : a.order ⟨idx.val + 1, hi.2⟩ =
              a.orderSequence.entryOrZero (idx.val + 1) :=
            (BeliOrderSequence.entryOrZero_of_lt a.orderSequence hi.2).symm
          have hbPrevious :
              b.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ =
                b.orderSequence.entryOrZero (idx.val - 2) :=
            (BeliOrderSequence.entryOrZero_of_lt b.orderSequence
              (show idx.val - 2 < n + 2 by omega)).symm
          have hbCurrent :
              b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
                b.orderSequence.entryOrZero (idx.val - 1) :=
            (BeliOrderSequence.entryOrZero_of_lt b.orderSequence
              (show idx.val - 1 < n + 2 by omega)).symm
          rw [haCurrent, haNext, hbPrevious, hbCurrent]
          have hidxNext : idx.val + 1 = left + 2 := by
            rw [hidxVal]
          have hidxPrevious : idx.val - 2 = left - 1 := by
            rw [hidxVal]
            omega
          rw [hidxNext, hidxPrevious, hidxPred, hidxVal]
          exact hcoefficient
        have hdefectNonneg := a.truncatedPrefixDefect_nonneg
          (alphaV := alphaV) (alphaW := alphaW) b 1
          (idx.val + 2) (idx.val - 2)
        unfold representationSecondaryDefect
        exact lt_of_lt_of_le (by exact_mod_cast hcoefficientOrder)
          (le_add_of_nonneg_right hdefectNonneg)
      by_contra hnot
      have halphaGt : 1 < a.alphaValue p := by
        simpa only [p] using lt_of_not_ge hnot
      let cutoff : ℚ :=
        ((a.orderSequence.entryOrZero left -
          a.orderSequence.entryOrZero right + 1 : Int) : ℚ)
      have hsourceLocal (j : Nat) (hjFirst : first ≤ j)
          (hj : j + 2 ≤ left) (heven : Even (j - first)) :
          (cutoff : WithTop ℚ) <
            a.truncatedPrefixDefect a (-1) j (j + 2) := by
        let jf : Fin (n + 1) := ⟨j, by omega⟩
        have hjp : jf ≤ p := by
          change j ≤ left
          omega
        letI : Beli2006AlphaLaws.{u, v} K := alphaV
        have hbound := a.alpha_le_order_sub_add_cappedAdjacent hjp
        by_contra hnotCut
        have hlocalLe : a.truncatedPrefixDefect a (-1) j (j + 2) ≤
            (cutoff : WithTop ℚ) := le_of_not_gt hnotCut
        have hsourceJ := hsourceAt j hjFirst (by omega) heven
        have hpSucc : a.order p.succ =
            a.orderSequence.entryOrZero right := by
          rw [a.orderSequence_entryOrZero_eq_order ⟨right, hrightBound⟩]
          apply congrArg a.order
          apply Fin.ext
          simp only [p, Fin.val_succ]
          exact hrightEq.symm
        have hjCast : a.order jf.castSucc =
            a.orderSequence.entryOrZero j := by
          rw [a.orderSequence_entryOrZero_eq_order ⟨j, by omega⟩]
          rfl
        have hformula :
            ((a.order p.succ - a.order jf.castSucc : Int) : ℚ) +
                cutoff = 1 := by
          rw [hpSucc, hjCast, hsourceJ]
          simp only [cutoff]
          push_cast
          ring
        have halphaTop : (a.alphaValue p : WithTop ℚ) ≤ 1 := by
          calc
            (a.alphaValue p : WithTop ℚ) ≤
                ((((a.order p.succ - a.order jf.castSucc : Int) : ℚ) :
                    WithTop ℚ) +
                  a.truncatedPrefixDefect a (-1) j (j + 2)) := by
              simpa only [jf] using hbound
            _ ≤ ((((a.order p.succ - a.order jf.castSucc : Int) : ℚ) :
                  WithTop ℚ) + cutoff) := add_le_add_right hlocalLe _
            _ = 1 := by exact_mod_cast hformula
        have halphaLe : a.alphaValue p ≤ 1 := by exact_mod_cast halphaTop
        exact (not_lt_of_ge halphaLe) halphaGt
      have htargetLocal (j : Nat) (hjFirst : first ≤ j)
          (hj : j + 2 ≤ left) (heven : Even (j - first)) :
          (cutoff : WithTop ℚ) <
            b.truncatedPrefixDefect b (-1) j (j + 2) := by
        let jf : Fin (n + 1) := ⟨j, by omega⟩
        have hpairParity : Even (left - j) := by
          rcases hleftParity with ⟨d, hd⟩
          rcases heven with ⟨e, he⟩
          exact ⟨d - e, by omega⟩
        have hpair := D.outer.leftPairEq j hj hpairParity
        have hsourceJ := hsourceAt j hjFirst (by omega) heven
        have htargetJ := htargetAt j hjFirst (by omega) heven
        have htargetNext : b.orderSequence.entryOrZero (j + 1) =
            a.orderSequence.entryOrZero (j + 1) - 1 := by omega
        have hsourceNextLe := a.orderSequence.entryOrZero_le_of_evenGap
          (j + 1) right (by omega) hrightBound (by
            rcases hleftParity with ⟨d, hd⟩
            rcases heven with ⟨e, he⟩
            refine ⟨d - e, ?_⟩
            rw [hrightEq]
            omega)
        have hjSucc : b.order jf.succ =
            b.orderSequence.entryOrZero (j + 1) := by
          rw [b.orderSequence_entryOrZero_eq_order ⟨j + 1, by omega⟩]
          rfl
        have hjCast : b.order jf.castSucc =
            b.orderSequence.entryOrZero j := by
          rw [b.orderSequence_entryOrZero_eq_order ⟨j, by omega⟩]
          rfl
        have hgapCut :
            ((b.order jf.succ - b.order jf.castSucc : Int) : ℚ) +
                cutoff ≤ -1 := by
          rw [hjSucc, hjCast, htargetNext, htargetJ]
          simp only [cutoff]
          push_cast
          exact_mod_cast (show
            a.orderSequence.entryOrZero (j + 1) - 1 -
                b.orderSequence.entryOrZero left +
                (a.orderSequence.entryOrZero left -
                  a.orderSequence.entryOrZero right + 1) ≤ -1 by
            omega)
        letI : Beli2006AlphaLaws.{u, w} K := alphaW
        have hbound := b.alpha_le_orderGap_add_cappedAdjacent jf
        by_contra hnotCut
        have hlocalLe : b.truncatedPrefixDefect b (-1) j (j + 2) ≤
            (cutoff : WithTop ℚ) := le_of_not_gt hnotCut
        have hnonnegative : (0 : WithTop ℚ) ≤ b.alphaValue jf := by
          exact_mod_cast (b.alpha_p2 jf).1
        have hnegative : (b.alphaValue jf : WithTop ℚ) ≤ (-1 : ℚ) := by
          calc
            (b.alphaValue jf : WithTop ℚ) ≤
                ((((b.order jf.succ - b.order jf.castSucc : Int) : ℚ) :
                    WithTop ℚ) +
                  b.truncatedPrefixDefect b (-1) j (j + 2)) := by
              simpa only [jf] using hbound
            _ ≤ ((((b.order jf.succ - b.order jf.castSucc : Int) : ℚ) :
                  WithTop ℚ) + cutoff) := add_le_add_right hlocalLe _
            _ ≤ (-1 : ℚ) := by exact_mod_cast hgapCut
        have himpossibleQ : (0 : ℚ) ≤ -1 := by
          exact_mod_cast hnonnegative.trans hnegative
        norm_num at himpossibleQ
      have hcentralSourceLocal :
          (cutoff : WithTop ℚ) <
            a.truncatedPrefixDefect a (-1) left (left + 2) := by
        letI : Beli2006AlphaLaws.{u, v} K := alphaV
        have hbound := a.alpha_le_orderGap_add_cappedAdjacent p
        by_contra hnotCut
        have hlocalLe : a.truncatedPrefixDefect a (-1) left (left + 2) ≤
            (cutoff : WithTop ℚ) := le_of_not_gt hnotCut
        have hpSucc : a.order p.succ =
            a.orderSequence.entryOrZero right := by
          rw [a.orderSequence_entryOrZero_eq_order ⟨right, hrightBound⟩]
          apply congrArg a.order
          apply Fin.ext
          simp only [p, Fin.val_succ]
          exact hrightEq.symm
        have hpCast : a.order p.castSucc =
            a.orderSequence.entryOrZero left := by
          rw [a.orderSequence_entryOrZero_eq_order ⟨left, by omega⟩]
          rfl
        have hformula :
            ((a.order p.succ - a.order p.castSucc : Int) : ℚ) +
                cutoff = 1 := by
          rw [hpSucc, hpCast]
          simp only [cutoff]
          push_cast
          ring
        have halphaTop : (a.alphaValue p : WithTop ℚ) ≤ 1 := by
          calc
            (a.alphaValue p : WithTop ℚ) ≤
                ((((a.order p.succ - a.order p.castSucc : Int) : ℚ) :
                    WithTop ℚ) +
                  a.truncatedPrefixDefect a (-1) left (left + 2)) := by
              simpa only [p] using hbound
            _ ≤ ((((a.order p.succ - a.order p.castSucc : Int) : ℚ) :
                  WithTop ℚ) + cutoff) := add_le_add_right hlocalLe _
            _ = 1 := by exact_mod_cast hformula
        have halphaLe : a.alphaValue p ≤ 1 := by exact_mod_cast halphaTop
        exact (not_lt_of_ge halphaLe) halphaGt
      have hbaseCommon : (cutoff : WithTop ℚ) <
          a.truncatedPrefixDefect b 1 first first := by
        letI : Beli2006AlphaLaws.{u, v} K := alphaV
        let firstIdx : RepresentationIndex (n + 2) (n + 2) :=
          ⟨first, hfirstPos, by omega, by omega⟩
        let previous : Fin (n + 1) := ⟨first - 1, by omega⟩
        have hclassification := a.beli2019Lemma63_sameRank_value
          b hdefect firstIdx (by
            intro k hk
            exact D.outer.firstDifference.before k
              (by simpa only [first, firstIdx] using hk))
        have halphaDefect : (a.alphaValue previous : WithTop ℚ) ≤
            a.truncatedPrefixDefect b 1 first first := by
          have hcondition := hdefect firstIdx
          rw [hclassification] at hcondition
          simpa only [firstIdx, previous] using hcondition
        have hsourceFirstOrder : a.order previous.succ =
            a.order p.castSucc := by
          rw [← a.orderSequence_entryOrZero_eq_order previous.succ,
            ← a.orderSequence_entryOrZero_eq_order p.castSucc]
          have hpreviousVal : previous.succ.val = first := by
            simp only [previous, Fin.val_succ]
            omega
          have hpVal : p.castSucc.val = left := by
            simp only [p, Fin.val_castSucc]
          change a.orderSequence.entryOrZero previous.succ.val =
            a.orderSequence.entryOrZero p.castSucc.val
          rw [hpreviousVal, hpVal]
          exact hsourceFirst
        have hendpoint := a.alphaRightEndpoint_antitone
          (show previous ≤ p by
            change first - 1 ≤ left
            omega)
        unfold alphaRightEndpoint at hendpoint
        rw [hsourceFirstOrder] at hendpoint
        have hcutAlpha : cutoff < a.alphaValue previous := by
          dsimp only [cutoff]
          have hrightOrder : a.order p.succ =
              a.orderSequence.entryOrZero right := by
            rw [a.orderSequence_entryOrZero_eq_order
              ⟨right, hrightBound⟩]
            apply congrArg a.order
            apply Fin.ext
            simp only [p, Fin.val_succ]
            exact hrightEq.symm
          have hleftOrder : a.order p.castSucc =
              a.orderSequence.entryOrZero left := by
            rw [a.orderSequence_entryOrZero_eq_order
              ⟨left, by omega⟩]
            rfl
          rw [hrightOrder, hleftOrder] at hendpoint
          push_cast
          linarith
        have hcutAlphaTop : (cutoff : WithTop ℚ) <
            (a.alphaValue previous : WithTop ℚ) := by
          exact_mod_cast hcutAlpha
        exact hcutAlphaTop.trans_le halphaDefect
      have hcommon (k : Nat) (hkFirst : first ≤ k) (hkLeft : k ≤ left)
          (hkParity : Even (k - first)) :
          (cutoff : WithTop ℚ) <
            a.truncatedPrefixDefect b 1 k k := by
        induction k using Nat.strong_induction_on with
        | h k ih =>
            by_cases hkBase : k = first
            · simpa only [hkBase] using hbaseCommon
            · have hkTwo : first + 2 ≤ k := by
                rcases hkParity with ⟨d, hd⟩
                omega
              have hprevParity : Even ((k - 2) - first) := by
                rcases hkParity with ⟨d, hd⟩
                exact ⟨d - 1, by omega⟩
              have hprev := ih (k - 2) (by omega) (by omega)
                (by omega) hprevParity
              have hsource := hsourceLocal (k - 2) (by omega)
                (by omega) hprevParity
              have htarget := htargetLocal (k - 2) (by omega)
                (by omega) hprevParity
              have hsourceReverse : (cutoff : WithTop ℚ) <
                  a.truncatedPrefixDefect a (-1) k (k - 2) := by
                rw [a.truncatedPrefixDefect_comm a (-1) k (k - 2)]
                simpa only [show k - 2 + 2 = k by omega] using hsource
              have hfirstDom := a.truncatedPrefixDefect_domination a b
                (-1) 1 k (k - 2) (k - 2)
              have hintermediate : (cutoff : WithTop ℚ) <
                  a.truncatedPrefixDefect b (-1) k (k - 2) :=
                (lt_min hsourceReverse hprev).trans_le (by
                  simpa using hfirstDom)
              have hsecondDom := a.truncatedPrefixDefect_domination b b
                (-1) (-1) k (k - 2) k
              exact (lt_min hintermediate (by
                simpa only [show k - 2 + 2 = k by omega] using htarget)).trans_le
                  (by simpa using hsecondDom)
      have hprefixGap : a.orderSequence.prefixGap b.orderSequence idx.val =
          1 := by
        have hbetween := D.outer.transition.gap_between (left + 1)
          (by omega) (by have hadjacent := D.adjacent; omega)
        simpa only [idx] using hbetween
      have hsum : b.orderSequence.prefixSum idx.val =
          a.orderSequence.prefixSum idx.val + 1 := by
        unfold BeliOrderSequence.prefixGap at hprefixGap
        omega
      have hzeroDefect := a.truncatedPrefixDefect_eq_zero_of_prefixSum_succ
        (alphaV := alphaV) (alphaW := alphaW) b idx.val
        (by simp only [idx]; omega) (by simp only [idx]; omega) hsum
      have hA := hdefect idx
      rw [hzeroDefect] at hA
      rw [a.coe_representationAlphaValue b idx,
        a.representationAlpha_eq_min_halfGap_prime b idx] at hA
      rcases min_le_iff.mp hA with hhalf | hprime
      · unfold representationHalfGap at hhalf
        letI : Beli2006AlphaLaws.{u, v} K := alphaV
        norm_cast at hhalf
        push_cast at hhalf
        simp only [Rat.divInt_eq_div] at hhalf
        have hleftBoundaryOrder :
            b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
              a.order ⟨idx.val - 1, by have := idx.lt_large; omega⟩ + 1 := by
          have hbEntry :
              b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
                b.orderSequence.entryOrZero (idx.val - 1) :=
            (BeliOrderSequence.entryOrZero_of_lt b.orderSequence
              (show idx.val - 1 < n + 2 by omega)).symm
          have haEntry :
              a.order ⟨idx.val - 1, by have := idx.lt_large; omega⟩ =
                a.orderSequence.entryOrZero (idx.val - 1) :=
            (BeliOrderSequence.entryOrZero_of_lt a.orderSequence
              (show idx.val - 1 < n + 2 by omega)).symm
          rw [hbEntry, haEntry, hidxPred]
          exact hleftGap
        have hgapUpper : a.orderGap p ≤
            1 - 2 * (ramificationIndex K : Int) := by
          unfold orderGap
          have hpCast : p.castSucc =
              (⟨idx.val - 1, by omega⟩ : Fin (n + 2)) := by
            apply Fin.ext
            simp only [p, Fin.val_castSucc]
            exact hidxPred.symm
          have hpSucc : p.succ =
              (⟨idx.val, idx.lt_large⟩ : Fin (n + 2)) := by
            apply Fin.ext
            simp only [p, Fin.val_succ]
            exact hidxVal.symm
          rw [hpCast, hpSucc]
          have hdiffQ :
              ((a.order ⟨idx.val, idx.lt_large⟩ -
                b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ :
                  Int) : ℚ) ≤ -(2 * (ramificationIndex K : ℚ)) := by
            linarith [hhalf]
          have hdiffInt :
              a.order ⟨idx.val, idx.lt_large⟩ -
                  b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ ≤
                -(2 * (ramificationIndex K : Int)) := by
            exact_mod_cast hdiffQ
          omega
        have hgapLower : -(2 * (ramificationIndex K : Int)) ≤
            a.orderGap p := by
          have h := a.toBONG.adjacentOrderGap_ge_neg_two_mul_e p.castSucc
            (Nat.succ_lt_succ p.isLt)
          change -(2 * (ramificationIndex K : Int)) ≤ a.orderGap p at h
          exact h
        have hgapEq : a.orderGap p =
            -(2 * (ramificationIndex K : Int)) := by
          by_contra hne
          have hoddGap : Odd (a.orderGap p) := by
            refine ⟨-(ramificationIndex K : Int), ?_⟩
            omega
          have hgapTwo : a.orderGap p ≤
              2 * (ramificationIndex K : Int) := by
            have hePos := ramificationIndex_pos (K := K)
            omega
          have halphaGap := (a.alpha_p3 p hgapTwo).2.mpr (Or.inr hoddGap)
          have halphaNonneg := (a.alpha_p2 p).1
          have hePos := ramificationIndex_pos (K := K)
          rw [halphaGap] at halphaNonneg
          have hgapNonneg : 0 ≤ a.orderGap p := by
            exact_mod_cast halphaNonneg
          omega
        have halphaZero := (a.alpha_p2 p).2.mpr hgapEq
        linarith
      · by_cases hi : 1 < idx.val ∧ idx.val + 1 < n + 2
        · rw [a.representationAlphaPrime_eq_min_primary_secondary b idx hi]
            at hprime
          rcases min_le_iff.mp hprime with hprimary | hsecondary
          · have hprimaryDefectLe :
                a.truncatedPrefixDefect b (-1) (idx.val + 1)
                    (idx.val - 1) ≤ (cutoff : WithTop ℚ) := by
              unfold representationPrimaryDefect at hprimary
              let z := a.truncatedPrefixDefect b (-1) (idx.val + 1)
                (idx.val - 1)
              have hz : z ≠ ⊤ := by
                intro htop
                rw [show a.truncatedPrefixDefect b (-1) (idx.val + 1)
                  (idx.val - 1) = z by rfl, htop] at hprimary
                simp at hprimary
              obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hz
              rw [show a.truncatedPrefixDefect b (-1) (idx.val + 1)
                  (idx.val - 1) = z by rfl, ← hd] at hprimary ⊢
              norm_cast at hprimary ⊢
              push_cast at hprimary ⊢
              have hrightOrder : a.order ⟨idx.val, idx.lt_large⟩ =
                  a.orderSequence.entryOrZero right := by
                rw [a.orderSequence_entryOrZero_eq_order
                  ⟨right, hrightBound⟩]
                apply congrArg a.order
                apply Fin.ext
                exact hidxRight
              have hleftOrder :
                  b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
                    b.orderSequence.entryOrZero left := by
                rw [b.orderSequence_entryOrZero_eq_order
                  ⟨left, by omega⟩]
                apply congrArg b.order
                apply Fin.ext
                exact hidxPred
              rw [hrightOrder, hleftOrder] at hprimary
              have hleftBoundaryQ :
                  (b.orderSequence.entryOrZero left : ℚ) =
                    (a.orderSequence.entryOrZero left : ℚ) + 1 := by
                exact_mod_cast hleftGap
              simp only [cutoff]
              push_cast
              linarith [hleftBoundaryQ]
            have hcentralCommon := hcommon left hfirstLeLeft le_rfl
              hleftParity
            have hcentralReverse : (cutoff : WithTop ℚ) <
                a.truncatedPrefixDefect a (-1) (left + 2) left := by
              rw [a.truncatedPrefixDefect_comm a (-1) (left + 2) left]
              exact hcentralSourceLocal
            have hdom := a.truncatedPrefixDefect_domination a b
              (-1) 1 (left + 2) left left
            have hcritical : (cutoff : WithTop ℚ) <
                a.truncatedPrefixDefect b (-1) (left + 2) left :=
              (lt_min hcentralReverse hcentralCommon).trans_le (by
                simpa using hdom)
            have hindexOne : idx.val + 1 = left + 2 := by
              simp only [idx]
            have hindexPred : idx.val - 1 = left := by
              simp only [idx]
              omega
            rw [hindexOne, hindexPred] at hprimaryDefectLe
            exact (not_le_of_gt hcritical) hprimaryDefectLe
          · exact (not_le_of_gt (hsecondaryPos hi)) hsecondary
        · rw [a.representationAlphaPrime_eq_primary_of_not_interior
              b idx hi] at hprime
          have hprimaryDefectLe :
              a.truncatedPrefixDefect b (-1) (idx.val + 1)
                  (idx.val - 1) ≤ (cutoff : WithTop ℚ) := by
            unfold representationPrimaryDefect at hprime
            let z := a.truncatedPrefixDefect b (-1) (idx.val + 1)
              (idx.val - 1)
            have hz : z ≠ ⊤ := by
              intro htop
              rw [show a.truncatedPrefixDefect b (-1) (idx.val + 1)
                (idx.val - 1) = z by rfl, htop] at hprime
              simp at hprime
            obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hz
            rw [show a.truncatedPrefixDefect b (-1) (idx.val + 1)
                (idx.val - 1) = z by rfl, ← hd] at hprime ⊢
            norm_cast at hprime ⊢
            push_cast at hprime ⊢
            have hrightOrder : a.order ⟨idx.val, idx.lt_large⟩ =
                a.orderSequence.entryOrZero right := by
              rw [a.orderSequence_entryOrZero_eq_order
                ⟨right, hrightBound⟩]
              apply congrArg a.order
              apply Fin.ext
              exact hidxRight
            have hleftOrder :
                b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
                  b.orderSequence.entryOrZero left := by
              rw [b.orderSequence_entryOrZero_eq_order
                ⟨left, by omega⟩]
              apply congrArg b.order
              apply Fin.ext
              exact hidxPred
            rw [hrightOrder, hleftOrder] at hprime
            have hleftBoundaryQ :
                (b.orderSequence.entryOrZero left : ℚ) =
                  (a.orderSequence.entryOrZero left : ℚ) + 1 := by
              exact_mod_cast hleftGap
            simp only [cutoff]
            push_cast
            linarith [hleftBoundaryQ]
          have hcentralCommon := hcommon left hfirstLeLeft le_rfl
            hleftParity
          have hcentralReverse : (cutoff : WithTop ℚ) <
              a.truncatedPrefixDefect a (-1) (left + 2) left := by
            rw [a.truncatedPrefixDefect_comm a (-1) (left + 2) left]
            exact hcentralSourceLocal
          have hdom := a.truncatedPrefixDefect_domination a b
            (-1) 1 (left + 2) left left
          have hcritical : (cutoff : WithTop ℚ) <
              a.truncatedPrefixDefect b (-1) (left + 2) left :=
            (lt_min hcentralReverse hcentralCommon).trans_le (by
              simpa using hdom)
          have hindexOne : idx.val + 1 = left + 2 := by
            simp only [idx]
          have hindexPred : idx.val - 1 = left := by
            simp only [idx]
            omega
          rw [hindexOne, hindexPred] at hprimaryDefectLe
          exact (not_le_of_gt hcritical) hprimaryDefectLe
end BONG.GoodBONG

end Bong
