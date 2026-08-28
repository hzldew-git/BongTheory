/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69CappedPropagation
import Bong.Bong.Beli2019AuxiliaryAlphaNormalForm
import Bong.Bong.Beli2019Lemma67Classification
import Bong.Bong.Beli2019OddPrefixDefect

/-!
# Beli (2019), Lemma 6.9(i): the type-III boundary alpha

This file proves the `alpha_t <= 1` conclusion needed by the nonoverlapping
type-III branch.  The proof follows the paper's domination argument.  Under
the Section 7 normalization `s = 1`, all earlier even pairs have capped
defect above the critical cut; two applications of defect domination per
pair propagate this strict bound to the central primary candidate.
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

/-- The type-III instance of the alpha bound in Lemma 6.9(i), normalized
so that the first unequal order is the first BONG entry. -/
theorem beli2019Lemma69_i_typeIII
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b) :
    a.alphaValue
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≤ 1 := by
  let left := D.outer.transition.lastZero
  let right := D.outer.transition.firstTwo - 1
  have hfirstTwoBound := D.outer.transition.firstTwo_le_rank
  have hleftBound : left < n := by
    simp only [left]
    rw [D.adjacent] at hfirstTwoBound
    omega
  have hrightEq : right = left + 1 := by
    simp only [right, left]
    rw [D.adjacent]
    omega
  have hrightBound : right < n + 1 := by omega
  let p : Fin n := ⟨left, hleftBound⟩
  let idx : RepresentationIndex (n + 1) (n + 1) := {
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
  have hleftEven : Even left := by
    by_cases heq : D.outer.first = left
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < left :=
        lt_of_le_of_ne D.outer.first_le_left heq
      simpa only [hfirst, left, Nat.sub_zero] using
        (D.outer.leftProfile hlt).1
  have hsourceEven (k : Nat) (hk : k ≤ left) (heven : Even k) :
      a.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero left := by
    by_cases hzero : left = 0
    · have hkZero : k = 0 := by omega
      rw [hkZero, hzero]
    · have hlt : D.outer.first < left := by
        rw [hfirst]
        omega
      have hp := D.outer.leftProfile hlt
      have hkEq := hp.2.2 k (by rw [hfirst]; omega) hk (by
        simpa only [hfirst, Nat.sub_zero] using heven)
      have hleftEq := hp.2.2 left D.outer.first_le_left
        le_rfl hp.1
      exact hkEq.trans hleftEq.symm
  have hsourceZero : a.orderSequence.entryOrZero 0 =
      a.orderSequence.entryOrZero left :=
    hsourceEven 0 (Nat.zero_le left) ⟨0, by omega⟩
  have htargetZero : b.orderSequence.entryOrZero 0 =
      b.orderSequence.entryOrZero left := by
    by_cases hzero : left = 0
    · rw [hzero]
    · have hlt : D.outer.first < left := by
        rw [hfirst]
        omega
      have hp := D.outer.leftProfile hlt
      have hupper := D.no_gap_two D.outer.first
        D.outer.firstDifference.bound
      rw [hfirst] at hupper
      have hfirstGap : b.orderSequence.entryOrZero 0 =
          a.orderSequence.entryOrZero 0 + 1 := by
        have hstrict := hp.2.1
        rw [hfirst] at hstrict
        omega
      have hleftGap := D.outer.transition.leftBoundary
      have hleftGap' : b.orderSequence.entryOrZero left =
          a.orderSequence.entryOrZero left + 1 := by
        simpa only [left] using hleftGap
      omega
  have htargetEven (k : Nat) (hk : k ≤ left) (heven : Even k) :
      b.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero left := by
    have hkBound : k < n + 1 := hk.trans_lt hleftBound |>.trans (by omega)
    have hleftRank : left < n + 1 := hleftBound.trans (by omega)
    have hleftK : Even (left - k) := by
      rcases hleftEven with ⟨d, hd⟩
      rcases heven with ⟨e, he⟩
      refine ⟨d - e, ?_⟩
      omega
    have hzeroK := b.orderSequence.entryOrZero_le_of_evenGap
      0 k (Nat.zero_le k) hkBound heven
    have hkLeft := b.orderSequence.entryOrZero_le_of_evenGap
      k left hk hleftRank hleftK
    omega
  have htargetNext_le_source
      (hnext : left + 2 < n + 1) :
      b.orderSequence.entryOrZero (left + 2) ≤
        a.orderSequence.entryOrZero (left + 2) := by
    by_cases hafter : D.outer.last < left + 2
    · exact (D.outer.lastDifference.after (left + 2) hafter hnext).symm.le
    · have hnextLast : left + 2 ≤ D.outer.last := by omega
      have hrightLast : right < D.outer.last := by omega
      have hp := D.outer.rightProfile hrightLast
      have hnextOneLast : left + 3 ≤ D.outer.last := by
        rcases hp.1 with ⟨d, hd⟩
        omega
      have hlastParity : Even (D.outer.last - (left + 3)) := by
        rcases hp.1 with ⟨d, hd⟩
        refine ⟨d - 1, ?_⟩
        omega
      have htargetSame :
          b.orderSequence.entryOrZero (left + 3) =
            b.orderSequence.entryOrZero D.outer.last := by
        exact hp.2.2 (left + 3) (by omega) hnextOneLast hlastParity
      have hsourceLe := a.orderSequence.entryOrZero_le_of_evenGap
        (left + 3) D.outer.last hnextOneLast
        D.outer.lastDifference.bound hlastParity
      have hpair := D.outer.rightPairEq (left + 2) (by
        have hadjacent := D.adjacent
        change D.outer.transition.firstTwo ≤
          D.outer.transition.lastZero + 2
        omega) (by
          have hlastBound := D.outer.lastDifference.bound
          omega) ⟨0, by omega⟩
      have hone : left + 2 + 1 = left + 3 := by omega
      rw [hone] at hpair
      have hlastStrict := hp.2.1
      omega
  have hsecondaryPos
      (hi : 1 < idx.val ∧ idx.val + 1 < n + 1) :
      (0 : WithTop ℚ) < a.representationSecondaryDefect b idx hi := by
    have hleftTwo : 2 ≤ left := by
      rcases hleftEven with ⟨d, hd⟩
      simp only [idx] at hi
      omega
    have hpairParity : Even (left - (left - 2)) := ⟨1, by omega⟩
    have hpair := D.outer.leftPairEq (left - 2) (by omega) hpairParity
    have hsourcePrev := hsourceEven (left - 2) (by omega) (by
      rcases hleftEven with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩)
    have htargetPrev := htargetEven (left - 2) (by omega) (by
      rcases hleftEven with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩)
    have htargetOdd :
        b.orderSequence.entryOrZero (left - 1) =
          a.orderSequence.entryOrZero (left - 1) - 1 := by
      have hone : left - 2 + 1 = left - 1 := by omega
      rw [hone] at hpair
      have hleftBoundary := D.outer.transition.leftBoundary
      have hleftBoundary' : b.orderSequence.entryOrZero left =
          a.orderSequence.entryOrZero left + 1 := by
        simpa only [left] using hleftBoundary
      omega
    have hsourceOddLe := a.orderSequence.entryOrZero_le_of_evenGap
      (left - 1) right (by omega) hrightBound ⟨1, by omega⟩
    have htargetMonotone := b.orderSequence.entryOrZero_le_of_evenGap
      left (left + 2) (by omega) (by simp only [idx] at hi; omega)
      ⟨1, by omega⟩
    have htargetSource := htargetNext_le_source (by
      simp only [idx] at hi
      omega)
    have hcoefficient : 0 <
        a.orderSequence.entryOrZero right +
          a.orderSequence.entryOrZero (left + 2) -
          b.orderSequence.entryOrZero (left - 1) -
          b.orderSequence.entryOrZero left := by
      omega
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
          (show idx.val - 2 < n + 1 by omega)).symm
      have hbCurrent :
          b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
            b.orderSequence.entryOrZero (idx.val - 1) :=
        (BeliOrderSequence.entryOrZero_of_lt b.orderSequence
          (show idx.val - 1 < n + 1 by omega)).symm
      rw [haCurrent, haNext, hbPrevious, hbCurrent]
      have hidxNext : idx.val + 1 = left + 2 := by
        rw [hidxVal]
      have hidxPrevious : idx.val - 2 = left - 1 := by
        rw [hidxVal]
        omega
      rw [hidxNext, hidxPrevious, hidxPred, hidxRight]
      exact hcoefficient
    have hdefectNonneg := a.truncatedPrefixDefect_nonneg
      (alphaV := alphaV) (alphaW := alphaW) b 1
      (idx.val + 2) (idx.val - 2)
    unfold representationSecondaryDefect
    calc
      (0 : WithTop ℚ) <
          (((a.order ⟨idx.val, idx.lt_large⟩ +
            a.order ⟨idx.val + 1, hi.2⟩ -
            b.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ -
            b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ :
              Int) : ℚ) : WithTop ℚ) := by
        exact_mod_cast hcoefficientOrder
      _ ≤ _ := le_add_of_nonneg_right hdefectNonneg
  by_contra hnot
  have halphaGt : 1 < a.alphaValue p := by
    simpa only [p] using lt_of_not_ge hnot
  let cutoff : ℚ :=
    ((a.orderSequence.entryOrZero left -
      a.orderSequence.entryOrZero right + 1 : Int) : ℚ)
  have hsourceLocal (j : Nat) (hj : j + 2 ≤ left)
      (heven : Even j) :
      (cutoff : WithTop ℚ) <
        a.truncatedPrefixDefect a (-1) j (j + 2) := by
    let jf : Fin n := ⟨j, by omega⟩
    have hjp : jf ≤ p := by
      change j ≤ left
      omega
    letI : Beli2006AlphaLaws.{u, v} K := alphaV
    have hbound := a.alpha_le_order_sub_add_cappedAdjacent hjp
    by_contra hnotCut
    have hlocalLe : a.truncatedPrefixDefect a (-1) j (j + 2) ≤
        (cutoff : WithTop ℚ) := le_of_not_gt hnotCut
    have hsourceJ := hsourceEven j (by omega) heven
    have hpSucc : a.order p.succ =
        a.orderSequence.entryOrZero right := by
      rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence hrightBound]
      apply congrArg a.order
      apply Fin.ext
      simp only [p, Fin.val_succ]
      omega
    have hjCast : a.order jf.castSucc =
        a.orderSequence.entryOrZero j := by
      rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
      apply congrArg a.order
      apply Fin.ext
      rfl
    have hformula :
        ((a.order p.succ - a.order jf.castSucc : Int) : ℚ) + cutoff = 1 := by
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
    linarith
  have htargetLocal (j : Nat) (hj : j + 2 ≤ left)
      (heven : Even j) :
      (cutoff : WithTop ℚ) <
        b.truncatedPrefixDefect b (-1) j (j + 2) := by
    let jf : Fin n := ⟨j, by omega⟩
    have hpairParity : Even (left - j) := by
      rcases hleftEven with ⟨d, hd⟩
      rcases heven with ⟨e, he⟩
      refine ⟨d - e, ?_⟩
      omega
    have hpair := D.outer.leftPairEq j hj hpairParity
    have hsourceJ := hsourceEven j (by omega) heven
    have htargetJ := htargetEven j (by omega) heven
    have htargetNext : b.orderSequence.entryOrZero (j + 1) =
        a.orderSequence.entryOrZero (j + 1) - 1 := by
      have hleftBoundary := D.outer.transition.leftBoundary
      have hleftBoundary' : b.orderSequence.entryOrZero left =
          a.orderSequence.entryOrZero left + 1 := by
        simpa only [left] using hleftBoundary
      omega
    have hsourceNextLe := a.orderSequence.entryOrZero_le_of_evenGap
      (j + 1) right (by omega) hrightBound (by
        rcases hleftEven with ⟨d, hd⟩
        rcases heven with ⟨e, he⟩
        refine ⟨d - e, ?_⟩
        simp only [hrightEq]
        omega)
    have hjSucc : b.order jf.succ =
        b.orderSequence.entryOrZero (j + 1) := by
      rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega)]
      apply congrArg b.order
      apply Fin.ext
      rfl
    have hjCast : b.order jf.castSucc =
        b.orderSequence.entryOrZero j := by
      rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega)]
      apply congrArg b.order
      apply Fin.ext
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
    have himpossible := hnonnegative.trans hnegative
    have himpossibleQ : (0 : ℚ) ≤ -1 := by
      exact_mod_cast himpossible
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
      rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence hrightBound]
      apply congrArg a.order
      apply Fin.ext
      simp only [p, Fin.val_succ]
      omega
    have hpCast : a.order p.castSucc =
        a.orderSequence.entryOrZero left := by
      rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (hleftBound.trans (by omega))]
      apply congrArg a.order
      apply Fin.ext
      rfl
    have hformula :
        ((a.order p.succ - a.order p.castSucc : Int) : ℚ) + cutoff = 1 := by
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
    linarith
  have hcommon (k : Nat) (hk : k ≤ left) (heven : Even k) :
      (cutoff : WithTop ℚ) <
        a.truncatedPrefixDefect b 1 k k := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
        by_cases hzero : k = 0
        · subst k
          unfold truncatedPrefixDefect
          rw [a.prefixAlphaCap_zero, b.prefixAlphaCap_zero]
          simp only [inf_top_eq]
          rw [show (1 : Kˣ) * a.prefixProduct 0 * b.prefixProduct 0 = 1 by
            simp [GoodBONG.prefixProduct]]
          rw [defectOrder_eq_top_of_isSquare]
          · exact WithTop.coe_lt_top cutoff
          · exact IsSquare.one
        · have hkTwo : 2 ≤ k := by
            rcases heven with ⟨d, hd⟩
            omega
          have hprevEven : Even (k - 2) := by
            rcases heven with ⟨d, hd⟩
            exact ⟨d - 1, by omega⟩
          have hprev := ih (k - 2) (by omega) (by omega) hprevEven
          have hsource := hsourceLocal (k - 2) (by omega) hprevEven
          have htarget := htargetLocal (k - 2) (by omega) hprevEven
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
  have hprefixGap : a.orderSequence.prefixGap b.orderSequence idx.val = 1 := by
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
    have hleftBoundary := D.outer.transition.leftBoundary
    have hleftBoundaryOrder :
        b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
          a.order ⟨idx.val - 1, by have := idx.lt_large; omega⟩ + 1 := by
      have hbEntry :
          b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
            b.orderSequence.entryOrZero (idx.val - 1) :=
        (BeliOrderSequence.entryOrZero_of_lt b.orderSequence
          (show idx.val - 1 < n + 1 by rw [hidxPred]; omega)).symm
      have haEntry :
          a.order ⟨idx.val - 1, by have := idx.lt_large; omega⟩ =
            a.orderSequence.entryOrZero (idx.val - 1) :=
        (BeliOrderSequence.entryOrZero_of_lt a.orderSequence
          (show idx.val - 1 < n + 1 by rw [hidxPred]; omega)).symm
      rw [hbEntry, haEntry]
      rw [hidxPred]
      simpa only [left] using hleftBoundary
    have hgapUpper : a.orderGap p ≤
        1 - 2 * (ramificationIndex K : Int) := by
      unfold orderGap
      have hpCast : p.castSucc =
          (⟨idx.val - 1, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ext
        simp only [p, Fin.val_castSucc]
        exact hidxPred.symm
      have hpSucc : p.succ =
          (⟨idx.val, idx.lt_large⟩ : Fin (n + 1)) := by
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
  · by_cases hi : 1 < idx.val ∧ idx.val + 1 < n + 1
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
          have hleftBoundary := D.outer.transition.leftBoundary
          have hrightOrder : a.order ⟨idx.val, idx.lt_large⟩ =
              a.orderSequence.entryOrZero right := by
            rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
              hrightBound]
            apply congrArg a.order
            apply Fin.ext
            change idx.val = right
            simpa only [idx] using hrightEq.symm
          have hleftOrder :
              b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
                b.orderSequence.entryOrZero left := by
            rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
              (hleftBound.trans (by omega))]
            apply congrArg b.order
            apply Fin.ext
            change idx.val - 1 = left
            simp only [idx]
            omega
          rw [hrightOrder, hleftOrder] at hprimary
          have hleftBoundaryQ :
              (b.orderSequence.entryOrZero left : ℚ) =
                (a.orderSequence.entryOrZero left : ℚ) + 1 := by
            exact_mod_cast (show
              b.orderSequence.entryOrZero left =
                a.orderSequence.entryOrZero left + 1 by
              simpa only [left] using hleftBoundary)
          simp only [cutoff]
          push_cast
          linarith [hleftBoundaryQ]
        have hcentralCommon := hcommon left le_rfl hleftEven
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
    · rw [a.representationAlphaPrime_eq_primary_of_not_interior b idx hi]
        at hprime
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
        have hleftBoundary := D.outer.transition.leftBoundary
        have hrightOrder : a.order ⟨idx.val, idx.lt_large⟩ =
            a.orderSequence.entryOrZero right := by
          rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
            hrightBound]
          apply congrArg a.order
          apply Fin.ext
          change idx.val = right
          simpa only [idx] using hrightEq.symm
        have hleftOrder :
            b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
              b.orderSequence.entryOrZero left := by
          rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
            (hleftBound.trans (by omega))]
          apply congrArg b.order
          apply Fin.ext
          change idx.val - 1 = left
          simp only [idx]
          omega
        rw [hrightOrder, hleftOrder] at hprime
        have hleftBoundaryQ :
            (b.orderSequence.entryOrZero left : ℚ) =
              (a.orderSequence.entryOrZero left : ℚ) + 1 := by
          exact_mod_cast (show
            b.orderSequence.entryOrZero left =
              a.orderSequence.entryOrZero left + 1 by
            simpa only [left] using hleftBoundary)
        simp only [cutoff]
        push_cast
        linarith [hleftBoundaryQ]
      have hcentralCommon := hcommon left le_rfl hleftEven
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
