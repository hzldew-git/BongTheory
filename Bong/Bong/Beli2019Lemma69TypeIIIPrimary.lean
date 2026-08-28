/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIII

/-!
# Beli (2019), Lemma 6.9(i): the type-III primary candidate

The last paragraph of the proof of Lemma 6.9 shows that the primary
candidate at a nonexceptional type-III transition is nonnegative.  The
argument is the weak, equality-case version of the capped-defect propagation
used to prove the preceding bound `alpha_t <= 1`.
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

/-- At a normalized type-III transition, `alpha_t = 1` makes the primary
candidate in `A_t(M, N)` nonnegative. -/
theorem lemma69_typeIII_primaryDefect_nonneg
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hAlpha : a.alphaValue
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1) :
    0 ≤ a.representationPrimaryDefect b {
      val := D.outer.transition.lastZero + 1
      pos := by omega
      lt_large := by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega
      le_small := by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega } := by
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
  have hAlphaP : a.alphaValue p = 1 := by
    simpa only [p, left] using hAlpha
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
  have htargetEven (k : Nat) (hk : k ≤ left) (heven : Even k) :
      b.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero left := by
    have hkBound : k < n + 1 :=
      hk.trans_lt hleftBound |>.trans (by omega)
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
    by_cases hzero : left = 0
    · have hkZero : k = 0 := by omega
      rw [hkZero, hzero]
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
      have hsourceZero := hsourceEven 0 (Nat.zero_le left) ⟨0, by omega⟩
      have hleftGap := D.outer.transition.leftBoundary
      have hleftGap' : b.orderSequence.entryOrZero left =
          a.orderSequence.entryOrZero left + 1 := by
        simpa only [left] using hleftGap
      omega
  let cutoff : ℚ :=
    ((a.orderSequence.entryOrZero left -
      a.orderSequence.entryOrZero right + 1 : Int) : ℚ)
  have hsourceLocal (j : Nat) (hj : j + 2 ≤ left)
      (heven : Even j) :
      (cutoff : WithTop ℚ) ≤
        a.truncatedPrefixDefect a (-1) j (j + 2) := by
    let jf : Fin n := ⟨j, by omega⟩
    have hjp : jf ≤ p := by
      change j ≤ left
      omega
    letI : Beli2006AlphaLaws.{u, v} K := alphaV
    have hbound := a.alpha_le_order_sub_add_cappedAdjacent hjp
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
        ((a.order p.succ - a.order jf.castSucc : Int) : ℚ) +
            cutoff = 1 := by
      rw [hpSucc, hjCast, hsourceJ]
      simp only [cutoff]
      push_cast
      ring
    by_contra hnot
    have hlocalLt : a.truncatedPrefixDefect a (-1) j (j + 2) <
        (cutoff : WithTop ℚ) := lt_of_not_ge hnot
    have hshiftLt :
        ((((a.order p.succ - a.order jf.castSucc : Int) : ℚ) :
            WithTop ℚ) +
              a.truncatedPrefixDefect a (-1) j (j + 2)) < 1 := by
      calc
        _ < ((((a.order p.succ - a.order jf.castSucc : Int) : ℚ) :
              WithTop ℚ) + (cutoff : WithTop ℚ)) :=
          WithTop.add_lt_add_left WithTop.coe_ne_top hlocalLt
        _ = 1 := by exact_mod_cast hformula
    have hAlphaLt : (a.alphaValue p : WithTop ℚ) < 1 :=
      hbound.trans_lt hshiftLt
    rw [hAlphaP] at hAlphaLt
    exact (lt_irrefl (1 : WithTop ℚ)) hAlphaLt
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
      (cutoff : WithTop ℚ) ≤
        a.truncatedPrefixDefect a (-1) left (left + 2) := by
    letI : Beli2006AlphaLaws.{u, v} K := alphaV
    have hbound := a.alpha_le_orderGap_add_cappedAdjacent p
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
        ((a.order p.succ - a.order p.castSucc : Int) : ℚ) +
            cutoff = 1 := by
      rw [hpSucc, hpCast]
      simp only [cutoff]
      push_cast
      ring
    by_contra hnot
    have hlocalLt : a.truncatedPrefixDefect a (-1) left (left + 2) <
        (cutoff : WithTop ℚ) := lt_of_not_ge hnot
    have hshiftLt :
        ((((a.order p.succ - a.order p.castSucc : Int) : ℚ) :
            WithTop ℚ) +
              a.truncatedPrefixDefect a (-1) left (left + 2)) < 1 := by
      calc
        _ < ((((a.order p.succ - a.order p.castSucc : Int) : ℚ) :
              WithTop ℚ) + (cutoff : WithTop ℚ)) :=
          WithTop.add_lt_add_left WithTop.coe_ne_top hlocalLt
        _ = 1 := by exact_mod_cast hformula
    have hAlphaLt : (a.alphaValue p : WithTop ℚ) < 1 :=
      hbound.trans_lt hshiftLt
    rw [hAlphaP] at hAlphaLt
    exact (lt_irrefl (1 : WithTop ℚ)) hAlphaLt
  have hcommon (k : Nat) (hk : k ≤ left) (heven : Even k) :
      (cutoff : WithTop ℚ) ≤
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
          · exact le_top
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
          have hsourceReverse : (cutoff : WithTop ℚ) ≤
              a.truncatedPrefixDefect a (-1) k (k - 2) := by
            rw [a.truncatedPrefixDefect_comm a (-1) k (k - 2)]
            simpa only [show k - 2 + 2 = k by omega] using hsource
          have hfirstDom := a.truncatedPrefixDefect_domination a b
            (-1) 1 k (k - 2) (k - 2)
          have hintermediate : (cutoff : WithTop ℚ) ≤
              a.truncatedPrefixDefect b (-1) k (k - 2) :=
            (le_min hsourceReverse hprev).trans (by simpa using hfirstDom)
          have hsecondDom := a.truncatedPrefixDefect_domination b b
            (-1) (-1) k (k - 2) k
          have htarget' : (cutoff : WithTop ℚ) ≤
              b.truncatedPrefixDefect b (-1) (k - 2) k := by
            simpa only [show k - 2 + 2 = k by omega] using htarget.le
          exact (le_min hintermediate htarget').trans
            (by simpa using hsecondDom)
  have hcentralCommon := hcommon left le_rfl hleftEven
  have hcentralReverse : (cutoff : WithTop ℚ) ≤
      a.truncatedPrefixDefect a (-1) (left + 2) left := by
    rw [a.truncatedPrefixDefect_comm a (-1) (left + 2) left]
    exact hcentralSourceLocal
  have hdom := a.truncatedPrefixDefect_domination a b
    (-1) 1 (left + 2) left left
  have hmixed : (cutoff : WithTop ℚ) ≤
      a.truncatedPrefixDefect b (-1) (left + 2) left :=
    (le_min hcentralReverse hcentralCommon).trans (by simpa using hdom)
  have hrightOrder : a.order ⟨idx.val, idx.lt_large⟩ =
      a.orderSequence.entryOrZero right := by
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence hrightBound]
    apply congrArg a.order
    apply Fin.ext
    exact hidxRight
  have hleftOrder :
      b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
        b.orderSequence.entryOrZero left := by
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
      (hleftBound.trans (by omega))]
    apply congrArg b.order
    apply Fin.ext
    exact hidxPred
  have hleftBoundary := D.outer.transition.leftBoundary
  have hleftBoundary' : b.orderSequence.entryOrZero left =
      a.orderSequence.entryOrZero left + 1 := by
    simpa only [left] using hleftBoundary
  have hcrossCut :
      ((((a.order ⟨idx.val, idx.lt_large⟩ -
        b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ : Int) :
          ℚ) : WithTop ℚ) + (cutoff : WithTop ℚ)) = 0 := by
    norm_cast
    rw [hrightOrder, hleftOrder, hleftBoundary']
    simp only [cutoff]
    push_cast
    ring
  have hmixedIdx : (cutoff : WithTop ℚ) ≤
      a.truncatedPrefixDefect b (-1) (idx.val + 1) (idx.val - 1) := by
    dsimp only [idx]
    simpa only [Nat.add_sub_cancel] using hmixed
  change 0 ≤ a.representationPrimaryDefect b idx
  unfold representationPrimaryDefect
  calc
    (0 : WithTop ℚ) =
        ((((a.order ⟨idx.val, idx.lt_large⟩ -
          b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ : Int) :
            ℚ) : WithTop ℚ) + (cutoff : WithTop ℚ)) :=
      hcrossCut.symm
    _ ≤ _ := by
      exact add_le_add le_rfl hmixedIdx

end BONG.GoodBONG

end Bong
