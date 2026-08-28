/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIAlphaTail
import Bong.Bong.Beli2019Lemma69CappedPropagation
import Bong.Bong.Beli2019AuxiliaryAlphaNormalForm
import Bong.Bong.Beli2019OddPrefixDefect

/-!
# Beli (2019), Lemma 6.9(i): the type-I pivot alpha

This file proves that the minimal left-tail pivot has alpha at most one.
The proof follows the paper's domination argument.  Pair equality gives a
prefix-sum gap of one at the pivot.  Local capped defects above the critical
cut propagate to the primary representation candidate, while minimality of
the pivot makes the secondary candidate strictly positive.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type v} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The alpha at the minimal type-I left pivot is at most one. -/
theorem beli2019Lemma69_i_typeI_pivotAlpha
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (P : Lemma69TypeILeftPivotData a b D C)
    (hdefect : a.RepresentationDefectCondition b) :
    a.alphaValue ⟨P.pivot, by
      have hleftBound := C.left_le_anchor.trans_lt D.anchor_bound
      have hpivotPrevious := P.pivot_le_previous
      omega⟩ ≤ 1 := by
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  have hpivotBound : P.pivot < n + 1 := by
    have hpivotPrevious := P.pivot_le_previous
    omega
  have hpivotEntryBound : P.pivot < n + 2 := hpivotBound.trans (by omega)
  have hpivotNextBound : P.pivot + 1 < n + 2 := by omega
  let p : Fin (n + 1) := ⟨P.pivot, hpivotBound⟩
  let idx : RepresentationIndex (n + 2) (n + 2) := {
    val := P.pivot + 1
    pos := by omega
    lt_large := by omega
    le_small := by omega }
  have hidxVal : idx.val = P.pivot + 1 := rfl
  have hidxPred : idx.val - 1 = P.pivot := by
    rw [hidxVal]
    omega
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hpivotAnchor : P.pivot ≤ D.anchor :=
    P.pivot_le_previous.trans (Nat.sub_le C.leftSwitch 2) |>.trans
      C.left_le_anchor
  have hpivotBefore : P.pivot < C.leftSwitch := by
    have hpivotPrevious := P.pivot_le_previous
    omega
  have hsourceEven (k : Nat) (hk : k ≤ P.pivot) (heven : Even k) :
      a.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero P.pivot := by
    have hkAnchor := hk.trans hpivotAnchor
    exact (C.source_to_anchor k hkAnchor heven).trans
      (C.source_to_anchor P.pivot hpivotAnchor P.pivot_even).symm
  have htargetEven (k : Nat) (hk : k ≤ P.pivot) (heven : Even k) :
      b.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero P.pivot := by
    have hkBefore : k < C.leftSwitch := hk.trans_lt hpivotBefore
    exact (C.target_before_left k hkBefore heven).trans
      (C.target_before_left P.pivot hpivotBefore P.pivot_even).symm
  have hpivotBoundary : b.orderSequence.entryOrZero P.pivot =
      a.orderSequence.entryOrZero P.pivot + 1 := by
    have ha := C.source_to_anchor P.pivot hpivotAnchor P.pivot_even
    have hb := C.target_before_left P.pivot hpivotBefore P.pivot_even
    omega
  have hprefixEven (k : Nat) (hk : k ≤ P.pivot) (heven : Even k) :
      a.orderSequence.prefixSum k = b.orderSequence.prefixSum k := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
        by_cases hzero : k = 0
        · subst k
          simp
        · have hkTwo : 2 ≤ k := by
            rcases heven with ⟨d, hd⟩
            omega
          have hprevEven : Even (k - 2) := by
            rcases heven with ⟨d, hd⟩
            exact ⟨d - 1, by omega⟩
          have hprev := ih (k - 2) (by omega) (by omega) hprevEven
          have hpairParity : Even (D.anchor - (k - 2)) := by
            rcases hanchorEven with ⟨d, hd⟩
            rcases hprevEven with ⟨e, he⟩
            exact ⟨d - e, by omega⟩
          have hpair := D.profile.leftPairEq (k - 2) (by omega)
            hpairParity
          have hkEq : k - 2 + 2 = k := by omega
          rw [← hkEq, a.orderSequence.prefixSum_add_two,
            b.orderSequence.prefixSum_add_two, hprev, hpair]
  have hprefixPivot := hprefixEven P.pivot le_rfl P.pivot_even
  have hsum : b.orderSequence.prefixSum idx.val =
      a.orderSequence.prefixSum idx.val + 1 := by
    rw [hidxVal, a.orderSequence.prefixSum_succ,
      b.orderSequence.prefixSum_succ, hprefixPivot, hpivotBoundary]
    omega
  have hsecondaryPos
      (hi : 1 < idx.val ∧ idx.val + 1 < n + 2) :
      (0 : WithTop ℚ) < a.representationSecondaryDefect b idx hi := by
    have hpivotTwo : 2 ≤ P.pivot := by
      rcases P.pivot_even with ⟨d, hd⟩
      simp only [idx] at hi
      omega
    have hpreviousEven : Even (P.pivot - 2) := by
      rcases P.pivot_even with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩
    have hpairParity : Even (D.anchor - (P.pivot - 2)) := by
      rcases hanchorEven with ⟨d, hd⟩
      rcases hpreviousEven with ⟨e, he⟩
      exact ⟨d - e, by omega⟩
    have hpair := D.profile.leftPairEq (P.pivot - 2) (by omega)
      hpairParity
    have hsourcePrev := hsourceEven (P.pivot - 2) (by omega)
      hpreviousEven
    have htargetPrev := htargetEven (P.pivot - 2) (by omega)
      hpreviousEven
    have htargetOdd :
        b.orderSequence.entryOrZero (P.pivot - 1) =
          a.orderSequence.entryOrZero (P.pivot - 1) - 1 := by
      have hone : P.pivot - 2 + 1 = P.pivot - 1 := by omega
      rw [hone] at hpair
      omega
    have hsourceNextStrict := P.earlier_next_lt
      (P.pivot - 2) (by omega) hpreviousEven
    have hpivotNextIndex : P.pivot - 2 + 1 = P.pivot - 1 := by omega
    rw [hpivotNextIndex] at hsourceNextStrict
    have hpivotPlusTwoEven : Even (P.pivot + 2) := by
      rcases P.pivot_even with ⟨d, hd⟩
      exact ⟨d + 1, by omega⟩
    have hpivotPlusTwoAnchor : P.pivot + 2 ≤ D.anchor := by
      have hpivotPrevious := P.pivot_le_previous
      have hleftAnchor := C.left_le_anchor
      omega
    have hsourcePlusTwo := C.source_to_anchor (P.pivot + 2)
      hpivotPlusTwoAnchor hpivotPlusTwoEven
    have hsourcePivot := C.source_to_anchor P.pivot hpivotAnchor
      P.pivot_even
    have hsourcePlusTwoEq :
        a.orderSequence.entryOrZero (P.pivot + 2) =
          a.orderSequence.entryOrZero P.pivot :=
      hsourcePlusTwo.trans hsourcePivot.symm
    have hcoefficient : 0 <
        a.orderSequence.entryOrZero (P.pivot + 1) +
          a.orderSequence.entryOrZero (P.pivot + 2) -
          b.orderSequence.entryOrZero (P.pivot - 1) -
          b.orderSequence.entryOrZero P.pivot := by
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
          (show idx.val - 2 < n + 2 by omega)).symm
      have hbCurrent :
          b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
            b.orderSequence.entryOrZero (idx.val - 1) :=
        (BeliOrderSequence.entryOrZero_of_lt b.orderSequence
          (show idx.val - 1 < n + 2 by omega)).symm
      rw [haCurrent, haNext, hbPrevious, hbCurrent]
      have hidxNext : idx.val + 1 = P.pivot + 2 := by
        rw [hidxVal]
      have hidxPrevious : idx.val - 2 = P.pivot - 1 := by
        rw [hidxVal]
        omega
      rw [hidxNext, hidxPrevious, hidxPred, hidxVal]
      exact hcoefficient
    have hdefectNonneg := a.truncatedPrefixDefect_nonneg
      (alphaV := alpha) (alphaW := alpha) b 1
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
    ((a.orderSequence.entryOrZero P.pivot -
      a.orderSequence.entryOrZero (P.pivot + 1) + 1 : Int) : ℚ)
  have hsourceLocal (j : Nat) (hj : j + 2 ≤ P.pivot)
      (heven : Even j) :
      (cutoff : WithTop ℚ) <
        a.truncatedPrefixDefect a (-1) j (j + 2) := by
    let jf : Fin (n + 1) := ⟨j, by omega⟩
    have hjp : jf ≤ p := by
      change j ≤ P.pivot
      omega
    have hbound := a.alpha_le_order_sub_add_cappedAdjacent hjp
    by_contra hnotCut
    have hlocalLe : a.truncatedPrefixDefect a (-1) j (j + 2) ≤
        (cutoff : WithTop ℚ) := le_of_not_gt hnotCut
    have hsourceJ := hsourceEven j (by omega) heven
    have hpSucc : a.order p.succ =
        a.orderSequence.entryOrZero (P.pivot + 1) := by
      rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        hpivotNextBound]
      apply congrArg a.order
      apply Fin.ext
      rfl
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
  have htargetLocal (j : Nat) (hj : j + 2 ≤ P.pivot)
      (heven : Even j) :
      (cutoff : WithTop ℚ) <
        b.truncatedPrefixDefect b (-1) j (j + 2) := by
    let jf : Fin (n + 1) := ⟨j, by omega⟩
    have hpairParity : Even (D.anchor - j) := by
      rcases hanchorEven with ⟨d, hd⟩
      rcases heven with ⟨e, he⟩
      exact ⟨d - e, by omega⟩
    have hpair := D.profile.leftPairEq j (by omega) hpairParity
    have hsourceJ := hsourceEven j (by omega) heven
    have htargetJ := htargetEven j (by omega) heven
    have htargetNext : b.orderSequence.entryOrZero (j + 1) =
        a.orderSequence.entryOrZero (j + 1) - 1 := by
      omega
    have hsourceNextLt := P.earlier_next_lt j (by omega) heven
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
            b.orderSequence.entryOrZero P.pivot +
            (a.orderSequence.entryOrZero P.pivot -
              a.orderSequence.entryOrZero (P.pivot + 1) + 1) ≤ -1 by
        omega)
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
        a.truncatedPrefixDefect a (-1) P.pivot (P.pivot + 2) := by
    have hbound := a.alpha_le_orderGap_add_cappedAdjacent p
    by_contra hnotCut
    have hlocalLe :
        a.truncatedPrefixDefect a (-1) P.pivot (P.pivot + 2) ≤
          (cutoff : WithTop ℚ) := le_of_not_gt hnotCut
    have hpSucc : a.order p.succ =
        a.orderSequence.entryOrZero (P.pivot + 1) := by
      rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        hpivotNextBound]
      apply congrArg a.order
      apply Fin.ext
      rfl
    have hpCast : a.order p.castSucc =
        a.orderSequence.entryOrZero P.pivot := by
      rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        hpivotEntryBound]
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
              a.truncatedPrefixDefect a (-1) P.pivot
                (P.pivot + 2)) := by
          simpa only [p] using hbound
        _ ≤ ((((a.order p.succ - a.order p.castSucc : Int) : ℚ) :
              WithTop ℚ) + cutoff) := add_le_add_right hlocalLe _
        _ = 1 := by exact_mod_cast hformula
    have halphaLe : a.alphaValue p ≤ 1 := by exact_mod_cast halphaTop
    linarith
  have hcommon (k : Nat) (hk : k ≤ P.pivot) (heven : Even k) :
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
  have hcentralCommon := hcommon P.pivot le_rfl P.pivot_even
  have hcentralReverse : (cutoff : WithTop ℚ) <
      a.truncatedPrefixDefect a (-1) (P.pivot + 2) P.pivot := by
    rw [a.truncatedPrefixDefect_comm a (-1) (P.pivot + 2) P.pivot]
    exact hcentralSourceLocal
  have hdom := a.truncatedPrefixDefect_domination a b
    (-1) 1 (P.pivot + 2) P.pivot P.pivot
  have hcritical : (cutoff : WithTop ℚ) <
      a.truncatedPrefixDefect b (-1) (P.pivot + 2) P.pivot :=
    (lt_min hcentralReverse hcentralCommon).trans_le (by
      simpa using hdom)
  have hprimaryFalse
      (hprimary : a.representationPrimaryDefect b idx ≤ 0) : False := by
    have hprimaryDefectLe :
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
          a.orderSequence.entryOrZero (P.pivot + 1) := by
        rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
          hpivotNextBound]
        apply congrArg a.order
        apply Fin.ext
        exact hidxVal
      have hleftOrder :
          b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
            b.orderSequence.entryOrZero P.pivot := by
        rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
          hpivotEntryBound]
        apply congrArg b.order
        apply Fin.ext
        exact hidxPred
      rw [hrightOrder, hleftOrder] at hprimary
      have hpivotBoundaryQ :
          (b.orderSequence.entryOrZero P.pivot : ℚ) =
            (a.orderSequence.entryOrZero P.pivot : ℚ) + 1 := by
        exact_mod_cast hpivotBoundary
      simp only [cutoff]
      push_cast
      linarith [hpivotBoundaryQ]
    have hindexOne : idx.val + 1 = P.pivot + 2 := by
      rw [hidxVal]
    rw [hindexOne, hidxPred] at hprimaryDefectLe
    exact (not_le_of_gt hcritical) hprimaryDefectLe
  have hzeroDefect := a.truncatedPrefixDefect_eq_zero_of_prefixSum_succ
    (alphaV := alpha) (alphaW := alpha) b idx.val
    (by simp only [idx]; omega) (by simp only [idx]; omega) hsum
  have hA := hdefect idx
  rw [hzeroDefect] at hA
  rw [a.coe_representationAlphaValue b idx,
    a.representationAlpha_eq_min_halfGap_prime b idx] at hA
  rcases min_le_iff.mp hA with hhalf | hprime
  · unfold representationHalfGap at hhalf
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
          (show idx.val - 1 < n + 2 by rw [hidxPred]; omega)).symm
      have haEntry :
          a.order ⟨idx.val - 1, by have := idx.lt_large; omega⟩ =
            a.orderSequence.entryOrZero (idx.val - 1) :=
        (BeliOrderSequence.entryOrZero_of_lt a.orderSequence
          (show idx.val - 1 < n + 2 by rw [hidxPred]; omega)).symm
      rw [hbEntry, haEntry, hidxPred]
      exact hpivotBoundary
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
      · exact hprimaryFalse hprimary
      · exact (not_le_of_gt (hsecondaryPos hi)) hsecondary
    · rw [a.representationAlphaPrime_eq_primary_of_not_interior b idx hi]
        at hprime
      exact hprimaryFalse hprime

end BONG.GoodBONG

end Bong
