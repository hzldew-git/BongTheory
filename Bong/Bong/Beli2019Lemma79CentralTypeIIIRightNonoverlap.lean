/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTypeIIIRightOverlap

/-!
# Beli (2019), Lemma 7.9(iii), case 9: nonoverlapping type III

Lemma 7.8 identifies the final even target self-prefix defect with the central
coefficient.  A hypothetical second alternative transfers that coefficient
to the comparison self-prefix.  Capped domination then produces a negative
odd order gap, contradicting the parity law for a good BONG.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 6000000 in
-- The proof joins the proper-suffix and full-rank endpoint forms of Lemma 7.8.
/-- Lemma 7.8 at the first common coordinate after a nonoverlapping type-III
difference interval. -/
theorem lemma79Central_typeIII_nonoverlap_terminalTargetPrefixDefect
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩) :
    b.truncatedPrefixDefect b
        ((-1) ^ ((D.outer.last + 1) / 2)) 0 (D.outer.last + 1) =
      (((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ) :
        WithTop ℚ) := by
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hbaseLast := D.outer.right_le_last
  have hrecover := Nat.sub_add_cancel hbaseLast
  have hlengthEven : Even (D.outer.last + 1) := by
    rcases hleftEven with ⟨d, hd⟩
    rcases D.outer.right_even_distance with ⟨e, he⟩
    rw [D.adjacent] at hrecover he
    exact ⟨d + e + 1, by omega⟩
  let leftFin : Fin (n + 2) := ⟨D.outer.transition.lastZero, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  let nextFin : Fin (n + 2) := ⟨D.outer.transition.lastZero + 1, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  by_cases hproper : D.outer.last < n + 1
  · have hraw := a.beli2019Lemma78_targetPrefixDefect_firstCommon_local
      b D hfirst hdefect hnotOverlap hinitial hproper hlengthEven
    calc
      b.truncatedPrefixDefect b
          ((-1) ^ ((D.outer.last + 1) / 2)) 0 (D.outer.last + 1) =
          ((((b.order leftFin - a.order nextFin : Int) : ℚ) :
            WithTop ℚ)) := by simpa only [leftFin, nextFin] using hraw
      _ = (((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ) :
            WithTop ℚ) := by
        rw [b.orderSequence_entryOrZero_eq_order leftFin,
          a.orderSequence_entryOrZero_eq_order nextFin]
  · have hlastBound := D.outer.lastDifference.bound
    have hlast : D.outer.last = n + 1 := by omega
    have hraw := a.beli2019Lemma78_targetPrefixDefect
      b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
        (D.outer.last + 1) (by
          have hright := D.outer.right_le_last
          rw [D.adjacent] at hright
          omega) le_rfl hlengthEven
    calc
      b.truncatedPrefixDefect b
          ((-1) ^ ((D.outer.last + 1) / 2)) 0 (D.outer.last + 1) =
          ((((b.order leftFin - a.order nextFin : Int) : ℚ) :
            WithTop ℚ)) := by simpa only [leftFin, nextFin] using hraw
      _ = (((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ) :
            WithTop ℚ) := by
        rw [b.orderSequence_entryOrZero_eq_order leftFin,
          a.orderSequence_entryOrZero_eq_order nextFin]

set_option maxHeartbeats 8000000 in
-- This is the terminal form of the paper's domination argument in case 9.
/-- The terminal second alternative is impossible in the nonoverlapping
type-III branch. -/
theorem lemma79Central_typeIIIRight_nonoverlap_terminal_second_not
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hiLast : i.val = D.outer.last)
    (htrigger : b.centralAlphaTrigger c i)
    (hcurrent :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.centralCurrentDefect c i) : False := by
  let left := D.outer.transition.lastZero
  let center : Fin (n + 1) := ⟨left, by
    have hbound := D.outer.transition.firstTwo_le_rank
    simp only [left]
    rw [D.adjacent] at hbound
    omega⟩
  let g : Int := a.orderGap center
  let C : Int := b.orderSequence.entryOrZero left -
    a.orderSequence.entryOrZero (left + 1)
  let length := i.val + 1
  let short := i.val - 1
  have hleftEven : Even left := by
    simpa only [left] using D.outer.left_even_of_first_eq_zero hfirst
  have hbaseI : D.outer.transition.firstTwo - 1 ≤ i.val := by omega
  have hiDistanceEven : Even
      (i.val - (D.outer.transition.firstTwo - 1)) := by
    simpa only [hiLast] using D.outer.right_even_distance
  have hbaseRecover := Nat.sub_add_cancel hbaseI
  have hlengthEven : Even length := by
    rcases hleftEven with ⟨d, hd⟩
    rcases hiDistanceEven with ⟨e, he⟩
    simp only [length]
    rw [D.adjacent] at hbaseRecover he
    exact ⟨d + e + 1, by omega⟩
  have hshortEven : Even short := by
    rcases hlengthEven with ⟨d, hd⟩
    exact ⟨d - 1, by simp only [length, short] at hd ⊢; omega⟩
  have hgapNonpositive : g ≤ 0 := by
    simpa only [g, center, left] using
      a.lemma79Central_typeIII_nonoverlap_centralGap_nonpositive
        b D hfirst hdefectAB hnotOverlap
  have hgapEven : Even g := by
    simpa only [g, center, left] using
      a.lemma78_typeIII_centralGap_even b D hfirst hdefectAB hnotOverlap
  have hleftBound : left < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    simp only [left]
    rw [D.adjacent] at hbound
    omega
  have hrightBound : left + 1 < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    simp only [left]
    rw [D.adjacent] at hbound
    omega
  have hgapEntries : g =
      a.orderSequence.entryOrZero (left + 1) -
        a.orderSequence.entryOrZero left := by
    dsimp only [g]
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence hrightBound,
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hleftBound]
    rfl
  have hleftBoundary : b.orderSequence.entryOrZero left =
      a.orderSequence.entryOrZero left + 1 := by
    simpa only [left] using D.outer.transition.leftBoundary
  have hCFormula : C = 1 - g := by
    dsimp only [C]
    rw [hleftBoundary, hgapEntries]
    ring
  have hdata := a.beli2019Lemma78_alphas_and_gap_local
    b D hfirst horderAB hdefectAB htotal hnotOverlap hinitial
  have hgapBound : 3 - 2 * (ramificationIndex K : Int) ≤ g + 1 := by
    simpa only [g, center, left] using hdata.2.2
  have hCUpper : C ≤ 2 * (ramificationIndex K : Int) - 1 := by
    rw [hCFormula]
    omega
  have htargetAlpha :=
    a.lemma79Central_typeIIIRight_terminal_currentAlpha_eq_one_of_center
      b D horderAB hdefectAB htotal hdata.2.1 i hright hiLast
  have hcap : b.prefixAlphaCap i.val = ((1 : ℚ) : WithTop ℚ) := by
    rw [b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large, htargetAlpha]
  have hmixed : ((C : ℚ) : WithTop ℚ) <
      b.centralCurrentDefect c i := by
    have hcurrent' := hcurrent
    rw [hcap] at hcurrent'
    let X := b.centralCurrentDefect c i
    change (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
      ((1 : ℚ) : WithTop ℚ) + X at hcurrent'
    change ((C : ℚ) : WithTop ℚ) < X
    by_cases htop : X = ⊤
    · rw [htop]
      exact WithTop.coe_lt_top _
    · rw [← WithTop.coe_untop X htop] at hcurrent' ⊢
      norm_cast at hcurrent' ⊢
      push_cast at hcurrent' ⊢
      have hCUpperQ : (C : ℚ) ≤
          2 * (ramificationIndex K : ℚ) - 1 := by
        exact_mod_cast hCUpper
      linarith
  have htargetPrefix :=
    a.lemma79Central_typeIII_nonoverlap_terminalTargetPrefixDefect
      b D hfirst horderAB hdefectAB htotal hnotOverlap hinitial
  have htargetPrefix' : b.truncatedPrefixDefect b
      ((-1) ^ (length / 2)) 0 length = ((C : ℚ) : WithTop ℚ) := by
    simpa only [length, hiLast, C, left] using htargetPrefix
  have hseparation : b.truncatedPrefixDefect b
      ((-1) ^ (length / 2)) 0 length <
        b.truncatedPrefixDefect c (-1) length short := by
    calc
      b.truncatedPrefixDefect b ((-1) ^ (length / 2)) 0 length =
          ((C : ℚ) : WithTop ℚ) := htargetPrefix'
      _ < b.centralCurrentDefect c i := hmixed
      _ = b.truncatedPrefixDefect c (-1) length short := by
        simp only [centralCurrentDefect, length, short]
  have hsharp := b.truncatedPrefixDefect_mul_eq_left_of_lt_right
    b c ((-1) ^ (length / 2)) (-1) 0 length short hseparation
  have hlengthShort : length = short + 2 := by
    simp only [length, short]
    have := i.one_lt
    omega
  have hexponent : length / 2 = short / 2 + 1 := by
    rcases hshortEven with ⟨d, hd⟩
    omega
  have hscalar : ((-1 : Kˣ) ^ (length / 2)) * (-1) =
      (-1) ^ (short / 2) := by
    rw [hexponent, pow_succ, mul_assoc]
    norm_num
  have hzeroLeft := b.truncatedPrefixDefect_zero_left_eq_self
    c ((-1) ^ (short / 2)) short
  rw [hscalar, hzeroLeft, htargetPrefix'] at hsharp
  have hthird : c.truncatedPrefixDefect c ((-1) ^ (short / 2)) 0 short =
      ((C : ℚ) : WithTop ℚ) := hsharp
  have hshortPos : 0 < short := by
    simp only [short]
    exact Nat.sub_pos_of_lt i.one_lt
  have hshortBound : short ≤ n + 2 := by
    simp only [short]
    have hiBound := i.lt_large
    omega
  rcases c.exists_even_capped_domination_order_bound
      short hshortPos hshortBound hshortEven with
    ⟨j, hjEven, hjlt, hjDefect, _hjOrder⟩
  have hjDefect' : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) ≤
      ((C : ℚ) : WithTop ℚ) := by
    rw [← hthird]
    exact hjDefect
  have hlocalTop :=
    (c.order_sub_add_alpha_le_cappedAdjacent j).trans hjDefect'
  have hlocalQ :
      ((c.order j.castSucc - c.order j.succ : Int) : ℚ) +
          c.alphaValue j ≤ (C : ℚ) :=
    WithTop.coe_le_coe.mp hlocalTop
  have halphaNonnegative := (c.alpha_p2 j).1
  have hlocalLowerQ : ((g - 1 : Int) : ℚ) ≤
      ((c.order j.succ - c.order j.castSucc : Int) : ℚ) := by
    rw [hCFormula] at hlocalQ
    push_cast at hlocalQ ⊢
    linarith
  have hlocalLower : g - 1 ≤
      c.order j.succ - c.order j.castSucc := by
    exact_mod_cast hlocalLowerQ
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstLower : a.orderSequence.entryOrZero 0 + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    calc
      a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
      _ ≤ c.order 0 := hnormOrder
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
  have hsourceLeft := D.outer.source_leftEven_eq_first
    hfirst left le_rfl hleftEven
  have hthirdMonotone := c.orderSequence.entryOrZero_le_of_evenGap
    0 j.val (Nat.zero_le _) j.castSucc.isLt hjEven
  have hjLower : a.orderSequence.entryOrZero left + 1 ≤
      c.order j.castSucc := by
    rw [hsourceLeft]
    calc
      a.orderSequence.entryOrZero 0 + 1 ≤
          c.orderSequence.entryOrZero 0 := hfirstLower
      _ ≤ c.orderSequence.entryOrZero j.val := hthirdMonotone
      _ = c.order j.castSucc :=
        c.orderSequence_entryOrZero_eq_order j.castSucc
  have hoddDistance : Even ((short - 1) - (j.val + 1)) := by
    rcases hshortEven with ⟨d, hd⟩
    rcases hjEven with ⟨e, he⟩
    exact ⟨d - e - 1, by omega⟩
  have hjSucc_le_shortPred : j.val + 1 ≤ short - 1 := by
    omega
  have hshortPredBound : short - 1 < n + 2 := by
    omega
  let shortPred : Fin (n + 2) := ⟨short - 1, hshortPredBound⟩
  have hoddMonotoneRaw := c.orderSequence.entryOrZero_le_of_evenGap
    (j.val + 1) (short - 1) hjSucc_le_shortPred hshortPredBound hoddDistance
  have hoddMonotone : c.order j.succ ≤
      c.order shortPred := by
    rw [← c.orderSequence_entryOrZero_eq_order j.succ,
      ← c.orderSequence_entryOrZero_eq_order shortPred]
    simpa only [Fin.val_succ] using hoddMonotoneRaw
  have htargetCurrent := D.outer.target_rightEven_eq_boundary
    i.val hbaseI (by omega) hiDistanceEven
  have hrightIndex : D.outer.transition.firstTwo - 1 = left + 1 := by
    simp only [left]
    rw [D.adjacent]
    omega
  have hrightBoundary : b.orderSequence.entryOrZero (left + 1) =
      a.orderSequence.entryOrZero (left + 1) + 1 := by
    have h := D.outer.transition.rightBoundary
    rw [hrightIndex] at h
    exact h
  have htargetOrder : b.order ⟨i.val, i.lt_large⟩ =
      a.orderSequence.entryOrZero (left + 1) + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order]
    exact htargetCurrent.trans (by simpa only [hrightIndex] using hrightBoundary)
  have hcross : c.order shortPred <
      b.order ⟨i.val, i.lt_large⟩ := by
    simpa only [shortPred, short, show i.val - 1 - 1 = i.val - 2 by
      have := i.one_lt
      omega] using htrigger.1
  rw [htargetOrder] at hcross
  have hlocalUpper : c.order j.succ - c.order j.castSucc ≤ g - 1 := by
    omega
  have hlocalEq : c.order j.succ - c.order j.castSucc = g - 1 := by
    omega
  have hcomparisonGap : c.orderGap j = g - 1 := by
    unfold orderGap
    exact hlocalEq
  have hnegative : c.orderGap j < 0 := by
    rw [hcomparisonGap]
    omega
  have hcomparisonEven := c.orderGap_even_of_negative j hnegative
  have hcomparisonOdd : Odd (c.orderGap j) := by
    rw [hcomparisonGap]
    rcases hgapEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  exact (Int.not_even_iff_odd.mpr hcomparisonOdd) hcomparisonEven

end BONG.GoodBONG

end Bong
