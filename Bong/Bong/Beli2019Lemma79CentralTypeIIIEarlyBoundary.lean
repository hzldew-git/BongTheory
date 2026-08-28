/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTypeIIEarly
import Bong.Bong.Beli2019Lemma78TargetPropagationLocal
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapCaseSixSecondParity
import Bong.Bong.Beli2019CappedDominationOrderBound
import Bong.Bong.Beli2019Lemma79RightTailGapOneParity

/-!
# Beli (2019), Lemma 7.9(iii), case 8

This file excludes the second Lemma 2.18 alternative at the type-III
transition boundary.  The overlapping central gap has an odd mixed prefix
and hence zero defect.  In the nonoverlapping branch Lemma 7.8 identifies
the target alternating prefix; capped domination then forces a negative odd
gap in a good BONG, which is impossible.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- In the overlapping type-III branch, the shifted target prefix has odd
order while the comparison prefix has even order. -/
theorem lemma79Central_typeIIIEarly_overlap_boundary_currentDefect_eq_zero
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hoverlap : a.orderGap ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val = D.outer.transition.lastZero + 1)
    (htrigger : b.centralAlphaTrigger c i) :
    b.centralCurrentDefect c i = 0 := by
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val, by
      have := i.one_lt
      omega, i.lt_large, i.lt_large.le⟩
  have hright : D.outer.transition.firstTwo - 1 ≤ idx.val := by
    dsimp only [idx]
    rw [D.adjacent]
    omega
  have hthroughLast : idx.val ≤ D.outer.last := by
    dsimp only [idx]
    have hright := D.outer.right_le_last
    rw [D.adjacent] at hright
    omega
  have heven : Even
      (idx.val - (D.outer.transition.firstTwo - 1)) := by
    refine ⟨0, ?_⟩
    dsimp only [idx]
    rw [D.adjacent]
    omega
  have htargetOdd :=
    beli2019Lemma79_typeIII_overlap_caseSix_targetPrefix_succ_odd
      a b D hfirst hoverlap idx hright hthroughLast heven
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have htargetCurrent :=
    beli2019Lemma79_typeIII_overlap_caseSix_targetCurrent_eq_reference_add_one
      a b D hoverlap idx hright hthroughLast heven
  have htargetCurrentOrder : b.order ⟨i.val, i.lt_large⟩ = T + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order]
    simpa only [idx, T] using htargetCurrent
  have hcCurrent : c.orderSequence.entryOrZero (i.val - 2) ≤ T := by
    have hcross := htrigger.1
    rw [htargetCurrentOrder] at hcross
    rw [c.orderSequence_entryOrZero_eq_order ⟨i.val - 2, by
      have := i.lt_large
      omega⟩]
    omega
  have hfirstLower :=
    beli2019Lemma79_typeIII_overlap_reference_le_thirdFirst
      a b c D hfirst hnorm
  have hcParityRaw :=
    c.prefixSum_modEq_mul_of_current_le_reference_le_first
      T (i.val - 2) (by
        have := i.lt_large
        omega) (by simpa only [T] using hfirstLower) hcCurrent
  have hcParity : Int.ModEq 2
      (c.orderSequence.prefixSum (i.val - 1))
      (((i.val - 1 : Nat) : Int) * T) := by
    simpa only [show i.val - 2 + 1 = i.val - 1 by
      have := i.one_lt
      omega] using hcParityRaw
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hreferenceEven : Even (((i.val - 1 : Nat) : Int) * T) := by
    rcases hleftEven with ⟨d, hd⟩
    have hlength : i.val - 1 = d + d := by omega
    refine ⟨(d : Int) * T, ?_⟩
    rw [hlength]
    push_cast
    ring
  have hcEven : Even (c.orderSequence.prefixSum (i.val - 1)) :=
    caseSix_even_of_modEq_two_of_even hcParity hreferenceEven
  have hsumOdd : Odd
      (b.orderSequence.prefixSum (idx.val + 1) +
        c.orderSequence.prefixSum (idx.val - 1)) := by
    rcases htargetOdd with ⟨d, hd⟩
    rcases hcEven with ⟨e, he⟩
    exact ⟨d + e, by
      dsimp only [idx] at hd he ⊢
      omega⟩
  have hproductOdd := signed_shifted_prefixProduct_order_odd_of_sum_odd
    b c idx hsumOdd
  unfold centralCurrentDefect
  apply truncatedPrefixDefect_eq_zero_of_odd_order_general
  simpa only [idx] using hproductOdd

/-- The central type-III source gap is nonpositive in the nonoverlapping
branch. -/
theorem lemma79Central_typeIII_nonoverlap_centralGap_nonpositive
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ ≠ 1) :
    a.orderGap ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ ≤ 0 := by
  let center : Fin (n + 1) := ⟨D.outer.transition.lastZero, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  have halpha := a.beli2019Lemma69_i_typeIII_local b D hdefectAB
  have hgapLe := a.orderGap_le_one_of_alphaValue_le_one center (by
    simpa only [center] using halpha)
  have hne : a.orderGap center ≠ 1 := by
    simpa only [center] using hnotOverlap
  have : a.orderGap center ≤ 0 := by omega
  simpa only [center] using this

/-- At the first even target prefix after the type-III center, Lemma 7.8
has a local form regardless of whether the unequal interval ends before,
at, or after the prefix. -/
theorem lemma79Central_typeIII_nonoverlap_centerTargetPrefixDefect
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
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
        omega⟩) :
    b.truncatedPrefixDefect b
        ((-1) ^ ((D.outer.transition.lastZero + 2) / 2)) 0
        (D.outer.transition.lastZero + 2) =
      (((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ) :
        WithTop ℚ) := by
  let length := D.outer.transition.lastZero + 2
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hlengthEven : Even length := by
    rcases hleftEven with ⟨d, hd⟩
    exact ⟨d + 1, by simp only [length]; omega⟩
  have hlengthStart : D.outer.transition.lastZero + 2 ≤ length :=
    le_rfl
  by_cases hbefore : length < D.outer.last
  · have hraw := a.beli2019Lemma78_targetPrefixDefect_beforeLast_local
      b D hfirst horderAB hdefectAB htotal hnotOverlap hinitial
        length hlengthStart hbefore hlengthEven
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order] at hraw
    simpa only [length] using hraw
  · have hlast : D.outer.last = D.outer.transition.lastZero + 1 := by
      have hright := D.outer.right_le_last
      have hrightEven := D.outer.right_even_distance
      rw [D.adjacent] at hright hrightEven
      rcases hrightEven with ⟨d, hd⟩
      simp only [length] at hbefore
      omega
    by_cases hfull : D.outer.last = n + 1
    · have hlength : length = n + 2 := by
        simp only [length]
        omega
      have hlength' : D.outer.transition.lastZero + 2 = n + 2 := by
        simpa only [length] using hlength
      have hsource := a.beli2019Lemma78_sourcePrefixDefect_local
        b D hfirst hdefectAB hnotOverlap hinitial length hlengthStart
          (by simp only [length]; omega) hlengthEven
      have hsource' :
          a.truncatedPrefixDefect a ((-1) ^ ((n + 2) / 2)) 0 (n + 2) =
            (((b.order ⟨D.outer.transition.lastZero, by
                    have hbound := D.outer.transition.firstTwo_le_rank
                    rw [D.adjacent] at hbound
                    omega⟩ -
                a.order ⟨D.outer.transition.lastZero + 1, by
                    have hbound := D.outer.transition.firstTwo_le_rank
                    rw [D.adjacent] at hbound
                    omega⟩ : Int) : ℚ) : WithTop ℚ) := by
        simpa only [hlength] using hsource
      have hself := a.truncatedPrefixDefect_self_full_eq
        b ((-1) ^ ((n + 2) / 2))
      rw [← b.orderSequence_entryOrZero_eq_order,
        ← a.orderSequence_entryOrZero_eq_order] at hsource'
      simpa only [hlength'] using hself.trans hsource'
    · have hproper : D.outer.last < n + 1 := by
        have hbound := D.outer.lastDifference.bound
        omega
      have hraw := a.beli2019Lemma78_targetPrefixDefect_firstCommon_local
        b D hfirst hdefectAB hnotOverlap hinitial hproper (by
          simpa only [hlast] using hlengthEven)
      rw [← b.orderSequence_entryOrZero_eq_order,
        ← a.orderSequence_entryOrZero_eq_order] at hraw
      simpa only [length, hlast] using hraw

set_option maxHeartbeats 6000000 in
/-- At the type-III transition boundary, the second Lemma 2.18 alternative
is impossible in the nonoverlapping branch.  The target prefix first
transports the central coefficient to a self-prefix of the comparison BONG.
A capped-domination pair then has a negative odd order gap, contradicting
the parity law for a good BONG. -/
theorem lemma79Central_typeIIIEarly_nonoverlap_boundary_second_not
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
    (hboundary : i.val = D.outer.transition.lastZero + 1)
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
  have hleftEven : Even left := by
    simpa only [left] using D.outer.left_even_of_first_eq_zero hfirst
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
  have htargetCenterAlpha :
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ = 1 := by
    simpa only [hboundary, left, show left + 1 - 1 = left by omega] using
      hdata.2.1
  have hcap : b.prefixAlphaCap i.val = ((1 : ℚ) : WithTop ℚ) := by
    rw [b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large, htargetCenterAlpha]
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
    a.lemma79Central_typeIII_nonoverlap_centerTargetPrefixDefect
      b D hfirst horderAB hdefectAB htotal hnotOverlap hinitial
  have htargetPrefix' : b.truncatedPrefixDefect b
      ((-1) ^ ((left + 2) / 2)) 0 (left + 2) =
        ((C : ℚ) : WithTop ℚ) := by
    simpa only [left, C] using htargetPrefix
  have hseparation : b.truncatedPrefixDefect b
      ((-1) ^ ((left + 2) / 2)) 0 (left + 2) <
        b.truncatedPrefixDefect c (-1) (left + 2) left := by
    calc
      b.truncatedPrefixDefect b ((-1) ^ ((left + 2) / 2)) 0 (left + 2) =
          ((C : ℚ) : WithTop ℚ) := htargetPrefix'
      _ < b.centralCurrentDefect c i := hmixed
      _ = b.truncatedPrefixDefect c (-1) (left + 2) left := by
        simp only [centralCurrentDefect, hboundary, left,
          show left + 1 + 1 = left + 2 by omega,
          show left + 1 - 1 = left by omega]
  have hsharp := b.truncatedPrefixDefect_mul_eq_left_of_lt_right
    b c ((-1) ^ ((left + 2) / 2)) (-1) 0 (left + 2) left hseparation
  have hexponent : (left + 2) / 2 = left / 2 + 1 := by
    rcases hleftEven with ⟨d, hd⟩
    omega
  have hscalar : ((-1 : Kˣ) ^ ((left + 2) / 2)) * (-1) =
      (-1) ^ (left / 2) := by
    rw [hexponent, pow_succ, mul_assoc]
    norm_num
  have hzeroLeft := b.truncatedPrefixDefect_zero_left_eq_self
    c ((-1) ^ (left / 2)) left
  rw [hscalar, hzeroLeft, htargetPrefix'] at hsharp
  have hthird : c.truncatedPrefixDefect c ((-1) ^ (left / 2)) 0 left =
      ((C : ℚ) : WithTop ℚ) := by
    exact hsharp
  have hleftPos : 0 < left := by
    have := i.one_lt
    omega
  rcases c.exists_even_capped_domination_order_bound
      left hleftPos (by omega) hleftEven with
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
  have hoddDistance : Even ((left - 1) - (j.val + 1)) := by
    rcases hleftEven with ⟨d, hd⟩
    rcases hjEven with ⟨e, he⟩
    exact ⟨d - e - 1, by omega⟩
  have hoddMonotoneRaw := c.orderSequence.entryOrZero_le_of_evenGap
    (j.val + 1) (left - 1) (by omega) (by omega) hoddDistance
  have hoddMonotone : c.order j.succ ≤
      c.order ⟨left - 1, by omega⟩ := by
    rw [← c.orderSequence_entryOrZero_eq_order j.succ,
      ← c.orderSequence_entryOrZero_eq_order ⟨left - 1, by omega⟩]
    simpa only [Fin.val_succ] using hoddMonotoneRaw
  have hrightIndex : D.outer.transition.firstTwo - 1 = left + 1 := by
    simp only [left]
    rw [D.adjacent]
    omega
  have hrightBoundary : b.orderSequence.entryOrZero (left + 1) =
      a.orderSequence.entryOrZero (left + 1) + 1 := by
    have h := D.outer.transition.rightBoundary
    rw [hrightIndex] at h
    exact h
  have hcross : c.order ⟨left - 1, by omega⟩ <
      b.order ⟨left + 1, hrightBound⟩ := by
    simpa only [hboundary, left,
      show left + 1 - 2 = left - 1 by omega] using htrigger.1
  have hrightOrder : b.order ⟨left + 1, hrightBound⟩ =
      a.orderSequence.entryOrZero (left + 1) + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order]
    exact hrightBoundary
  rw [hrightOrder] at hcross
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

/-- In the overlapping type-III branch the current mixed defect vanishes,
while the target alpha at the boundary is at most one.  Hence the second
Lemma 2.18 alternative cannot exceed `2e`. -/
theorem lemma79Central_typeIIIEarly_overlap_boundary_second_not
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
    (hoverlap : a.orderGap ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val = D.outer.transition.lastZero + 1)
    (htrigger : b.centralAlphaTrigger c i)
    (hcurrent :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.centralCurrentDefect c i) : False := by
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have htargetAlpha := a.beli2019Lemma69_i_typeIII_targetLeftTail_local
    b D hfirst horderAB hdefectAB htotal D.outer.transition.lastZero
      le_rfl hleftEven
  have hcurrentZero :=
    a.lemma79Central_typeIIIEarly_overlap_boundary_currentDefect_eq_zero
      b c D hfirst hoverlap hnorm i hboundary htrigger
  have hcap : b.prefixAlphaCap i.val =
      (b.alphaValue ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ : WithTop ℚ) := by
    rw [b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large]
    congr 2
    apply Fin.ext
    simp only [hboundary]
    omega
  rw [hcap, hcurrentZero, add_zero] at hcurrent
  have hcurrentQ : 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ := by
    exact_mod_cast hcurrent
  have heOneNat : 1 ≤ ramificationIndex K :=
    ramificationIndex_pos (K := K)
  have heOne : (1 : ℚ) ≤ ramificationIndex K := by
    exact_mod_cast heOneNat
  linarith

/-- Complete exclusion of the second Lemma 2.18 alternative at the first
type-III transition boundary. -/
theorem lemma79Central_typeIIIEarly_boundary_second_not
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
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val = D.outer.transition.lastZero + 1)
    (htrigger : b.centralAlphaTrigger c i)
    (hcurrent :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.centralCurrentDefect c i) : False := by
  by_cases hoverlap : a.orderGap ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ = 1
  · exact a.lemma79Central_typeIIIEarly_overlap_boundary_second_not
      b c D hfirst horderAB hdefectAB htotal hoverlap hnorm i hboundary
        htrigger hcurrent
  · exact a.lemma79Central_typeIIIEarly_nonoverlap_boundary_second_not
      b c D hfirst horderAB hdefectAB htotal hoverlap hinitial hnorm i
        hboundary htrigger hcurrent

end BONG.GoodBONG

end Bong
