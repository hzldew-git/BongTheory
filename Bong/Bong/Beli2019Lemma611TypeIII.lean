/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma611TypeII
import Bong.Bong.Beli2019Lemma69TypeIII
import Bong.Bong.Beli2019Lemma73

/-!
# Beli (2019), Lemma 6.11: the nonoverlapping type-III parity profile

The paper treats a pair satisfying both types II and III as type II.  In the
remaining type-III case the central gap is not one.  Lemma 6.9 gives alpha at
most one there; the general alpha lower bound therefore makes the integral
gap at most one, hence nonpositive.  Its parity is then even by the good-BONG
gap law.  Lemma 6.6 propagates this parity through both outer intervals.
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

/-- The alpha bound used in Lemma 6.9 forces the integral order gap to be at
most one. -/
theorem orderGap_le_one_of_alphaValue_le_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (halpha : b.alphaValue i ≤ 1) : b.orderGap i ≤ 1 := by
  have hePos := ramificationIndex_pos (K := K)
  have halphaTwo :
      b.alphaValue i ≤ 2 * (ramificationIndex K : ℚ) := by
    have hone : (1 : ℚ) ≤ 2 * (ramificationIndex K : ℚ) := by
      exact_mod_cast (show (1 : Int) ≤
        2 * (ramificationIndex K : Int) by omega)
    exact halpha.trans hone
  have hgapTwo : b.orderGap i ≤
      2 * (ramificationIndex K : Int) :=
    (b.alphaValue_le_twoE_iff_orderGap_le_twoE i).mp halphaTwo
  have hgapAlpha := (b.beli2009Lemma27_iii i hgapTwo).1
  have hgapOneQ : (b.orderGap i : ℚ) ≤ 1 := hgapAlpha.trans halpha
  exact_mod_cast hgapOneQ

/-- The entrywise parity data from Lemma 6.11(iii). -/
structure Lemma611TypeIIIConsequences
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeIII a b) : Prop where
  central_gap_even : Even
    (a.orderSequence.entryOrZero (D.outer.transition.firstTwo - 1) -
      a.orderSequence.entryOrZero D.outer.transition.lastZero)
  source (k : Nat) (hk : k ≤ D.outer.last) :
    Int.ModEq 2 (a.orderSequence.entryOrZero k)
      (a.orderSequence.entryOrZero D.outer.transition.lastZero)
  target (k : Nat) (hk : k ≤ D.outer.last) :
    Int.ModEq 2 (b.orderSequence.entryOrZero k)
      (b.orderSequence.entryOrZero
        (D.outer.transition.firstTwo - 1))

/-- Beli (2019), Lemma 6.11(iii), for type III but not the overlapping
type-II/III case.  The alpha hypothesis is precisely the boundary conclusion
of Lemma 6.9(i). -/
theorem lemma611TypeIII
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (halpha : a.alphaValue
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≤ 1)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1) :
    Lemma611TypeIIIConsequences a b D := by
  let left := D.outer.transition.lastZero
  let right := D.outer.transition.firstTwo - 1
  have hfirstTwoBound := D.outer.transition.firstTwo_le_rank
  have hleftBound : left < n := by
    simp only [left]
    rw [D.adjacent] at hfirstTwoBound
    omega
  let gap : Fin n := ⟨left, hleftBound⟩
  have hrightEq : right = left + 1 := by
    simp only [right, left]
    rw [D.adjacent]
    omega
  have hgapFormula : a.orderGap gap =
      a.orderSequence.entryOrZero right -
        a.orderSequence.entryOrZero left := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (show right < n + 1 by omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (show left < n + 1 by omega)]
    change a.order gap.succ - a.order gap.castSucc = _
    congr 1 <;> apply congrArg a.order <;> apply Fin.ext
    · change gap.1 + 1 = right
      simpa only [gap] using hrightEq.symm
  have halphaGap : a.alphaValue gap ≤ 1 := by
    simpa only [gap, left] using halpha
  have hgapNe : a.orderGap gap ≠ 1 := by
    simpa only [gap, left] using hnotOverlap
  have hgapLe := a.orderGap_le_one_of_alphaValue_le_one gap halphaGap
  have hgapNonpositive : a.orderGap gap ≤ 0 := by omega
  have hgapEvenRaw := a.orderGap_even_of_nonpositive gap hgapNonpositive
  have hcentralEven : Even
      (a.orderSequence.entryOrZero right -
        a.orderSequence.entryOrZero left) := by
    rwa [hgapFormula] at hgapEvenRaw
  have hleftRank : left < n + 1 := hleftBound.trans (by omega)
  have hrightRank : right < n + 1 := by omega
  have hlastBound := D.outer.lastDifference.bound
  have hleftEven : Even left := by
    by_cases heq : D.outer.first = left
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < left :=
        lt_of_le_of_ne D.outer.first_le_left heq
      have hp := (D.outer.leftProfile hlt).1
      simpa only [hfirst, left, Nat.sub_zero] using hp
  have hsourceLeft :
      a.orderSequence.entryOrZero 0 =
        a.orderSequence.entryOrZero left := by
    by_cases heq : D.outer.first = left
    · simpa only [hfirst, left] using congrArg
        (fun k ↦ a.orderSequence.entryOrZero k) heq
    · have hlt : D.outer.first < left :=
        lt_of_le_of_ne D.outer.first_le_left heq
      have hp := D.outer.leftProfile hlt
      have heqSource := (hp.2.2 left D.outer.first_le_left
        le_rfl hp.1).symm
      simpa only [hfirst, left] using heqSource
  have htargetLeft :
      b.orderSequence.entryOrZero 0 =
        b.orderSequence.entryOrZero left := by
    by_cases heq : D.outer.first = left
    · simpa only [hfirst, left] using congrArg
        (fun k ↦ b.orderSequence.entryOrZero k) heq
    · have hlt : D.outer.first < left :=
        lt_of_le_of_ne D.outer.first_le_left heq
      have hp := D.outer.leftProfile hlt
      have hupper := D.no_gap_two D.outer.first
        D.outer.firstDifference.bound
      have hfirstGap :
          b.orderSequence.entryOrZero D.outer.first =
            a.orderSequence.entryOrZero D.outer.first + 1 := by
        omega
      rw [hfirst] at hfirstGap
      have hboundary : b.orderSequence.entryOrZero left =
          a.orderSequence.entryOrZero left + 1 := by
        simpa only [left] using D.outer.transition.leftBoundary
      calc
        b.orderSequence.entryOrZero 0 =
            a.orderSequence.entryOrZero 0 + 1 := hfirstGap
        _ = a.orderSequence.entryOrZero left + 1 := by
          rw [hsourceLeft]
        _ = b.orderSequence.entryOrZero left := hboundary.symm
  have hrightEven : Even (D.outer.last - right) := by
    by_cases heq : right = D.outer.last
    · rw [← heq]
      exact ⟨0, by omega⟩
    · have hlt : right < D.outer.last :=
        lt_of_le_of_ne (by simpa only [right] using
          D.outer.right_le_last) heq
      simpa only [right] using (D.outer.rightProfile hlt).1
  have htargetRight :
      b.orderSequence.entryOrZero right =
        b.orderSequence.entryOrZero D.outer.last := by
    by_cases heq : right = D.outer.last
    · rw [heq]
    · have hlt : right < D.outer.last :=
        lt_of_le_of_ne (by simpa only [right] using
          D.outer.right_le_last) heq
      have hp := D.outer.rightProfile hlt
      exact hp.2.2 right le_rfl
        (by simpa only [right] using D.outer.right_le_last)
        (by simpa only [right] using hp.1)
  have hsourceRight :
      a.orderSequence.entryOrZero right =
        a.orderSequence.entryOrZero D.outer.last := by
    by_cases heq : right = D.outer.last
    · rw [heq]
    · have hlt : right < D.outer.last :=
        lt_of_le_of_ne (by simpa only [right] using
          D.outer.right_le_last) heq
      have hp := D.outer.rightProfile hlt
      have hupper := D.no_gap_two D.outer.last hlastBound
      have hlastGap :
          b.orderSequence.entryOrZero D.outer.last =
            a.orderSequence.entryOrZero D.outer.last + 1 := by
        omega
      have hboundary : b.orderSequence.entryOrZero right =
          a.orderSequence.entryOrZero right + 1 := by
        simpa only [right] using D.outer.transition.rightBoundary
      calc
        a.orderSequence.entryOrZero right =
            b.orderSequence.entryOrZero right - 1 := by omega
        _ = b.orderSequence.entryOrZero D.outer.last - 1 := by
          rw [htargetRight]
        _ = a.orderSequence.entryOrZero D.outer.last := by omega
  have hsourceLeftMod (k : Nat) (hk : k ≤ left) :
      Int.ModEq 2 (a.orderSequence.entryOrZero k)
        (a.orderSequence.entryOrZero left) := by
    have hmod := a.entryOrZero_modEq_of_equal_even_endpoints
      (i := 0) (j := left) (k := k) (by omega) hleftRank
      (Nat.zero_le k) hk (by omega) hleftEven hsourceLeft
    simpa only [hsourceLeft] using hmod
  have htargetLeftMod (k : Nat) (hk : k ≤ left) :
      Int.ModEq 2 (b.orderSequence.entryOrZero k)
        (b.orderSequence.entryOrZero left) := by
    have hmod := b.entryOrZero_modEq_of_equal_even_endpoints
      (i := 0) (j := left) (k := k) (by omega) hleftRank
      (Nat.zero_le k) hk (by omega) hleftEven htargetLeft
    simpa only [htargetLeft] using hmod
  have hsourceRightMod (k : Nat) (hrightK : right ≤ k)
      (hk : k ≤ D.outer.last) :
      Int.ModEq 2 (a.orderSequence.entryOrZero k)
        (a.orderSequence.entryOrZero right) := by
    exact a.entryOrZero_modEq_of_equal_even_endpoints
      (i := right) (j := D.outer.last) (k := k) hrightRank
      hlastBound hrightK hk (hk.trans_lt hlastBound)
      hrightEven hsourceRight
  have htargetRightMod (k : Nat) (hrightK : right ≤ k)
      (hk : k ≤ D.outer.last) :
      Int.ModEq 2 (b.orderSequence.entryOrZero k)
        (b.orderSequence.entryOrZero right) := by
    exact b.entryOrZero_modEq_of_equal_even_endpoints
      (i := right) (j := D.outer.last) (k := k) hrightRank
      hlastBound hrightK hk (hk.trans_lt hlastBound)
      hrightEven htargetRight
  have hsourceCentral : Int.ModEq 2
      (a.orderSequence.entryOrZero right)
      (a.orderSequence.entryOrZero left) :=
    int_modEq_two_of_even_sub hcentralEven
  have htargetCentral : Int.ModEq 2
      (b.orderSequence.entryOrZero right)
      (b.orderSequence.entryOrZero left) := by
    have hleftBoundary := D.outer.transition.leftBoundary
    have hrightBoundary := D.outer.transition.rightBoundary
    rw [hrightBoundary, hleftBoundary]
    exact hsourceCentral.add Int.ModEq.rfl
  refine {
    central_gap_even := hcentralEven
    source := ?_
    target := ?_ }
  · intro k hk
    by_cases hkLeft : k ≤ left
    · exact hsourceLeftMod k hkLeft
    · have hrightK : right ≤ k := by omega
      exact (hsourceRightMod k hrightK hk).trans hsourceCentral
  · intro k hk
    by_cases hkLeft : k ≤ left
    · exact (htargetLeftMod k hkLeft).trans htargetCentral.symm
    · have hrightK : right ≤ k := by omega
      exact htargetRightMod k hrightK hk

/-- Lemma 6.11(iii) with its Lemma 6.9(i) alpha input discharged from the
representation defect condition. -/
theorem lemma611TypeIII_of_defect
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1) :
    Lemma611TypeIIIConsequences a b D := by
  have halpha := a.beli2019Lemma69_i_typeIII
    (alphaV := alphaV) (alphaW := alphaW) b D hfirst hdefect
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  exact a.lemma611TypeIII b D hfirst halpha hnotOverlap

end BONG.GoodBONG

end Bong
