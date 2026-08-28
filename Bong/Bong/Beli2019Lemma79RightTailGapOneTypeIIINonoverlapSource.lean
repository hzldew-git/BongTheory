/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapBase
import Bong.Bong.Beli2019Lemma79RightTailSourceDomination

/-!
# Beli (2019), Lemma 7.9(ii), case 8: type-III source prefixes

The local form of Lemma 7.8 gives the source-prefix defect through the first
coordinate beyond the type-III profile.  Every subsequent alternating pair
has larger defect, so sharp multiplication preserves the central value.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Lemma 7.8 at the first even prefix beyond the last unequal coordinate. -/
theorem beli2019Lemma79_typeIII_nonoverlap_firstSourcePrefixDefect
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩) :
    a.truncatedPrefixDefect a
        ((-1) ^ ((D.outer.last + 1) / 2)) 0 (D.outer.last + 1) =
      ((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : Rat) := by
  have hstart : D.outer.transition.lastZero + 2 ≤ D.outer.last + 1 := by
    have hright := D.outer.right_le_last
    rw [D.adjacent] at hright
    omega
  exact a.beli2019Lemma78_sourcePrefixDefect_local
    b D hfirst hdefect hnotOverlap hinitial (D.outer.last + 1)
      hstart le_rfl
      (beli2019Lemma79_typeIII_last_succ_even a b D hfirst)

/-- Appending one or more strict-tail source pairs preserves the central
type-III defect. -/
theorem beli2019Lemma79_typeIII_nonoverlap_sourcePrefixDefect_succ
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hlast : D.outer.last < n + 1)
    {tailLast : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.outer.last, hlast⟩ tailLast)
    (hstrictTail : b.alphaValue tailLast < a.alphaValue tailLast)
    (pairs : Nat)
    (hend : D.outer.last + 1 + 2 * pairs ≤ tailLast.val) :
    a.truncatedPrefixDefect a
        ((-1) ^ ((D.outer.last + 1 + 2 * (pairs + 1)) / 2)) 0
        (D.outer.last + 1 + 2 * (pairs + 1)) =
      ((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : Rat) := by
  let first : Fin (n + 1) := ⟨D.outer.last, hlast⟩
  let start : Fin (n + 1) := ⟨D.outer.last + 1, by omega⟩
  let central : WithTop Rat :=
    (((b.order ⟨D.outer.transition.lastZero, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ -
        a.order ⟨D.outer.transition.lastZero + 1, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ : Int) : Rat) : WithTop Rat)
  have hfirstTail : first ≤ tailLast := by
    change D.outer.last ≤ tailLast.val
    omega
  have hfirstStart : first < start := by
    change D.outer.last < D.outer.last + 1
    omega
  have hstartTail : start ≤ tailLast := by
    change D.outer.last + 1 ≤ tailLast.val
    omega
  have hsuffix : ∀ k, first.val + 1 ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply D.outer.lastDifference.after k
    · simp only [first] at hk
      omega
    · exact hkn
  have hsegmentRaw := H.source_alternating_defect_gt
    hsuffix hstrictTail start hfirstStart hstartTail pairs (by
      simpa only [start] using hend)
  have hstartIndex : start.castSucc = first.succ := by
    apply Fin.ext
    rfl
  rw [hstartIndex, sub_self] at hsegmentRaw
  norm_num at hsegmentRaw
  have hcentralLeQ :=
    beli2019Lemma79_typeIII_nonoverlap_central_le_firstBeta
      a b D hfirst hdefect hnotOverlap hlast H hfirstTail hstrictTail
  have hcentralLe : central ≤ (b.alphaValue first : WithTop Rat) := by
    exact WithTop.coe_le_coe.mpr (by
      simpa only [central, first] using hcentralLeQ)
  have hsegment : central <
      a.truncatedPrefixDefect a ((-1) ^ (pairs + 1)) start.val
        (start.val + 2 * (pairs + 1)) := by
    apply hcentralLe.trans_lt
    rw [b.coe_alphaValue]
    simpa only [first] using hsegmentRaw
  have hinitialDefect :=
    beli2019Lemma79_typeIII_nonoverlap_firstSourcePrefixDefect
      a b D hfirst hdefect hnotOverlap hinitial
  have hseparation :
      a.truncatedPrefixDefect a
          ((-1) ^ ((D.outer.last + 1) / 2)) 0 start.val <
        a.truncatedPrefixDefect a ((-1) ^ (pairs + 1)) start.val
          (start.val + 2 * (pairs + 1)) := by
    rw [show a.truncatedPrefixDefect a
        ((-1) ^ ((D.outer.last + 1) / 2)) 0 start.val = central by
      simpa only [start, central] using hinitialDefect]
    exact hsegment
  have hsharp := a.truncatedPrefixDefect_mul_eq_left_of_lt_right
    a a ((-1) ^ ((D.outer.last + 1) / 2))
      ((-1) ^ (pairs + 1)) 0 start.val
      (start.val + 2 * (pairs + 1)) hseparation
  have hsign :
      ((-1 : Kˣ) ^ ((D.outer.last + 1) / 2)) *
          ((-1) ^ (pairs + 1)) =
        (-1) ^ ((D.outer.last + 1 + 2 * (pairs + 1)) / 2) := by
    rcases beli2019Lemma79_typeIII_last_succ_even a b D hfirst with
      ⟨d, hd⟩
    have hhalfStart : (D.outer.last + 1) / 2 = d := by omega
    have hhalfEnd :
        (D.outer.last + 1 + 2 * (pairs + 1)) / 2 =
          d + pairs + 1 := by omega
    rw [hhalfStart, hhalfEnd, ← pow_add]
    congr 1
  calc
    a.truncatedPrefixDefect a
        ((-1) ^ ((D.outer.last + 1 + 2 * (pairs + 1)) / 2)) 0
        (D.outer.last + 1 + 2 * (pairs + 1)) =
      a.truncatedPrefixDefect a
        (((-1) ^ ((D.outer.last + 1) / 2)) *
          ((-1) ^ (pairs + 1))) 0
        (start.val + 2 * (pairs + 1)) := by rw [hsign]
    _ = a.truncatedPrefixDefect a
        ((-1) ^ ((D.outer.last + 1) / 2)) 0 start.val := hsharp
    _ = _ := by simpa only [start] using hinitialDefect

/-- Every even source prefix from the end of the type-III profile through
the strict beta tail has the central Lemma 7.8 defect. -/
theorem beli2019Lemma79_typeIII_nonoverlap_sourcePrefixDefect
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hlast : D.outer.last < n + 1)
    {tailLast : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.outer.last, hlast⟩ tailLast)
    (hstrictTail : b.alphaValue tailLast < a.alphaValue tailLast)
    (length : Nat) (hstart : D.outer.last + 1 ≤ length)
    (hend : length ≤ tailLast.val + 1) (heven : Even length) :
    a.truncatedPrefixDefect a ((-1) ^ (length / 2)) 0 length =
      ((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : Rat) := by
  rcases beli2019Lemma79_typeIII_last_succ_even a b D hfirst with
    ⟨d, hd⟩
  rcases heven with ⟨e, he⟩
  have hde : d ≤ e := by omega
  let pairs := e - d
  have hlength : length = D.outer.last + 1 + 2 * pairs := by
    simp only [pairs]
    omega
  by_cases hpairsZero : pairs = 0
  ·
      have hlengthBase : length = D.outer.last + 1 := by
        rw [hpairsZero] at hlength
        simpa only [Nat.mul_zero, add_zero] using hlength
      simpa only [hlengthBase] using
        beli2019Lemma79_typeIII_nonoverlap_firstSourcePrefixDefect
          a b D hfirst hdefect hnotOverlap hinitial
  · obtain ⟨pairs, hpairs⟩ := Nat.exists_eq_succ_of_ne_zero hpairsZero
    have hprevious : D.outer.last + 1 + 2 * pairs ≤ tailLast.val := by
      rw [hlength, hpairs] at hend
      omega
    have hresult :=
      beli2019Lemma79_typeIII_nonoverlap_sourcePrefixDefect_succ
        a b D hfirst hdefect hnotOverlap hinitial hlast H hstrictTail
          pairs hprevious
    rw [hlength, hpairs]
    simpa only [Nat.succ_eq_add_one] using hresult

end BONG.GoodBONG

end Bong
