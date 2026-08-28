/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019CappedDefectSharp
import Bong.Bong.Beli2019Lemma74
import Bong.Bong.Beli2019Lemma78AlphaZero

/-!
# Beli (2019), Lemma 7.8: the first alternating prefix defect

The target prefix ending immediately before the type-III center has defect
strictly above the central mixed defect.  Sharp capped-defect multiplication
then identifies the first source prefix after the center exactly.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The alternating target prefix immediately before the type-III center
lies strictly above the central mixed-defect value. -/
theorem lemma78_typeIII_targetPrefix_gt_mixedShift
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0) :
    (((b.order ⟨D.outer.transition.lastZero, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ -
        a.order ⟨D.outer.transition.lastZero + 1, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ : Int) : ℚ) : WithTop ℚ) <
      b.truncatedPrefixDefect b
        ((-1) ^ (D.outer.transition.lastZero / 2)) 0
        D.outer.transition.lastZero := by
  cases n with
  | zero =>
      have hbound := D.outer.transition.firstTwo_le_rank
      have hadjacent := D.adjacent
      omega
  | succ n =>
      let left := D.outer.transition.lastZero
      let right := D.outer.transition.firstTwo - 1
      have hfirstTwoBound := D.outer.transition.firstTwo_le_rank
      have hleftBound : left < n + 1 := by
        simp only [left]
        rw [D.adjacent] at hfirstTwoBound
        omega
      have hrightEq : right = left + 1 := by
        simp only [right, left]
        rw [D.adjacent]
        omega
      have hrightBound : right < n + 2 := by omega
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
        have hkBound : k < n + 2 :=
          hk.trans_lt hleftBound |>.trans (by omega)
        have hleftRank : left < n + 2 := hleftBound.trans (by omega)
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
          have hsourceZero :=
            hsourceEven 0 (Nat.zero_le left) ⟨0, by omega⟩
          have hleftGap := D.outer.transition.leftBoundary
          have hleftGap' : b.orderSequence.entryOrZero left =
              a.orderSequence.entryOrZero left + 1 := by
            simpa only [left] using hleftGap
          omega
      by_cases hleftZero : left = 0
      · have htop : b.truncatedPrefixDefect b
            ((-1) ^ (left / 2)) 0 left = ⊤ := by
          rw [hleftZero]
          unfold truncatedPrefixDefect
          rw [b.prefixAlphaCap_zero]
          simp only [inf_top_eq]
          rw [show ((-1 : Kˣ) ^ (0 / 2) * b.prefixProduct 0 *
              b.prefixProduct 0) = 1 by
            simp [GoodBONG.prefixProduct]]
          rw [defectOrder_eq_top_of_isSquare]
          exact IsSquare.one
        rw [htop]
        exact WithTop.coe_lt_top _
      · have hleftTwo : 2 ≤ left := by
          rcases hleftEven with ⟨d, hd⟩
          omega
        let first : Fin (n + 1) := ⟨0, by omega⟩
        let last : Fin (n + 1) := ⟨left - 2, by omega⟩
        have htargetZero :=
          htargetEven 0 (Nat.zero_le left) ⟨0, by omega⟩
        have htargetPrevious := htargetEven (left - 2) (by omega) (by
          rcases hleftEven with ⟨d, hd⟩
          exact ⟨d - 1, by omega⟩)
        have htargetEntries : b.orderSequence.entryOrZero first.val =
            b.orderSequence.entryOrZero last.val := by
          simpa only [first, last] using
            htargetZero.trans htargetPrevious.symm
        have horder : b.order first.castSucc =
            b.order last.castSucc := by
          calc
            b.order first.castSucc =
                b.orderSequence.entryOrZero first.val :=
              (b.orderSequence_entryOrZero_eq_order first.castSucc).symm
            _ = b.orderSequence.entryOrZero last.val := htargetEntries
            _ = b.order last.castSucc :=
              b.orderSequence_entryOrZero_eq_order last.castSucc
        have h74 := b.beli2019Lemma74_i first last
          (by change first.val ≤ last.val; simp only [first, last]; omega)
          (by
            rcases hleftEven with ⟨d, hd⟩
            refine ⟨d - 1, ?_⟩
            simp only [first, last]
            omega)
          horder
        have hexponent :
            (last.val - first.val + 2) / 2 = left / 2 := by
          simp only [first, last]
          omega
        have hend : last.val + 2 = left := by
          simp only [last]
          omega
        have h74' :
            (((((b.order last.castSucc - b.order last.succ : Int) : ℚ) +
                b.alphaValue last : ℚ)) : WithTop ℚ) ≤
              b.truncatedPrefixDefect b ((-1) ^ (left / 2)) 0 left := by
          simpa only [first, Nat.zero_div, hexponent, hend] using h74
        have hpairParity : Even (left - (left - 2)) := ⟨1, by omega⟩
        have hpair := D.outer.leftPairEq (left - 2)
          (by omega) hpairParity
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
        have horderBound :
            b.order last.castSucc - b.order last.succ ≥
              b.order ⟨left, by omega⟩ -
                a.order ⟨left + 1, by omega⟩ + 1 := by
          have hlastCast : b.order last.castSucc =
              b.orderSequence.entryOrZero (left - 2) := by
            rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
              (show left - 2 < n + 2 by omega)]
            apply congrArg b.order
            apply Fin.ext
            simp only [last, Fin.val_castSucc]
          have hlastSucc : b.order last.succ =
              b.orderSequence.entryOrZero (left - 1) := by
            rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
              (show left - 1 < n + 2 by omega)]
            apply congrArg b.order
            apply Fin.ext
            simp only [last, Fin.val_succ]
            omega
          have hbLeft : b.order ⟨left, by omega⟩ =
              b.orderSequence.entryOrZero left := by
            exact (b.orderSequence_entryOrZero_eq_order
              ⟨left, by omega⟩).symm
          have haRight : a.order ⟨left + 1, by omega⟩ =
              a.orderSequence.entryOrZero right := by
            rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
              hrightBound]
            apply congrArg a.order
            apply Fin.ext
            exact hrightEq.symm
          rw [hlastCast, hlastSucc, hbLeft, haRight]
          omega
        have hAlphaNonnegative : 0 ≤ b.alphaValue last :=
          (b.alpha_p2 last).1
        have hcriticalQ :
            ((b.order ⟨left, by omega⟩ -
                a.order ⟨left + 1, by omega⟩ : Int) : ℚ) <
              ((b.order last.castSucc - b.order last.succ : Int) : ℚ) +
                b.alphaValue last := by
          have horderBoundQ :
              ((b.order ⟨left, by omega⟩ -
                  a.order ⟨left + 1, by omega⟩ : Int) : ℚ) + 1 ≤
                ((b.order last.castSucc - b.order last.succ : Int) : ℚ) := by
            exact_mod_cast horderBound
          linarith
        have hcriticalTop :
            (((b.order ⟨left, by omega⟩ -
                a.order ⟨left + 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) <
              (((((b.order last.castSucc - b.order last.succ : Int) : ℚ) +
                b.alphaValue last : ℚ)) : WithTop ℚ) := by
          exact_mod_cast hcriticalQ
        simpa only [left] using hcriticalTop.trans_le h74'

/-- Lemma 7.8 at `i = t + 1`: the first alternating source prefix after
the type-III center has the central mixed-defect value. -/
theorem beli2019Lemma78_firstSourcePrefixDefect
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 1) + 2 =
      b.orderSequence.prefixSum (n + 1))
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
        ((-1) ^ ((D.outer.transition.lastZero + 2) / 2)) 0
        (D.outer.transition.lastZero + 2) =
      ((((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : ℚ)) : WithTop ℚ) := by
  let left := D.outer.transition.lastZero
  let eta : Kˣ := (-1) ^ (left / 2)
  have hleftEven : Even left := by
    by_cases heq : D.outer.first = left
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < left :=
        lt_of_le_of_ne D.outer.first_le_left heq
      simpa only [hfirst, left, Nat.sub_zero] using
        (D.outer.leftProfile hlt).1
  have hmixed := a.beli2019Lemma78_centralMixedDefect_exact
    b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
  have htarget := a.lemma78_typeIII_targetPrefix_gt_mixedShift
    b D hfirst
  have htargetTransfer :
      b.truncatedPrefixDefect a eta left 0 =
        b.truncatedPrefixDefect b eta left 0 :=
    b.truncatedPrefixDefect_zero_right_eq_self a eta left
  have htargetComm : b.truncatedPrefixDefect b eta left 0 =
      b.truncatedPrefixDefect b eta 0 left :=
    b.truncatedPrefixDefect_comm b eta left 0
  have hseparation :
      a.truncatedPrefixDefect b (-1) (left + 2) left <
        b.truncatedPrefixDefect a eta left 0 := by
    rw [htargetTransfer, htargetComm]
    rw [hmixed]
    simpa only [eta, left] using htarget
  have hsharp := a.truncatedPrefixDefect_mul_eq_left_of_lt_right
    b a (-1) eta (left + 2) left 0 hseparation
  have hsign : (-1 : Kˣ) * eta =
      (-1) ^ ((left + 2) / 2) := by
    rcases hleftEven with ⟨d, hd⟩
    have hhalf : left / 2 = d := by omega
    have hhalfNext : (left + 2) / 2 = d + 1 := by omega
    dsimp only [eta]
    rw [hhalf, hhalfNext, pow_succ]
    ac_rfl
  calc
    a.truncatedPrefixDefect a ((-1) ^ ((left + 2) / 2)) 0
        (left + 2) =
      a.truncatedPrefixDefect a ((-1) ^ ((left + 2) / 2))
        (left + 2) 0 :=
      a.truncatedPrefixDefect_comm a
        ((-1) ^ ((left + 2) / 2)) 0 (left + 2)
    _ = a.truncatedPrefixDefect a ((-1) * eta) (left + 2) 0 := by
      rw [hsign]
    _ = a.truncatedPrefixDefect b (-1) (left + 2) left := hsharp
    _ = _ := by simpa only [left] using hmixed

end BONG.GoodBONG

end Bong
