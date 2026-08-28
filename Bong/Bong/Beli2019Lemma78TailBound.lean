/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma74Boundary
import Bong.Bong.Beli2019Lemma78PrefixDefect

/-!
# Beli (2019), Lemma 7.8: the source tail bound

On the right type-III plateau, Lemma 7.4(ii) bounds every later alternating
source segment strictly above the central mixed-defect value.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Every source entry of the right parity on the type-III right interval
equals the source entry at its left endpoint. -/
theorem lemma78_typeIII_sourceRightPlateau
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (D : Lemma67TypeIII a b) (k : Nat)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (hk : k ≤ D.outer.last)
    (heven : Even
      (k - (D.outer.transition.firstTwo - 1))) :
    a.orderSequence.entryOrZero k =
      a.orderSequence.entryOrZero
        (D.outer.transition.firstTwo - 1) := by
  let right := D.outer.transition.firstTwo - 1
  by_cases heq : right = D.outer.last
  · have hkEq : k = right := by omega
    rw [hkEq]
  · have hrightLast : right < D.outer.last :=
      lt_of_le_of_ne D.outer.right_le_last heq
    have hp := D.outer.rightProfile hrightLast
    have htargetRight : b.orderSequence.entryOrZero right =
        b.orderSequence.entryOrZero D.outer.last :=
      hp.2.2 right le_rfl D.outer.right_le_last hp.1
    have hrightBoundary := D.outer.transition.rightBoundary
    have hrightGap : b.orderSequence.entryOrZero right =
        a.orderSequence.entryOrZero right + 1 := by
      simpa only [right] using hrightBoundary
    have hlastStrict := hp.2.1
    have hlastUpper := D.no_gap_two D.outer.last
      D.outer.lastDifference.bound
    have hlastGap : b.orderSequence.entryOrZero D.outer.last =
        a.orderSequence.entryOrZero D.outer.last + 1 := by
      omega
    have hendpoints : a.orderSequence.entryOrZero right =
        a.orderSequence.entryOrZero D.outer.last := by
      omega
    have hrightK := a.orderSequence.entryOrZero_le_of_evenGap
      right k hright (hk.trans_lt D.outer.lastDifference.bound) heven
    have hlastK : Even (D.outer.last - k) := by
      rcases hp.1 with ⟨d, hd⟩
      rcases heven with ⟨e, he⟩
      refine ⟨d - e, ?_⟩
      omega
    have hkLast := a.orderSequence.entryOrZero_le_of_evenGap
      k D.outer.last hk D.outer.lastDifference.bound hlastK
    have hkRight : a.orderSequence.entryOrZero k ≤
        a.orderSequence.entryOrZero right := by
      rw [hendpoints]
      exact hkLast
    exact le_antisymm hkRight hrightK

/-- A later alternating source tail is strictly larger than the central
mixed-defect value.  The rank is written as `n + 2` to expose the two
internal alpha indices used by Lemma 7.4(ii). -/
theorem lemma78_typeIII_sourceTail_gt_mixedShift
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0) (i : Nat)
    (hiStart : D.outer.transition.lastZero + 4 ≤ i)
    (hiLast : i ≤ D.outer.last + 1) (hiEven : Even i) :
    (((b.order ⟨D.outer.transition.lastZero, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ -
        a.order ⟨D.outer.transition.lastZero + 1, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ : Int) : ℚ) : WithTop ℚ) <
      a.truncatedPrefixDefect a
        ((-1) ^ ((i - (D.outer.transition.lastZero + 2)) / 2))
        (D.outer.transition.lastZero + 2) i := by
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
  have hiBound : i ≤ n + 2 :=
    hiLast.trans (Nat.succ_le_of_lt D.outer.lastDifference.bound)
  have hleftEven : Even left := by
    by_cases heq : D.outer.first = left
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < left :=
        lt_of_le_of_ne D.outer.first_le_left heq
      simpa only [hfirst, left, Nat.sub_zero] using
        (D.outer.leftProfile hlt).1
  have hfirstPlateau := a.lemma78_typeIII_sourceRightPlateau b D
    (left + 3) (by rw [D.adjacent]; omega)
    (by omega) (by
      change Even (left + 3 - right)
      rw [hrightEq]
      exact ⟨1, by omega⟩)
  have hlastPlateau := a.lemma78_typeIII_sourceRightPlateau b D
    (i - 1) (by rw [D.adjacent]; omega)
    (by omega) (by
      change Even (i - 1 - right)
      rw [hrightEq]
      rcases hiEven with ⟨d, hd⟩
      rcases hleftEven with ⟨e, he⟩
      exact ⟨d - e - 1, by omega⟩)
  have horder : a.order ⟨left + 3, by omega⟩ =
      a.order ⟨i - 1, by omega⟩ := by
    calc
      a.order ⟨left + 3, by omega⟩ =
          a.orderSequence.entryOrZero (left + 3) := by
        exact (a.orderSequence_entryOrZero_eq_order
          ⟨left + 3, by omega⟩).symm
      _ = a.orderSequence.entryOrZero right := hfirstPlateau
      _ = a.orderSequence.entryOrZero (i - 1) := hlastPlateau.symm
      _ = a.order ⟨i - 1, by omega⟩ :=
        a.orderSequence_entryOrZero_eq_order ⟨i - 1, by omega⟩
  have h74 := a.beli2019Lemma74_ii_nat (left + 3) (i - 1)
    (by omega) (by omega) (by omega) (by omega)
    (by
      rcases hiEven with ⟨d, hd⟩
      rcases hleftEven with ⟨e, he⟩
      refine ⟨d - e - 2, ?_⟩
      omega)
    horder
  let previous : Fin (n + 1) := ⟨left + 2, by omega⟩
  have h74' :
      (((((a.order previous.castSucc - a.order previous.succ : Int) : ℚ) +
          a.alphaValue previous : ℚ)) : WithTop ℚ) ≤
        a.truncatedPrefixDefect a
          ((-1) ^ ((i - (left + 2)) / 2)) (left + 2) i := by
    simpa only [previous,
      show (i - 1 - (left + 3) + 2) / 2 =
        (i - (left + 2)) / 2 by omega,
      show left + 3 - 1 = left + 2 by omega,
      show i - 1 + 1 = i by omega] using h74
  have hrightLast : right < D.outer.last := by omega
  have hp := D.outer.rightProfile hrightLast
  have htargetRight : b.orderSequence.entryOrZero right =
      b.orderSequence.entryOrZero D.outer.last :=
    hp.2.2 right le_rfl D.outer.right_le_last hp.1
  have htargetAfter : b.orderSequence.entryOrZero (left + 3) =
      b.orderSequence.entryOrZero D.outer.last := by
    apply hp.2.2 (left + 3) (by omega) (by omega)
    rcases hp.1 with ⟨d, hd⟩
    rw [D.adjacent] at hd
    exact ⟨d - 1, by omega⟩
  have hrightBoundary := D.outer.transition.rightBoundary
  have hrightGap : b.orderSequence.entryOrZero right =
      a.orderSequence.entryOrZero right + 1 := by
    simpa only [right] using hrightBoundary
  have hsourceAfter : a.orderSequence.entryOrZero (left + 3) =
      a.orderSequence.entryOrZero right := hfirstPlateau
  have htargetAfterGap : b.orderSequence.entryOrZero (left + 3) =
      a.orderSequence.entryOrZero (left + 3) + 1 := by
    omega
  have hpair := D.outer.rightPairEq (left + 2)
    (by rw [D.adjacent]) (by omega) ⟨0, by omega⟩
  have hsourceTargetNext :
      a.orderSequence.entryOrZero (left + 2) =
        b.orderSequence.entryOrZero (left + 2) + 1 := by
    have hone : left + 2 + 1 = left + 3 := by omega
    rw [hone] at hpair
    omega
  have htargetMonotone := b.orderSequence.entryOrZero_le_of_evenGap
    left (left + 2) (by omega) (by omega) ⟨1, by omega⟩
  have hpreviousCast : a.order previous.castSucc =
      a.orderSequence.entryOrZero (left + 2) := by
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
    apply congrArg a.order
    apply Fin.ext
    simp only [previous, Fin.val_castSucc]
  have hpreviousSucc : a.order previous.succ =
      a.orderSequence.entryOrZero (left + 3) := by
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
    apply congrArg a.order
    apply Fin.ext
    simp only [previous, Fin.val_succ]
  have hbLeft : b.order ⟨left, by omega⟩ =
      b.orderSequence.entryOrZero left :=
    (b.orderSequence_entryOrZero_eq_order ⟨left, by omega⟩).symm
  have haRight : a.order ⟨left + 1, by omega⟩ =
      a.orderSequence.entryOrZero right := by
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence hrightBound]
    apply congrArg a.order
    apply Fin.ext
    exact hrightEq.symm
  have horderBound :
      b.order ⟨left, by omega⟩ - a.order ⟨left + 1, by omega⟩ + 1 ≤
        a.order previous.castSucc - a.order previous.succ := by
    rw [hpreviousCast, hpreviousSucc, hbLeft, haRight]
    omega
  have hAlphaNonnegative : 0 ≤ a.alphaValue previous :=
    (a.alpha_p2 previous).1
  have hcriticalQ :
      ((b.order ⟨left, by omega⟩ -
          a.order ⟨left + 1, by omega⟩ : Int) : ℚ) <
        ((a.order previous.castSucc - a.order previous.succ : Int) : ℚ) +
          a.alphaValue previous := by
    have horderBoundQ :
        ((b.order ⟨left, by omega⟩ -
            a.order ⟨left + 1, by omega⟩ : Int) : ℚ) + 1 ≤
          ((a.order previous.castSucc - a.order previous.succ : Int) : ℚ) := by
      exact_mod_cast horderBound
    linarith
  have hcriticalTop :
      (((b.order ⟨left, by omega⟩ -
          a.order ⟨left + 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) <
        (((((a.order previous.castSucc - a.order previous.succ : Int) : ℚ) +
          a.alphaValue previous : ℚ)) : WithTop ℚ) := by
    exact_mod_cast hcriticalQ
  simpa only [left] using hcriticalTop.trans_le h74'

end BONG.GoodBONG

end Bong
