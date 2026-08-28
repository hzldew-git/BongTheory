/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma720Central

/-!
# Beli (2019), Section 7 after Lemma 7.19: long-prefix condition

This file proves condition 2.1(iv) for all three replacement normal forms.
Before the common suffix, the explicit order profiles rule out the strict
jump in the trigger. At and after the stopping boundary, the source trigger
and representation are transported through the prefix isometries of Lemma 7.19.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]
variable [Beli2009AlphaParityLaws.{u, v} K]
variable [laws : DyadicDiscriminantClassLaws K]

theorem longRepresentationAt_of_prefix_isometric720
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (hac : RepresentationConditions a c le_rfl)
    (i : LongRepresentationIndex (n + 3) (n + 3))
    (hnext : a.order ⟨i.val + 1, i.succ_lt_large⟩ =
      b.order ⟨i.val + 1, i.succ_lt_large⟩)
    (hcurrent : a.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩ ≤
      b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩)
    (hprefix : (a.prefixDiagonalSpace (i.val + 1) i.next_le_sameRank).IsIsometric
      (b.prefixDiagonalSpace (i.val + 1) i.next_le_sameRank))
    (htrigger : b.LongRepresentationTrigger c i) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1) i.previous_le_sameRank)
      (b.prefixValues (i.val + 1) i.next_le_sameRank) := by
  have hiSucc := i.succ_lt_large
  have hiOne := i.one_lt
  have htriggerA : a.LongRepresentationTrigger c i := by
    unfold LongRepresentationTrigger at htrigger ⊢
    constructor
    · rw [hnext]
      exact htrigger.1
    · constructor
      · rw [hnext]
        exact htrigger.2.1
      · calc
          a.order ⟨i.val, by omega⟩ +
                2 * (ramificationIndex K : Int) ≤
              b.order ⟨i.val, by omega⟩ +
                2 * (ramificationIndex K : Int) := by omega
          _ ≤ c.order ⟨i.val - 2, by omega⟩ +
                2 * (ramificationIndex K : Int) := htrigger.2.2
  have hacRep :=
    (a.longRepresentationConditions_iff_forall_trigger c).mp
      hac.longRepresentations i htriggerA
  have habRep := diagonalRepresents_prefixValues_of_prefix_isometric
    a b (i.val + 1) i.next_le_sameRank hprefix
  exact hacRep.trans habRep

theorem strictOrderJump_of_longRepresentationTrigger720
    (b : GoodBONG q M (n + 3)) (c : GoodBONG q N (n + 3))
    (i : LongRepresentationIndex (n + 3) (n + 3))
    (htrigger : b.LongRepresentationTrigger c i) :
    b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩ + 2 * (ramificationIndex K : Int) <
      b.order ⟨i.val + 1, i.succ_lt_large⟩ := by
  have hiSucc := i.succ_lt_large
  have hiOne := i.one_lt
  exact htrigger.2.2.trans_lt htrigger.2.1

theorem Lemma718TypeINormalForm.sourceOrder_le_target_of_sMinusOne_le
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (i : Fin (n + 3)) (hsi : s - 1 ≤ i.val) :
    a.order i ≤ b.order i := by
  by_cases htail : s ≤ i.val
  · exact le_of_eq (D.tailOrder a b R s i htail)
  · have hi : i.val = s - 1 := by omega
    rcases D.stopping.even with ⟨d, hd⟩
    have hiOdd : Odd i.val := ⟨d - 1, by
      have := D.stopping.two_le
      omega⟩
    have ha := D.sourceOrder_odd a b R s i (by omega) hiOdd
    have hb := D.targetOrder_odd a b R s i (by omega) hiOdd
    omega

theorem Lemma718TypeIINormalForm.sourceOrder_le_target_of_sMinusOne_le
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (i : Fin (n + 3)) (hsi : s - 1 ≤ i.val) :
    a.order i ≤ b.order i := by
  by_cases htail : s ≤ i.val
  · exact le_of_eq (D.tailOrder a b R s i htail)
  · have hi : i.val = s - 1 := by omega
    rcases D.stopping.even with ⟨d, hd⟩
    have hiOdd : Odd i.val := ⟨d - 1, by
      have := D.stopping.two_le
      omega⟩
    have ha := D.sourceOrder_odd a b R s i (by omega) hiOdd
    have hb := D.targetOrder_odd a b R s i (by omega) hiOdd
    split at hb <;> omega

theorem Lemma718TypeIIINormalForm.sourceOrder_le_target_of_sMinusOne_le
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s)
    (i : Fin (n + 3)) (hsi : s - 1 ≤ i.val) :
    a.order i ≤ b.order i := by
  by_cases htail : s ≤ i.val
  · exact le_of_eq (D.tailOrder a b R s i htail)
  · have hi : i.val = s - 1 := by omega
    rcases D.stopping.even with ⟨d, hd⟩
    have hiOdd : Odd i.val := ⟨d - 1, by
      have := D.stopping.two_le
      omega⟩
    have ha := D.sourceOrder_odd a b R s i (by omega) hiOdd
    have hb := D.targetOrder_odd a b R s i (by omega) hiOdd
    omega

theorem Lemma718TypeINormalForm.longTrigger_false_of_le_sMinusTwo
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (i : LongRepresentationIndex (n + 3) (n + 3))
    (hi : i.val ≤ s - 2) :
    ¬ b.LongRepresentationTrigger c i := by
  intro htrigger
  have hiSucc := i.succ_lt_large
  have hsTwo := D.stopping.two_le
  let current : Fin (n + 3) := ⟨i.val, by omega⟩
  let next : Fin (n + 3) := ⟨i.val + 1, i.succ_lt_large⟩
  have hjump : b.order current + 2 * (ramificationIndex K : Int) <
      b.order next := by
    have hstrict := strictOrderJump_of_longRepresentationTrigger720 b c i htrigger
    simpa only [current, next] using hstrict
  have hcurrentS : current.val < s := by dsimp only [current]; omega
  have hnextS : next.val < s := by dsimp only [next]; omega
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · have hcurrentEven : Even current.val := by simpa only [current] using hiEven
    have hnextOdd : Odd next.val := by
      rcases hiEven with ⟨d, hd⟩
      exact ⟨d, by dsimp only [next]; omega⟩
    have hc := D.targetOrder_even a b R s current hcurrentS hcurrentEven
    have hn := D.targetOrder_odd a b R s next hnextS hnextOdd
    rw [hc, hn] at hjump
    omega
  · have hcurrentOdd : Odd current.val := by simpa only [current] using hiOdd
    have hnextEven : Even next.val := by
      rcases hiOdd with ⟨d, hd⟩
      exact ⟨d + 1, by dsimp only [next]; omega⟩
    have hc := D.targetOrder_odd a b R s current hcurrentS hcurrentOdd
    have hn := D.targetOrder_even a b R s next hnextS hnextEven
    rw [hc, hn] at hjump
    omega

theorem Lemma718TypeIINormalForm.longTrigger_false_of_le_sMinusTwo
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (i : LongRepresentationIndex (n + 3) (n + 3))
    (hi : i.val ≤ s - 2) :
    ¬ b.LongRepresentationTrigger c i := by
  intro htrigger
  have hiSucc := i.succ_lt_large
  have hiOne := i.one_lt
  have hsTwo := D.stopping.two_le
  let current : Fin (n + 3) := ⟨i.val, by omega⟩
  let next : Fin (n + 3) := ⟨i.val + 1, i.succ_lt_large⟩
  have hjump : b.order current + 2 * (ramificationIndex K : Int) <
      b.order next := by
    have hstrict := strictOrderJump_of_longRepresentationTrigger720 b c i htrigger
    simpa only [current, next] using hstrict
  have hcurrentS : current.val < s := by dsimp only [current]; omega
  have hnextS : next.val < s := by dsimp only [next]; omega
  have hcurrentTwo : ¬ current.val < 2 := by dsimp only [current]; omega
  have hnextTwo : ¬ next.val < 2 := by dsimp only [next]; omega
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · have hcurrentEven : Even current.val := by simpa only [current] using hiEven
    have hnextOdd : Odd next.val := by
      rcases hiEven with ⟨d, hd⟩
      exact ⟨d, by dsimp only [next]; omega⟩
    have hc := D.targetOrder_even a b R s current hcurrentS hcurrentEven
    have hn := D.targetOrder_odd a b R s next hnextS hnextOdd
    rw [if_neg hcurrentTwo] at hc
    rw [if_neg hnextTwo] at hn
    rw [hc, hn] at hjump
    omega
  · have hcurrentOdd : Odd current.val := by simpa only [current] using hiOdd
    have hnextEven : Even next.val := by
      rcases hiOdd with ⟨d, hd⟩
      exact ⟨d + 1, by dsimp only [next]; omega⟩
    have hc := D.targetOrder_odd a b R s current hcurrentS hcurrentOdd
    have hn := D.targetOrder_even a b R s next hnextS hnextEven
    rw [if_neg hcurrentTwo] at hc
    rw [if_neg hnextTwo] at hn
    rw [hc, hn] at hjump
    omega

theorem Lemma718TypeIIINormalForm.longTrigger_false_of_le_sMinusTwo
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s)
    (i : LongRepresentationIndex (n + 3) (n + 3))
    (hi : i.val ≤ s - 2) :
    ¬ b.LongRepresentationTrigger c i := by
  intro htrigger
  have hiSucc := i.succ_lt_large
  have hsTwo := D.stopping.two_le
  have he := ramificationIndex_pos (K := K)
  let current : Fin (n + 3) := ⟨i.val, by omega⟩
  let next : Fin (n + 3) := ⟨i.val + 1, i.succ_lt_large⟩
  have hjump : b.order current + 2 * (ramificationIndex K : Int) <
      b.order next := by
    have hstrict := strictOrderJump_of_longRepresentationTrigger720 b c i htrigger
    simpa only [current, next] using hstrict
  have hcurrentS : current.val < s := by dsimp only [current]; omega
  have hnextS : next.val < s := by dsimp only [next]; omega
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · have hcurrentEven : Even current.val := by simpa only [current] using hiEven
    have hnextOdd : Odd next.val := by
      rcases hiEven with ⟨d, hd⟩
      exact ⟨d, by dsimp only [next]; omega⟩
    have hc := D.targetOrder_even a b R s current hcurrentS hcurrentEven
    have hn := D.targetOrder_odd a b R s next hnextS hnextOdd
    rw [hc, hn] at hjump
    omega
  · have hcurrentOdd : Odd current.val := by simpa only [current] using hiOdd
    have hnextEven : Even next.val := by
      rcases hiOdd with ⟨d, hd⟩
      exact ⟨d + 1, by dsimp only [next]; omega⟩
    have hc := D.targetOrder_odd a b R s current hcurrentS hcurrentOdd
    have hn := D.targetOrder_even a b R s next hnextS hnextEven
    rw [hc, hn] at hjump
    omega

theorem Lemma718TypeINormalForm.longRepresentationConditions
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (hac : RepresentationConditions a c le_rfl) :
    b.LongRepresentationConditions c := by
  rw [b.longRepresentationConditions_iff_forall_trigger c]
  intro i htrigger
  by_cases hLate : s - 1 ≤ i.val
  · have hiSucc := i.succ_lt_large
    have hnext : a.order ⟨i.val + 1, i.succ_lt_large⟩ =
        b.order ⟨i.val + 1, i.succ_lt_large⟩ :=
      D.tailOrder a b R s ⟨i.val + 1, i.succ_lt_large⟩ (by
        change s ≤ i.val + 1
        omega)
    have hcurrent : a.order ⟨i.val, by omega⟩ ≤
        b.order ⟨i.val, by omega⟩ :=
      D.sourceOrder_le_target_of_sMinusOne_le a b R s
        ⟨i.val, by omega⟩ hLate
    have h719 := a.beli2019Lemma719_of_normalForm b R s
      (Beli2019Lemma718NormalForm.typeI D)
    have hprefix := h719.prefixIsometric_of_s_le a b R s
      (i.val + 1) (by omega) i.next_le_sameRank
    exact longRepresentationAt_of_prefix_isometric720
      a b c hac i hnext hcurrent hprefix htrigger
  · have hsTwo := D.stopping.two_le
    have hEarly : i.val ≤ s - 2 := by omega
    exact (D.longTrigger_false_of_le_sMinusTwo
      a b c R s i hEarly htrigger).elim

theorem Lemma718TypeIINormalForm.longRepresentationConditions
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (hac : RepresentationConditions a c le_rfl) :
    b.LongRepresentationConditions c := by
  rw [b.longRepresentationConditions_iff_forall_trigger c]
  intro i htrigger
  by_cases hLate : s - 1 ≤ i.val
  · have hiSucc := i.succ_lt_large
    have hnext : a.order ⟨i.val + 1, i.succ_lt_large⟩ =
        b.order ⟨i.val + 1, i.succ_lt_large⟩ :=
      D.tailOrder a b R s ⟨i.val + 1, i.succ_lt_large⟩ (by
        change s ≤ i.val + 1
        omega)
    have hcurrent : a.order ⟨i.val, by omega⟩ ≤
        b.order ⟨i.val, by omega⟩ :=
      D.sourceOrder_le_target_of_sMinusOne_le a b R s
        ⟨i.val, by omega⟩ hLate
    have h719 := a.beli2019Lemma719_of_normalForm b R s
      (Beli2019Lemma718NormalForm.typeII D)
    have hprefix := h719.prefixIsometric_of_s_le a b R s
      (i.val + 1) (by omega) i.next_le_sameRank
    exact longRepresentationAt_of_prefix_isometric720
      a b c hac i hnext hcurrent hprefix htrigger
  · have hsTwo := D.stopping.two_le
    have hEarly : i.val ≤ s - 2 := by omega
    exact (D.longTrigger_false_of_le_sMinusTwo
      a b c R s i hEarly htrigger).elim

theorem Lemma718TypeIIINormalForm.longRepresentationConditions
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s)
    (hac : RepresentationConditions a c le_rfl) :
    b.LongRepresentationConditions c := by
  rw [b.longRepresentationConditions_iff_forall_trigger c]
  intro i htrigger
  by_cases hLate : s - 1 ≤ i.val
  · have hiSucc := i.succ_lt_large
    have hnext : a.order ⟨i.val + 1, i.succ_lt_large⟩ =
        b.order ⟨i.val + 1, i.succ_lt_large⟩ :=
      D.tailOrder a b R s ⟨i.val + 1, i.succ_lt_large⟩ (by
        change s ≤ i.val + 1
        omega)
    have hcurrent : a.order ⟨i.val, by omega⟩ ≤
        b.order ⟨i.val, by omega⟩ :=
      D.sourceOrder_le_target_of_sMinusOne_le a b R s
        ⟨i.val, by omega⟩ hLate
    have h719 := a.beli2019Lemma719_of_normalForm b R s
      (Beli2019Lemma718NormalForm.typeIII D)
    have hprefix := h719.prefixIsometric_of_s_le a b R s
      (i.val + 1) (by omega) i.next_le_sameRank
    exact longRepresentationAt_of_prefix_isometric720
      a b c hac i hnext hcurrent hprefix htrigger
  · have hsTwo := D.stopping.two_le
    have hEarly : i.val ≤ s - 2 := by omega
    exact (D.longTrigger_false_of_le_sMinusTwo
      a b c R s i hEarly htrigger).elim

/-- Condition 2.1(iv) survives every normal form of Lemma 7.18. -/
theorem Beli2019Lemma718NormalForm.longRepresentationConditions
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Beli2019Lemma718NormalForm a b R s)
    (hac : RepresentationConditions a c le_rfl) :
    b.LongRepresentationConditions c := by
  cases D with
  | typeI data =>
      exact data.longRepresentationConditions a b c R s hac
  | typeII data =>
      exact data.longRepresentationConditions a b c R s hac
  | typeIII data =>
      exact data.longRepresentationConditions a b c R s hac

end BONG.GoodBONG

end Bong
