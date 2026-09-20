/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.He2022ClassicSectionTwo
import Bong.Bong.Beli2019Lemma75

/-!
# He (2024), Proposition 2.4

The extra strength of the classic-integral hypothesis enters through the
scale formula: every adjacent order sum is nonnegative, and paper-even
orders are bounded below by `-e` rather than `-2e`.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- All six clauses of He, Proposition 2.4, in zero-based indexing. -/
structure HeClassicProposition24Conclusions {n : Nat}
    (a : GoodBONG q L (n + 2)) : Prop where
  oddIndexed (i j : Fin (n + 2)) (hij : i ≤ j)
      (hi : Even i.val) (hj : Even j.val) :
    0 ≤ a.order i ∧ a.order i ≤ a.order j
  evenIndexed (i j : Fin (n + 2)) (hij : i ≤ j)
      (hi : Odd i.val) (hj : Odd j.val) :
    -(ramificationIndex K : Int) ≤ a.order i ∧
      a.order i ≤ a.order j
  adjacentOrderSum (i : Fin (n + 1)) :
    0 ≤ a.adjacentOrderSum i
  zeroAtPaperOdd (j : Fin (n + 2)) (hj : Even j.val)
      (hjOrder : a.order j = 0) :
    (∀ i : Fin (n + 2), i ≤ j → Even i.val → a.order i = 0) ∧
      (∀ i : Fin (n + 2), i ≤ j → Even (a.order i))
  extremalPaperEven (j : Fin (n + 2)) (hj : Odd j.val)
      (hjOrder : a.order j = -(ramificationIndex K : Int)) :
    (∀ i : Fin (n + 2), i ≤ j → Odd i.val →
      let gap : Fin (n + 1) := ⟨i.val - 1, by omega⟩
      let previous : Fin (n + 2) := ⟨i.val - 1, by omega⟩
      a.order previous = (ramificationIndex K : Int) ∧
        a.order i = -(ramificationIndex K : Int) ∧
        ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
          a.heHuAdjacentCappedDefect gap ∧
        ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
          a.adjacentDefect gap) ∧
      (let lastGap : Fin (n + 1) := ⟨j.val - 1, by omega⟩
       ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
         a.truncatedPrefixDefect a
           ((-1) ^ ((lastGap.val + 2) / 2)) 0 (lastGap.val + 2))
  nonnegativeOfFirstZero (hfirst : a.order 0 = 0) :
    ∀ i : Fin (n + 2), 0 ≤ a.order i
  zeroThroughNonpositivePair (hfirst : a.order 0 = 0)
      (j : Fin (n + 1)) (hsum : a.adjacentOrderSum j ≤ 0) :
    ∀ i : Fin (n + 2), i ≤ j.castSucc → a.order i = 0
  zeroPairForcesPrefixZero (j : Fin (n + 1))
      (hleft : a.order j.castSucc = 0)
      (hright : a.order j.succ = 0) :
    ∀ i : Fin (n + 2), i ≤ j.succ → a.order i = 0
  alphaOneOnZeroPrefix (j : Fin (n + 1))
      (horders : ∀ i : Fin (n + 2), i ≤ j.castSucc → a.order i = 0)
      (k : Fin (n + 1)) (hkj : k ≤ j) (halpha : a.alphaValue k ≤ 1) :
    ∀ i : Fin (n + 1), i < j → a.alphaValue i = 1

/-- He, Proposition 2.4. -/
theorem he2022ClassicProposition24 {n : Nat}
    (a : GoodBONG q L (n + 2))
    (hClassic : Lattice.IsClassicIntegral q L) :
    HeClassicProposition24Conclusions a := by
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  letI : Beli2009AlphaParityLaws.{u, v} K :=
    beliUniversalAlphaParityLaws
  let hIntegral := hClassic.isIntegral
  let ordinary := a.heHu2022Proposition27i hIntegral
  have hfirstPair := (a.isClassicIntegral_iff_firstOrders).1 hClassic
  have hAdjacentSum (i : Fin (n + 1)) :
      0 ≤ a.adjacentOrderSum i := by
    have hmono := a.adjacentOrderSum_monotone (Fin.zero_le i)
    have hzero : a.adjacentOrderSum (0 : Fin (n + 1)) =
        a.order 0 + a.order 1 := by rfl
    rw [hzero] at hmono
    exact hfirstPair.2.trans hmono
  have hOdd (i j : Fin (n + 2)) (hij : i ≤ j)
      (hi : Even i.val) (hj : Even j.val) :
      0 ≤ a.order i ∧ a.order i ≤ a.order j :=
    ordinary.oddIndexed i j hij hi hj
  have hEven (i j : Fin (n + 2)) (hij : i ≤ j)
      (hi : Odd i.val) (hj : Odd j.val) :
      -(ramificationIndex K : Int) ≤ a.order i ∧
        a.order i ≤ a.order j := by
    have hmono := (ordinary.evenIndexed i j hij hi hj).2
    have hiPos : 0 < i.val := by
      rcases hi with ⟨t, ht⟩
      omega
    let previous : Fin (n + 2) := ⟨i.val - 1, by omega⟩
    let gap : Fin (n + 1) := ⟨i.val - 1, by omega⟩
    have hindices : gap.castSucc = previous ∧ gap.succ = i := by
      constructor
      · apply Fin.ext
        rfl
      · apply Fin.ext
        simp only [gap, Fin.val_succ]
        omega
    have hsum := hAdjacentSum gap
    have hgap := a.orderGap_ge_neg_two_mul_e gap
    unfold adjacentOrderSum at hsum
    unfold orderGap at hgap
    rw [hindices.1, hindices.2] at hsum hgap
    constructor
    · omega
    · exact hmono
  have hNonnegative (hfirst : a.order 0 = 0)
      (i : Fin (n + 2)) : 0 ≤ a.order i := by
    rcases Nat.even_or_odd i.val with hiEven | hiOdd
    · have h := hOdd 0 i (Fin.zero_le i) Even.zero hiEven
      exact h.1.trans h.2
    · have hiPos : 0 < i.val := by
        rcases hiOdd with ⟨t, ht⟩
        omega
      let one : Fin (n + 2) := ⟨1, by omega⟩
      have hOneOdd : Odd one.val := by simp [one]
      have hOneNonnegative : 0 ≤ a.order one := by
        have hsum := hAdjacentSum (0 : Fin (n + 1))
        change 0 ≤ a.order 0 + a.order 1 at hsum
        rw [hfirst, zero_add] at hsum
        change 0 ≤ a.order (1 : Fin (n + 2)) at hsum
        have hone : one = (1 : Fin (n + 2)) := by
          apply Fin.ext
          rfl
        rw [hone]
        exact hsum
      exact hOneNonnegative.trans
        (hEven one i (Fin.mk_le_mk.mpr hiPos) hOneOdd hiOdd).2
  refine {
    oddIndexed := hOdd
    evenIndexed := hEven
    adjacentOrderSum := hAdjacentSum
    zeroAtPaperOdd := ?_
    extremalPaperEven := ?_
    nonnegativeOfFirstZero := hNonnegative
    zeroThroughNonpositivePair := ?_
    zeroPairForcesPrefixZero := ?_
    alphaOneOnZeroPrefix := ?_ }
  · intro j hj hjOrder
    let C := a.heHu2022Proposition27ii hIntegral j hj hjOrder
    exact ⟨C.precedingPaperOddOrders, C.precedingOrdersEven⟩
  · intro j hj hjOrder
    have hjPos : 0 < j.val := by
      rcases hj with ⟨t, ht⟩
      omega
    let lastGap : Fin (n + 1) := ⟨j.val - 1, by omega⟩
    let previous : Fin (n + 2) := ⟨j.val - 1, by omega⟩
    have hlastEven : Even lastGap.val := by
      rcases hj with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      simp only [lastGap]
      omega
    have hpreviousEven : Even previous.val := by
      simpa only [previous, lastGap] using hlastEven
    have hpreviousLe : previous ≤ j := Fin.mk_le_mk.mpr (by omega)
    have hpreviousOrder :
        a.order previous = (ramificationIndex K : Int) := by
      have hlower := hAdjacentSum lastGap
      have hgap := a.orderGap_ge_neg_two_mul_e lastGap
      have hindices : lastGap.castSucc = previous ∧ lastGap.succ = j := by
        constructor
        · apply Fin.ext
          rfl
        · apply Fin.ext
          simp only [lastGap, Fin.val_succ]
          omega
      unfold adjacentOrderSum at hlower
      unfold orderGap at hgap
      rw [hindices.1, hindices.2, hjOrder] at hlower hgap
      omega
    have hfirstOrder : a.order (0 : Fin (n + 2)) =
        (ramificationIndex K : Int) := by
      have hfirstLower : 0 ≤ a.order (0 : Fin (n + 2)) :=
        (hOdd 0 previous (Fin.zero_le previous) Even.zero hpreviousEven).1
      have hone : (1 : Fin (n + 2)) ≤ j :=
        Fin.mk_le_mk.mpr hjPos
      have hOneOrder : a.order (1 : Fin (n + 2)) =
          -(ramificationIndex K : Int) := by
        have hOneOdd : Odd (1 : Nat) := odd_one
        have hbounds := hEven 1 j hone hOneOdd hj
        omega
      have hsum := hAdjacentSum (0 : Fin (n + 1))
      have hgap := a.orderGap_ge_neg_two_mul_e (0 : Fin (n + 1))
      change 0 ≤ a.order 0 + a.order 1 at hsum
      change -(2 * (ramificationIndex K : Int)) ≤
        a.order 1 - a.order 0 at hgap
      rw [hOneOrder] at hsum hgap
      omega
    let first : Fin (n + 1) := ⟨0, by omega⟩
    have hterminal : a.order lastGap.succ =
        (ramificationIndex K : Int) -
          2 * (ramificationIndex K : Int) := by
      have hindex : lastGap.succ = j := by
        apply Fin.ext
        simp only [lastGap, Fin.val_succ]
        omega
      rw [hindex, hjOrder]
      ring
    have hfirstCast : first.castSucc = (0 : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    let D := a.beli2019Lemma75 first lastGap
      (ramificationIndex K : Int) (Fin.zero_le lastGap)
      (by simpa only [first, Nat.sub_zero] using hlastEven)
      (by simpa only [hfirstCast] using hfirstOrder) hterminal
    constructor
    · intro i hij hi
      have hiPos : 0 < i.val := by
        rcases hi with ⟨t, ht⟩
        omega
      let gap : Fin (n + 1) := ⟨i.val - 1, by omega⟩
      let iprevious : Fin (n + 2) := ⟨i.val - 1, by omega⟩
      have hgapEven : Even (gap.val - first.val) := by
        rcases hi with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        simp only [gap, first, Nat.sub_zero]
        omega
      have hgapLe : gap ≤ lastGap :=
        Fin.mk_le_mk.mpr (Nat.sub_le_sub_right hij 1)
      have hindices : gap.castSucc = iprevious ∧ gap.succ = i := by
        constructor
        · apply Fin.ext
          rfl
        · apply Fin.ext
          simp only [gap, Fin.val_succ]
          omega
      have hprev := D.arithmetic.even_order gap (Fin.zero_le gap)
        hgapLe hgapEven
      have hcurrent := D.arithmetic.odd_order gap.succ (by
          simp only [gap, first, Fin.val_succ]
          omega) (by
          simp only [gap, lastGap, Fin.val_succ]
          omega) (by
          simpa [Fin.val_succ, first] using hgapEven)
      rw [hindices.1] at hprev
      rw [hindices.2] at hcurrent
      have hcurrent' : a.order i =
          -(ramificationIndex K : Int) := by
        rw [hcurrent]
        ring
      have hgapValue : a.orderGap gap =
          -(2 * (ramificationIndex K : Int)) := by
        unfold orderGap
        rw [hindices.1, hindices.2, hprev, hcurrent]
        ring
      have halpha : a.alphaValue gap = 0 :=
        (a.he2022ClassicProposition23 gap).alphaZero.mpr hgapValue
      have hcapped :=
        (a.he2022ClassicProposition23 gap).alphaZeroDefect halpha
      have hraw := (a.heHu2022Corollary23ii gap hgapValue).rawDefectLower
      exact ⟨hprev, hcurrent', hcapped, hraw⟩
    · simpa [first, lastGap] using D.arithmetic.defect_ge_two_mul_e
  · intro hfirst j hsum i hij
    have hiNonnegative := hNonnegative hfirst i
    have hiValLe : i.val ≤ j.val := Fin.mk_le_mk.mp hij
    let gap : Fin (n + 1) := ⟨i.val, lt_of_le_of_lt hiValLe j.isLt⟩
    have hgapLe : gap ≤ j := Fin.mk_le_mk.mpr hij
    have hmono := a.adjacentOrderSum_monotone hgapLe
    have hgapSum : a.adjacentOrderSum gap ≤ 0 := hmono.trans hsum
    have hleftNonnegative := hNonnegative hfirst gap.castSucc
    have hrightNonnegative := hNonnegative hfirst gap.succ
    unfold adjacentOrderSum at hgapSum
    have hleft : gap.castSucc = i := by
      apply Fin.ext
      rfl
    rw [hleft] at hgapSum hleftNonnegative
    omega
  · intro j hleft hright
    have hsum : a.adjacentOrderSum j = 0 := by
      unfold adjacentOrderSum
      rw [hleft, hright]
      omega
    have hfirst : a.order (0 : Fin (n + 2)) = 0 := by
      rcases Nat.even_or_odd j.val with hjEven | hjOdd
      · exact (a.heHu2022Proposition27ii hIntegral j.castSucc
          (by simpa using hjEven) hleft).precedingPaperOddOrders
          0 (Fin.zero_le _) Even.zero
      · have hsuccEven : Even j.succ.val := by
          rcases hjOdd with ⟨t, ht⟩
          refine ⟨t + 1, ?_⟩
          simp only [Fin.val_succ]
          omega
        exact (a.heHu2022Proposition27ii hIntegral j.succ
          hsuccEven hright).precedingPaperOddOrders
          0 (Fin.zero_le _) Even.zero
    intro i hij
    by_cases hi : i = j.succ
    · subst i
      exact hright
    · have hile : i ≤ j.castSucc := by
        have hval : i.val ≤ j.val + 1 := Fin.mk_le_mk.mp hij
        have hneVal : i.val ≠ j.val + 1 := by
          intro heq
          apply hi
          apply Fin.ext
          simpa only [Fin.val_succ] using heq
        exact Fin.mk_le_mk.mpr (by omega)
      have h := hNonnegative hfirst i
      have hiValLe : i.val ≤ j.val := Fin.mk_le_mk.mp hile
      let gap : Fin (n + 1) :=
        ⟨i.val, lt_of_le_of_lt hiValLe j.isLt⟩
      have hgapLe : gap ≤ j := Fin.mk_le_mk.mpr hile
      have hmono := a.adjacentOrderSum_monotone hgapLe
      rw [hsum] at hmono
      unfold adjacentOrderSum at hmono
      have hidx : gap.castSucc = i := by
        apply Fin.ext
        rfl
      have hrightNonnegative := hNonnegative hfirst gap.succ
      rw [hidx] at hmono
      omega
  · intro j horders k hkj halpha i hij
    have hiSuccLe : i.succ ≤ j.castSucc :=
      Fin.mk_le_mk.mpr hij
    have hiOrder := horders i.castSucc (by
      exact Fin.mk_le_mk.mpr (Nat.le_of_lt hij))
    have hiSuccOrder := horders i.succ hiSuccLe
    have hiGap : a.orderGap i = 0 := by
      unfold orderGap
      rw [hiOrder, hiSuccOrder]
      omega
    have hiAlphaNe : a.alphaValue i ≠ 0 := by
      intro hzero
      have hendpoint := (a.he2022ClassicProposition23 i).alphaZero.mp hzero
      rw [hiGap] at hendpoint
      have hePos := ramificationIndex_pos (K := K)
      omega
    have hiLower := a.heHuOne_le_alphaValue_of_ne_zero i hiAlphaNe
    have hiUpper : a.alphaValue i ≤ a.alphaValue k := by
      by_cases hik : i ≤ k
      · have hmono :=
          (a.he2022ClassicProposition22).endpointMonotonicity i k hik
        have hkOrder := horders k.castSucc (Fin.mk_le_mk.mpr hkj)
        unfold alphaLeftEndpoint at hmono
        rw [hiOrder, hkOrder] at hmono
        norm_num at hmono
        exact hmono.1
      · have hki : k ≤ i := le_of_not_ge hik
        have hkLtJ : k < j := hki.trans_lt hij
        have hkOrder := horders k.castSucc
          (Fin.mk_le_mk.mpr (Nat.le_of_lt hkLtJ))
        have hkSuccOrder := horders k.succ
          (Fin.mk_le_mk.mpr hkLtJ)
        have hmono :=
          (a.he2022ClassicProposition22).endpointMonotonicity k i hki
        unfold alphaRightEndpoint at hmono
        rw [hkSuccOrder, hiSuccOrder] at hmono
        norm_num at hmono
        exact hmono.2
    exact le_antisymm (hiUpper.trans halpha) hiLower

end BONG.GoodBONG

end Bong
