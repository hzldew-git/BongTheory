/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716LongExceptional

/-!
# Beli (2019), Lemma 7.16: condition (iv)

This file closes the long-prefix representation condition.  Before the
replacement boundary, its strict order jump is impossible except at the
single type-I index `s - 3`, handled by the endpoint-tower argument.  At and
after the unchanged tail, the original condition (iv) transports through the
prefix isometries of Lemma 7.15.
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
variable [DyadicDiscriminantClassLaws K]
variable [DyadicAlternatingEndpointTowerRepresentationLaws K]

private theorem longRepresentationIndex_eq_of_val_eq
    {m n : Nat} {i j : LongRepresentationIndex m n}
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  simp_all

/-- Transport one instance of condition (iv) from the original BONG to the
replacement.  Equality of the next order transfers the two strict clauses;
the weak inequality at the current order transfers in the required
direction. -/
theorem lemma716_longRepresentationAt_of_prefix_isometric
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (hac : RepresentationConditionsPrime a c le_rfl)
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
                2 * (ramificationIndex K : Int) := by
            omega
          _ ≤ c.order ⟨i.val - 2, by omega⟩ +
                2 * (ramificationIndex K : Int) := htrigger.2.2
  have hacRep :=
    (a.longRepresentationConditions_iff_forall_trigger c).mp
      hac.longRepresentations i htriggerA
  have habRep := diagonalRepresents_prefixValues_of_prefix_isometric
    a b (i.val + 1) i.next_le_sameRank hprefix
  exact hacRep.trans habRep

/-- In the elementary type-I prefix, condition (iv)'s strict jump cannot
occur before `s - 3`: adjacent orders differ by exactly `2e` in the upward
direction and have the reverse inequality in the other parity. -/
theorem lemma716_typeI_longTrigger_false_of_lt_sMinusThree
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (i : LongRepresentationIndex (n + 3) (n + 3))
    (hi : i.val < s - 3) :
    ¬ b.LongRepresentationTrigger c i := by
  intro htrigger
  let current : Fin (n + 3) := ⟨i.val, by
    have := i.succ_lt_large
    omega⟩
  let next : Fin (n + 3) := ⟨i.val + 1, i.succ_lt_large⟩
  have hjump : b.order current + 2 * (ramificationIndex K : Int) <
      b.order next := by
    have h := htrigger.2.2.trans_lt htrigger.2.1
    simpa only [current, next] using h
  rcases Nat.even_or_odd i.val with heven | hodd
  · have hnextOdd : Odd next.val := by
      rcases heven with ⟨d, hd⟩
      exact ⟨d, by dsimp only [next]; omega⟩
    have hcurrent := a.lemma716_typeI_prefix_order_eq_high b R s D hthird
      hvalues current (by dsimp only [current]; omega) (by
        simpa only [current] using heven)
    have hnext := a.lemma716_typeI_prefix_order_eq_low b R s D hthird
      hvalues next (by dsimp only [next]; omega) hnextOdd
    have he := ramificationIndex_pos (K := K)
    rw [hcurrent, hnext] at hjump
    omega
  · have hnextEven : Even next.val := by
      rcases hodd with ⟨d, hd⟩
      exact ⟨d + 1, by dsimp only [next]; omega⟩
    have hcurrent := a.lemma716_typeI_prefix_order_eq_low b R s D hthird
      hvalues current (by dsimp only [current]; omega) (by
        simpa only [current] using hodd)
    have hnext := a.lemma716_typeI_prefix_order_eq_high b R s D hthird
      hvalues next (by dsimp only [next]; omega) hnextEven
    rw [hcurrent, hnext] at hjump
    omega

/-- The same alternating calculation excludes every type-II long trigger at
an index below `s - 3`. -/
theorem lemma716_typeII_longTrigger_false_of_lt_sMinusThree
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hII : Lemma714IsTypeII a R s) (ε η : Kˣ)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η j)
    (i : LongRepresentationIndex (n + 3) (n + 3))
    (hi : i.val < s - 3) :
    ¬ b.LongRepresentationTrigger c i := by
  intro htrigger
  let current : Fin (n + 3) := ⟨i.val, by
    have := i.succ_lt_large
    omega⟩
  let next : Fin (n + 3) := ⟨i.val + 1, i.succ_lt_large⟩
  have hjump : b.order current + 2 * (ramificationIndex K : Int) <
      b.order next := by
    have h := htrigger.2.2.trans_lt htrigger.2.1
    simpa only [current, next] using h
  rcases Nat.even_or_odd i.val with heven | hodd
  · have hnextOdd : Odd next.val := by
      rcases heven with ⟨d, hd⟩
      exact ⟨d, by dsimp only [next]; omega⟩
    have hcurrent := a.lemma716_typeII_prefix_order_eq_high b R s D hthird
      hII ε η hvalues current (by dsimp only [current]; omega) (by
        simpa only [current] using heven)
    have hnext := a.lemma716_typeII_prefix_order_eq_low b R s D hthird
      hII ε η hvalues next (by dsimp only [next]; omega) hnextOdd
    have he := ramificationIndex_pos (K := K)
    rw [hcurrent, hnext] at hjump
    omega
  · have hnextEven : Even next.val := by
      rcases hodd with ⟨d, hd⟩
      exact ⟨d + 1, by dsimp only [next]; omega⟩
    have hcurrent := a.lemma716_typeII_prefix_order_eq_low b R s D hthird
      hII ε η hvalues current (by dsimp only [current]; omega) (by
        simpa only [current] using hodd)
    have hnext := a.lemma716_typeII_prefix_order_eq_high b R s D hthird
      hII ε η hvalues next (by dsimp only [next]; omega) hnextEven
    rw [hcurrent, hnext] at hjump
    omega

/-- In type II the strict jump required by condition (iv) is impossible at
all paper indices `i ≤ s - 1`. -/
theorem lemma716_typeII_longTrigger_false_of_le_sMinusOne
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hII : Lemma714IsTypeII a R s) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η j)
    (i : LongRepresentationIndex (n + 3) (n + 3))
    (hi : i.val ≤ s - 1) :
    ¬ b.LongRepresentationTrigger c i := by
  by_cases hEarly : i.val < s - 3
  · exact a.lemma716_typeII_longTrigger_false_of_lt_sMinusThree
      b c R s D hthird hII ε η hvalues i hEarly
  intro htrigger
  let current : Fin (n + 3) := ⟨i.val, by
    have := i.succ_lt_large
    omega⟩
  let next : Fin (n + 3) := ⟨i.val + 1, i.succ_lt_large⟩
  have hjump : b.order current + 2 * (ramificationIndex K : Int) <
      b.order next := by
    have h := htrigger.2.2.trans_lt htrigger.2.1
    simpa only [current, next] using h
  have hsRank := D.le_rank
  have hsInterior := Classical.choose hII
  have he := ramificationIndex_pos (K := K)
  by_cases hFirst : i.val = s - 3
  · have hsSix : 6 ≤ s := by
      rcases D.even with ⟨d, hd⟩
      have := i.one_lt
      omega
    have hcurrentOdd : Odd current.val := by
      rcases D.even with ⟨d, hd⟩
      exact ⟨d - 2, by dsimp only [current]; omega⟩
    have hcurrentOrder : b.order current =
        R - 2 * (ramificationIndex K : Int) + 1 :=
      a.lemma716_typeII_prefix_order_eq_low b R s D hthird
        hII ε η hvalues current (by
          dsimp only [current]
          omega) hcurrentOdd
    have hnextIndex : next = ⟨s - 2, by omega⟩ := by
      apply Fin.ext
      dsimp only [next]
      omega
    have hnextOrder : b.order next = R + 1 := by
      rw [hnextIndex]
      exact a.lemma716_typeII_leftBoundary_order_eq b R s D hII
        ε η hεUnit hηUnit hvalues
    rw [hcurrentOrder, hnextOrder] at hjump
    omega
  · by_cases hSecond : i.val = s - 2
    · have hcurrentIndex : current = ⟨s - 2, by omega⟩ := by
        apply Fin.ext
        dsimp only [current]
        omega
      have hnextIndex : next = ⟨s - 1, by omega⟩ := by
        apply Fin.ext
        dsimp only [next]
        omega
      have hcurrentOrder : b.order current = R + 1 := by
        rw [hcurrentIndex]
        exact a.lemma716_typeII_leftBoundary_order_eq b R s D hII
          ε η hεUnit hηUnit hvalues
      have hnextOrder : b.order next =
          R - 2 * (ramificationIndex K : Int) + 3 := by
        rw [hnextIndex]
        exact a.lemma716_typeII_rightBoundary_order_eq b R s D hII
          ε η hεUnit hηUnit hvalues
      rw [hcurrentOrder, hnextOrder] at hjump
      omega
    · have hThird : i.val = s - 1 := by omega
      have hcurrentIndex : current = ⟨s - 1, by omega⟩ := by
        apply Fin.ext
        dsimp only [current]
        omega
      have hnextIndex : next = ⟨s, hsInterior⟩ := by
        apply Fin.ext
        dsimp only [next]
        omega
      have hcurrentOrder : b.order current =
          R - 2 * (ramificationIndex K : Int) + 3 := by
        rw [hcurrentIndex]
        exact a.lemma716_typeII_rightBoundary_order_eq b R s D hII
          ε η hεUnit hηUnit hvalues
      have hnextOrder : b.order next = R + 1 := by
        rw [hnextIndex]
        exact a.lemma716_typeII_tailBoundary_order_eq b R s D hII
          ε η hεUnit hηUnit hvalues
      rw [hcurrentOrder, hnextOrder] at hjump
      omega

/-- The second exceptional type-I coefficient is followed by a lower-order
coefficient, so it can never be the left side of condition (iv)'s strict
jump. -/
theorem lemma716_typeI_longTrigger_false_at_sMinusTwo
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (i : LongRepresentationIndex (n + 3) (n + 3))
    (hi : i.val = s - 2) :
    ¬ b.LongRepresentationTrigger c i := by
  intro htrigger
  let current : Fin (n + 3) := ⟨i.val, by
    have := i.succ_lt_large
    omega⟩
  let next : Fin (n + 3) := ⟨i.val + 1, i.succ_lt_large⟩
  have hjump : b.order current + 2 * (ramificationIndex K : Int) <
      b.order next := by
    have h := htrigger.2.2.trans_lt htrigger.2.1
    simpa only [current, next] using h
  have hsRank := D.le_rank
  have hsTwo := D.two_le
  have hcurrentIndex : current = ⟨s - 2, by omega⟩ := by
    apply Fin.ext
    change i.val = s - 2
    exact hi
  have hnextIndex : next = ⟨s - 1, by omega⟩ := by
    apply Fin.ext
    change i.val + 1 = s - 1
    rw [hi]
    omega
  have hcurrentOrder : b.order current = R + 2 := by
    rw [hcurrentIndex]
    exact a.lemma716_typeI_leftBoundary_order_eq b R s D hfirst hvalues
  have hnextOrder : b.order next =
      R - 2 * (ramificationIndex K : Int) + 2 := by
    rw [hnextIndex]
    exact a.lemma716_typeI_rightBoundary_order_eq b R s D hsecond hvalues
  have he := ramificationIndex_pos (K := K)
  have hjumpNumeric : R + 2 + 2 * (ramificationIndex K : Int) <
      R - 2 * (ramificationIndex K : Int) + 2 := by
    calc
      R + 2 + 2 * (ramificationIndex K : Int) =
          b.order current + 2 * (ramificationIndex K : Int) := by
        rw [hcurrentOrder]
      _ < b.order next := hjump
      _ = R - 2 * (ramificationIndex K : Int) + 2 := hnextOrder
  omega

/-- Complete condition (iv) in the type-I branch of Lemma 7.16. -/
theorem lemma716_typeI_longRepresentationConditions
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (hprefix : ∀ (k : Nat), s ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk)) :
    b.LongRepresentationConditions c := by
  rw [b.longRepresentationConditions_iff_forall_trigger c]
  intro i htrigger
  by_cases hEarly : i.val < s - 3
  · exact (a.lemma716_typeI_longTrigger_false_of_lt_sMinusThree
      b c R s D hthird hvalues i hEarly htrigger).elim
  by_cases hExceptional : i.val = s - 3
  · have hsSix : 6 ≤ s := by
      rcases D.even with ⟨d, hd⟩
      have := i.one_lt
      omega
    let j : LongRepresentationIndex (n + 3) (n + 3) :=
      { val := s - 3
        one_lt := by omega
        succ_lt_large := by have := D.le_rank; omega
        le_small_succ := by have := D.le_rank; omega }
    have hij : i = j := longRepresentationIndex_eq_of_val_eq hExceptional
    rw [hij] at htrigger ⊢
    have hrep := a.lemma716_typeI_sMinusThree_longRepresentationAt b c R s D
      hfirst hthird hnorm hvalues hsSix htrigger
    exact prefixRepresents_cast c b (by dsimp only [j]; omega)
      (by dsimp only [j]; omega) hrep
  · by_cases hMinusTwo : i.val = s - 2
    · exact (a.lemma716_typeI_longTrigger_false_at_sMinusTwo b c R s D
        hfirst hsecond hvalues i hMinusTwo htrigger).elim
    · have htail : s - 1 ≤ i.val := by omega
      have hnext : a.order ⟨i.val + 1, i.succ_lt_large⟩ =
          b.order ⟨i.val + 1, i.succ_lt_large⟩ :=
        horders _ (by
          change s ≤ i.val + 1
          omega)
      have hcurrent : a.order ⟨i.val, by
            have := i.succ_lt_large
            omega⟩ ≤
          b.order ⟨i.val, by
            have := i.succ_lt_large
            omega⟩ := by
        by_cases hboundary : i.val = s - 1
        · have hsFour : 4 ≤ s := by
            rcases D.even with ⟨d, hd⟩
            have := i.one_lt
            omega
          have ha := a.lemma714_selected_last_order R s
            D.toLemma714MinimalityData hsFour hthird
          have hb := a.lemma716_typeI_rightBoundary_order_eq b R s D hsecond
            hvalues
          have hi : (⟨i.val, by
                have := i.succ_lt_large
                omega⟩ : Fin (n + 3)) = ⟨s - 1, by
                  have := D.le_rank
                  omega⟩ := by
            apply Fin.ext
            exact hboundary
          rw [hi, ha, hb]
          omega
        · apply (horders _ ?_).le
          change s ≤ i.val
          omega
      have hp := hprefix (i.val + 1) (by
        change s ≤ i.val + 1
        omega) i.next_le_sameRank
      exact a.lemma716_longRepresentationAt_of_prefix_isometric b c hac i
        hnext hcurrent hp htrigger

/-- Complete condition (iv) in the type-II branch of Lemma 7.16. -/
theorem lemma716_typeII_longRepresentationConditions
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hII : Lemma714IsTypeII a R s) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η j)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (hprefix : ∀ (k : Nat), s + 1 ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk)) :
    b.LongRepresentationConditions c := by
  rw [b.longRepresentationConditions_iff_forall_trigger c]
  intro i htrigger
  by_cases hEarly : i.val ≤ s - 1
  · exact (a.lemma716_typeII_longTrigger_false_of_le_sMinusOne b c R s D
      hthird hII ε η hεUnit hηUnit hvalues i hEarly htrigger).elim
  · have htail : s ≤ i.val := by omega
    have hnext : a.order ⟨i.val + 1, i.succ_lt_large⟩ =
        b.order ⟨i.val + 1, i.succ_lt_large⟩ :=
      horders _ (by
        change s ≤ i.val + 1
        omega)
    have hcurrent : a.order ⟨i.val, by
          have := i.succ_lt_large
          omega⟩ ≤
        b.order ⟨i.val, by
          have := i.succ_lt_large
          omega⟩ := (horders _ htail).le
    have hp := hprefix (i.val + 1) (by
      change s + 1 ≤ i.val + 1
      omega) i.next_le_sameRank
    exact a.lemma716_longRepresentationAt_of_prefix_isometric b c hac i
      hnext hcurrent hp htrigger

end BONG.GoodBONG

end Bong
