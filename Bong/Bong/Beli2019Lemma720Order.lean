/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma718OrderProfiles
import Bong.Bong.Beli2019Lemma719Closure
import Bong.Bong.Beli2019Lemma716OrdersBasic

/-!
# Beli (2019), Section 7 after Lemma 7.19: order condition

For each normal form of Lemma 7.18, this file proves that the replacement
BONG satisfies condition 2.1(i) relative to the comparison lattice. The
common suffix transfers the old order clause, while the modified prefix is
controlled by the strict norm-ideal inequality. Type III uses the alternative
adjacent-pair inequality at its odd positions.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

theorem Lemma718TypeINormalForm.tailOrder
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (i : Fin (n + 3)) (hsi : s ≤ i.val) :
    a.order i = b.order i := by
  have hv : b.valueUnit i = a.valueUnit i :=
    lemma718_typeI_realized_suffix a b s D.targetValues i hsi
  calc
    a.order i = ordUnit K (a.valueUnit i) := a.toBONG.order_eq_ordUnit i
    _ = ordUnit K (b.valueUnit i) := congrArg (ordUnit K) hv.symm
    _ = b.order i := (b.toBONG.order_eq_ordUnit i).symm

theorem Lemma718TypeIINormalForm.tailOrder
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (i : Fin (n + 3)) (hsi : s ≤ i.val) :
    a.order i = b.order i := by
  have hv : b.valueUnit i = a.valueUnit i :=
    lemma718_typeII_realized_suffix a b s D.targetValues i hsi
  calc
    a.order i = ordUnit K (a.valueUnit i) := a.toBONG.order_eq_ordUnit i
    _ = ordUnit K (b.valueUnit i) := congrArg (ordUnit K) hv.symm
    _ = b.order i := (b.toBONG.order_eq_ordUnit i).symm

theorem Lemma718TypeIIINormalForm.tailOrder
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s)
    (i : Fin (n + 3)) (hsi : s ≤ i.val) :
    a.order i = b.order i := by
  have hv : b.valueUnit i = a.valueUnit i :=
    lemma718_typeIII_realized_suffix a b s D.targetValues i hsi
  calc
    a.order i = ordUnit K (a.valueUnit i) := a.toBONG.order_eq_ordUnit i
    _ = ordUnit K (b.valueUnit i) := congrArg (ordUnit K) hv.symm
    _ = b.order i := (b.toBONG.order_eq_ordUnit i).symm

theorem Lemma718TypeINormalForm.representationOrderCondition
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationOrderCondition c le_rfl := by
  have hfirst : a.order 0 = R :=
    D.sourceOrder_even a b R s ⟨0, by omega⟩ (by
      change 0 < s
      have hsTwo := D.stopping.two_le
      omega) (by simp)
  intro i
  by_cases his : i.val < s
  · rcases Nat.even_or_odd i.val with hiEven | hiOdd
    · left
      have hcomparison := a.lemma716_comparison_even_order_ge c R hfirst
        hnorm i hiEven
      rw [D.targetOrder_even a b R s i his hiEven]
      exact hcomparison
    · left
      have hcomparison := a.lemma716_comparison_odd_order_ge c R hfirst
        hnorm i hiOdd
      rw [D.targetOrder_odd a b R s i his hiOdd]
      exact hcomparison
  · exact lemma716_orderClause_of_tail_order_eq a b c s hac
      (fun j hsj ↦ D.tailOrder a b R s j hsj) i (by omega)

theorem Lemma718TypeIINormalForm.representationOrderCondition
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationOrderCondition c le_rfl := by
  have hfirst : a.order 0 = R :=
    D.sourceOrder_even a b R s ⟨0, by omega⟩ (by
      change 0 < s
      have hsTwo := D.stopping.two_le
      omega) (by simp)
  intro i
  by_cases his : i.val < s
  · rcases Nat.even_or_odd i.val with hiEven | hiOdd
    · left
      have hcomparison := a.lemma716_comparison_even_order_ge c R hfirst
        hnorm i hiEven
      have htarget := D.targetOrder_even a b R s i his hiEven
      rw [htarget]
      split <;> omega
    · left
      have hcomparison := a.lemma716_comparison_odd_order_ge c R hfirst
        hnorm i hiOdd
      have htarget := D.targetOrder_odd a b R s i his hiOdd
      rw [htarget]
      split <;> omega
  · exact lemma716_orderClause_of_tail_order_eq a b c s hac
      (fun j hsj ↦ D.tailOrder a b R s j hsj) i (by omega)

theorem Lemma718TypeIIINormalForm.representationOrderCondition
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationOrderCondition c le_rfl := by
  have hfirst : a.order 0 = R :=
    D.sourceOrder_even a b R s ⟨0, by omega⟩ (by
      change 0 < s
      have hsTwo := D.stopping.two_le
      omega) (by simp)
  intro i
  by_cases his : i.val < s
  · rcases Nat.even_or_odd i.val with hiEven | hiOdd
    · left
      have hcomparison := a.lemma716_comparison_even_order_ge c R hfirst
        hnorm i hiEven
      rw [D.targetOrder_even a b R s i his hiEven]
      omega
    · right
      have hi0 : 0 < i.val := by
        rcases hiOdd with ⟨j, hj⟩
        omega
      rcases D.typeIII with ⟨hsRank, hsourceAtS⟩
      have hiLarge : i.val + 1 < n + 3 := by omega
      refine ⟨hi0, hiLarge, ?_⟩
      let previous : Fin (n + 3) := ⟨i.val - 1, by omega⟩
      let next : Fin (n + 3) := ⟨i.val + 1, hiLarge⟩
      have hpreviousEven : Even previous.val := by
        rcases hiOdd with ⟨j, hj⟩
        exact ⟨j, by
          change i.val - 1 = j + j
          omega⟩
      have hnextEven : Even next.val := by
        rcases hiOdd with ⟨j, hj⟩
        exact ⟨j + 1, by
          change i.val + 1 = (j + 1) + (j + 1)
          omega⟩
      have hprevious := a.lemma716_comparison_even_order_ge c R hfirst
        hnorm previous hpreviousEven
      have hcurrent := a.lemma716_comparison_odd_order_ge c R hfirst
        hnorm i hiOdd
      have htargetCurrent := D.targetOrder_odd a b R s i his hiOdd
      have htargetNext : b.order next = R := by
        by_cases hnextPrefix : next.val < s
        · exact D.targetOrder_even a b R s next hnextPrefix hnextEven
        · have hnextNot : ¬i.val + 1 < s := by
            simpa only [next] using hnextPrefix
          have hnextEq : next.val = s := by
            change i.val + 1 = s
            omega
          have htail := D.tailOrder a b R s next (by omega)
          have hsource : a.order next = R := by
            have hindex : next = (⟨s, hsRank⟩ : Fin (n + 3)) :=
              Fin.ext hnextEq
            simpa only [hindex] using hsourceAtS
          omega
      have hsum : b.order i + b.order next ≤
          c.order previous + c.order i := by
        omega
      simpa only [previous, next] using hsum
  · exact lemma716_orderClause_of_tail_order_eq a b c s hac
      (fun j hsj ↦ D.tailOrder a b R s j hsj) i (by omega)

variable [laws : DyadicDiscriminantClassLaws K]

/-- All three replacements have the original target order sequence on the
common suffix. -/
theorem Beli2019Lemma718NormalForm.tailOrder
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Beli2019Lemma718NormalForm a b R s)
    (i : Fin (n + 3)) (hsi : s ≤ i.val) :
    a.order i = b.order i := by
  cases D with
  | typeI data => exact data.tailOrder a b R s i hsi
  | typeII data => exact data.tailOrder a b R s i hsi
  | typeIII data => exact data.tailOrder a b R s i hsi

/-- Condition 2.1(i) survives each of the three replacements in Lemma 7.18. -/
theorem Beli2019Lemma718NormalForm.representationOrderCondition
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Beli2019Lemma718NormalForm a b R s)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationOrderCondition c le_rfl := by
  cases D with
  | typeI data =>
      exact data.representationOrderCondition a b c R s hac hnorm
  | typeII data =>
      exact data.representationOrderCondition a b c R s hac hnorm
  | typeIII data =>
      exact data.representationOrderCondition a b c R s hac hnorm

end BONG.GoodBONG

end Bong
