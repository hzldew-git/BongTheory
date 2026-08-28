/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma718OrderProfiles
import Bong.Bong.Beli2019Lemma718Realization

/-!
# Beli (2019), Lemma 7.18: volume change

The replacement coefficients never lower an order.  Type I and type III
raise at least one coefficient, and type II does so exactly when the selected
prefix contains a hyperbolic block after its initial discriminant block
(`s > 2`).  Hence those nontrivial replacements are proper sublattices and
strictly increase the target volume order.
-/

namespace Bong

open Dyadic
open scoped BigOperators

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

private theorem volumeOrder_lt_of_order_le_of_exists_lt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (hle : ∀ i, a.order i ≤ b.order i)
    (hlt : ∃ i, a.order i < b.order i) :
    Lattice.volumeOrder q L < Lattice.volumeOrder q M := by
  rw [a.toBONG.volumeOrder_eq_sum_order,
    b.toBONG.volumeOrder_eq_sum_order]
  rcases hlt with ⟨i, hi⟩
  exact Finset.sum_lt_sum (fun j _ ↦ hle j)
    ⟨i, Finset.mem_univ i, hi⟩

/-- Pointwise order formula for a realized type-I replacement. -/
theorem Lemma718TypeINormalForm.targetOrder_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (i : Fin (n + 3)) :
    b.order i = if i.val < s then a.order i + 1 else a.order i := by
  calc
    b.order i = ordUnit K (b.valueUnit i) :=
      b.toBONG.order_eq_ordUnit i
    _ = ordUnit K (lemma718TypeITargetValues a s i) := by
      rw [D.targetValues]
    _ = if i.val < s then a.order i + 1 else a.order i := by
      split
      · exact ordUnit_lemma718TypeITargetValues_prefix a s i (by assumption)
      · rw [lemma718TypeITargetValues_suffix a s i (by omega)]
        exact (a.toBONG.order_eq_ordUnit i).symm

/-- Type I always replaces at least one hyperbolic block and therefore has
strictly larger volume order. -/
theorem Lemma718TypeIRealization.volumeOrder_lt
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma718TypeIRealization a R s) :
    Lattice.volumeOrder q L < Lattice.volumeOrder q D.target := by
  apply volumeOrder_lt_of_order_le_of_exists_lt a D.bong
  · intro i
    rw [D.normalForm.targetOrder_eq a D.bong R s i]
    split <;> omega
  · refine ⟨0, ?_⟩
    rw [D.normalForm.targetOrder_eq a D.bong R s]
    simp only [Fin.val_zero]
    rw [if_pos (by exact D.normalForm.stopping.two_le.trans_lt' (by omega))]
    omega

/-- Pointwise order formula for a realized type-II replacement. -/
theorem Lemma718TypeIINormalForm.targetOrder_eq
    [DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (i : Fin (n + 3)) :
    b.order i = if 2 ≤ i.val ∧ i.val < s then
      a.order i + 1 else a.order i := by
  calc
    b.order i = ordUnit K (b.valueUnit i) :=
      b.toBONG.order_eq_ordUnit i
    _ = ordUnit K (lemma718TypeIITargetValues a s i) := by
      rw [D.targetValues]
    _ = if 2 ≤ i.val ∧ i.val < s then
        a.order i + 1 else a.order i := by
      split
      · exact ordUnit_lemma718TypeIITargetValues_changed
          a s i (by omega) (by omega)
      · by_cases hiTwo : i.val < 2
        · rw [lemma718TypeIITargetValues_initial a s i hiTwo]
          exact (a.toBONG.order_eq_ordUnit i).symm
        · rw [lemma718TypeIITargetValues_suffix a s i (by omega)]
          exact (a.toBONG.order_eq_ordUnit i).symm

/-- A nontrivial type-II replacement (`s > 2`) has strictly larger volume
order.  At `s = 2` Lemma 7.17 gives no hyperbolic plane to replace. -/
theorem Lemma718TypeIIRealization.volumeOrder_lt
    [DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma718TypeIIRealization a R s) (hs : 2 < s) :
    Lattice.volumeOrder q L < Lattice.volumeOrder q D.target := by
  apply volumeOrder_lt_of_order_le_of_exists_lt a D.bong
  · intro i
    rw [D.normalForm.targetOrder_eq a D.bong R s i]
    split <;> omega
  · let i : Fin (n + 3) := ⟨2, by
      have hRank := D.normalForm.stopping.le_rank
      omega⟩
    refine ⟨i, ?_⟩
    rw [D.normalForm.targetOrder_eq a D.bong R s i]
    rw [if_pos (by simp only [i, Fin.val_mk]; omega)]
    omega

/-- Pointwise order formula for a realized type-III replacement. -/
theorem Lemma718TypeIIINormalForm.targetOrder_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s)
    (i : Fin (n + 3)) :
    b.order i = if i.val < s ∧ Odd i.val then
      a.order i + 2 else a.order i := by
  calc
    b.order i = ordUnit K (b.valueUnit i) :=
      b.toBONG.order_eq_ordUnit i
    _ = ordUnit K (lemma718TypeIIITargetValues a s i) := by
      rw [D.targetValues]
    _ = if i.val < s ∧ Odd i.val then
        a.order i + 2 else a.order i := by
      split
      · exact ordUnit_lemma718TypeIIITargetValues_changed
          a s i ‹i.val < s ∧ Odd i.val›.1
            ‹i.val < s ∧ Odd i.val›.2
      · by_cases his : i.val < s
        · have hiEven : Even i.val := by
            rw [← Nat.not_odd_iff_even]
            intro hiOdd
            exact ‹¬(i.val < s ∧ Odd i.val)› ⟨his, hiOdd⟩
          rw [lemma718TypeIIITargetValues_even a s i hiEven]
          exact (a.toBONG.order_eq_ordUnit i).symm
        · rw [lemma718TypeIIITargetValues_suffix a s i (by omega)]
          exact (a.toBONG.order_eq_ordUnit i).symm

/-- Type III changes every low entry by `π²`; since `s ≥ 2`, at least the
second coefficient changes and the volume increase is strict. -/
theorem Lemma718TypeIIIRealization.volumeOrder_lt
    [DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma718TypeIIIRealization a R s) :
    Lattice.volumeOrder q L < Lattice.volumeOrder q D.target := by
  apply volumeOrder_lt_of_order_le_of_exists_lt a D.bong
  · intro i
    rw [D.normalForm.targetOrder_eq a D.bong R s i]
    split <;> omega
  · let i : Fin (n + 3) := ⟨1, by omega⟩
    refine ⟨i, ?_⟩
    rw [D.normalForm.targetOrder_eq a D.bong R s i]
    rw [if_pos]
    · omega
    · constructor
      · simp only [i]
        have hsTwo := D.normalForm.stopping.two_le
        omega
      · exact ⟨0, by simp only [i]; omega⟩

end BONG.GoodBONG

end Bong
