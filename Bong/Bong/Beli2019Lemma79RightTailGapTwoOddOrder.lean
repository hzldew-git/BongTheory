/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoEvenComplete
import Bong.Bong.Beli2019Lemma79RightTailGapOneComparison

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the odd comparison order

At an odd current index, the target prefix through `i - 1` has the
initial gap-two congruence.  The intervening target orders contribute an
even number of terms of one parity, so the comparison-prefix congruence
puts its last order strictly above the norm floor by Lemma 6.6(i).  This
formalizes lines 5948--5952 of the v2 paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- At an odd coordinate in the type-I gap-two tail, the last order of
the comparison prefix is at least the target order at the gap boundary.
In the paper this is `T_i >= T + 1 = S_u`. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_odd_comparisonOrder_ge_boundary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 <= i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.profile.last hlast) (caseEightLastAlphaIndex i))
    (hiOdd : Odd i.val)
    (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val)) :
    b.order (Fin.mk D.profile.last hlast).castSucc <=
      c.order (evenTargetPreviousIndex i) := by
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_initialData
    a b D hfirst hgapTwo with ⟨I⟩
  let first : Fin (n + 1) := Fin.mk D.profile.last hlast
  let reference : Int := a.orderSequence.entryOrZero D.anchor + 1
  have hfirstLast : first <= caseEightLastAlphaIndex i := by
    change D.profile.last <= i.val - 1
    omega
  have htargetBoundary : b.order first.castSucc = reference + 1 := by
    rw [<- b.orderSequence_entryOrZero_eq_order first.castSucc]
    change b.orderSequence.entryOrZero D.profile.last =
      (a.orderSequence.entryOrZero D.anchor + 1) + 1
    calc
      b.orderSequence.entryOrZero D.profile.last =
          a.orderSequence.entryOrZero D.anchor + 2 := I.target_last
      _ = (a.orderSequence.entryOrZero D.anchor + 1) + 1 := by omega
  have htailEntry (k : Nat) (hkStart : first.val + 1 <= k)
      (hkEnd : k < i.val) :
      Int.ModEq 2 (b.orderSequence.entryOrZero k)
        (b.order first.succ) := by
    have hkBound : k < n + 2 := hkEnd.trans i.lt_large
    let j : Fin (n + 1) := ⟨k - 1, by omega⟩
    have hjFirst : first <= j := by
      change first.val <= k - 1
      omega
    have hjLast : j <= caseEightLastAlphaIndex i := by
      change k - 1 <= i.val - 1
      omega
    have hjMod := H.order_modEq j hjFirst hjLast
    have hsucc : j.succ = (Fin.mk k hkBound : Fin (n + 2)) := by
      apply Fin.ext
      simp only [j, Fin.val_succ]
      omega
    rw [b.orderSequence_entryOrZero_eq_order (Fin.mk k hkBound)]
    simpa only [hsucc] using hjMod
  have htargetRaw := b.orderSequence.prefixSum_modEq_add_mul_of_tail
    ((((first.val + 1 : Nat) : Int) * reference) + 1)
      (b.order first.succ) hafter I.target_prefix_last htailEntry
  have hdeltaEven : Even (i.val - (first.val + 1)) := by
    rcases I.last_even with ⟨d, hd⟩
    rcases hiOdd with ⟨r, hr⟩
    refine ⟨r - d, ?_⟩
    simp only [first]
    omega
  have hdeltaEvenInt : Even
      (((i.val - (first.val + 1) : Nat) : Int)) := by
    rcases hdeltaEven with ⟨d, hd⟩
    refine ⟨(d : Int), ?_⟩
    exact_mod_cast hd
  have hdeltaZero : Int.ModEq 2
      (((i.val - (first.val + 1) : Nat) : Int)) 0 := by
    apply int_modEq_two_of_even_sub
    simpa only [sub_zero] using hdeltaEvenInt
  have hindex : Int.ModEq 2 ((first.val + 1 : Nat) : Int)
      (i.val : Int) := by
    have hadd := (Int.ModEq.rfl : Int.ModEq 2
      ((first.val + 1 : Nat) : Int) ((first.val + 1 : Nat) : Int)).add
        hdeltaZero
    have hfirstAfter : first.val + 1 <= i.val := by
      simpa only [first] using hafter
    have hsplit : first.val + 1 + (i.val - (first.val + 1)) = i.val := by
      omega
    have hcastSplit :
        ((first.val + 1 : Nat) : Int) +
            ((i.val - (first.val + 1) : Nat) : Int) = (i.val : Int) := by
      exact_mod_cast hsplit
    simpa only [hcastSplit, add_zero] using hadd.symm
  have hbase : Int.ModEq 2
      ((((first.val + 1 : Nat) : Int) * reference) + 1)
      ((i.val : Int) * reference + 1) := by
    exact (hindex.mul_right reference).add
      (Int.ModEq.rfl : Int.ModEq 2 (1 : Int) 1)
  have htailZero : Int.ModEq 2
      (((i.val - (first.val + 1) : Nat) : Int) * b.order first.succ) 0 := by
    simpa only [zero_mul] using hdeltaZero.mul_right (b.order first.succ)
  have htargetFormula : Int.ModEq 2
      (((((first.val + 1 : Nat) : Int) * reference) + 1) +
        (((i.val - (first.val + 1) : Nat) : Int) * b.order first.succ))
      ((i.val : Int) * reference + 1) := by
    simpa only [add_zero] using hbase.add htailZero
  have htarget : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      ((i.val : Int) * reference + 1) :=
    htargetRaw.trans htargetFormula
  have hcomparison : Int.ModEq 2 (c.orderSequence.prefixSum i.val)
      ((i.val : Int) * reference + 1) := hprefix.symm.trans htarget
  have hsourceZeroEntry : a.orderSequence.entryOrZero 0 =
      a.orderSequence.entryOrZero D.anchor := by
    exact I.canonical.source_to_anchor 0 (Nat.zero_le _) ⟨0, by omega⟩
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstLower : reference <= c.orderSequence.entryOrZero 0 := by
    have haZero : a.order (0 : Fin (n + 2)) =
        a.orderSequence.entryOrZero D.anchor := by
      rw [<- a.orderSequence_entryOrZero_eq_order (0 : Fin (n + 2))]
      simpa using hsourceZeroEntry
    have hcZero : c.orderSequence.entryOrZero 0 =
        c.order (0 : Fin (n + 2)) := by
      simpa using c.orderSequence_entryOrZero_eq_order
        (0 : Fin (n + 2))
    change a.order (0 : Fin (n + 2)) + 1 <=
      c.order (0 : Fin (n + 2)) at hnormOrder
    rw [haZero, <- hcZero] at hnormOrder
    simpa only [reference] using hnormOrder
  have hlastAbove := c.last_entry_ge_reference_add_one_of_odd_prefix_modEq
    i.val reference i.pos i.lt_large.le hiOdd hcomparison hfirstLower
  have hlastOrder : c.orderSequence.entryOrZero (i.val - 1) =
      c.order (evenTargetPreviousIndex i) := by
    simpa only [evenTargetPreviousIndex] using
      c.orderSequence_entryOrZero_eq_order (evenTargetPreviousIndex i)
  rw [hlastOrder] at hlastAbove
  simpa only [first, htargetBoundary] using hlastAbove

/-- At an odd coordinate in the type-I gap-two tail, the target prefix
through `i - 1` lies in the paper's congruence class `T + 1`. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_odd_targetPrefix_modEq
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 <= i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.profile.last hlast) (caseEightLastAlphaIndex i))
    (hiOdd : Odd i.val) :
    Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (a.orderSequence.entryOrZero D.anchor + 2) := by
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_initialData
    a b D hfirst hgapTwo with ⟨I⟩
  let first : Fin (n + 1) := Fin.mk D.profile.last hlast
  let reference : Int := a.orderSequence.entryOrZero D.anchor + 1
  have htailEntry (k : Nat) (hkStart : first.val + 1 <= k)
      (hkEnd : k < i.val) :
      Int.ModEq 2 (b.orderSequence.entryOrZero k)
        (b.order first.succ) := by
    have hkBound : k < n + 2 := hkEnd.trans i.lt_large
    let j : Fin (n + 1) := ⟨k - 1, by omega⟩
    have hjFirst : first <= j := by
      change first.val <= k - 1
      omega
    have hjLast : j <= caseEightLastAlphaIndex i := by
      change k - 1 <= i.val - 1
      omega
    have hjMod := H.order_modEq j hjFirst hjLast
    have hsucc : j.succ = (Fin.mk k hkBound : Fin (n + 2)) := by
      apply Fin.ext
      simp only [j, Fin.val_succ]
      omega
    rw [b.orderSequence_entryOrZero_eq_order (Fin.mk k hkBound)]
    simpa only [hsucc] using hjMod
  have htargetRaw := b.orderSequence.prefixSum_modEq_add_mul_of_tail
    ((((first.val + 1 : Nat) : Int) * reference) + 1)
      (b.order first.succ) hafter I.target_prefix_last htailEntry
  have hdeltaEven : Even (i.val - (first.val + 1)) := by
    rcases I.last_even with ⟨d, hd⟩
    rcases hiOdd with ⟨r, hr⟩
    refine ⟨r - d, ?_⟩
    simp only [first]
    omega
  have hdeltaEvenInt : Even
      (((i.val - (first.val + 1) : Nat) : Int)) := by
    rcases hdeltaEven with ⟨d, hd⟩
    refine ⟨(d : Int), ?_⟩
    exact_mod_cast hd
  have hdeltaZero : Int.ModEq 2
      (((i.val - (first.val + 1) : Nat) : Int)) 0 := by
    apply int_modEq_two_of_even_sub
    simpa only [sub_zero] using hdeltaEvenInt
  have hindex : Int.ModEq 2 ((first.val + 1 : Nat) : Int)
      (i.val : Int) := by
    have hadd := (Int.ModEq.rfl : Int.ModEq 2
      ((first.val + 1 : Nat) : Int) ((first.val + 1 : Nat) : Int)).add
        hdeltaZero
    have hfirstAfter : first.val + 1 <= i.val := by
      simpa only [first] using hafter
    have hsplit : first.val + 1 + (i.val - (first.val + 1)) = i.val := by
      omega
    have hcastSplit :
        ((first.val + 1 : Nat) : Int) +
            ((i.val - (first.val + 1) : Nat) : Int) = (i.val : Int) := by
      exact_mod_cast hsplit
    simpa only [hcastSplit, add_zero] using hadd.symm
  have hbase : Int.ModEq 2
      ((((first.val + 1 : Nat) : Int) * reference) + 1)
      ((i.val : Int) * reference + 1) := by
    exact (hindex.mul_right reference).add
      (Int.ModEq.rfl : Int.ModEq 2 (1 : Int) 1)
  have htailZero : Int.ModEq 2
      (((i.val - (first.val + 1) : Nat) : Int) * b.order first.succ) 0 := by
    simpa only [zero_mul] using hdeltaZero.mul_right (b.order first.succ)
  have htarget : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      ((i.val : Int) * reference + 1) :=
    htargetRaw.trans (by
      simpa only [add_zero] using hbase.add htailZero)
  have hiOne : Int.ModEq 2 (i.val : Int) 1 := by
    rcases hiOdd with ⟨d, hd⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨-(d : Int), ?_⟩
    have hdInt : (i.val : Int) = 2 * (d : Int) + 1 := by
      exact_mod_cast hd
    omega
  have hreference : Int.ModEq 2 ((i.val : Int) * reference + 1)
      (reference + 1) := by
    simpa only [one_mul] using (hiOne.mul_right reference).add
      (Int.ModEq.rfl : Int.ModEq 2 (1 : Int) 1)
  have hfinal := htarget.trans hreference
  have href : reference + 1 =
      a.orderSequence.entryOrZero D.anchor + 2 := by
    simp only [reference]
    omega
  rw [href] at hfinal
  exact hfinal

end BONG.GoodBONG

end Bong
