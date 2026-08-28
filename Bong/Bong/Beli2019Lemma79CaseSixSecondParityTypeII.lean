/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityJumpWitness

/-!
# Beli (2019), Lemma 7.9(ii), case 6: the type-II second parity branch

For even indices the odd third prefix itself supplies the jump witness.  For
odd indices Lemma 7.2(ii) makes the target prefix of length `i + 1` odd, and
the shifted comparison congruence transfers oddness to the third prefix of
length `i - 1`.  The common witness theorem then closes both branches.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Congruence modulo two transports oddness from the right side to the
left side. -/
theorem caseSix_odd_of_modEq_two_of_odd {x y : Int}
    (hmod : Int.ModEq 2 x y) (hy : Odd y) : Odd x := by
  rw [Int.modEq_iff_dvd] at hmod
  rcases hmod with ⟨z, hz⟩
  rcases hy with ⟨d, hd⟩
  exact ⟨d - z, by omega⟩

/-- Odd comparison-prefix order and opposite current orders identify the
target prefix of length `i + 1` with the third prefix of length `i - 1`
modulo two. -/
theorem caseSix_shiftedPrefix_modEq_of_comparison_odd_and_current_opposite
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1) + 1)) :
    Int.ModEq 2 (b.orderSequence.prefixSum (i.val + 1))
      (c.orderSequence.prefixSum (i.val - 1)) := by
  have hcomparisonOrder :
      ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val) =
        b.orderSequence.prefixSum i.val +
          c.orderSequence.prefixSum i.val := by
    rw [ordUnit_mul,
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        i.val i.lt_large.le,
      c.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        i.val i.lt_large.le]
  have hcPrefix : c.orderSequence.prefixSum i.val =
      c.orderSequence.prefixSum (i.val - 1) +
        c.orderSequence.entryOrZero (i.val - 1) := by
    simpa only [Nat.sub_add_cancel i.pos] using
      c.orderSequence.prefixSum_succ (i.val - 1)
  rw [hcomparisonOrder, hcPrefix] at hcomparison
  rcases hcomparison with ⟨z, hz⟩
  rw [Int.modEq_iff_dvd] at horders ⊢
  rcases horders with ⟨d, hd⟩
  rw [b.orderSequence.prefixSum_succ]
  refine ⟨c.orderSequence.prefixSum (i.val - 1) - z + d - 1, ?_⟩
  omega

/-- The profile current identity converts opposite current parity into the
congruence of the third current order with the type-II reference `T`. -/
theorem caseSix_thirdPrevious_modEq_typeII_reference
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1) + 1)) :
    Int.ModEq 2 (c.orderSequence.entryOrZero (i.val - 1))
      (b.orderSequence.entryOrZero D.outer.transition.lastZero) := by
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have hcurrentBoundary := D.outer.target_rightEven_eq_boundary
    i.val hright hthroughLast heven
  have hcurrent : b.orderSequence.entryOrZero i.val = T + 1 := by
    rw [hcurrentBoundary, D.right_target]
  have hone : Int.ModEq 2 (1 : Int) 1 := Int.ModEq.refl 1
  have hshifted := horders.sub hone
  simpa only [hcurrent, T, add_sub_cancel_right] using hshifted.symm

/-- The type-II reference `T` is no larger than the third first order. -/
theorem beli2019Lemma79_typeII_caseSix_reference_le_thirdFirst
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.orderSequence.entryOrZero D.outer.transition.lastZero ≤
      c.orderSequence.entryOrZero 0 := by
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstOrder : a.orderSequence.entryOrZero 0 + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    calc
      a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
      _ ≤ c.order 0 := hnormOrder
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hleftValue := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two D.outer.transition.lastZero le_rfl hleftEven
  omega

/-- At an odd type-II case-6 index, the target prefix of length `i + 1`
has odd order. -/
theorem beli2019Lemma79_typeII_caseSix_targetPrefix_succ_odd_of_index_odd
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hiOdd : Odd i.val) :
    Odd (b.orderSequence.prefixSum (i.val + 1)) := by
  let base := D.outer.transition.firstTwo - 1
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  let P := a.beli2019Lemma72_ii b D hfirst
  rcases hiOdd with ⟨d, hd⟩
  rcases heven with ⟨e, he⟩
  have hbaseOdd : Odd base := ⟨d - e, by
    simp only [base]
    omega⟩
  rcases hbaseOdd with ⟨f, hf⟩
  have hiSuccInt : ((i.val + 1 : Nat) : Int) =
      (d + 1 : Int) + (d + 1 : Int) := by
    exact_mod_cast (show i.val + 1 = (d + 1) + (d + 1) by omega)
  have hbaseInt' : (base : Int) = 2 * (f : Int) + 1 := by
    exact_mod_cast hf
  have hbaseInt : (base : Int) = (f : Int) + (f : Int) + 1 := by
    omega
  have hmod := P.target_after (i.val + 1) (by omega) (by omega)
  apply caseSix_odd_of_modEq_two_of_odd
    (by simpa only [T, base] using hmod)
  refine ⟨(d + 1 : Int) * (T + 1) + (f : Int), ?_⟩
  rw [hiSuccInt, hbaseInt]
  ring

/-- The even-index, opposite-current-parity subcase of type-II case 6. -/
theorem beli2019Lemma79_typeII_caseSix_secondParity_evenIndex
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hiEven : Even i.val)
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1) + 1)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have htarget :=
    beli2019Lemma79_typeII_caseSix_targetPrefix_even_of_index_even
      a b D hfirst i hright hthroughLast heven hiEven
  have hthirdPrefix :=
    caseSix_thirdPrefix_odd_of_comparison_odd_and_target_even
      b c i hcomparison htarget
  have hfirstLower :=
    beli2019Lemma79_typeII_caseSix_reference_le_thirdFirst
      a b c D hfirst hnorm
  have hfinalMod := caseSix_thirdPrevious_modEq_typeII_reference
    a b c D i hright hthroughLast heven horders
  have hfinalBound : i.val - 1 < n + 2 :=
    (Nat.sub_le i.val 1).trans_lt i.lt_large
  have hlengthFinal : i.val - 1 ≤ i.val - 1 := le_rfl
  rcases c.exists_odd_entryPair_above_reference_of_even_prefix_odd
      i.val (i.val - 1) T i.pos i.lt_large.le hiEven hthirdPrefix
      hfinalBound hlengthFinal (by simpa only [T] using hfirstLower)
      (by simpa only [T] using hfinalMod) with
    ⟨k, hkFinal, hkOdd, hkAbove⟩
  have hiLarge := i.lt_large
  have hkBound : k < n + 1 := by omega
  let j : Fin (n + 1) := ⟨k, hkBound⟩
  have hsumOdd : Odd (c.order j.castSucc + c.order j.succ) := by
    rw [← c.orderSequence_entryOrZero_eq_order j.castSucc,
      ← c.orderSequence_entryOrZero_eq_order j.succ]
    simpa only [j, Fin.val_castSucc, Fin.val_succ] using hkOdd
  have hreference : T < c.order j.castSucc := by
    rw [← c.orderSequence_entryOrZero_eq_order j.castSucc]
    simpa only [j, Fin.val_castSucc] using hkAbove
  have hjlt : j.val + 1 < i.val := by
    change k + 1 < i.val
    have hiPos := i.pos
    omega
  exact beli2019Lemma79_typeII_caseSix_secondParity_of_oddPairAboveReference
    a b c D i hright hthroughLast heven j hjlt hsumOdd hreference

/-- The odd-index, opposite-current-parity subcase of type-II case 6. -/
theorem beli2019Lemma79_typeII_caseSix_secondParity_oddIndex
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hiOdd : Odd i.val)
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1) + 1)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have htargetOdd :=
    beli2019Lemma79_typeII_caseSix_targetPrefix_succ_odd_of_index_odd
      a b D hfirst i hright hthroughLast heven hiOdd
  have hshifted :=
    caseSix_shiftedPrefix_modEq_of_comparison_odd_and_current_opposite
      b c i hcomparison horders
  have hthirdPrefix : Odd
      (c.orderSequence.prefixSum (i.val - 1)) :=
    caseSix_odd_of_modEq_two_of_odd hshifted.symm htargetOdd
  rcases hiOdd with ⟨d, hd⟩
  have hlengthEven : Even (i.val - 1) := ⟨d, by omega⟩
  have hlengthPos : 0 < i.val - 1 := by
    have hlong := D.long
    omega
  have hfirstLower :=
    beli2019Lemma79_typeII_caseSix_reference_le_thirdFirst
      a b c D hfirst hnorm
  have hfinalMod := caseSix_thirdPrevious_modEq_typeII_reference
    a b c D i hright hthroughLast heven horders
  have hlengthBound : i.val - 1 ≤ n + 2 :=
    (Nat.sub_le i.val 1).trans i.lt_large.le
  have hfinalBound : i.val - 1 < n + 2 :=
    (Nat.sub_le i.val 1).trans_lt i.lt_large
  have hlengthFinal : i.val - 1 - 1 ≤ i.val - 1 := Nat.sub_le _ _
  rcases c.exists_odd_entryPair_above_reference_of_even_prefix_odd
      (i.val - 1) (i.val - 1) T hlengthPos hlengthBound hlengthEven
      hthirdPrefix hfinalBound hlengthFinal
      (by simpa only [T] using hfirstLower)
      (by simpa only [T] using hfinalMod) with
    ⟨k, hkFinal, hkOdd, hkAbove⟩
  have hiLarge := i.lt_large
  have hkBound : k < n + 1 := by omega
  let j : Fin (n + 1) := ⟨k, hkBound⟩
  have hsumOdd : Odd (c.order j.castSucc + c.order j.succ) := by
    rw [← c.orderSequence_entryOrZero_eq_order j.castSucc,
      ← c.orderSequence_entryOrZero_eq_order j.succ]
    simpa only [j, Fin.val_castSucc, Fin.val_succ] using hkOdd
  have hreference : T < c.order j.castSucc := by
    rw [← c.orderSequence_entryOrZero_eq_order j.castSucc]
    simpa only [j, Fin.val_castSucc] using hkAbove
  have hjlt : j.val + 1 < i.val := by
    change k + 1 < i.val
    have hiPos := i.pos
    omega
  exact beli2019Lemma79_typeII_caseSix_secondParity_of_oddPairAboveReference
    a b c D i hright hthroughLast heven j hjlt hsumOdd hreference

/-- The complete opposite-current-parity part of the type-II second parity
branch. -/
theorem beli2019Lemma79_typeII_caseSix_secondParity_oppositeCurrentParity
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1) + 1)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · exact beli2019Lemma79_typeII_caseSix_secondParity_evenIndex
      a b c D hfirst hnorm i hright hthroughLast heven hiEven
        hcomparison horders
  · exact beli2019Lemma79_typeII_caseSix_secondParity_oddIndex
      a b c D hfirst hnorm i hright hthroughLast heven hiOdd
        hcomparison horders

end BONG.GoodBONG

end Bong
