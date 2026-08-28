/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTypeIIRight

/-!
# Beli (2019), Lemma 7.9(iii), case 9: overlapping type III

For a central-gap-one type-III profile, Lemma 7.2 has the same target-prefix
congruence as type II.  At the final difference coordinate it is opposite to
the comparison-prefix congruence, so the mixed defect vanishes.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- At the final difference coordinate of an overlapping type-III profile,
the shifted target/comparison product has odd order. -/
theorem lemma79Central_typeIIIOverlapRight_terminal_currentProduct_odd
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hoverlap : a.orderGap ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hiLast : i.val = D.outer.last)
    (htrigger : b.centralAlphaTrigger c i) :
    Odd (ordUnit K ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
      c.prefixProduct (i.val - 1))) := by
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have hbaseLast := D.outer.right_le_last
  have hbaseI : D.outer.transition.firstTwo - 1 ≤ i.val := by omega
  have hiEven : Even
      (i.val - (D.outer.transition.firstTwo - 1)) := by
    simpa only [hiLast] using D.outer.right_even_distance
  let currentIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val, by have := i.one_lt; omega, i.lt_large, i.lt_large.le⟩
  have htargetCurrent :=
    beli2019Lemma79_typeIII_overlap_caseSix_targetCurrent_eq_reference_add_one
      a b D hoverlap currentIdx (by simpa only [currentIdx] using hbaseI)
        (by simp only [currentIdx]; omega) (by
          simpa only [currentIdx] using hiEven)
  have htargetCurrentOrder : b.order ⟨i.val, i.lt_large⟩ = T + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order]
    simpa only [currentIdx, T] using htargetCurrent
  have hcCurrent : c.orderSequence.entryOrZero (i.val - 2) ≤ T := by
    have hcross := htrigger.1
    rw [htargetCurrentOrder] at hcross
    rw [c.orderSequence_entryOrZero_eq_order ⟨i.val - 2, by
      have := i.lt_large
      omega⟩]
    omega
  have hfirstLower :=
    beli2019Lemma79_typeIII_overlap_reference_le_thirdFirst
      a b c D hfirst hnorm
  have hcRaw := c.prefixSum_modEq_mul_of_current_le_reference_le_first
    T (i.val - 2) (by
      have := i.lt_large
      omega) (by simpa only [T] using hfirstLower) hcCurrent
  have hc : Int.ModEq 2
      (c.orderSequence.prefixSum (i.val - 1))
      (((i.val - 1 : Nat) : Int) * T) := by
    simpa only [show i.val - 2 + 1 = i.val - 1 by
      have := i.one_lt
      omega] using hcRaw
  let P := a.beli2019Lemma72_ii_typeIII_overlap b D hfirst hoverlap
  have hbRaw := P.target_after (i.val + 1) (by omega) (by omega)
  have hb : Int.ModEq 2
      (b.orderSequence.prefixSum (i.val + 1))
      (((i.val + 1 : Nat) : Int) * (T + 1) +
        ((D.outer.transition.firstTwo - 1 : Nat) : Int)) := by
    simpa only [P, T] using hbRaw
  have hsumMod := hb.add hc
  have hformulaOdd : Odd
      (((i.val + 1 : Nat) : Int) * (T + 1) +
        ((D.outer.transition.firstTwo - 1 : Nat) : Int) +
        ((i.val - 1 : Nat) : Int) * T) := by
    have hrecover := Nat.sub_add_cancel hbaseI
    rcases hiEven with ⟨d, hd⟩
    have hiCast : (i.val : Int) =
        ((D.outer.transition.firstTwo - 1 : Nat) : Int) +
          (d : Int) + (d : Int) := by
      exact_mod_cast (show i.val =
        (D.outer.transition.firstTwo - 1) + d + d by omega)
    rw [Nat.cast_sub i.one_lt.le]
    push_cast
    refine ⟨(i.val : Int) * T +
      ((D.outer.transition.firstTwo - 1 : Nat) : Int) + (d : Int), ?_⟩
    rw [hiCast]
    ring
  have hsumOdd : Odd
      (b.orderSequence.prefixSum (i.val + 1) +
        c.orderSequence.prefixSum (i.val - 1)) :=
    caseSix_odd_of_modEq_two_of_odd hsumMod hformulaOdd
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val, by have := i.one_lt; omega, i.lt_large, i.lt_large.le⟩
  have hproduct := signed_shifted_prefixProduct_order_odd_of_sum_odd
    b c idx (by simpa only [idx] using hsumOdd)
  change Odd (ordUnit K ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
    c.prefixProduct (i.val - 1))) at hproduct
  exact hproduct

/-- The terminal mixed defect is zero in the overlapping type-III branch. -/
theorem lemma79Central_typeIIIOverlapRight_terminal_currentDefect_eq_zero
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hoverlap : a.orderGap ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hiLast : i.val = D.outer.last)
    (htrigger : b.centralAlphaTrigger c i) :
    b.centralCurrentDefect c i = 0 := by
  unfold centralCurrentDefect
  apply truncatedPrefixDefect_eq_zero_of_odd_order_general
  exact lemma79Central_typeIIIOverlapRight_terminal_currentProduct_odd
    a b c D hfirst hoverlap hnorm i hright hiLast htrigger

end BONG.GoodBONG

end Bong
