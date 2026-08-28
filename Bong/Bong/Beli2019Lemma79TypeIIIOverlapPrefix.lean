/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma72TypeIIIOverlap
import Bong.Bong.Beli2019Lemma79CaseSixProfile
import Bong.Bong.Beli2019Lemma79TypeIIRightComparison
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIIOverlap

/-!
# Beli (2019), Lemma 7.9(ii): overlap prefix parity

The type-II prefix congruences of an overlapping type-III profile give the
opposite-parity input for case 6 and the two odd mixed-prefix products in the
strict subbranch of case 7.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- In the overlapping type-II/III branch, case-6 source and target prefixes
have opposite order parity. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_prefix_opposite
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    Int.ModEq 2 (a.orderSequence.prefixSum i.val + 1)
      (b.orderSequence.prefixSum i.val) := by
  let base := D.outer.transition.firstTwo - 1
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  let P := a.beli2019Lemma72_ii_typeIII_overlap b D hfirst hoverlap
  have hleftSource : D.outer.transition.lastZero + 1 ≤ i.val := by
    rw [D.adjacent] at hright
    omega
  have hsource := P.source_after i.val hleftSource (by omega)
  have hone : Int.ModEq 2 (1 : Int) 1 := Int.ModEq.refl 1
  have hsourceOne : Int.ModEq 2
      (a.orderSequence.prefixSum i.val + 1) ((i.val : Int) * T) := by
    have hadd := hsource.add hone
    simpa only [T, add_assoc, sub_add_cancel] using hadd
  by_cases hbeforeTransition : i.val < D.outer.transition.firstTwo
  · have htarget := P.target_before i.val hbeforeTransition
    exact hsourceOne.trans (by simpa only [T] using htarget.symm)
  · have hiBase : Int.ModEq 2 (i.val : Int) (base : Int) :=
      modEq_two_of_even_nat_sub base i.val (by simpa only [base] using hright)
        (by simpa only [base] using heven)
    have hbaseSelf : Int.ModEq 2 (base : Int) (base : Int) :=
      Int.ModEq.refl _
    have hsumRaw := hiBase.add hbaseSelf
    have hbaseDouble : Int.ModEq 2
        ((base : Int) + (base : Int)) 0 := by
      rw [Int.modEq_iff_dvd]
      exact ⟨-(base : Int), by ring⟩
    have hsum : Int.ModEq 2
        ((i.val : Int) + (base : Int)) 0 :=
      hsumRaw.trans hbaseDouble
    have hproductSelf : Int.ModEq 2
        ((i.val : Int) * T) ((i.val : Int) * T) := Int.ModEq.refl _
    have hbridgeRaw := hproductSelf.add hsum
    have hbridge : Int.ModEq 2 ((i.val : Int) * T)
        ((i.val : Int) * (T + 1) + (base : Int)) := by
      symm
      convert hbridgeRaw using 1 <;> ring
    have htarget := P.target_after i.val (by omega) (by omega)
    exact hsourceOne.trans (hbridge.trans (by
      simpa only [T, base] using htarget.symm))

set_option maxHeartbeats 2000000 in
-- The proof expands both type-II-style prefix normal forms simultaneously.
/-- In the strict overlap case-7 subbranch, both mixed prefix defects vanish. -/
theorem lemma79_typeIII_overlap_right_comparisonPrefixes_eq_zero
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1)))
    (hcurrent : c.order ⟨i.val - 1, by
      have hi := i.lt_large
      omega⟩ < b.order ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩) :
    b.truncatedPrefixDefect c 1 i.val i.val = 0 ∧
      a.truncatedPrefixDefect c 1 i.val i.val = 0 := by
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  let k := i.val - 1
  have hk : k < n + 2 := by
    dsimp only [k]
    have hiBound := i.lt_large
    omega
  have hrightK : D.outer.transition.firstTwo - 1 ≤ k := by
    dsimp only [k]
    omega
  have hlastK : k ≤ D.outer.last := by
    dsimp only [k]
    omega
  have hevenK : Even (k - (D.outer.transition.firstTwo - 1)) := by
    rcases hodd with ⟨d, hd⟩
    exact ⟨d, by
      dsimp only [k]
      omega⟩
  have hcurrentEntries : c.orderSequence.entryOrZero k <
      b.orderSequence.entryOrZero k := by
    dsimp only [k]
    rw [c.orderSequence.entryOrZero_of_lt (by omega),
      b.orderSequence.entryOrZero_of_lt (by omega)]
    exact hcurrent
  have htargetBoundary := D.outer.target_rightEven_eq_boundary
    k hrightK hlastK hevenK
  have htargetLast := D.outer.target_rightEven_eq_boundary
    D.outer.last D.outer.right_le_last le_rfl D.outer.right_even_distance
  have hlastValue :=
    a.beli2019Lemma79_typeIII_overlap_lastTarget_eq_left_add_one
      b D hoverlap
  have hbCurrent : b.orderSequence.entryOrZero k = T + 1 := by
    calc
      b.orderSequence.entryOrZero k =
          b.orderSequence.entryOrZero (D.outer.transition.firstTwo - 1) :=
        htargetBoundary
      _ = b.orderSequence.entryOrZero D.outer.last := htargetLast.symm
      _ = T + 1 := by simpa only [T] using hlastValue
  have hcCurrent : c.orderSequence.entryOrZero k ≤ T := by omega
  have hreferenceFirst :=
    a.beli2019Lemma79_typeIII_overlap_reference_le_thirdFirst
      b c D hfirst hnorm
  have hcParityRaw :=
    c.prefixSum_modEq_mul_of_current_le_reference_le_first
      T k hk (by simpa only [T] using hreferenceFirst) hcCurrent
  have hcParity : Int.ModEq 2 (c.orderSequence.prefixSum i.val)
      ((i.val : Int) * T) := by
    simpa only [k, Nat.sub_add_cancel i.pos] using hcParityRaw
  let P := a.beli2019Lemma72_ii_typeIII_overlap b D hfirst hoverlap
  have haParity := P.source_after i.val (by
    rw [D.adjacent] at hright
    omega) (by omega)
  have hbParity := P.target_after i.val hright (by omega)
  let X : Int := (i.val : Int) * T
  have hshift : Int.ModEq 2 (X - 1) (X + 1) := by
    rw [Int.modEq_iff_dvd]
    exact ⟨1, by ring⟩
  have hcPlus := hcParity.add
    (Int.ModEq.rfl : Int.ModEq 2 (1 : Int) 1)
  have hacParity : Int.ModEq 2
      (a.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val + 1) := by
    have haBase : Int.ModEq 2
        (a.orderSequence.prefixSum i.val) (X - 1) := by
      simpa only [P, T, X] using haParity
    exact (haBase.trans hshift).trans (by
      simpa only [X] using hcPlus.symm)
  have hgapEven : Even (i.val - D.outer.transition.firstTwo) := by
    rcases hodd with ⟨d, hd⟩
    exact ⟨d, by
      have hseparated := D.outer.transition.separated
      omega⟩
  let Y : Int :=
    (i.val : Int) * (T + 1) +
      ((D.outer.transition.firstTwo - 1 : Nat) : Int)
  have hyx : Int.ModEq 2 Y (X - 1) := by
    rw [Int.modEq_iff_dvd]
    rcases hgapEven with ⟨d, hd⟩
    refine ⟨-(((d + D.outer.transition.firstTwo : Nat) : Int)), ?_⟩
    dsimp only [Y, X]
    rw [Nat.cast_sub (by
      have hseparated := D.outer.transition.separated
      omega : 1 ≤ D.outer.transition.firstTwo)]
    push_cast
    ring_nf
    omega
  have hbcParity : Int.ModEq 2
      (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val + 1) := by
    have hbBase : Int.ModEq 2
        (b.orderSequence.prefixSum i.val) Y := by
      simpa only [P, T, Y] using hbParity
    exact ((hbBase.trans hyx).trans hshift).trans (by
      simpa only [X] using hcPlus.symm)
  have hacOdd :=
    a.comparisonPrefixProduct_order_odd_of_modEq_add_one c i hacParity
  have hbcOdd :=
    b.comparisonPrefixProduct_order_odd_of_modEq_add_one c i hbcParity
  exact ⟨
    b.truncatedPrefixDefect_eq_zero_of_odd_order c i.val hbcOdd,
    a.truncatedPrefixDefect_eq_zero_of_odd_order c i.val hacOdd⟩

/-- Replacing the source by the target preserves the mixed prefix defect in
the strict overlap case-7 subbranch. -/
theorem lemma79_typeIII_overlap_right_comparisonPrefixes_eq_of_comparison_lt_target
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1)))
    (hcurrent : c.order ⟨i.val - 1, by
      have hi := i.lt_large
      omega⟩ < b.order ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩) :
    b.truncatedPrefixDefect c 1 i.val i.val =
      a.truncatedPrefixDefect c 1 i.val i.val := by
  have hzero := lemma79_typeIII_overlap_right_comparisonPrefixes_eq_zero
    a b c D hfirst hoverlap hnorm i hright hbeforeLast hodd hcurrent
  exact hzero.1.trans hzero.2.symm

end BONG.GoodBONG

end Bong
