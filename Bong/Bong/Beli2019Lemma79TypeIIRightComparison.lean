/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIRight

/-!
# Beli (2019), Lemma 7.9(ii): the strict type-II case-7 subbranch

When the comparison order is strictly below the target order, Lemmas 6.6
and 7.2(ii) show that both mixed prefix products have odd valuation.  Their
capped quadratic defects therefore both vanish.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 2000000 in
-- The two prefix congruences use different normal forms from Lemma 7.2(ii).
/-- In the strict type-II case-7 subbranch, both mixed prefix defects are
zero. -/
theorem lemma79_typeII_right_comparisonPrefixes_eq_zero
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
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
    have hi := i.lt_large
    omega
  have hrightK : D.outer.transition.firstTwo - 1 ≤ k := by
    dsimp only [k]
    have hlong := D.long
    omega
  have hlastK : k ≤ D.outer.last := by
    dsimp only [k]
    have hi := hbeforeLast
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
  have hbCurrent : b.orderSequence.entryOrZero k = T + 1 := by
    rw [htargetBoundary, D.right_target]
  have hcCurrent : c.orderSequence.entryOrZero k ≤ T := by omega
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
  have hreferenceFirst : T ≤ c.orderSequence.entryOrZero 0 := by
    simpa only [T, hleftValue] using hfirstOrder
  have hcParityRaw :=
    c.prefixSum_modEq_mul_of_current_le_reference_le_first
      T k hk hreferenceFirst hcCurrent
  have hcParity : Int.ModEq 2 (c.orderSequence.prefixSum i.val)
      ((i.val : Int) * T) := by
    simpa only [k, Nat.sub_add_cancel i.pos] using hcParityRaw
  let P := a.beli2019Lemma72_ii b D hfirst
  have haParity := P.source_after i.val (by
    have hlong := D.long
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
      have hlong := D.long
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
      have hlong := D.long
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
the strict type-II case-7 subbranch. -/
theorem lemma79_typeII_right_comparisonPrefixes_eq_of_comparison_lt_target
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
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
  have hzero := lemma79_typeII_right_comparisonPrefixes_eq_zero
    a b c D hfirst hnorm i hright hbeforeLast hodd hcurrent
  exact hzero.1.trans hzero.2.symm

end BONG.GoodBONG

end Bong
