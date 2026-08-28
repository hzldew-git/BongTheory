/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemmas48To410
import Bong.Bong.BinaryDefectAdaptedValues

/-!
# Beli (2003), Definition 10, Lemma 4.11, and Remark 4.12

Definition 10 is restated using the intrinsic property-B predicate.  The deep
spinor-norm conclusion of Lemma 4.11 is isolated as a non-default local law.
Remark 4.12 is proved from the binary lower bound and the neighboring-gap
condition in property B.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- Beli (2003), Definition 10, with the endpoint convention made explicit. -/
theorem beliDefinition10 (b : BONG V q L (n + 1)) :
    b.HasPropertyB ↔
      b.HasPropertyA ∧
        ∀ i : Fin n, b.propertyBTrigger i →
          (∀ j : Fin (n + 1), j.1 + 1 = i.1 →
            2 * (ramificationIndex K : Int) + 1 ≤
              b.order i.castSucc - b.order j) ∧
          (∀ k : Fin (n + 1), i.1 + 2 = k.1 →
            2 * (ramificationIndex K : Int) + 1 ≤
              b.order k - b.order i.succ) :=
  Iff.rfl

/-- Every adjacent BONG order gap is at least `-2e`. -/
theorem adjacentOrderGap_ge_neg_two_mul_e (b : BONG V q L n)
    (i : Fin n) (hi : i.1 + 1 < n) :
    -(2 * (ramificationIndex K : Int)) ≤
      b.order ⟨i.1 + 1, hi⟩ - b.order i := by
  have hbound : i.1 + 2 ≤ n := by omega
  rcases b.exists_segmentWitness i.1 2 hbound with ⟨w⟩
  have h := w.bong.binaryOrderGap_ge_neg_two_mul_e
  change -(2 * (ramificationIndex K : Int)) ≤
    w.bong.order 1 - w.bong.order 0 at h
  rw [w.order_eq, w.order_eq] at h
  simpa [SegmentWitness.sourceIndex] using h

/-- An adjacent BONG gap of odd parity is at least one. -/
theorem adjacentOrderGap_pos_of_odd (b : BONG V q L n)
    (i : Fin n) (hi : i.1 + 1 < n)
    (hodd : Odd (b.order ⟨i.1 + 1, hi⟩ - b.order i)) :
    0 < b.order ⟨i.1 + 1, hi⟩ - b.order i := by
  have hbound : i.1 + 2 ≤ n := by omega
  rcases b.exists_segmentWitness i.1 2 hbound with ⟨w⟩
  have hoddParameter : Odd (ordUnit K w.bong.binaryParameter) := by
    change Odd w.bong.binaryParameterOrder
    rw [w.bong.binaryParameterOrder_eq_orderGap]
    change Odd (w.bong.order 1 - w.bong.order 0)
    rw [w.order_eq, w.order_eq]
    simpa [SegmentWitness.sourceIndex] using hodd
  have hnonneg :=
    w.bong.binaryParameter_isBinaryParameterAdmissible.ordUnit_nonneg_of_odd
      hoddParameter
  have hpositive : 0 < ordUnit K w.bong.binaryParameter := by
    rcases hoddParameter with ⟨z, hz⟩
    omega
  change 0 < w.bong.binaryParameterOrder at hpositive
  rw [w.bong.binaryParameterOrder_eq_orderGap] at hpositive
  change 0 < w.bong.order 1 - w.bong.order 0 at hpositive
  rw [w.order_eq, w.order_eq] at hpositive
  simpa [SegmentWitness.sourceIndex] using hpositive

namespace SegmentWitness

/-- Definition 10: consecutive segments preserve property B. -/
theorem hasPropertyB {b : BONG V q L (n + 1)} {start m : Nat}
    {bound : start + (m + 1) ≤ n + 1}
    (w : SegmentWitness b start (m + 1) bound)
    (hb : b.HasPropertyB) :
    w.bong.HasPropertyB := by
  refine ⟨w.hasPropertyA hb.hasPropertyA, ?_⟩
  intro i hiTrigger
  let p : Fin n := ⟨start + i.1, by omega⟩
  have hcast : w.sourceIndex i.castSucc = p.castSucc := by
    apply Fin.ext
    simp [sourceIndex, p]
  have hsucc : w.sourceIndex i.succ = p.succ := by
    apply Fin.ext
    simp only [sourceIndex_val, Fin.val_succ]
    simp only [p]
    omega
  have hnormalized : w.bong.normalizedAdjacentDefectOrder i =
      b.normalizedAdjacentDefectOrder p := by
    unfold normalizedAdjacentDefectOrder normalizedAdjacentProduct
    rw [w.normalizedValue_eq, w.normalizedValue_eq, hcast, hsucc]
  have hpTrigger : b.propertyBTrigger p := by
    unfold propertyBTrigger at hiTrigger ⊢
    rw [w.order_eq, w.order_eq, hcast, hsucc, hnormalized] at hiTrigger
    exact hiTrigger
  refine ⟨?_, ?_⟩
  · intro j hj
    have hjGlobal := (hb.2 p hpTrigger).1 (w.sourceIndex j) (by
      simp only [sourceIndex_val]
      simp only [p]
      omega)
    rw [w.order_eq, w.order_eq, hcast]
    exact hjGlobal
  · intro k hk
    have hkGlobal := (hb.2 p hpTrigger).2 (w.sourceIndex k) (by
      simp only [sourceIndex_val]
      simp only [p]
      omega)
    rw [w.order_eq, w.order_eq, hsucc]
    exact hkGlobal

end SegmentWitness

/--
Beli (2003), Remark 4.12: property B forces every two-step order increase to
be at least two.
-/
theorem HasPropertyB.twoStep_add_two_le
    {b : BONG V q L (n + 1)} (hb : b.HasPropertyB)
    (i : Fin (n + 1)) (hi : i.1 + 2 < n + 1) :
    b.order i + 2 ≤ b.order ⟨i.1 + 2, hi⟩ := by
  let i1 : Fin (n + 1) := ⟨i.1 + 1, by omega⟩
  let i2 : Fin (n + 1) := ⟨i.1 + 2, hi⟩
  let p0 : Fin n := ⟨i.1, by omega⟩
  let p1 : Fin n := ⟨i.1 + 1, by omega⟩
  let d0 : Int := b.order i1 - b.order i
  let d1 : Int := b.order i2 - b.order i1
  have hp0Cast : p0.castSucc = i := by
    apply Fin.ext
    simp [p0]
  have hp0Succ : p0.succ = i1 := by
    apply Fin.ext
    simp [p0, i1]
  have hp1Cast : p1.castSucc = i1 := by
    apply Fin.ext
    simp [p1, i1]
  have hp1Succ : p1.succ = i2 := by
    apply Fin.ext
    simp [p1, i2]
  have hd0Lower : -(2 * (ramificationIndex K : Int)) ≤ d0 := by
    simpa [d0, i1] using b.adjacentOrderGap_ge_neg_two_mul_e i (by omega)
  have hd1Lower : -(2 * (ramificationIndex K : Int)) ≤ d1 := by
    simpa [d1, i1, i2] using
      b.adjacentOrderGap_ge_neg_two_mul_e i1 (by omega)
  have hstrict : b.order i < b.order i2 := by
    simpa [i2] using hb.hasPropertyA i hi
  by_contra hnot
  have hupper : b.order i2 < b.order i + 2 := by
    rw [not_le] at hnot
    simpa [i2] using hnot
  have hsum : d0 + d1 = 1 := by
    simp only [d0, d1]
    omega
  rcases Int.even_or_odd d0 with hd0Even | hd0Odd
  · have hd1Odd : Odd d1 := by
      have honeOdd : Odd (1 : Int) := odd_one
      have : Odd (1 - d0) := honeOdd.sub_even hd0Even
      convert this using 1 <;> omega
    have hd1Pos : 0 < d1 := by
      have hodd : Odd (b.order ⟨i1.1 + 1, by omega⟩ - b.order i1) := by
        simpa [d1, i1, i2] using hd1Odd
      simpa [d1, i1, i2] using
        b.adjacentOrderGap_pos_of_odd i1 (by omega) hodd
    have htrigger : b.propertyBTrigger p1 := by
      left
      constructor
      · rw [hp1Succ, hp1Cast]
        change d1 ≤ 2 * (ramificationIndex K : Int) + 1
        omega
      · simpa [d1, hp1Cast, hp1Succ] using hd1Odd
    have hleft := (hb.2 p1 htrigger).1 i (by simp [p1])
    have : 2 * (ramificationIndex K : Int) + 1 ≤ d0 := by
      simpa [d0, hp1Cast] using hleft
    omega
  · have hd0Pos : 0 < d0 := by
      have hodd : Odd (b.order ⟨i.1 + 1, by omega⟩ - b.order i) := by
        simpa [d0, i1] using hd0Odd
      simpa [d0, i1] using
        b.adjacentOrderGap_pos_of_odd i (by omega) hodd
    have htrigger : b.propertyBTrigger p0 := by
      left
      constructor
      · rw [hp0Succ, hp0Cast]
        change d0 ≤ 2 * (ramificationIndex K : Int) + 1
        omega
      · simpa [d0, hp0Cast, hp0Succ] using hd0Odd
    have hright := (hb.2 p0 htrigger).2 i2 (by simp [p0, i2])
    have : 2 * (ramificationIndex K : Int) + 1 ≤ d1 := by
      simpa [d1, hp0Succ] using hright
    omega

/-- Unit-valued BONG entries commute with removing the head. -/
theorem valueUnit_tail (b : BONG V q L (n + 2))
    (i : Fin (n + 1)) :
    b.tail.valueUnit i = b.valueUnit i.succ := by
  apply Units.ext
  exact b.value_tail i

/-- Normalized BONG values commute with removing the head. -/
theorem normalizedValue_tail (b : BONG V q L (n + 2))
    (i : Fin (n + 1)) :
    b.tail.normalizedValue i = b.normalizedValue i.succ := by
  rw [normalizedValue, normalizedValue, b.valueUnit_tail i,
    b.order_tail i]

/-- Normalized adjacent defect orders commute with removing the head. -/
theorem normalizedAdjacentDefectOrder_tail
    (b : BONG V q L (n + 2)) (i : Fin n) :
    b.tail.normalizedAdjacentDefectOrder i =
      b.normalizedAdjacentDefectOrder i.succ := by
  unfold normalizedAdjacentDefectOrder normalizedAdjacentProduct
  congr 2
  rw [b.normalizedValue_tail i.castSucc,
    b.normalizedValue_tail i.succ]
  have hcast : i.castSucc.succ = i.succ.castSucc := by
    apply Fin.ext
    simp
  rw [hcast]

/-- Property B passes to the recursive BONG tail. -/
theorem HasPropertyB.tail
    {b : BONG V q L (n + 2)} (hB : b.HasPropertyB) :
    b.tail.HasPropertyB := by
  refine ⟨hB.hasPropertyA.tail, ?_⟩
  intro i hi
  let p : Fin (n + 1) := i.succ
  have hpTrigger : b.propertyBTrigger p := by
    unfold propertyBTrigger at hi ⊢
    rw [b.order_tail i.castSucc, b.order_tail i.succ,
      b.normalizedAdjacentDefectOrder_tail i] at hi
    have hcast : i.castSucc.succ = i.succ.castSucc := by
      apply Fin.ext
      simp
    simpa only [p, hcast] using hi
  refine ⟨?_, ?_⟩
  · intro j hj
    have hleft := (hB.2 p hpTrigger).1 j.succ (by
      simp only [Fin.val_succ, p]
      omega)
    rw [b.order_tail i.castSucc, b.order_tail j]
    have hcast : i.castSucc.succ = p.castSucc := by
      apply Fin.ext
      simp [p]
    simpa only [hcast] using hleft
  · intro k hk
    have hright := (hB.2 p hpTrigger).2 k.succ (by
      simp only [Fin.val_succ, p]
      omega)
    rw [b.order_tail k, b.order_tail i.succ]
    have hsucc : i.succ.succ = p.succ := by
      apply Fin.ext
      simp [p]
    simpa only [hsucc] using hright

end BONG

/-- The remaining integral implication in Beli (2003), Lemma 4.11. -/
class BeliLemma411Laws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  full_spinorNormImage_of_propertyA_not_propertyB
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 1)) :
    b.HasPropertyA → ¬b.HasPropertyB →
      Lattice.spinorNormImage (q := q) (L := L) = Set.univ

namespace BONG

variable [BeliLemma411Laws.{u, v} K]

/-- Beli (2003), Lemma 4.11. -/
theorem beliLemma411 (b : BONG V q L (n + 1))
    (hA : b.HasPropertyA) (hnotB : ¬b.HasPropertyB) :
    Lattice.spinorNormImage (q := q) (L := L) = Set.univ :=
  BeliLemma411Laws.full_spinorNormImage_of_propertyA_not_propertyB b hA hnotB

end BONG

end Bong
