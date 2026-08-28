/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderSumRigidity

/-!
# Beli (2019), Lemma 5.5(iv): fixed-total-gap interval sums

The paper uses closed, one-based intervals.  Here `segmentSum x i j` is
zero-based and half-open: it is the sum over `[i, j)`.  Thus the paper's
`x_i + ... + x_j` is represented by `segmentSum x (i - 1) j`.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- The sum over the half-open interval `[i, j)`. -/
def segmentSum {n : Nat} (x : BeliOrderSequence n Gamma)
    (i j : Nat) : Gamma :=
  x.prefixSum j - x.prefixSum i

omit [IsOrderedAddMonoid Gamma] in
theorem prefix_add_segment_add_suffix {n : Nat}
    (x : BeliOrderSequence n Gamma) (i j : Nat) (hj : j ≤ n) :
    x.prefixSum i + x.segmentSum i j + x.suffixSum j =
      x.prefixSum n := by
  rw [segmentSum, x.suffixSum_eq_total_sub_prefix j hj]
  abel

omit [IsOrderedAddMonoid Gamma] in
theorem segmentSum_eq_total_sub_prefix_sub_suffix {n : Nat}
    (x : BeliOrderSequence n Gamma) (i j : Nat) (hj : j ≤ n) :
    x.segmentSum i j =
      x.prefixSum n - x.prefixSum i - x.suffixSum j := by
  rw [segmentSum, x.suffixSum_eq_total_sub_prefix j hj]
  abel

end BeliOrderSequence

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- If two ordered summands are bounded componentwise and their sums agree,
then both component inequalities are equalities. -/
theorem add_eq_components_of_le {a b c d : Gamma}
    (hab : a ≤ b) (hcd : c ≤ d) (hsum : a + c = b + d) :
    a = b ∧ c = d := by
  constructor
  · apply le_antisymm hab
    apply le_of_add_le_add_right
    calc
      b + c ≤ b + d := add_le_add_right hcd _
      _ = a + c := hsum.symm
  · apply le_antisymm hcd
    apply le_of_add_le_add_left
    calc
      a + d ≤ b + d := add_le_add_left hab _
      _ = a + c := hsum.symm

/-- Under a fixed nonnegative total gap, the source interval plus the gap
dominates the target interval.  This is Lemma 5.5(iv)'s inequality. -/
theorem segmentSum_le_add_totalGap {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    {κ : Gamma} (htotal : x.prefixSum n + κ = y.prefixSum n)
    (i j : Nat) (hij : i ≤ j) (hj : j ≤ n) :
    y.segmentSum i j ≤ x.segmentSum i j + κ := by
  have hprefix := h.prefixSum_le i (hij.trans hj)
  have hsuffix := h.suffixSum_le j hj
  rw [y.segmentSum_eq_total_sub_prefix_sub_suffix i j hj,
    x.segmentSum_eq_total_sub_prefix_sub_suffix i j hj]
  calc
    y.prefixSum n - y.prefixSum i - y.suffixSum j =
        (x.prefixSum n + κ) - y.prefixSum i - y.suffixSum j := by
      rw [htotal]
    _ ≤ (x.prefixSum n + κ) - x.prefixSum i - x.suffixSum j :=
      sub_le_sub (sub_le_sub_left hprefix _) hsuffix
    _ = (x.prefixSum n - x.prefixSum i - x.suffixSum j) + κ := by
      abel

/-- Equality in Lemma 5.5(iv) occurs exactly when the prefix before the
interval and the suffix after the interval both attain equality. -/
theorem segmentSum_add_totalGap_eq_iff {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    {κ : Gamma} (htotal : x.prefixSum n + κ = y.prefixSum n)
    (i j : Nat) (hij : i ≤ j) (hj : j ≤ n) :
    x.segmentSum i j + κ = y.segmentSum i j ↔
      x.prefixSum i = y.prefixSum i ∧ x.suffixSum j = y.suffixSum j := by
  have hprefix := h.prefixSum_le i (hij.trans hj)
  have hsuffix := h.suffixSum_le j hj
  have hxDecompose := x.prefix_add_segment_add_suffix i j hj
  have hyDecompose := y.prefix_add_segment_add_suffix i j hj
  constructor
  · intro hsegment
    have hxTotal : x.prefixSum n = y.prefixSum n - κ :=
      (eq_sub_iff_add_eq).2 htotal
    have hxSegment : x.segmentSum i j = y.segmentSum i j - κ :=
      (eq_sub_iff_add_eq).2 hsegment
    have hcomplement :
        x.prefixSum i + x.suffixSum j =
          y.prefixSum i + y.suffixSum j := by
      calc
        x.prefixSum i + x.suffixSum j =
            x.prefixSum n - x.segmentSum i j := by
          rw [← hxDecompose]
          abel
        _ = (y.prefixSum n - κ) -
            (y.segmentSum i j - κ) := by
          rw [hxTotal, hxSegment]
        _ = y.prefixSum n - y.segmentSum i j := by
          abel
        _ = y.prefixSum i + y.suffixSum j := by
          rw [← hyDecompose]
          abel
    constructor
    · apply le_antisymm hprefix
      apply le_of_add_le_add_right
      calc
        y.prefixSum i + x.suffixSum j ≤
            y.prefixSum i + y.suffixSum j :=
          add_le_add_right hsuffix _
        _ = x.prefixSum i + x.suffixSum j := hcomplement.symm
    · apply le_antisymm hsuffix
      apply le_of_add_le_add_left
      calc
        x.prefixSum i + y.suffixSum j ≤
            y.prefixSum i + y.suffixSum j :=
          add_le_add_left hprefix _
        _ = x.prefixSum i + x.suffixSum j := hcomplement.symm
  · rintro ⟨hprefixEq, hsuffixEq⟩
    rw [x.segmentSum_eq_total_sub_prefix_sub_suffix i j hj,
      y.segmentSum_eq_total_sub_prefix_sub_suffix i j hj,
      hprefixEq, hsuffixEq, ← htotal]
    abel

/-- The paper assumes `κ ≥ 0` in Lemma 5.5(iv); it already follows from
the order relation and the displayed total-gap identity. -/
theorem totalGap_nonneg {n : Nat} {x y : BeliOrderSequence n Gamma}
    (h : BeliOrderLE x y) {κ : Gamma}
    (htotal : x.prefixSum n + κ = y.prefixSum n) :
    0 ≤ κ := by
  have hsum := h.prefixSum_le n le_rfl
  have hself : x.prefixSum n ≤ x.prefixSum n + κ := by
    rw [htotal]
    exact hsum
  simpa only [le_add_iff_nonneg_right] using hself

end BeliOrderLE

end Bong
