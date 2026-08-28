/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIInterval

/-!
# Segment sums of the `W`-sequence

Consecutive even-odd pairs of the `W`-sequence telescope to adjacent BONG
order sums.  Consequently, equality of adjacent order sums throughout an
interval gives equality of the corresponding even-length `W`-segments.
This is the sum calculation in Beli (2019), Lemma 6.9(v).
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

omit [IsOrderedAddMonoid Gamma] in
/-- Extend a segment by the adjacent pair beginning at its right endpoint. -/
theorem segmentSum_add_pair {n : Nat} (x : BeliOrderSequence n Gamma)
    (start finish : Nat) :
    x.segmentSum start (finish + 2) =
      x.segmentSum start finish +
        (x.entryOrZero finish + x.entryOrZero (finish + 1)) := by
  unfold segmentSum
  rw [x.prefixSum_add_two finish]
  abel

omit [IsOrderedAddMonoid Gamma] in
/-- Equality of aligned adjacent pairs gives equality of the segment made
from those pairs. -/
theorem segmentSum_two_mul_eq_of_pair_eq {n : Nat}
    (x y : BeliOrderSequence n Gamma) (left count : Nat)
    (hpair : ∀ k, left ≤ k → k < left + count →
      x.entryOrZero (2 * k) + x.entryOrZero (2 * k + 1) =
        y.entryOrZero (2 * k) + y.entryOrZero (2 * k + 1)) :
    x.segmentSum (2 * left) (2 * (left + count)) =
      y.segmentSum (2 * left) (2 * (left + count)) := by
  induction count with
  | zero =>
      simp [segmentSum]
  | succ count ih =>
      have hprevious : ∀ k, left ≤ k → k < left + count →
          x.entryOrZero (2 * k) + x.entryOrZero (2 * k + 1) =
            y.entryOrZero (2 * k) + y.entryOrZero (2 * k + 1) := by
        intro k hkLeft hkRight
        exact hpair k hkLeft (by omega)
      have ih' := ih hprevious
      have hlast := hpair (left + count) (by omega) (by omega)
      rw [show 2 * (left + (count + 1)) =
          2 * (left + count) + 2 by omega,
        x.segmentSum_add_pair, y.segmentSum_add_pair, ih', hlast]

omit [IsOrderedAddMonoid Gamma] in
/-- Endpoint form of `segmentSum_two_mul_eq_of_pair_eq`. -/
theorem segmentSum_two_mul_eq_of_pair_eq_between {n : Nat}
    (x y : BeliOrderSequence n Gamma) (left right : Nat)
    (hleftRight : left ≤ right)
    (hpair : ∀ k, left ≤ k → k < right →
      x.entryOrZero (2 * k) + x.entryOrZero (2 * k + 1) =
        y.entryOrZero (2 * k) + y.entryOrZero (2 * k + 1)) :
    x.segmentSum (2 * left) (2 * right) =
      y.segmentSum (2 * left) (2 * right) := by
  have h := x.segmentSum_two_mul_eq_of_pair_eq y left (right - left)
    (by
      intro k hkLeft hkRight
      exact hpair k hkLeft (by omega))
  simpa only [show left + (right - left) = right by omega] using h

end BeliOrderSequence

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type v} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  [Beli2006AlphaLaws.{u, v} K]

/-- Each even-odd pair of `W(L)` sums to the adjacent BONG order sum. -/
theorem weightSequence_entryPair
    (b : GoodBONG q L (n + 2)) (k : Nat) (hk : k < n + 1) :
    b.weightSequence.entryOrZero (2 * k) +
        b.weightSequence.entryOrZero (2 * k + 1) =
      (b.order ⟨k, by omega⟩ : ℚ) + b.order ⟨k + 1, by omega⟩ := by
  have heven : 2 * k < 2 * (n + 1) := by omega
  have hodd : 2 * k + 1 < 2 * (n + 1) := by omega
  rw [BeliOrderSequence.entryOrZero_of_lt b.weightSequence heven,
    BeliOrderSequence.entryOrZero_of_lt b.weightSequence hodd]
  change b.weightSequence.value ⟨2 * k, heven⟩ +
      b.weightSequence.value ⟨2 * k + 1, hodd⟩ = _
  let kFin : Fin (n + 1) := ⟨k, hk⟩
  have hevenValue := b.weightSequence_even kFin
  have hoddValue := b.weightSequence_odd kFin
  rw [show (⟨2 * k, heven⟩ : Fin (2 * (n + 1))) =
      ⟨2 * kFin.1, by omega⟩ by apply Fin.ext; rfl,
    show (⟨2 * k + 1, hodd⟩ : Fin (2 * (n + 1))) =
      ⟨2 * kFin.1 + 1, by omega⟩ by apply Fin.ext; rfl]
  rw [hevenValue, hoddValue]
  have hkCast : kFin.castSucc = ⟨k, by omega⟩ := by
    apply Fin.ext
    rfl
  have hkSucc : kFin.succ = ⟨k + 1, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.succ, kFin]
  rw [hkCast, hkSucc]
  ring

/-- Equality of adjacent BONG order sums implies equality of the matching
`W`-segment. -/
theorem weightSegmentSum_eq_of_adjacentOrderSums
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (left right : Nat) (hleftRight : left ≤ right)
    (hright : right ≤ n + 1)
    (horder : ∀ k (_ : left ≤ k) (hkRight : k < right),
      (a.order ⟨k, by omega⟩ : ℚ) + a.order ⟨k + 1, by omega⟩ =
        (b.order ⟨k, by omega⟩ : ℚ) + b.order ⟨k + 1, by omega⟩) :
    a.weightSequence.segmentSum (2 * left) (2 * right) =
      b.weightSequence.segmentSum (2 * left) (2 * right) := by
  apply BeliOrderSequence.segmentSum_two_mul_eq_of_pair_eq_between
    a.weightSequence b.weightSequence left right hleftRight
  intro k hkLeft hkRight
  rw [a.weightSequence_entryPair k (by omega),
    b.weightSequence_entryPair k (by omega)]
  exact horder k hkLeft hkRight

end BONG.GoodBONG

end Bong
