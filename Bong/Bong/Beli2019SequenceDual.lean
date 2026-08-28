/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderSequence
import Bong.Bong.BeliLemma411
import Mathlib.Data.Fin.Rev

/-!
# Beli (2019), reversal of ordered valuation sequences

This file formalizes the involution
`(x_1, ..., x_n) ↦ (-x_n, ..., -x_1)` from the end of Section 1.  It
preserves `B_n(kappa)` and reverses Beli's order on each fixed-rank stratum.
The final declarations identify this combinatorial involution with the order
sequence of a reverse-dual good BONG.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- The reversed, negated sequence `x* = (-x_n, ..., -x_1)`. -/
def reverseNegate {n : Nat} (x : BeliOrderSequence n Gamma) :
    BeliOrderSequence n Gamma where
  value i := -x.value (Fin.rev i)
  twoStep := by
    intro i hi
    let j : Fin n := Fin.rev ⟨i + 2, hi⟩
    have hj : j.1 + 2 < n := by
      simp [j]
      omega
    have hmono := x.twoStep j.1 hj
    have hindex : (⟨j.1 + 2, hj⟩ : Fin n) = Fin.rev ⟨i, by omega⟩ := by
      apply Fin.ext
      simp [j]
      omega
    rw [hindex] at hmono
    exact neg_le_neg hmono

@[simp]
theorem reverseNegate_value {n : Nat} (x : BeliOrderSequence n Gamma)
    (i : Fin n) : x.reverseNegate.value i = -x.value (Fin.rev i) :=
  rfl

@[simp]
theorem reverseNegate_entry {n : Nat} (x : BeliOrderSequence n Gamma)
    (i : Nat) (hi : i < n) :
    x.reverseNegate.entry i hi = -x.value (Fin.rev ⟨i, hi⟩) :=
  rfl

@[simp]
theorem reverseNegate_reverseNegate {n : Nat}
    (x : BeliOrderSequence n Gamma) : x.reverseNegate.reverseNegate = x := by
  apply BeliOrderSequence.ext
  funext i
  simp

private theorem reverseNegate_isKappaBounded {n : Nat}
    {x : BeliOrderSequence n Gamma} {κ : Gamma}
    (h : x.IsKappaBounded κ) : x.reverseNegate.IsKappaBounded κ := by
  intro i hi
  let j : Fin n := Fin.rev ⟨i + 1, hi⟩
  have hj : j.1 + 1 < n := by
    simp [j]
    omega
  have hbound := h j.1 hj
  have hindex : (⟨j.1 + 1, hj⟩ : Fin n) = Fin.rev ⟨i, by omega⟩ := by
    apply Fin.ext
    simp [j]
    omega
  change -x.value (Fin.rev ⟨i, by omega⟩) ≤
    -x.value (Fin.rev ⟨i + 1, hi⟩) + κ
  change x.value j ≤ x.value ⟨j.1 + 1, hj⟩ + κ at hbound
  rw [hindex] at hbound
  apply (sub_le_iff_le_add).1
  simpa only [sub_eq_add_neg, neg_add_rev, add_comm] using neg_le_neg hbound

/-- Reversal preserves Definition 3's adjacent `kappa`-bound. -/
theorem reverseNegate_isKappaBounded_iff {n : Nat}
    (x : BeliOrderSequence n Gamma) (κ : Gamma) :
    x.reverseNegate.IsKappaBounded κ ↔ x.IsKappaBounded κ := by
  constructor
  · intro h
    have := reverseNegate_isKappaBounded (x := x.reverseNegate) h
    simpa using this
  · exact reverseNegate_isKappaBounded

end BeliOrderSequence

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

private theorem reverseNegate_mono {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y) :
    BeliOrderLE y.reverseNegate x.reverseNegate where
  rank := le_rfl
  compare := by
    intro i hi
    let j : Fin n := Fin.rev ⟨i, hi⟩
    rcases h.compare j.1 j.isLt with hcurrent | ⟨hj0, hjNext, hpair⟩
    · exact Or.inl (neg_le_neg hcurrent)
    · have hi0 : 0 < i := by
        simp [j] at hjNext
        omega
      have hiNext : i + 1 < n := by
        simp [j] at hj0
        omega
      refine Or.inr ⟨hi0, hiNext, ?_⟩
      have hneg := neg_le_neg hpair
      change
        -y.value (Fin.rev ⟨i, hi⟩) +
            -y.value (Fin.rev ⟨i + 1, hiNext⟩) ≤
          -x.value (Fin.rev ⟨i - 1, by omega⟩) +
            -x.value (Fin.rev ⟨i, hi⟩)
      have hleft : Fin.rev ⟨i + 1, hiNext⟩ = ⟨j.1 - 1, by omega⟩ := by
        apply Fin.ext
        simp [j]
        omega
      have hright : Fin.rev ⟨i - 1, by omega⟩ =
          ⟨j.1 + 1, hjNext⟩ := by
        apply Fin.ext
        simp [j]
        omega
      rw [hleft, hright]
      change -y.value j + -y.value ⟨j.1 - 1, by omega⟩ ≤
        -x.value ⟨j.1 + 1, hjNext⟩ + -x.value j
      simpa only [neg_add_rev, BeliOrderSequence.entry] using hneg

/-- On a fixed-rank stratum, `x ≤ y` iff `y* ≤ x*`. -/
theorem reverseNegate_le_reverseNegate_iff {n : Nat}
    (x y : BeliOrderSequence n Gamma) :
    BeliOrderLE x.reverseNegate y.reverseNegate ↔ BeliOrderLE y x := by
  constructor
  · intro h
    have := reverseNegate_mono h
    simpa using this
  · exact reverseNegate_mono

end BeliOrderLE

namespace BONG.GoodBONG

open BeliOrderSequence
open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The order sequence of every good BONG belongs to `B_n(2e)`. -/
theorem orderSequence_isKappaBounded_two_mul_e (b : GoodBONG q L n) :
    b.orderSequence.IsKappaBounded (2 * (ramificationIndex K : Int)) := by
  intro i hi
  have hgap := b.toBONG.adjacentOrderGap_ge_neg_two_mul_e ⟨i, by omega⟩ hi
  change -(2 * (ramificationIndex K : Int)) ≤
    b.order ⟨i + 1, hi⟩ - b.order ⟨i, by omega⟩ at hgap
  change b.order ⟨i, by omega⟩ ≤
    b.order ⟨i + 1, hi⟩ + 2 * (ramificationIndex K : Int)
  omega

/-- A reverse-dual good BONG realizes the combinatorial `star` operation. -/
theorem exists_reverseDual_orderSequence
    [BONGStructuralLaws.{u, v} K] (b : GoodBONG q L n) :
    ∃ c : GoodBONG q (Lattice.dualLattice q L) n,
      c.orderSequence = b.orderSequence.reverseNegate := by
  rcases b.exists_reverseDual_with_values with ⟨c, _, _, horders⟩
  refine ⟨c, ?_⟩
  apply BeliOrderSequence.ext
  funext i
  exact horders i

end BONG.GoodBONG

end Bong
