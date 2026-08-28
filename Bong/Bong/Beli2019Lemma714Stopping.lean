/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714BoundaryOrders

/-!
# Beli (2019), Lemma 7.14: choosing the minimal even endpoint

The special equal-gap branch chooses the least even prefix length at which
the next same-parity order crosses `R - 2e + 1`, or the last possible even
prefix if the lattice ends first.  This finite choice supplies exactly
`Lemma714StoppingData` and removes another caller-provided certificate from
Section 7.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The minimal even endpoint used by Lemmas 7.14--7.16 always exists. -/
theorem exists_lemma714StoppingData
    (b : GoodBONG q L (n + 3)) (R : Int) :
    ∃ s, Lemma714StoppingData b R s := by
  classical
  let threshold : Int := R - 2 * (ramificationIndex K : Int) + 1
  let P : Nat → Prop := fun s =>
    Even s ∧ 2 ≤ s ∧ s ≤ n + 3 ∧
      (n + 3 < s + 2 ∨
        threshold < b.orderSequence.entryOrZero (s + 1))
  have hexists : ∃ s, P s := by
    by_cases hEven : Even (n + 3)
    · refine ⟨n + 3, hEven, by omega, le_rfl, Or.inl (by omega)⟩
    · have hOdd : Odd (n + 3) := Nat.not_even_iff_odd.mp hEven
      let s := (n + 3) - 1
      have hsEven : Even s := by
        exact Nat.Odd.sub_odd hOdd odd_one
      refine ⟨s, hsEven, by dsimp only [s]; omega,
        by dsimp only [s]; omega, Or.inl ?_⟩
      dsimp only [s]
      omega
  let s := Nat.find hexists
  have hsP : P s := Nat.find_spec hexists
  refine ⟨s, {
    even := hsP.1
    two_le := hsP.2.1
    le_rank := hsP.2.2.1
    before := ?_
    at_stop := ?_ }⟩
  · intro t htTwo hts htEven htBound
    by_contra hnot
    have hstrict : threshold < b.order ⟨t + 1, by omega⟩ := by
      omega
    have hentry :
        b.orderSequence.entryOrZero (t + 1) =
          b.order ⟨t + 1, by omega⟩ :=
      orderSequence_entryOrZero_eq_order b ⟨t + 1, by omega⟩
    have htP : P t := by
      refine ⟨htEven, htTwo, by omega, Or.inr ?_⟩
      exact hstrict.trans_eq hentry.symm
    exact (Nat.find_min hexists hts) htP
  · intro hsBound
    rcases hsP.2.2.2 with hend | hstrict
    · omega
    · have hentry :
          b.orderSequence.entryOrZero (s + 1) =
            b.order ⟨s + 1, by omega⟩ :=
        orderSequence_entryOrZero_eq_order b ⟨s + 1, by omega⟩
      exact hstrict.trans_eq hentry

end BONG.GoodBONG

end Bong
