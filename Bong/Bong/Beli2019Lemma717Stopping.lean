/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma717Cases

/-!
# Beli (2019), Lemma 7.17: choosing the maximal even endpoint

In the equal-first-gap branch the second order is `R - 2e`, so the set of
even prefix lengths ending at that order is nonempty.  Its greatest element
is the stopping index used throughout Lemmas 7.17--7.20.  This file performs
that finite choice explicitly; callers no longer need to supply a stopping
certificate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The maximal even endpoint of Lemma 7.17 exists as soon as the displayed
second order has the exceptional value `R - 2e`. -/
theorem exists_lemma717StoppingData
    (b : GoodBONG q L (n + 3)) (R : Int)
    (hsecond : b.order (1 : Fin (n + 3)) =
      R - 2 * (ramificationIndex K : Int)) :
    ∃ s, Lemma717StoppingData b R s := by
  classical
  let P : Nat → Prop := fun k =>
    Even k ∧ 2 ≤ k ∧
      b.orderSequence.entryOrZero (k - 1) =
        R - 2 * (ramificationIndex K : Int)
  have hPtwo : P 2 := by
    refine ⟨even_two, by omega, ?_⟩
    have hindex : b.orderSequence.entryOrZero 1 =
        b.order (1 : Fin (n + 3)) := by
      convert orderSequence_entryOrZero_eq_order b (1 : Fin (n + 3)) using 1
      norm_num
    exact hindex.trans hsecond
  let s := Nat.findGreatest P (n + 3)
  have hsP : P s := by
    exact Nat.findGreatest_spec (P := P) (n := n + 3) (m := 2)
      (by omega) hPtwo
  have hsLe : s ≤ n + 3 := by
    exact Nat.findGreatest_le (P := P) (n + 3)
  refine ⟨s, {
    even := hsP.1
    two_le := hsP.2.1
    le_rank := hsLe
    terminal := ?_
    maximal := ?_ }⟩
  · have hentry := hsP.2.2
    have hindex :
        b.orderSequence.entryOrZero (s - 1) =
          b.order ⟨s - 1, by omega⟩ := by
      exact b.orderSequence_entryOrZero_eq_order ⟨s - 1, by omega⟩
    exact hindex.symm.trans hentry
  · intro hsBound
    have hnot : ¬ P (s + 2) := by
      apply Nat.findGreatest_is_greatest
          (P := P) (n := n + 3) (k := s + 2)
      · simp only [s]
        omega
      · exact hsBound
    intro hnext
    apply hnot
    refine ⟨hsP.1.add even_two, by omega, ?_⟩
    have hindex :
        b.orderSequence.entryOrZero ((s + 2) - 1) =
          b.order ⟨s + 1, by omega⟩ := by
      rw [show (s + 2) - 1 = s + 1 by omega]
      exact orderSequence_entryOrZero_eq_order b ⟨s + 1, by omega⟩
    exact hindex.trans hnext

end BONG.GoodBONG

end Bong
