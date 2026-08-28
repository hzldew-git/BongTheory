/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrescribedHead

/-!
# Beli (2019), Corollary 5.10: the one-vector base step

This file proves the complete `i = 1` step of Corollary 5.10.  The prescribed
head is extended by the candidate constructed from its projected lattice.  The
four alternatives are discharged respectively by rank two, equality of the
second projected norm ideal, the strict two-step order condition, and the
maximal adjacent gap condition.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

private theorem orderSequence_entryOrZero {L : Lattice K V} {m : Nat}
    (b : GoodBONG q L m) (i : Nat) (hi : i < m) :
    b.orderSequence.entryOrZero i = b.order ⟨i, hi⟩ := by
  rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence hi]
  exact b.orderSequence_at i hi

/-- Corollary 5.10 for a one-vector prefix.  The comparison data are exactly
the output of the enlarged-lattice construction in Lemma 5.7. -/
theorem prescribedHeadCandidateWithTail_isGood_of_trigger_one
    [BeliLemma47Laws.{u, v} K]
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hNM : N ≤ M) (hzero : a.order 0 = b.order 0)
    (tail : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head b.toBONG.head_isAnisotropic)
      (n + 1))
    (x : BeliOrderSequence (n + 2) Int)
    (D : NormGeneratorComparisonData a
      (a.prescribedHeadCandidateWithTail b hNM hzero tail) x)
    (htrigger : BeliPrefixExtensionTrigger (ramificationIndex K : Int)
      a.orderSequence b.orderSequence 1) :
    (a.prescribedHeadCandidateWithTail b hNM hzero tail).IsGood := by
  let c := a.prescribedHeadCandidateWithTail b hNM hzero tail
  change NormGeneratorComparisonData a c x at D
  change c.IsGood
  cases n with
  | zero =>
      exact c.isGood_of_length_le_two (by omega)
  | succ n =>
      cases htrigger with
      | terminal hterminal =>
          omega
      | nextOrder _ _ horder =>
          have hsecond : a.order 1 = b.order 1 := by
            rw [orderSequence_entryOrZero a 1 (by omega),
              orderSequence_entryOrZero b 1 (by omega)] at horder
            simpa using horder
          have hsourceIdealAtB :
              Lattice.normIdeal
                  (q.orthogonalSpace b.toBONG.head
                    b.toBONG.head_isAnisotropic)
                  (N.projectedLattice q b.toBONG.head
                    b.toBONG.head_isAnisotropic) =
                Lattice.powerIdeal (K := K) (b.order 1) := by
            rw [b.toBONG.tail.normIdeal_eq_powerIdeal_order_zero,
              b.toBONG.order_tail]
            rfl
          have hprojected :
              N.projectedLattice q b.toBONG.head
                  b.toBONG.head_isAnisotropic ≤
                M.projectedLattice q b.toBONG.head
                  b.toBONG.head_isAnisotropic :=
            Lattice.projectedLattice_mono q hNM b.toBONG.head
              b.toBONG.head_isAnisotropic
          have hlower :
              Lattice.powerIdeal (K := K) (a.order 1) ≤
                Lattice.normIdeal
                  (q.orthogonalSpace b.toBONG.head
                    b.toBONG.head_isAnisotropic)
                  (M.projectedLattice q b.toBONG.head
                    b.toBONG.head_isAnisotropic) := by
            rw [hsecond, ← hsourceIdealAtB]
            exact Lattice.normIdeal_mono
              (q.orthogonalSpace b.toBONG.head
                b.toBONG.head_isAnisotropic) hprojected
          have hupper := D.projectedNormIdeal_le
          change Lattice.normIdeal
              (q.orthogonalSpace b.toBONG.head
                b.toBONG.head_isAnisotropic)
              (M.projectedLattice q b.toBONG.head
                b.toBONG.head_isAnisotropic) ≤
            Lattice.powerIdeal (K := K) (a.order 1) at hupper
          have hcriterion := D.projectedNormIdeal_eq_iff_isGood
          change Lattice.normIdeal
              (q.orthogonalSpace b.toBONG.head
                b.toBONG.head_isAnisotropic)
              (M.projectedLattice q b.toBONG.head
                b.toBONG.head_isAnisotropic) =
                Lattice.powerIdeal (K := K) (a.order 1) ↔
              c.IsGood at hcriterion
          exact hcriterion.mp (le_antisymm hupper hlower)
      | strictTwoStep _ hstrict =>
          have hfirstThird : a.order 0 < a.order 2 := by
            rw [orderSequence_entryOrZero a 0 (by omega),
              orderSequence_entryOrZero a 2 (by omega)] at hstrict
            have htwo :
                (⟨2, by omega⟩ : Fin (n + 1 + 2)) =
                  (2 : Fin (n + 1 + 2)) := by
              apply Fin.ext
              change 2 = 2 % (n + 1 + 2)
              rw [Nat.mod_eq_of_lt (by omega)]
            rw [htwo] at hstrict
            exact hstrict
          exact D.isGood_of_first_lt_third hfirstThird
      | maximalGap _ hgap =>
          have hmaximalGap :
              a.order 1 - a.order 0 =
                2 * (ramificationIndex K : Int) := by
            rw [orderSequence_entryOrZero a 1 (by omega),
              orderSequence_entryOrZero a 0 (by omega)] at hgap
            simpa using hgap
          exact D.isGood_of_second_gap_eq_two_mul_e hmaximalGap

/-- The canonical prescribed-head candidate, bundled with the base-step
goodness proof. -/
noncomputable def prescribedHeadGoodCandidate
    [BeliLemma47Laws.{u, v} K]
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hNM : N ≤ M) (hzero : a.order 0 = b.order 0)
    (tail : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head b.toBONG.head_isAnisotropic)
      (n + 1))
    (x : BeliOrderSequence (n + 2) Int)
    (D : NormGeneratorComparisonData a
      (a.prescribedHeadCandidateWithTail b hNM hzero tail) x)
    (htrigger : BeliPrefixExtensionTrigger (ramificationIndex K : Int)
      a.orderSequence b.orderSequence 1) :
    GoodBONG q M (n + 2) where
  toBONG := a.prescribedHeadCandidateWithTail b hNM hzero tail
  good := a.prescribedHeadCandidateWithTail_isGood_of_trigger_one
    b hNM hzero tail x D htrigger

@[simp]
theorem prescribedHeadGoodCandidate_head
    [BeliLemma47Laws.{u, v} K]
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hNM : N ≤ M) (hzero : a.order 0 = b.order 0)
    (tail : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head b.toBONG.head_isAnisotropic)
      (n + 1))
    (x : BeliOrderSequence (n + 2) Int)
    (D : NormGeneratorComparisonData a
      (a.prescribedHeadCandidateWithTail b hNM hzero tail) x)
    (htrigger : BeliPrefixExtensionTrigger (ramificationIndex K : Int)
      a.orderSequence b.orderSequence 1) :
    (a.prescribedHeadGoodCandidate b hNM hzero tail x D htrigger).toBONG.head =
      b.toBONG.head := by
  exact a.prescribedHeadCandidateWithTail_head b hNM hzero tail

/-- Corollary 5.10's base step, as an existence theorem for a good BONG of
the ambient lattice beginning with the prescribed sublattice head. -/
theorem exists_goodBONG_beginning_with_head_of_trigger_one
    [BeliLemma47Laws.{u, v} K]
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hNM : N ≤ M) (hzero : a.order 0 = b.order 0)
    (tail : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head b.toBONG.head_isAnisotropic)
      (n + 1))
    (x : BeliOrderSequence (n + 2) Int)
    (D : NormGeneratorComparisonData a
      (a.prescribedHeadCandidateWithTail b hNM hzero tail) x)
    (htrigger : BeliPrefixExtensionTrigger (ramificationIndex K : Int)
      a.orderSequence b.orderSequence 1) :
    ∃ c : GoodBONG q M (n + 2), c.toBONG.head = b.toBONG.head := by
  exact ⟨a.prescribedHeadGoodCandidate b hNM hzero tail x D htrigger,
    a.prescribedHeadGoodCandidate_head b hNM hzero tail x D htrigger⟩

end BONG.GoodBONG

end Bong
