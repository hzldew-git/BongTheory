/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma66

/-!
# Beli (2003), Lemma 6.7

Failure of property B, in the presence of property A, produces an adjacent
pair whose exceptional trigger has a neighboring gap smaller than `2e + 1`.
The paper's local norm-group calculation then says that the corresponding
adjacent factor together with the principal-unit factor is the full square-
class group.  The logical extraction of the violating pair and its passage to
the global right-hand side of Theorem 1 are proved here unconditionally.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- A concrete neighboring-gap violation of property B. -/
structure Lemma67Violation (b : BONG V q L (n + 3)) where
  /-- The exceptional adjacent pair. -/
  index : Fin (n + 2)
  /-- The pair satisfies one of the two triggers in Definition 10. -/
  trigger : b.propertyBTrigger index
  /-- At least one existing neighboring gap is strictly smaller than
  `2e + 1`. -/
  neighborFailure :
    (∃ j : Fin (n + 3), j.1 + 1 = index.1 ∧
      b.order index.castSucc - b.order j <
        2 * (ramificationIndex K : Int) + 1) ∨
    (∃ k : Fin (n + 3), index.1 + 2 = k.1 ∧
      b.order k - b.order index.succ <
        2 * (ramificationIndex K : Int) + 1)

/-- Property A together with failure of property B yields a concrete
Definition 10 violation. -/
theorem exists_lemma67Violation (b : BONG V q L (n + 3))
    (hA : b.HasPropertyA) (hnotB : ¬b.HasPropertyB) :
    Nonempty b.Lemma67Violation := by
  classical
  by_contra hnone
  apply hnotB
  refine ⟨hA, ?_⟩
  intro i hi
  constructor
  · intro j hj
    by_contra hgap
    apply hnone
    refine ⟨{
      index := i
      trigger := hi
      neighborFailure := Or.inl ⟨j, hj, ?_⟩
    }⟩
    exact lt_of_not_ge hgap
  · intro k hk
    by_contra hgap
    apply hnone
    refine ⟨{
      index := i
      trigger := hi
      neighborFailure := Or.inr ⟨k, hk, ?_⟩
    }⟩
    exact lt_of_not_ge hgap

/-- The local factor displayed in Lemma 6.7 for the adjacent pair `i`. -/
noncomputable def lemma67LocalFactor (b : BONG V q L (n + 3))
    (i : Fin (n + 2)) : Subgroup (SquareClass K) :=
  beliSpinorGroup K
      (b.adjacentUnitSquareClass i.castSucc (by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
          Nat.succ_lt_succ i.isLt)) ⊔
    b.theoremOneCongruenceFactor

/-- Every Lemma 6.7 local factor is contained in the global right-hand side
of Theorem 1. -/
theorem lemma67LocalFactor_le_theoremOneRHS
    (b : BONG V q L (n + 3)) (i : Fin (n + 2)) :
    b.lemma67LocalFactor i ≤ b.theoremOneRHS := by
  unfold lemma67LocalFactor theoremOneRHS theoremOneAdjacentFactor
  exact sup_le_sup (le_iSup (fun j : Fin (n + 2) =>
    beliSpinorGroup K
      (b.adjacentUnitSquareClass j.castSucc (by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
          Nat.succ_lt_succ j.isLt))) i) le_rfl

/-- The remaining local norm-group calculation in Beli (2003), Lemma 6.7.
This interface has no default instance. -/
class BeliLemma67Laws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  local_factor_eq_top_of_violation
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 3)) (hA : b.HasPropertyA)
    (w : b.Lemma67Violation) :
    b.lemma67LocalFactor w.index = ⊤

variable [BeliLemma67Laws.{u, v} K]

/-- Beli (2003), Lemma 6.7: one of the displayed local factors is the full
square-class group when property B fails. -/
theorem beliLemma67 (b : BONG V q L (n + 3))
    (hA : b.HasPropertyA) (hnotB : ¬b.HasPropertyB) :
    ∃ i : Fin (n + 2), b.lemma67LocalFactor i = ⊤ := by
  rcases b.exists_lemma67Violation hA hnotB with ⟨w⟩
  exact ⟨w.index,
    BeliLemma67Laws.local_factor_eq_top_of_violation b hA w⟩

/-- Lemma 6.7 makes the entire right-hand side of Theorem 1 full. -/
theorem theoremOneRHS_eq_top_of_not_propertyB
    (b : BONG V q L (n + 3))
    (hA : b.HasPropertyA) (hnotB : ¬b.HasPropertyB) :
    b.theoremOneRHS = ⊤ := by
  rcases b.beliLemma67 hA hnotB with ⟨i, hi⟩
  apply top_unique
  rw [← hi]
  exact b.lemma67LocalFactor_le_theoremOneRHS i

end BONG

end Bong
