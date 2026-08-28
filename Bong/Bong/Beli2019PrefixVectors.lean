/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019GoodTailReplacement

/-!
# Beli (2019), vector prefixes in Corollary 5.10

The phrase "begins with" in Corollary 5.10 concerns the actual ambient BONG
vectors, not only their orders.  This file introduces that relation and proves
the successor step obtained by replacing a projected tail and prepending the
common prescribed head.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {m n p : Nat}

/-- Two BONGs in the same ambient quadratic space have the same first `p`
ambient vectors. -/
structure AmbientPrefixAgreement
    (a : BONG V q L m) (b : BONG V q M n) (p : Nat) : Prop where
  leftBound : p ≤ m
  rightBound : p ≤ n
  ambient_eq (j : Nat) (hj : j < p) :
    a.ambientVector ⟨j, hj.trans_le leftBound⟩ =
      b.ambientVector ⟨j, hj.trans_le rightBound⟩

/-- The zeroth ambient vector at an explicitly bounded natural-number index
is the recursive head. -/
theorem ambientVector_mk_zero (b : BONG V q L (n + 1))
    (hzero : 0 < n + 1) :
    b.ambientVector ⟨0, hzero⟩ = b.head := by
  have hindex : (⟨0, hzero⟩ : Fin (n + 1)) = 0 := by
    apply Fin.ext
    simp
  rw [hindex, ambientVector_zero_eq_head]

/-- The ambient lift of a tail vector at a natural-number index is the next
ambient vector of the full BONG. -/
theorem coe_ambientVector_tail_mk (b : BONG V q L (n + 1))
    (j : Nat) (hj : j < n) (hjs : j + 1 < n + 1) :
    (b.tail.ambientVector ⟨j, hj⟩ : V) =
      b.ambientVector ⟨j + 1, hjs⟩ := by
  have hindex : (⟨j, hj⟩ : Fin n).succ =
      (⟨j + 1, hjs⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp
  rw [← hindex]
  exact b.coe_ambientVector_tail ⟨j, hj⟩

end BONG

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n p : Nat}

/-- The canonical base-step candidate has the prescribed first ambient
vector. -/
theorem prescribedHeadGoodCandidate_prefix_one
    [BeliLemma47Laws.{u, v} K]
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hNM : N ≤ M) (hzero : a.order 0 = b.order 0)
    (initialTail : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head b.toBONG.head_isAnisotropic)
      (n + 1))
    (x : BeliOrderSequence (n + 2) Int)
    (D : NormGeneratorComparisonData a
      (a.prescribedHeadCandidateWithTail b hNM hzero initialTail) x)
    (htrigger : BeliPrefixExtensionTrigger (ramificationIndex K : Int)
      a.orderSequence b.orderSequence 1) :
    BONG.AmbientPrefixAgreement
      (a.prescribedHeadGoodCandidate b hNM hzero initialTail x D htrigger).toBONG
      b.toBONG 1 where
  leftBound := by omega
  rightBound := by omega
  ambient_eq j hj := by
    have hj0 : j = 0 := by omega
    subst j
    rw [BONG.ambientVector_mk_zero, BONG.ambientVector_mk_zero]
    exact a.prescribedHeadGoodCandidate_head b hNM hzero initialTail x D htrigger

/-- A common prefix of projected tails becomes a one-vector-longer common
prefix after the prescribed head is prepended. -/
theorem replaceTailGood_prefix_succ
    [BeliLemma47Laws.{u, v} K]
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hNM : N ≤ M) (hzero : a.order 0 = b.order 0)
    (initialTail : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head b.toBONG.head_isAnisotropic)
      (n + 1))
    (x : BeliOrderSequence (n + 2) Int)
    (D : NormGeneratorComparisonData a
      (a.prescribedHeadCandidateWithTail b hNM hzero initialTail) x)
    (htrigger : BeliPrefixExtensionTrigger (ramificationIndex K : Int)
      a.orderSequence b.orderSequence 1)
    (t : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head b.toBONG.head_isAnisotropic)
      (n + 1))
    (htail : BONG.AmbientPrefixAgreement t.toBONG b.tail.toBONG p) :
    BONG.AmbientPrefixAgreement
      ((a.prescribedHeadGoodCandidate b hNM hzero initialTail x D
        htrigger).replaceTailGood t).toBONG b.toBONG (p + 1) := by
  let c := a.prescribedHeadGoodCandidate b hNM hzero initialTail x D htrigger
  let d := c.replaceTailGood t
  change BONG.AmbientPrefixAgreement d.toBONG b.toBONG (p + 1)
  refine
    { leftBound := by
        have := htail.leftBound
        omega
      rightBound := by
        have := htail.rightBound
        omega
      ambient_eq := ?_ }
  intro j hj
  cases j with
  | zero =>
      rw [BONG.ambientVector_mk_zero, BONG.ambientVector_mk_zero]
      change c.toBONG.head = b.toBONG.head
      exact a.prescribedHeadGoodCandidate_head b hNM hzero initialTail x D htrigger
  | succ j =>
      have hjp : j < p := by omega
      have hjn : j < n + 1 := hjp.trans_le htail.leftBound
      have hjs : j + 1 < n + 2 := by omega
      let jt : Fin (n + 1) := ⟨j, hjp.trans_le htail.leftBound⟩
      let jb : Fin (n + 1) := ⟨j, hjp.trans_le htail.rightBound⟩
      have htailEq : t.toBONG.ambientVector jt = b.tail.toBONG.ambientVector jb :=
        htail.ambient_eq j hjp
      calc
        d.toBONG.ambientVector ⟨j + 1, hjs⟩ =
            (d.toBONG.tail.ambientVector jt : V) := by
          symm
          exact d.toBONG.coe_ambientVector_tail_mk j hjn hjs
        _ = (t.toBONG.ambientVector jt : V) := by
          rfl
        _ = (b.tail.toBONG.ambientVector jb : V) :=
          congrArg Subtype.val htailEq
        _ = b.toBONG.ambientVector ⟨j + 1, hjs⟩ :=
          b.toBONG.coe_ambientVector_tail_mk j hjn hjs

end BONG.GoodBONG

end Bong
