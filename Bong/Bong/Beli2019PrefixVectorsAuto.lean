/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrefixExtensionBaseAuto
import Bong.Bong.Beli2019PrefixVectors

/-!
# Beli (2019), automatic vector-prefix extension

These are the vector-prefix versions of the automatic base construction.
They remove the explicit Lemma 5.7 comparison data from both the one-vector
base case and the prepend step used in Corollary 5.10's induction.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n p : Nat}

/-- The automatic base candidate agrees with the prescribed BONG on its
first ambient vector. -/
theorem prescribedHeadGoodCandidateAuto_prefix_one
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hNM : N ≤ M) (hzero : a.order 0 = b.order 0)
    (initialTail : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head
        b.toBONG.head_isAnisotropic) (n + 1))
    (htrigger : BeliPrefixExtensionTrigger (ramificationIndex K : Int)
      a.orderSequence b.orderSequence 1) :
    BONG.AmbientPrefixAgreement
      (a.prescribedHeadGoodCandidateAuto b hNM hzero initialTail
        htrigger).toBONG b.toBONG 1 where
  leftBound := by omega
  rightBound := by omega
  ambient_eq j hj := by
    have hj0 : j = 0 := by omega
    subst j
    rw [BONG.ambientVector_mk_zero, BONG.ambientVector_mk_zero]
    exact a.prescribedHeadGoodCandidateAuto_head b hNM hzero initialTail
      htrigger

/-- Replacing the projected tail after the automatic base construction
extends a common tail prefix by the prescribed head. -/
theorem replaceTailGoodAuto_prefix_succ
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hNM : N ≤ M) (hzero : a.order 0 = b.order 0)
    (initialTail : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head
        b.toBONG.head_isAnisotropic) (n + 1))
    (htrigger : BeliPrefixExtensionTrigger (ramificationIndex K : Int)
      a.orderSequence b.orderSequence 1)
    (t : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head
        b.toBONG.head_isAnisotropic) (n + 1))
    (htail : BONG.AmbientPrefixAgreement t.toBONG b.tail.toBONG p) :
    BONG.AmbientPrefixAgreement
      ((a.prescribedHeadGoodCandidateAuto b hNM hzero initialTail
        htrigger).replaceTailGood t).toBONG b.toBONG (p + 1) := by
  let c := a.prescribedHeadGoodCandidateAuto b hNM hzero initialTail
    htrigger
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
      exact a.prescribedHeadGoodCandidateAuto_head b hNM hzero
        initialTail htrigger
  | succ j =>
      have hjp : j < p := by omega
      have hjn : j < n + 1 := hjp.trans_le htail.leftBound
      have hjs : j + 1 < n + 2 := by omega
      let jt : Fin (n + 1) := ⟨j, hjp.trans_le htail.leftBound⟩
      let jb : Fin (n + 1) := ⟨j, hjp.trans_le htail.rightBound⟩
      have htailEq : t.toBONG.ambientVector jt =
          b.tail.toBONG.ambientVector jb := htail.ambient_eq j hjp
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
