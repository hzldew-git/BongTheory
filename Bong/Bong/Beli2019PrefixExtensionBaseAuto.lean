/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019ComparisonExistence
import Bong.Bong.Beli2019PrefixExtensionBase

/-!
# Beli (2019), unconditional construction for Corollary 5.10 at `i = 1`

The earlier base-step theorem accepted the comparison sequence from Lemma
5.7 as input.  The enlarged-lattice construction now supplies that sequence
automatically, so the prescribed-head candidate is good from exactly the four
triggers stated in Corollary 5.10.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- Corollary 5.10 at a one-vector prefix, with the Lemma 5.7 comparison
sequence constructed internally. -/
theorem prescribedHeadCandidateWithTail_isGood_of_trigger_one_auto
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hNM : N ≤ M) (hzero : a.order 0 = b.order 0)
    (tail : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head
        b.toBONG.head_isAnisotropic) (n + 1))
    (htrigger : BeliPrefixExtensionTrigger (ramificationIndex K : Int)
      a.orderSequence b.orderSequence 1) :
    (a.prescribedHeadCandidateWithTail b hNM hzero tail).IsGood := by
  rcases a.exists_normGeneratorComparisonData_prescribedHeadCandidateWithTail
    b hNM hzero tail with ⟨x, comparison⟩
  exact a.prescribedHeadCandidateWithTail_isGood_of_trigger_one b hNM
    hzero tail x comparison htrigger

/-- The automatically certified good BONG beginning with the prescribed
head. -/
noncomputable def prescribedHeadGoodCandidateAuto
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hNM : N ≤ M) (hzero : a.order 0 = b.order 0)
    (tail : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head
        b.toBONG.head_isAnisotropic) (n + 1))
    (htrigger : BeliPrefixExtensionTrigger (ramificationIndex K : Int)
      a.orderSequence b.orderSequence 1) :
    GoodBONG q M (n + 2) where
  toBONG := a.prescribedHeadCandidateWithTail b hNM hzero tail
  good := a.prescribedHeadCandidateWithTail_isGood_of_trigger_one_auto
    b hNM hzero tail htrigger

@[simp]
theorem prescribedHeadGoodCandidateAuto_head
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hNM : N ≤ M) (hzero : a.order 0 = b.order 0)
    (tail : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head
        b.toBONG.head_isAnisotropic) (n + 1))
    (htrigger : BeliPrefixExtensionTrigger (ramificationIndex K : Int)
      a.orderSequence b.orderSequence 1) :
    (a.prescribedHeadGoodCandidateAuto b hNM hzero tail htrigger).toBONG.head =
      b.toBONG.head :=
  rfl

/-- Existence form of the automatic one-vector prefix extension. -/
theorem exists_goodBONG_beginning_with_head_of_trigger_one_auto
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hNM : N ≤ M) (hzero : a.order 0 = b.order 0)
    (tail : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head
        b.toBONG.head_isAnisotropic) (n + 1))
    (htrigger : BeliPrefixExtensionTrigger (ramificationIndex K : Int)
      a.orderSequence b.orderSequence 1) :
    ∃ c : GoodBONG q M (n + 2), c.toBONG.head = b.toBONG.head := by
  exact ⟨a.prescribedHeadGoodCandidateAuto b hNM hzero tail htrigger,
    a.prescribedHeadGoodCandidateAuto_head b hNM hzero tail htrigger⟩

end BONG.GoodBONG

end Bong
