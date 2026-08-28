/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrefixVectorsAuto
import Bong.Bong.GoodExistence
import Bong.Bong.BeliLemmas45To47

/-!
# Beli (2019), Corollary 5.10

This file performs the induction on the prescribed prefix length.  After the
automatic one-vector construction, the order hypothesis descends to the two
projected tails; the recursively constructed tail is then prepended to the
fixed head.  The output agrees with the prescribed BONG on actual ambient
vectors, not merely on their orders.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n p : Nat}

/-- A positive order-prefix agreement gives equality of the first BONG
orders. -/
theorem order_zero_eq_of_prefixAgreement
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (h : a.orderSequence.PrefixAgreement b.orderSequence p)
    (hp : 0 < p) : a.order 0 = b.order 0 := by
  have heq := h.entry_eq 0 hp
  rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega),
    BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega)] at heq
  change a.order 0 = b.order 0 at heq
  exact heq

/-- Good BONGs of one lattice have the same complete order sequence. -/
theorem orderSequence_eq_of_same_lattice
    [BeliLemma47Laws.{u, v} K]
    (a b : GoodBONG q M (n + 1)) :
    a.orderSequence = b.orderSequence := by
  apply BeliOrderSequence.ext
  funext i
  change a.order i = b.order i
  exact a.toBONG.beliLemma47_orders_eq b.toBONG a.good b.good i

/-- Beli (2019), Corollary 5.10: under its order-prefix hypothesis, a good
BONG of the larger lattice can be chosen to begin with the prescribed ambient
vectors of the smaller lattice. -/
theorem exists_goodBONG_with_ambientPrefix
    [BONGStructuralLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (hNM : N ≤ M)
    (h : BeliPrefixExtensionHypothesis (ramificationIndex K : Int)
      a.orderSequence b.orderSequence p) :
    ∃ c : GoodBONG q M (n + 1),
      BONG.AmbientPrefixAgreement c.toBONG b.toBONG p := by
  induction n generalizing V p with
  | zero =>
      cases p with
      | zero =>
          refine ⟨a, ?_⟩
          exact
            { leftBound := by omega
              rightBound := by omega
              ambient_eq := by
                intro j hj
                omega }
      | succ p =>
          have hpzero : p = 0 := by
            have := h.agreement.leftBound
            omega
          subst p
          have hzero := a.order_zero_eq_of_prefixAgreement b
            h.agreement (by omega)
          let cB := a.prescribedHeadCandidate b hNM hzero
          let c : GoodBONG q M 1 :=
            { toBONG := cB
              good := cB.isGood_of_length_le_two (by omega) }
          refine ⟨c, ?_⟩
          refine
            { leftBound := by omega
              rightBound := by omega
              ambient_eq := ?_ }
          intro j hj
          have hjzero : j = 0 := by omega
          subst j
          rw [BONG.ambientVector_mk_zero, BONG.ambientVector_mk_zero]
          exact a.prescribedHeadCandidate_head b hNM hzero
  | succ n ih =>
      letI : Module.Finite K V := M.moduleFinite
      cases p with
      | zero =>
          refine ⟨a, ?_⟩
          exact
            { leftBound := by omega
              rightBound := by omega
              ambient_eq := by
                intro j hj
                omega }
      | succ p =>
          have hzero := a.order_zero_eq_of_prefixAgreement b
            h.agreement (by omega)
          have hfin : Module.finrank K
              (q.vectorOrthogonal b.toBONG.head) = n + 1 := by
            have hdim := q.finrank_vectorOrthogonal
              b.toBONG.head_isAnisotropic
            have hlength := a.toBONG.length_eq_finrank
            omega
          let initialTail :=
            (GoodBONG.ofLattice
              (q.orthogonalSpace b.toBONG.head
                b.toBONG.head_isAnisotropic)
              (M.projectedLattice q b.toBONG.head
                b.toBONG.head_isAnisotropic)).castLength hfin
          cases p with
          | zero =>
              let c := a.prescribedHeadGoodCandidateAuto b hNM hzero
                initialTail h.trigger
              refine ⟨c, ?_⟩
              exact a.prescribedHeadGoodCandidateAuto_prefix_one b hNM
                hzero initialTail h.trigger
          | succ p =>
              have baseTrigger :
                  BeliPrefixExtensionTrigger
                    (ramificationIndex K : Int) a.orderSequence
                    b.orderSequence 1 :=
                BeliPrefixExtensionTrigger.nextOrder (by omega) (by omega)
                  (h.agreement.entry_eq 1 (by omega))
              let c := a.prescribedHeadGoodCandidateAuto b hNM hzero
                initialTail baseTrigger
              have hcOrder : c.orderSequence = a.orderSequence :=
                c.orderSequence_eq_of_same_lattice a
              have hInitialOrder : initialTail.orderSequence =
                  a.orderSequence.tail := by
                apply BeliOrderSequence.ext
                funext i
                change initialTail.order i = a.order i.succ
                calc
                  initialTail.order i = c.order i.succ := by rfl
                  _ = a.order i.succ := by
                    change c.orderSequence.value i.succ =
                      a.orderSequence.value i.succ
                    rw [hcOrder]
              have hbTailOrder : b.tail.orderSequence =
                  b.orderSequence.tail := b.orderSequence_tail.symm
              have htail := h.tail (p := p + 1) (by omega)
              rw [← hInitialOrder, ← hbTailOrder] at htail
              have hprojected :
                  N.projectedLattice q b.toBONG.head
                      b.toBONG.head_isAnisotropic ≤
                    M.projectedLattice q b.toBONG.head
                      b.toBONG.head_isAnisotropic :=
                Lattice.projectedLattice_mono q hNM b.toBONG.head
                  b.toBONG.head_isAnisotropic
              rcases ih (V := q.vectorOrthogonal b.toBONG.head)
                (q := q.orthogonalSpace b.toBONG.head
                  b.toBONG.head_isAnisotropic)
                (M := M.projectedLattice q b.toBONG.head
                  b.toBONG.head_isAnisotropic)
                (N := N.projectedLattice q b.toBONG.head
                  b.toBONG.head_isAnisotropic)
                (p := p + 1) initialTail b.tail hprojected htail with
                ⟨tailWitness, htailWitness⟩
              refine ⟨c.replaceTailGood tailWitness, ?_⟩
              exact a.replaceTailGoodAuto_prefix_succ b hNM hzero
                initialTail baseTrigger tailWitness htailWitness

end BONG.GoodBONG

end Bong
