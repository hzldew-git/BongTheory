/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrescribedHead

/-!
# Beli (2019), comparison data for a prescribed good tail

Lemma 5.7 chooses a good BONG of the projected lattice before adjoining the
prescribed norm-generator head.  For that candidate, tail goodness and the
identification of tail orders are automatic.  This file packages the remaining
three conclusions of the enlarged-lattice argument into
`NormGeneratorComparisonData`.
-/

namespace Bong

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- Build the comparison interface for the prescribed-head candidate with a
chosen good projected tail.  Only the order relation, the suffix-volume
identity, and the artificial sequence's tail entries remain to be supplied. -/
theorem normGeneratorComparisonData_prescribedHeadCandidateWithTail
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hNM : N ≤ M) (hzero : a.order 0 = b.order 0)
    (tail : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head b.toBONG.head_isAnisotropic)
      (n + 1))
    (x : BeliOrderSequence (n + 2) Int)
    (horder : BeliOrderLE x a.orderSequence)
    (hsum : x.suffixSum 1 = a.orderSequence.suffixSum 1)
    (htailOrder : ∀ i : Fin (n + 1),
      x.entryOrZero (i.val + 1) = tail.order i) :
    NormGeneratorComparisonData a
      (a.prescribedHeadCandidateWithTail b hNM hzero tail) x where
  order_le := horder
  tail_sum := hsum
  tail_good := by
    rw [a.prescribedHeadCandidateWithTail_tail b hNM hzero tail]
    exact tail.good
  tail_order i := by
    calc
      x.entryOrZero (i.val + 1) = tail.order i := htailOrder i
      _ = (a.prescribedHeadCandidateWithTail b hNM hzero tail).order i.succ := by
        rw [← (a.prescribedHeadCandidateWithTail b hNM hzero tail).order_tail i,
          a.prescribedHeadCandidateWithTail_tail b hNM hzero tail]
        rfl

end BONG.GoodBONG

end Bong
