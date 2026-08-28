/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderLeftBoundary

/-!
# Beli (2019), Lemma 7.9(i): the type-II constant middle

Strictly inside the long type-II transition, two consecutive source and
target orders agree.  The old comparison with the third lattice can therefore
be reused without any defect calculation.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The range `t < i ≤ t' - 2` in part 5 of the proof of Lemma 7.9(i),
written in zero-based coordinates. -/
theorem beli2019Lemma79_i_typeII_constantMiddle
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (k : Nat) (hleft : D.outer.transition.lastZero < k)
    (hright : k + 2 < D.outer.transition.firstTwo) :
    b.orderSequence.entry k (by
        have hbound := D.outer.transition.firstTwo_le_rank
        omega) ≤
      c.orderSequence.entry k (by
        have hbound := D.outer.transition.firstTwo_le_rank
        omega) ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k (by
              have hbound := D.outer.transition.firstTwo_le_rank
              omega) +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k (by
              have hbound := D.outer.transition.firstTwo_le_rank
              omega) := by
  have hbound := D.outer.transition.firstTwo_le_rank
  have hk : k < n + 2 := by omega
  have hcurrentEq := D.outer.transition.middle k hleft (by omega)
  have hnextEq := D.outer.transition.middle (k + 1) (by omega) (by omega)
  have hcurrent : b.orderSequence.entryOrZero k ≤
      a.orderSequence.entryOrZero k := le_of_eq hcurrentEq.symm
  have hpair : b.orderSequence.entryOrZero k +
      b.orderSequence.entryOrZero (k + 1) ≤
        a.orderSequence.entryOrZero k +
          a.orderSequence.entryOrZero (k + 1) := by
    rw [← hcurrentEq, ← hnextEq]
  have hacSequence :=
    (a.representationOrderCondition_iff c le_rfl).mp hac
  exact BeliOrderLE.compare_of_source_bounds
    hacSequence k hk hcurrent hpair

end BONG.GoodBONG

end Bong
