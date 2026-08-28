/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019RepresentationTransitivity
import Bong.Bong.Beli2019OrderSequence

/-!
# Beli (2019), Section 4(iv): order consequences

The two order implications referred to as "see 2.2" in Section 4(iv) are
instances of Lemma 1.8(ii) for the two good-BONG order sequences.  They are
recorded here with the exact indices used by the two outer branches of the
proof.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M : Lattice K V} {n : Nat}

/-- If the middle order at `i - 1` lies more than `2e` above the source
order at `i - 2`, condition (i) forces the preceding middle order below
the corresponding source order. -/
theorem previous_order_le_of_middle_source_crossGap
    (b : GoodBONG q L (n + 1)) (c : GoodBONG q M (n + 1))
    (horder : b.RepresentationOrderCondition c le_rfl)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (hstrict :
      c.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ + 2 * (ramificationIndex K : Int) <
        b.order ⟨i.val - 1, by
          have := i.succ_lt_large
          omega⟩) :
    b.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ ≤
      c.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ := by
  let O := (b.representationOrderCondition_iff c le_rfl).mp horder
  have hgap : 2 * (ramificationIndex K : Int) ≤
      b.order ⟨i.val - 1, by
        have := i.succ_lt_large
        omega⟩ -
        c.order ⟨i.val - 2, by
          have := i.succ_lt_large
          omega⟩ := by
    omega
  have hpair := BeliOrderSequence.le_pair_of_large_crossGap O
    b.orderSequence_isKappaBounded_two_mul_e
    c.orderSequence_isKappaBounded_two_mul_e
    (i.val - 2) (by
      have := i.succ_lt_large
      omega) (by
      have := i.succ_lt_large
      omega) (by
      simpa only [orderSequence_at, show i.val - 2 + 1 = i.val - 1 by
        have := i.one_lt
        omega] using hgap)
  simpa only [orderSequence_at] using hpair.1

/-- If the target order at `i + 1` lies more than `2e` above the middle
order at `i`, condition (i) forces the next target order below the next
middle order. -/
theorem next_order_le_of_target_middle_crossGap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (hstrict :
      b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩ + 2 * (ramificationIndex K : Int) <
        a.order ⟨i.val + 1, i.succ_lt_large⟩) :
    a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
      b.order ⟨i.val + 1, i.succ_lt_large⟩ := by
  let O := (a.representationOrderCondition_iff b le_rfl).mp horder
  have hgap : 2 * (ramificationIndex K : Int) ≤
      a.order ⟨i.val + 1, i.succ_lt_large⟩ -
        b.order ⟨i.val, by
          have := i.succ_lt_large
          omega⟩ := by
    omega
  have hpair := BeliOrderSequence.le_pair_of_large_crossGap O
    a.orderSequence_isKappaBounded_two_mul_e
    b.orderSequence_isKappaBounded_two_mul_e
    i.val (by
      have := i.succ_lt_large
      omega) i.succ_lt_large (by
      simpa only [orderSequence_at] using hgap)
  simpa only [orderSequence_at] using hpair.2 i.succ_lt_large

end BONG.GoodBONG

end Bong
