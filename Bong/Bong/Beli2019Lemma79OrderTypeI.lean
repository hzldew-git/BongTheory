/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderReduction

/-!
# Beli (2019), Lemma 7.9(i): the elementary type-I middle branch

On every odd zero-based coordinate strictly between the canonical type-I
switches, the source order is two above the index-`p` target order and the
following adjacent sums agree.  Both alternatives of the old order condition
therefore transport to the new pair.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}
  [Beli2006AlphaLaws.{u, v} K]

/-- The nonexceptional middle subcase in part 4 of the proof of condition
2.1(i) in Lemma 7.9. -/
theorem beli2019Lemma79_i_typeI_middleOdd
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (k : Nat) (hk : k < n + 2) (hkOdd : Odd k)
    (hleft : C.leftSwitch ≤ k) (hright : k < C.rightSwitch) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  have hacSequence :=
    (a.representationOrderCondition_iff c le_rfl).mp hac
  have hcurrentGap := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst k hkOdd hleft hright.le
  have hcurrent : b.orderSequence.entryOrZero k ≤
      a.orderSequence.entryOrZero k := by
    omega
  have hpairEq := lemma69_v_typeI_adjacent_entry_sum_eq
    a b D C hfirst k hleft hright
  have hpair : b.orderSequence.entryOrZero k +
      b.orderSequence.entryOrZero (k + 1) ≤
        a.orderSequence.entryOrZero k +
          a.orderSequence.entryOrZero (k + 1) := by
    exact le_of_eq hpairEq.symm
  exact BeliOrderLE.compare_of_source_bounds
    hacSequence k hk hcurrent hpair

end BONG.GoodBONG

end Bong
