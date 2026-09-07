/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCSectionThree

/-!
# The literal published representation conditions in He (2025), Theorem 3.6

The publisher uses the sum-of-two-capped-defects trigger in condition (iii).
The older `heADC2025Theorem36` exports an equivalent four-condition package
with an auxiliary-alpha trigger. Both packages are proved equivalent under
conditions (i) and (ii); individual pointwise failures must use the appropriate
literal trigger. In particular, Lemma 6.6 uses the endpoint below.
-/

namespace Bong.BONG.GoodBONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- He (2025), Theorem 3.6, with the publisher's literal capped-defect
trigger in condition (iii), including the exceptional terminal indices. -/
theorem heADC2025Theorem36Published {m n : Nat}
    (hRank : n ≤ m) (ambient : q.Represents r)
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1)) :
    Lattice.Represents q r L M ↔ RepresentationConditionsPrime a b hRank :=
  beli2019Theorem21_prime hRank ambient a b

/-- The published Theorem 3.6 with ambient representability retained
inside the right-hand conjunction, as printed in the paper. -/
theorem heADC2025Theorem36PublishedFull {m n : Nat}
    (hRank : n ≤ m) (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1)) :
    Lattice.Represents q r L M ↔ q.Represents r ∧ RepresentationConditionsPrime a b hRank := by
  constructor
  · intro hrep
    exact ⟨hrep.ambient, (heADC2025Theorem36Published hRank hrep.ambient a b).mp hrep⟩
  · rintro ⟨hspace, hconditions⟩
    exact (heADC2025Theorem36Published hRank hspace a b).mpr hconditions

end Bong.BONG.GoodBONG
