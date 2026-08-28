/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderSequence
import Bong.Bong.Representation

/-!
# Beli (2019), order sequences of nested lattices

The proof of Lemma 5.7 uses the necessity of condition 2.1(i) for an inclusion
`N ≤ M` and deduces `r(M) ≤ r(N)`.  This file constructs the identity
representation associated with a lattice inclusion and isolates that strictly
smaller local input, without assuming the full representation theorem.
-/

namespace Bong

namespace Lattice.Representation

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- A sublattice inclusion is an integral representation whose ambient map is
the identity. -/
def ofLe (q : QuadraticSpace K V) {L M : Lattice K V} (hLM : L ≤ M) :
    Lattice.Representation q q L M where
  toLinearMap := LinearMap.id
  injective := Function.injective_id
  map_bilin _ _ := rfl
  map_mem hx := hLM hx

end Lattice.Representation

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Every lattice represents each of its sublattices by inclusion. -/
theorem represents_of_le (q : QuadraticSpace K V) {L M : Lattice K V}
    (hLM : L ≤ M) : Lattice.Represents q q M L :=
  ⟨Lattice.Representation.ofLe q hLM⟩

end Lattice

/-- The order-theoretic necessity input used in Section 5.  Unlike
`GoodBONGRepresentationLaws`, this interface contains only condition 2.1(i)
for a literal inclusion of equal-rank lattices. -/
class Beli2019OrderNecessityLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  nestedOrder
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}
    (a : BONG.GoodBONG q M (n + 1))
    (b : BONG.GoodBONG q L (n + 1))
    (hLM : L ≤ M) : BeliOrderLE a.orderSequence b.orderSequence

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Theorem 2.1(i) for two nested lattices in the same quadratic space:
the good-BONG order sequence of the larger lattice is below that of the
smaller lattice. -/
theorem orderSequence_le_of_lattice_le
    [Beli2019OrderNecessityLaws.{u, v} K]
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q L (n + 1))
    (hLM : L ≤ M) : BeliOrderLE a.orderSequence b.orderSequence :=
  Beli2019OrderNecessityLaws.nestedOrder a b hLM

end BONG.GoodBONG

end Bong
