/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006AlphaP7Proof
import Bong.Bong.BeliLemmas48To410

/-!
# Reverse-dual transport of Beli's alpha invariant

This is the constructive P7 consequence used both in Beli (2006), Section 3,
and in the later 2009 compression argument.  It is kept below both theorem
modules so neither paper has to import the other merely to use reverse
duality.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

variable [BONGStructuralLaws.{u, v} K]

/- Property P7 together with an actual reverse-dual good BONG and the
corresponding vector, value, and order formulas. -/
theorem exists_reverseDual_with_alpha (b : GoodBONG q L (n + 1)) :
    ∃ c : GoodBONG q (Lattice.dualLattice q L) (n + 1),
      (∀ i, c.toBONG.ambientVector i = b.toBONG.reverseDualVector i) ∧
      (∀ i, c.value i = ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K)) ∧
      (∀ i, c.order i = -b.order (Fin.rev i)) ∧
      ∀ i, c.alphaValue i = b.alphaValue (Fin.rev i) := by
  rcases b.exists_reverseDual_with_values with ⟨c, hvectors, hvalues, horders⟩
  exact ⟨c, hvectors, hvalues, horders,
    b.satisfiesAlphaP7_proved c hvectors⟩

end BONG.GoodBONG

end Bong
