/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006AlphaP1Proof
import Bong.Bong.Beli2006AlphaP4P6Proof
import Bong.Bong.Beli2006AlphaP7Proof
import Bong.Bong.Beli2006AlphaLaws
import Bong.Bong.Beli2006ReverseDualAlpha
import Bong.Bong.Beli2006SectionTwo
import Bong.Bong.BeliLemmas48To410
import Bong.Bong.Classification
import Bong.Bong.Beli2009JordanAlphaTransport

/-!
# Beli (2006), Section 3

This file states the seven properties of the invariants `α_i`, proves that
the order and alpha sequences are independent of the chosen good BONG, and
records Theorem 3.2 in its exact good-BONG form.

Properties P1 and P4--P7 are proved from the finite candidate definition,
the two-step order condition, and reverse-dual candidate transport.  The
remaining calculations P2, P3 and O'Meara's Theorem 93:28 are exposed
through explicit classes without default instances.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

/-- The sequences `R_i` and `α_i` do not depend on the chosen good BONG of a
fixed lattice. -/
theorem order_alpha_invariant (a b : GoodBONG q L (n + 1)) :
    a.SameOrders b ∧ a.SameAlphas b := by
  let f : Lattice.Isometry q q L L := Lattice.Isometry.refl q L
  exact ⟨a.sameOrders_of_latticeIsometry b f,
    a.sameAlphas_of_latticeIsometry b f⟩

theorem order_invariant (a b : GoodBONG q L (n + 1)) : a.SameOrders b :=
  (a.order_alpha_invariant b).1

theorem alpha_invariant (a b : GoodBONG q L (n + 1)) : a.SameAlphas b :=
  (a.order_alpha_invariant b).2

end BONG.GoodBONG

variable {W : Type w} [AddCommGroup W] [Module K W]
  {r : QuadraticSpace K W} {M : Lattice K W}
  [GoodBONGClassificationLaws.{u, v, w} K]

/-- Beli (2006), Theorem 3.2: O'Meara's classification theorem translated
into the four explicit good-BONG conditions. -/
theorem beli2006Theorem32
    (ambient : q.IsIsometric r)
    (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG r M (n + 1)) :
    Lattice.IsIsometric q r L M ↔ ClassificationConditions a b :=
  isometric_iff_classificationConditions ambient a b

end Bong
