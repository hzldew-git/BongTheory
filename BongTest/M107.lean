/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006SectionThree

/-!
# M107 Beli 2006, Section 3 smoke tests
-/

namespace BongTest.M107

open Bong Bong.Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (b : BONG.GoodBONG q L (n + 1)) (i : Fin n) :
    b.orderGap i = b.order i.succ - b.order i.castSucc :=
  rfl

example (b : BONG.GoodBONG q L (n + 1)) (i : Fin n) :
    (b.halfGapValue i : WithTop ℚ) = b.halfGapCandidate i :=
  b.coe_halfGapValue i

variable [Beli2006AlphaLaws.{u, v} K]

example (b : BONG.GoodBONG q L (n + 1)) : b.SatisfiesAlphaP1 :=
  b.alpha_p1

example (b : BONG.GoodBONG q L (n + 1)) : b.SatisfiesAlphaP2 :=
  b.alpha_p2

example (b : BONG.GoodBONG q L (n + 1)) : b.SatisfiesAlphaP3 :=
  b.alpha_p3

example (b : BONG.GoodBONG q L (n + 1)) : b.SatisfiesAlphaP4 :=
  b.alpha_p4

example (b : BONG.GoodBONG q L (n + 1)) : b.SatisfiesAlphaP5 :=
  b.alpha_p5

example (b : BONG.GoodBONG q L (n + 1)) : b.SatisfiesAlphaP6 :=
  b.alpha_p6

example (b : BONG.GoodBONG q L (n + 1)) : b.SatisfiesAlphaP7 :=
  b.alpha_p7

variable [BONGStructuralLaws.{u, v} K]

example (b : BONG.GoodBONG q L (n + 1)) :
    ∃ c : BONG.GoodBONG q (Lattice.dualLattice q L) (n + 1),
      (∀ i, c.toBONG.ambientVector i = b.toBONG.reverseDualVector i) ∧
      (∀ i, c.value i = ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K)) ∧
      (∀ i, c.order i = -b.order (Fin.rev i)) ∧
      ∀ i, c.alphaValue i = b.alphaValue (Fin.rev i) :=
  b.exists_reverseDual_with_alpha

variable [GoodBONGClassificationLaws.{u, v, v} K]

example (a b : BONG.GoodBONG q L (n + 1)) :
    a.SameOrders b ∧ a.SameAlphas b :=
  a.order_alpha_invariant b

variable {W : Type w} [AddCommGroup W] [Module K W]
  {r : QuadraticSpace K W} {M : Lattice K W}
  [GoodBONGClassificationLaws.{u, v, w} K]

example (ambient : q.IsIsometric r)
    (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG r M (n + 1)) :
    Lattice.IsIsometric q r L M ↔ ClassificationConditions a b :=
  beli2006Theorem32 ambient a b

#print axioms Bong.BONG.GoodBONG.coe_halfGapValue
#print axioms Bong.BONG.GoodBONG.alpha_p3
#print axioms Bong.BONG.GoodBONG.exists_reverseDual_with_alpha
#print axioms Bong.BONG.GoodBONG.order_alpha_invariant
#print axioms Bong.beli2006Theorem32

end BongTest.M107
