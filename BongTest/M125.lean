/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Approximation

/-!
# M125 Beli 2019, Section 3 approximation smoke tests
-/

namespace BongTest.M125

open Bong

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

example (b : BONG.GoodBONG q L (n + 1)) (i : Nat) :
    b.IsPrefixApproximation i (b.prefixProduct i) :=
  b.isPrefixApproximation_prefixProduct i

example [GoodBONGClassificationLaws.{u, v, v} K]
    (a a' : BONG.GoodBONG q L (n + 1)) (i : Nat) (X : Kˣ) :
    a.IsPrefixApproximation i X ↔ a'.IsPrefixApproximation i X :=
  a.isPrefixApproximation_changeBONG_iff a' i X

example (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1)) (epsilon : Kˣ)
    (i j : Nat) (X Y : Kˣ) (hX : a.IsPrefixApproximation i X)
    (hY : b.IsPrefixApproximation j Y) :
    a.truncatedPrefixDefect b epsilon i j =
      a.truncatedApproximationDefect b epsilon i j X Y :=
  a.truncatedPrefixDefect_eq_of_approximations b epsilon i j X Y hX hY

example [Beli2006AlphaLaws.{u, v} K]
    (b : BONG.GoodBONG q L (n + 2)) (i : Nat) (X : Kˣ)
    (hi0 : 0 < i) (hi : i + 2 < n + 2)
    (houter : b.order ⟨i, by omega⟩ = b.order ⟨i + 2, hi⟩)
    (hX : b.IsPrefixApproximation i X) :
    b.IsPrefixApproximation (i + 2) (-X) :=
  b.isPrefixApproximation_neg_add_two_of_outerOrders_eq i X hi0 hi
    houter hX

#print axioms Bong.BONG.GoodBONG.isPrefixApproximation_changeBONG_iff
#print axioms Bong.BONG.GoodBONG.truncatedPrefixDefect_eq_of_approximations
#print axioms Bong.BONG.GoodBONG.isPrefixApproximation_neg_add_two
#print axioms Bong.BONG.GoodBONG.isPrefixApproximation_neg_add_two_of_outerOrders_eq
#print axioms Bong.BONG.GoodBONG.isSpaceApproximation_of_vacuous

end BongTest.M125
