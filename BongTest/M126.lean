/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019JordanApproximation

/-!
# M126 Beli 2019, Lemma 3.2 Jordan approximation smoke tests
-/

namespace BongTest.M126

open Bong

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (b : BONG.GoodBONG q L (n + 2))
    (C : b.JordanBlockCoordinates) (i : Nat)
    (hstart : C.start ≤ i) (hnext : i + 2 < C.stop) :
    b.order (C.index i (by omega)) =
      b.order (C.index (i + 2) hnext) :=
  C.order_add_two_eq i hstart hnext

example [Beli2006AlphaLaws.{u, v} K]
    (b : BONG.GoodBONG q L (n + 2))
    (C : b.JordanBlockCoordinates)
    (S : b.JordanApproximationSeeds C) (k : Nat)
    (hpos : C.start + 2 * k < C.stop) :
    b.IsPrefixApproximation (C.start + 2 * k)
      ((-1 : Kˣ) ^ k * S.leftDet) :=
  S.evenApproximation k hpos

example [Beli2006AlphaLaws.{u, v} K]
    (b : BONG.GoodBONG q L (n + 2))
    (C : b.JordanBlockCoordinates)
    (S : b.JordanApproximationSeeds C) (k : Nat)
    (hpos : C.start + 1 + 2 * k < C.stop) :
    b.IsPrefixApproximation (C.start + 1 + 2 * k)
      ((-1 : Kˣ) ^ k * (S.normGenerator * S.leftDet)) :=
  S.oddApproximation k hpos

#print axioms Bong.BONG.GoodBONG.JordanBlockCoordinates.order_add_two_eq
#print axioms Bong.BONG.GoodBONG.JordanApproximationSeeds.evenApproximation
#print axioms Bong.BONG.GoodBONG.JordanApproximationSeeds.oddApproximation

end BongTest.M126
