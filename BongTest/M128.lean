/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SpaceApproximation

/-!
# M128 Beli 2019, Lemma 3.8 space approximation smoke tests
-/

namespace BongTest.M128

open Bong

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example [GoodBONGClassificationLaws.{u, v, v} K]
    (a a' : BONG.GoodBONG q L (n + 1)) (i : Fin n) :
    a.leftApproximationTrigger i ↔ a'.leftApproximationTrigger i :=
  a.leftApproximationTrigger_changeBONG_iff a' i

example [GoodBONGClassificationLaws.{u, v, v} K]
    (a a' : BONG.GoodBONG q L (n + 1)) (i : Fin n) :
    a.rightApproximationTrigger i ↔ a'.rightApproximationTrigger i :=
  a.rightApproximationTrigger_changeBONG_iff a' i

example [GoodBONGClassificationLaws.{u, v, v} K]
    (a a' : BONG.GoodBONG q L (n + 1)) (i : Fin n)
    (c : Fin (i.1 + 1) → Kˣ)
    (D : BONG.GoodBONG.SpaceApproximationRepresentationBridge a a' i c) :
    a.IsSpaceApproximation i c ↔ a'.IsSpaceApproximation i c :=
  D.isSpaceApproximation_iff

#print axioms Bong.BONG.GoodBONG.leftApproximationTrigger_changeBONG_iff
#print axioms Bong.BONG.GoodBONG.rightApproximationTrigger_changeBONG_iff
#print axioms Bong.BONG.GoodBONG.SpaceApproximationRepresentationBridge.isLeftSpaceApproximation_iff
#print axioms
  Bong.BONG.GoodBONG.SpaceApproximationRepresentationBridge.isRightSpaceApproximation_iff
#print axioms Bong.BONG.GoodBONG.SpaceApproximationRepresentationBridge.isSpaceApproximation_iff

end BongTest.M128
