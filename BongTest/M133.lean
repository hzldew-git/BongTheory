/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019RepresentationTransitivity

/-!
# M133 Beli 2019, Section 4 representation transitivity smoke tests
-/

namespace BongTest.M133

open Bong Bong.Dyadic

universe u v w z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U}
  {n : Nat}

example {l m k : Nat} {x : Fin l → K} {y : Fin m → K}
    {z : Fin k → K} (hxy : DiagonalRepresents x y)
    (hyz : DiagonalRepresents y z) : DiagonalRepresents x z :=
  hxy.trans hyz

example (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (c : BONG.GoodBONG s N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (data : BONG.GoodBONG.SectionFourTransitivityData a b c) :
    RepresentationConditions a c le_rfl :=
  a.representationConditions_trans_sameRank b c hab hbc data

#print axioms Bong.DiagonalRepresents.trans
#print axioms Bong.BONG.GoodBONG.CentralRepresentationCertificate.represents
#print axioms Bong.BONG.GoodBONG.LongRepresentationCertificate.represents
#print axioms Bong.BONG.GoodBONG.representationConditions_trans_sameRank

end BongTest.M133
