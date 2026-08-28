/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliTheoremTwo

/-!
# M102 Beli 2003, Theorem 2 smoke tests
-/

namespace BongTest.M102

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t n : Nat}
  [BeliTheoremTwoLaws.{u, v} K]

example (S : Lattice.HyperbolicTowerSplitting q L t n) :
    Lattice.SpinorNormIsUnitBounded q L ↔
      S.SatisfiesTheoremTwoConditions :=
  Lattice.beliTheoremTwo S

example (S : Lattice.HyperbolicTowerSplitting q L t n)
    (hconditions : S.SatisfiesTheoremTwoConditions) (ht : 0 < t) :
    Lattice.spinorNormImageSubgroup (q := q) (L := L) =
      valuationUnitSquareClassSubgroup K :=
  Lattice.beliTheoremTwo_eq_unit S hconditions ht

example (S : Lattice.HyperbolicTowerSplitting q L t n) :
    ¬Lattice.SpinorNormIsUnitBounded q L ↔
      ¬S.SatisfiesTheoremTwoConditions :=
  Lattice.not_spinorNormIsUnitBounded_iff_not_theoremTwoConditions S

#print axioms Bong.Lattice.beliTheoremTwo
#print axioms Bong.Lattice.beliTheoremTwo_eq_unit
#print axioms Bong.Lattice.not_spinorNormIsUnitBounded_iff_not_theoremTwoConditions

end BongTest.M102
