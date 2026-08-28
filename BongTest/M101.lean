/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma71Proof

/-!
# M101 Beli 2003, Lemma 7.1 smoke tests
-/

namespace BongTest.M101

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

example (a : Kˣ) :
    squareClass K a ∈ valuationUnitSquareClassSubgroup K ↔
      Even (ordUnit K a) :=
  squareClass_mem_valuationUnitSquareClassSubgroup_iff_even a

example (D : Lattice.OrthogonalDecomposition q L t)
    (N : Lattice.OrthogonalComponentNormData D)
    (hunit : Lattice.SpinorNormIsUnitBounded q L)
    (i j : Fin t) :
    Int.ModEq 2 (N i).order (N j).order :=
  Lattice.beliLemma71_i D N hunit i j

example (S : Lattice.HyperbolicPlaneSplitting q L)
    (hunit : S.RemainderIsUnitBounded)
    (hparity : S.NormOrdersSameParity) :
    Lattice.spinorNormImageSubgroup (q := q) (L := L) =
      valuationUnitSquareClassSubgroup K :=
  Lattice.beliLemma71_ii_same S hunit hparity

example (S : Lattice.HyperbolicPlaneSplitting q L)
    (hunit : S.RemainderIsUnitBounded)
    (hparity : ¬S.NormOrdersSameParity) :
    Lattice.spinorNormImageSubgroup (q := q) (L := L) = ⊤ :=
  Lattice.beliLemma71_ii_different S hunit hparity

#print axioms Bong.Dyadic.squareClass_mem_valuationUnitSquareClassSubgroup_iff_even
#print axioms Bong.Lattice.beliLemma71_i
#print axioms Bong.Lattice.beliLemma71_ii_same
#print axioms Bong.Lattice.beliLemma71_ii_different
#print axioms Bong.Lattice.beliLemma71_ii
#print axioms Bong.Lattice.beliLemma71_i_proved
#print axioms Bong.Lattice.beliLemma71_ii_same_proved
#print axioms Bong.Lattice.beliLemma71_ii_different_proved
#print axioms Bong.beliLemma71LawsProved

end BongTest.M101
