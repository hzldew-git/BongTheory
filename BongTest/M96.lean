/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma64

/-!
# M96 Beli 2003, Lemma 6.4 smoke tests
-/

namespace BongTest.M96

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}

example (D : Lattice.OrthogonalDecomposition q L t) (i : Fin t)
    (r : Int)
    (hH : (D.component i).ContainsScaledHyperbolicPlane r) :
    Lattice.ContainsScaledHyperbolicPlane q L r :=
  D.containsScaledHyperbolicPlane_of_component i r hH

variable [BeliLemma64Laws.{u, v} K]

example {r : Int} (S : Lattice.UnaryFirstSplitting q L r) :
    ¬Lattice.ContainsScaledHyperbolicPlane q L r :=
  BONG.beliLemma64_i S

example {r : Int} (S : Lattice.BinaryFirstModularSplitting q L r) :
    Lattice.ContainsScaledHyperbolicPlane q L r ↔
      (S.component 0).ContainsScaledHyperbolicPlane r :=
  BONG.beliLemma64_ii S

example (b : BONG V q L (n + 3)) (hgood : b.IsGood)
    (h13 : b.order 0 < b.order 2) :
    Lattice.ContainsScaledHyperbolicPlane q L
        ((b.order 0 + b.order 1) / 2) ↔
      Lattice.QuadraticSublattice.ContainsScaledHyperbolicPlane
        (b.prefixWitness 2 (by omega)).quadraticSublattice
        ((b.order 0 + b.order 1) / 2) :=
  b.beliLemma64_iii hgood h13

#print axioms Bong.Lattice.OrthogonalDecomposition.component_mem_parent
#print axioms Bong.Lattice.OrthogonalDecomposition.containsScaledHyperbolicPlane_of_component
#print axioms Bong.BONG.PrefixWitness.containsScaledHyperbolicPlane_parent
#print axioms Bong.BONG.beliLemma64_i
#print axioms Bong.BONG.beliLemma64_ii
#print axioms Bong.BONG.beliLemma64_iii

end BongTest.M96
