/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliTheoremOneReverse

/-!
# M100 Beli 2003, Theorem 1 reverse inclusion smoke tests
-/

namespace BongTest.M100

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example {x : V} {hx : q.IsAnisotropic x}
    (generator : Lattice.IsNormGenerator q L x)
    (g : Lattice.IntegralOrthogonalGroup q L)
    (hfix : g.toLinearEquiv x = x) :
    Lattice.projectedAutomorphismHom generator
      (Lattice.restrictFixingVector (anisotropic := hx) g hfix) = g :=
  Lattice.projectedAutomorphismHom_restrictFixingVector
    generator g hfix

example (b : BONG V q L (n + 2)) (hB : b.HasPropertyB) :
    b.tail.HasPropertyB :=
  hB.tail

example (b : BONG V q L (n + 3)) :
    b.sectionSixRHS = b.theoremOneRHS :=
  b.sectionSixRHS_eq_theoremOneRHS

variable [BinarySpinorLocalLaws.{u, v} K]
  [BONG.BeliLemma66Laws.{u, v} K]

example (b : BONG V q L (n + 2)) (hB : b.HasPropertyB) :
    Lattice.spinorNormImageSubgroup (q := q) (L := L) ≤
      b.sectionSixRHS :=
  b.spinorNormImageSubgroup_le_sectionSixRHS_of_propertyB hB

variable [BONG.BeliLemma67Laws.{u, v} K]
  [BeliLemma411Laws.{u, v} K]

example (b : BONG V q L (n + 3)) (hA : b.HasPropertyA) :
    Lattice.spinorNormImageSubgroup (q := q) (L := L) ≤
      b.theoremOneRHS :=
  b.spinorNormImageSubgroup_le_theoremOneRHS hA

variable [BeliLemma49Laws.{u, v} K]
  [BeliTheoremOneTernaryLaws.{u, v} K]

example (b : BONG V q L (n + 3)) (hA : b.HasPropertyA) :
    Lattice.spinorNormImageSubgroup (q := q) (L := L) =
      b.theoremOneRHS :=
  b.beliTheoremOne hA

example (b : BONG V q L (n + 3)) (hA : b.HasPropertyA) :
    Lattice.spinorNormImage (q := q) (L := L) =
      (b.theoremOneRHS : Set (SquareClass K)) :=
  b.beliTheoremOne_set hA

#print axioms Bong.Lattice.projectedAutomorphismHom_restrictFixingVector
#print axioms Bong.Lattice.integralSpinorNorm_restrictFixingVector
#print axioms Bong.BONG.HasPropertyB.tail
#print axioms Bong.BONG.sectionSixRHS_eq_theoremOneRHS
#print axioms Bong.BONG.spinorNormImageSubgroup_le_sectionSixRHS_of_propertyB
#print axioms Bong.BONG.spinorNormImageSubgroup_le_theoremOneRHS
#print axioms Bong.BONG.beliTheoremOne
#print axioms Bong.BONG.beliTheoremOne_set

end BongTest.M100
