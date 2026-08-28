/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.SectionTwo

/-!
# M10 smoke tests

The one-step determinant projection law and Beli's recursive determinant
formula are available without an extra local-law assumption.
-/

namespace BongTest.M10

open Bong
open Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

example : BONGDeterminantProjectionLaws.{u, v} K := inferInstance

example (q : QuadraticSpace K V) (L : Lattice K V) (x : V)
    (generator : Lattice.IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x) :
    Lattice.determinantClass q L =
      unitSquareClass K (Units.mk0 (q.quadratic x) anisotropic) *
        Lattice.determinantClass (q.orthogonalSpace x anisotropic)
          (L.projectedLattice q x anisotropic) :=
  Lattice.determinantClass_projection q L x generator anisotropic

example {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) :
    Lattice.determinantClass q L = unitSquareClass K b.valueProduct :=
  b.determinantClass_eq_valueProduct

#print axioms Bong.Lattice.determinantClass_projection_of_normGenerator
#print axioms Bong.BONG.determinantClass_eq_valueProduct

end BongTest.M10
