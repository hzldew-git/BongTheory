/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M15 reflection smoke tests

These examples exercise the reflection layer used by the spinor norm.
-/

namespace BongTest.M15

open Bong
open Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {x : V}

example (hx : q.IsAnisotropic x) : QuadraticSpace.Isometry q q :=
  q.reflectionIsometry x hx

example (hx : q.IsAnisotropic x) (hy : x ∈ L)
    (hcoefficient : ∀ y : V, y ∈ L →
      2 * q.bilin x y / q.quadratic x ∈ IntegerRing K) :
    Lattice.IsIntegralReflection (L := L) hx :=
  Lattice.isIntegralReflection_of_coefficient_mem_integerRing
    hx hy hcoefficient

example (hx : q.IsAnisotropic x)
    (integral : Lattice.IsIntegralReflection (L := L) hx) :
    Lattice.IntegralOrthogonalGroup q L :=
  Lattice.integralReflection hx integral

example (hx : q.IsAnisotropic x)
    (z : q.vectorOrthogonal x)
    (hz : (q.orthogonalSpace x hx).IsAnisotropic z) :
    QuadraticSpace.orthogonalExtensionIsometry
        ((q.orthogonalSpace x hx).reflectionIsometry z hz) =
      q.reflectionIsometry (z : V) hz :=
  q.orthogonalExtensionIsometry_reflection x hx z hz

#print axioms Bong.QuadraticSpace.reflectionIsometry
#print axioms Bong.QuadraticSpace.orthogonalExtensionIsometry_reflection
#print axioms Bong.Lattice.integralReflection
#print axioms Bong.Lattice.isIntegralReflection_of_projectedLattice

end

end BongTest.M15
