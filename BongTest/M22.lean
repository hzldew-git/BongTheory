/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M22 isometric transport of BONGs smoke tests
-/

namespace BongTest.M22

open Bong Bong.Dyadic

noncomputable section

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

example (f : QuadraticSpace.Isometry q r) (x : V)
    (hx : q.IsAnisotropic x) :
    Lattice.projectedLattice r (Lattice.map f.toLinearEquiv L)
        (f.toLinearEquiv x) (f.map_isAnisotropic hx) =
      Lattice.map (f.orthogonalLinearEquiv x)
        (Lattice.projectedLattice q L x hx) :=
  Lattice.projectedLattice_map_isometry f x hx

example (f : QuadraticSpace.Isometry q r) (b : BONG V q L n)
    (i : Fin n) :
    (b.map f).value i = b.value i :=
  BONG.value_map f b i

example (f : Lattice.Isometry q r L M) (b : BONG V q L n) :
    BONG W r M n :=
  b.mapLatticeIsometry f

#print axioms Bong.Lattice.projectedLattice_map_isometry
#print axioms Bong.BONG.map
#print axioms Bong.BONG.value_map
#print axioms Bong.BONG.ambientVector_mapLatticeIsometry

end

end BongTest.M22
