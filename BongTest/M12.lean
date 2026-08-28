/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M12 transporter smoke tests

These examples exercise Beli (2003), Corollary 2.4 and Section 2.5.
-/

namespace BongTest.M12

open Bong
open Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {x : V}
  {hx : q.IsAnisotropic x}

example (generatorL : Lattice.IsNormGenerator q L x)
    (generatorM : Lattice.IsNormGenerator q M x)
    (f : Lattice.Isometry (q.orthogonalSpace x hx)
      (q.orthogonalSpace x hx)
      (L.projectedLattice q x hx) (M.projectedLattice q x hx)) :
    Lattice.Isometry q q L M :=
  f.extendProjectedIsometry generatorL generatorM

example (generator : Lattice.IsNormGenerator q L x)
    (f : Lattice.Isometry (q.orthogonalSpace x hx)
      (q.orthogonalSpace x hx)
      (L.projectedLattice q x hx) (L.projectedLattice q x hx)) :
    (f.extendProjectedAutomorphism generator).toLinearEquiv x = x :=
  f.extendProjectedAutomorphism_apply_distinguished generator

example (generator : Lattice.IsNormGenerator q L x)
    (f : Lattice.Isometry (q.orthogonalSpace x hx)
      (q.orthogonalSpace x hx)
      (L.projectedLattice q x hx) (L.projectedLattice q x hx))
    (y : V) :
    q.projectionToOrthogonal x hx
        ((f.extendProjectedAutomorphism generator).toLinearEquiv y) =
      f.toLinearEquiv (q.projectionToOrthogonal x hx y) :=
  f.projection_extendProjectedAutomorphism generator y

#print axioms Bong.QuadraticSpace.orthogonalExtensionIsometry
#print axioms Bong.Lattice.projectedLattice_map_orthogonalExtension
#print axioms Bong.Lattice.Isometry.extendProjectedIsometry
#print axioms Bong.Lattice.Isometry.extendProjectedAutomorphism

end

end BongTest.M12
