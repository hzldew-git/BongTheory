/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M14 integral orthogonal-group smoke tests

These examples exercise the group embedding in Beli (2003), Section 2.5.
-/

namespace BongTest.M14

open Bong
open Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {x : V}
  {hx : q.IsAnisotropic x}

example : Group (Lattice.IntegralOrthogonalGroup q L) :=
  inferInstance

example (generator : Lattice.IsNormGenerator q L x) :
    Lattice.IntegralOrthogonalGroup (q.orthogonalSpace x hx)
        (L.projectedLattice q x hx) →*
      Lattice.IntegralOrthogonalGroup q L :=
  Lattice.projectedAutomorphismHom generator

example (generator : Lattice.IsNormGenerator q L x) :
    Function.Injective
      (Lattice.projectedAutomorphismHom (anisotropic := hx) generator) :=
  Lattice.projectedAutomorphismHom_injective generator

#print axioms Bong.Lattice.extendProjectedAutomorphism_mul
#print axioms Bong.Lattice.projectedAutomorphismHom
#print axioms Bong.Lattice.projectedAutomorphismHom_injective

end

end BongTest.M14
