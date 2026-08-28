/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M18 spinor normalization and projection smoke tests
-/

namespace BongTest.M18

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} [FiniteDimensional K V]

example {x : V} (hx : q.IsAnisotropic x) :
    QuadraticSpace.spinorNorm (q.reflectionIsometry x hx) =
      squareClass K (Units.mk0 (q.quadratic x) hx) :=
  QuadraticSpace.spinorNorm_reflection hx

example {x : V} (hx : q.IsAnisotropic x)
    (f : QuadraticSpace.Isometry (q.orthogonalSpace x hx)
      (q.orthogonalSpace x hx)) :
    QuadraticSpace.spinorNorm
        (QuadraticSpace.orthogonalExtensionIsometry f) =
      QuadraticSpace.spinorNorm f :=
  QuadraticSpace.spinorNorm_orthogonalExtension f

variable [ValuativeRel K] [TopologicalSpace K] [DyadicContext K]
  {L : Lattice K V}

example {x : V} {hx : q.IsAnisotropic x}
    (generator : Lattice.IsNormGenerator q L x) :
    Lattice.spinorNormImage
        (q := q.orthogonalSpace x hx)
        (L := Lattice.projectedLattice q L x hx) ⊆
      Lattice.spinorNormImage (q := q) (L := L) :=
  Lattice.spinorNormImage_projectedLattice_subset generator

#print axioms Bong.QuadraticSpace.spinorNorm_reflection
#print axioms Bong.QuadraticSpace.spinorNorm_orthogonalExtension
#print axioms Bong.Lattice.integralSpinorNorm_integralReflection
#print axioms Bong.Lattice.spinorNormImage_projectedLattice_subset

end

end BongTest.M18
