/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.SpinorNormMultiplicative

/-!
# M72 integral-reflection and multiplicativity smoke tests
-/

namespace BongTest.M72

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {x : V}

example (generator : Lattice.IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x) :
    Lattice.IsIntegralReflection (L := L) anisotropic :=
  generator.isIntegralReflection anisotropic

example (f g : Lattice.IntegralOrthogonalGroup q L) :
    Lattice.integralSpinorNorm (f * g) =
      Lattice.integralSpinorNorm f * Lattice.integralSpinorNorm g :=
  Lattice.integralSpinorNorm_mul f g

#print axioms Bong.Lattice.IsNormGenerator.isIntegralReflection
#print axioms Bong.Lattice.integralSpinorNorm_mul
#print axioms Bong.Lattice.coe_spinorNormImageSubgroup

end

end BongTest.M72
