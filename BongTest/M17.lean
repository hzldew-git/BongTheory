/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M17 Wall determinant and spinor-norm smoke tests
-/

namespace BongTest.M17

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} [FiniteDimensional K V]

example (f : QuadraticSpace.Isometry q q) :
    QuadraticSpace.wallDeterminant f ≠ 0 :=
  QuadraticSpace.wallDeterminant_ne_zero f

example (f : QuadraticSpace.Isometry q q) :
    QuadraticSpace.spinorNorm f =
      squareClass K
        (Units.mk0 (QuadraticSpace.wallDeterminant f)
          (QuadraticSpace.wallDeterminant_ne_zero f)) :=
  QuadraticSpace.spinorNorm_eq_wallDeterminant f

variable [ValuativeRel K] [TopologicalSpace K] [DyadicContext K]
  {L : Lattice K V}

example (a : SquareClass K) :
    a ∈ Lattice.spinorNormImage (q := q) (L := L) ↔
      ∃ f : Lattice.IntegralRotation q L,
        f.spinorNorm = a :=
  Lattice.mem_spinorNormImage_iff a

#print axioms Bong.QuadraticSpace.wallForm_nondegenerate
#print axioms Bong.QuadraticSpace.wallDeterminant_ne_zero
#print axioms Bong.QuadraticSpace.spinorNorm
#print axioms Bong.Lattice.integralSpinorNorm
#print axioms Bong.Lattice.spinorNormImage

end

end BongTest.M17
