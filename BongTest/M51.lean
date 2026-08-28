/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryAdmissibility

/-!
# M51 binary admissibility stability smoke tests
-/

namespace BongTest.M51

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example (a s : Kˣ) (hs : IsValuationUnit K (s : K)) :
    BONG.IsBinaryParameterAdmissible (a * s ^ 2) ↔
      BONG.IsBinaryParameterAdmissible a :=
  BONG.isBinaryParameterAdmissible_mul_valuationUnit_square_iff a s hs

example (a : Kˣ) :
    BONG.IsBinaryInvariantClassAdmissible (unitSquareClass K a) ↔
      BONG.IsBinaryParameterAdmissible a :=
  BONG.isBinaryInvariantClassAdmissible_unitSquareClass_iff a

#print axioms Bong.BONG.IsBinaryParameterAdmissible.mul_integral_square
#print axioms Bong.BONG.isBinaryParameterAdmissible_iff_of_unitSquareClass_eq
#print axioms Bong.BONG.isBinaryInvariantClassAdmissible_unitSquareClass_iff

end

end BongTest.M51
