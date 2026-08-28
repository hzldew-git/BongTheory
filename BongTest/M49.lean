/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryDefectCriterion

/-!
# M49 Beli binary defect criterion smoke tests
-/

namespace BongTest.M49

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example {a : Kˣ} (ha : BONG.IsBinaryParameterAdmissible a) :
    -(2 * (ramificationIndex K : Int)) ≤ ordUnit K a :=
  ha.ordUnit_ge_neg_two_mul_e

variable [QuadraticDefectLaws K]

example (a : Kˣ) :
    BONG.IsBinaryParameterAdmissible a ↔
      BONG.IsBeliBinaryParameterAdmissible a :=
  BONG.isBinaryParameterAdmissible_iff_beli a

example (A : UnitSquareClass K) :
    BONG.IsBinaryInvariantClassAdmissible A ↔
      BONG.IsBeliBinaryInvariantClassAdmissible A :=
  BONG.isBinaryInvariantClassAdmissible_iff_beli A

#print axioms Bong.Dyadic.two_mul_mem_integerRing_of_not_isSquare_of_sub_sq_mem
#print axioms Bong.BONG.IsBinaryParameterAdmissible.ordUnit_ge_neg_two_mul_e
#print axioms Bong.BONG.isBinaryParameterAdmissible_iff_beli
#print axioms Bong.BONG.isBinaryInvariantClassAdmissible_iff_beli

end

end BongTest.M49
