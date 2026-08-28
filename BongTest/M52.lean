/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryAdmissibility

/-!
# M52 uniform order-and-defect criterion smoke tests
-/

namespace BongTest.M52

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example (a : Kˣ) :
    HasNonnegativeAbsoluteQuadraticDefect a ↔
      ∃ x : K, (a : K) - x ^ 2 ∈ IntegerRing K :=
  hasNonnegativeAbsoluteQuadraticDefect_iff_exists_sub_sq_mem a

variable [QuadraticDefectLaws K]

example (a : Kˣ) :
    BONG.IsBinaryParameterAdmissible a ↔
      0 ≤ ordUnit K a + 2 * (ramificationIndex K : Int) ∧
        HasNonnegativeAbsoluteQuadraticDefect (-a) :=
  BONG.isBinaryParameterAdmissible_iff_order_add_two_e_and_defect a

#print axioms Bong.Dyadic.hasNonnegativeAbsoluteQuadraticDefect_iff_exists_sub_sq_mem
#print axioms Bong.BONG.isBinaryParameterAdmissible_iff_order_add_two_e_and_defect

end

end BongTest.M52
