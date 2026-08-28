/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.QuadraticDefectHensel
import Bong.Bong.Beli2019MainTheorem

/-!
# Quadratic-defect Hensel audit

This test confirms that `DyadicContext` now supplies `QuadraticDefectLaws`
without an extra hypothesis and records the kernel dependencies of the new
square theorem and its instance.
-/

namespace BongTest

open Bong Bong.Dyadic

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example : QuadraticDefectLaws K := inferInstance

#print axioms Bong.Dyadic.isSquare_of_ord_sub_one_gt_two_mul_e
#print axioms Bong.Dyadic.isSquare_of_quadraticDefect_gt_two_mul_e
#print axioms Bong.Dyadic.quadraticDefectLawsOfHensel
#print axioms Bong.beli2019Theorem21
#print axioms Bong.beli2019Theorem21_prime

end BongTest
