/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem

/-!
# Dyadic unit-defect classification audit

This test checks that the refined defect, square-difference, filtration, and
unit-spectrum interfaces are all inferred from `DyadicContext`.
-/

namespace BongTest

open Bong Bong.Dyadic

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example : DyadicSquareDifferenceLaws K := inferInstance
example : PrincipalUnitSquareClassFiltrationLaws K := inferInstance
example : UnitQuadraticDefectParityLaws K := inferInstance
example : BONG.DyadicUnitDefectSpectrumLaws K := inferInstance

#print axioms Bong.Dyadic.even_order_one_sub_sq_of_lt_two_mul_e_proved
#print axioms Bong.Dyadic.one_sub_four_mul_unit_ne_sq_of_residue_two_proved
#print axioms Bong.Dyadic.principalUnitSquareClassFiltrationLawsProved
#print axioms Bong.Dyadic.unitQuadraticDefectParityLawsProved
#print axioms Bong.Dyadic.exists_unit_quadraticDefect_eq_odd
#print axioms Bong.BONG.dyadicUnitDefectSpectrumLawsProved
#print axioms Bong.beli2019Theorem21
#print axioms Bong.beli2019Theorem21_prime

end BongTest
