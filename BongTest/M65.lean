/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinarySpinorGroupFormula

/-!
# M65 Beli Definitions 4 and 5 smoke tests
-/

namespace BongTest.M65

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hquarter : unitSquareClass K a ≠
      unitSquareClass K (negativeQuarterUnit K))
    (hR : 4 * (ramificationIndex K : Int) < ordUnit K a) :
    beliSpinorGroupRepresentative K a =
      cyclicSquareClassSubgroup K a :=
  beliSpinorGroupRepresentative_caseI K a ha hquarter hR

example (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hquarter : unitSquareClass K a ≠
      unitSquareClass K (negativeQuarterUnit K))
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    beliSpinorGroupRepresentative K a =
      cyclicSquareClassSubgroup K a ⊔
        beliAuxiliarySpinorGroup K a hR :=
  beliSpinorGroupRepresentative_eq_cyclic_sup_auxiliary
    K a ha hquarter hR

#print axioms Bong.Dyadic.beliSpinorGroupRepresentative_caseII_low
#print axioms Bong.Dyadic.beliSpinorGroupRepresentative_caseIII_high
#print axioms
  Bong.Dyadic.beliSpinorGroupRepresentative_eq_cyclic_sup_auxiliary

end

end BongTest.M65
