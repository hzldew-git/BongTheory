/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryAuxiliarySpinorGroup

/-!
# M67 Definition 5 quotient descent smoke tests
-/

namespace BongTest.M67

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example (a s : Kˣ) (hs : IsValuationUnit K (s : K)) :
    beliAuxiliarySpinorGroupRepresentative K (a * s ^ 2) =
      beliAuxiliarySpinorGroupRepresentative K a := by
  apply
    beliAuxiliarySpinorGroupRepresentative_eq_of_unitSquareClass_eq K
  exact unitSquareClass_mul_unit_square K a s hs

example (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hquarter : unitSquareClass K a ≠
      unitSquareClass K (negativeQuarterUnit K))
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    beliSpinorGroup K (unitSquareClass K a) =
      cyclicSquareClassSubgroupOnClass K (unitSquareClass K a) ⊔
        beliAuxiliarySpinorGroupClass K (unitSquareClass K a)
          (by simpa using hR) := by
  apply beliSpinorGroup_eq_cyclic_sup_auxiliaryClass K
  · exact ⟨a, rfl, ha⟩
  · exact hquarter

#print axioms
  Bong.Dyadic.beliAuxiliarySpinorGroupRepresentative_eq_of_unitSquareClass_eq
#print axioms
  Bong.Dyadic.beliSpinorGroup_eq_cyclic_sup_auxiliaryClass

end

end BongTest.M67
