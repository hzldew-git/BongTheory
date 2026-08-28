/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinarySpinorGroupInvariant

/-!
# M66 Definition 4 quotient descent smoke tests
-/

namespace BongTest.M66

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example (a s : Kˣ) (hs : IsValuationUnit K (s : K)) :
    beliSpinorGroupRepresentative K (a * s ^ 2) =
      beliSpinorGroupRepresentative K a := by
  apply beliSpinorGroupRepresentative_eq_of_unitSquareClass_eq K
  exact unitSquareClass_mul_unit_square K a s hs

example (a : Kˣ) :
    beliSpinorGroup K (unitSquareClass K a) =
      beliSpinorGroupRepresentative K a :=
  beliSpinorGroup_unitSquareClass K a

example (a : Kˣ) :
    unitSquareClassOrder K (unitSquareClass K a) = ordUnit K a :=
  unitSquareClassOrder_unitSquareClass K a

#print axioms
  Bong.Dyadic.beliParameterDefect_mul_valuationUnit_square
#print axioms
  Bong.Dyadic.beliSpinorGroupRepresentative_eq_of_unitSquareClass_eq
#print axioms Bong.Dyadic.beliSpinorGroup_unitSquareClass

end

end BongTest.M66
