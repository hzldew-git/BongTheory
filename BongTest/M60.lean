/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.CongruenceSubgroup

/-!
# M60 congruence square-class subgroup smoke tests
-/

namespace BongTest.M60

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example {m n : Nat} (hmn : m ≤ n) :
    principalUnitSquareClassSubgroup K n ≤
      principalUnitSquareClassSubgroup K m :=
  principalUnitSquareClassSubgroup_anti K hmn

example (n : Nat) :
    principalUnitSquareClassSubgroup K n ≤
      valuationUnitSquareClassSubgroup K :=
  principalUnitSquareClassSubgroup_le_valuationUnit K n

#print axioms Bong.Dyadic.principalUnitSubgroup
#print axioms Bong.Dyadic.principalUnitSubgroup_anti
#print axioms Bong.Dyadic.principalUnitSquareClassSubgroup_anti
#print axioms Bong.Dyadic.quadraticNormSquareClassSubgroup

end

end BongTest.M60
