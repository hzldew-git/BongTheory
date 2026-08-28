/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.CongruenceSubgroup

/-!
# M61 valuation-unit square-class smoke tests
-/

namespace BongTest.M61

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example {m n : Nat} (hmn : m ≤ n) :
    principalUnitValuationClassSubgroup K n ≤
      principalUnitValuationClassSubgroup K m :=
  principalUnitValuationClassSubgroup_anti K hmn

#print axioms Bong.Dyadic.ValuationUnitClass
#print axioms Bong.Dyadic.principalUnitValuationClassSubgroup
#print axioms Bong.Dyadic.quadraticNormValuationClassSubgroup
#print axioms Bong.Dyadic.principalUnitValuationClassSubgroup_anti

end

end BongTest.M61
