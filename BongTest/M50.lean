/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryExactRealization

/-!
# M50 exact binary realization smoke tests
-/

namespace BongTest.M50

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    (BONG.binaryExactModelBONG a c htwo hdiag).value 1 = (a : K) := by
  simp

example (a : Kˣ) :
    BONG.IsBinaryParameterAdmissible a ↔
      ∃ (c : K)
        (htwo : (2 : K) * c ∈ IntegerRing K)
        (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K),
        (BONG.binaryExactModelBONG a c htwo hdiag).binaryParameter = a :=
  BONG.isBinaryParameterAdmissible_iff_exists_exactModelBONG a

#print axioms Bong.BONG.binaryModel_projectedLattice
#print axioms Bong.BONG.binaryExactModelBONG_value_one
#print axioms Bong.BONG.binaryExactModelBONG_binaryParameter
#print axioms Bong.BONG.isBinaryParameterAdmissible_iff_exists_exactModelBONG

end

end BongTest.M50
