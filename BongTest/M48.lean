/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryRealization

/-!
# M48 explicit binary realization smoke tests
-/

namespace BongTest.M48

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (a : Kˣ) (c : K) :
    (QuadraticSpace.binaryModelMatrix a c).det = (a : K) :=
  QuadraticSpace.binaryModelMatrix_det a c

example (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    (BONG.binaryModelBONG a c htwo hdiag).binaryUnitSquareClass =
      unitSquareClass K a :=
  BONG.binaryModelBONG_binaryUnitSquareClass a c htwo hdiag

example (b : BONG V q L 2) :
    BONG.IsBinaryParameterAdmissible b.binaryParameter :=
  b.binaryParameter_isBinaryParameterAdmissible

example (b : BONG V q L 2) :
    BONG.IsBinaryInvariantClassAdmissible b.binaryUnitSquareClass :=
  b.binaryUnitSquareClass_isAdmissible

#print axioms Bong.QuadraticSpace.binaryModelMatrix_det
#print axioms Bong.BONG.binaryModelFirst_isNormGenerator
#print axioms Bong.BONG.binaryModelBONG_binaryUnitSquareClass
#print axioms Bong.BONG.binaryParameter_isBinaryParameterAdmissible
#print axioms Bong.BONG.IsBinaryInvariantClassAdmissible.exists_modelBONG

end

end BongTest.M48
