/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019CanonicalApproximation

/-!
# M211 formalized the canonical BONG-prefix approximating spaces
-/

namespace BongTest.M211

open Bong
open Bong.Dyadic

#check BONG.GoodBONG.prefixValueUnits
#check BONG.diagonalQuadratic_value_eq
#check BONG.coordinateChange
#check BONG.diagonalRepresents_values
#check BONG.GoodBONG.fullPrefix_represents
#check BONG.GoodBONG.diagonalUnitCoefficients_prefixValueUnits
#check BONG.GoodBONG.diagonalUnitDeterminant_prefixValueUnits
#check BONG.GoodBONG.isSpaceApproximation_prefixValueUnits
#check BONG.GoodBONG.spaceApproximationRepresentationBridge_prefixValueUnits
#check BONG.GoodBONG.isSpaceApproximation_prefixValueUnits_of_bridge

#print axioms BONG.GoodBONG.diagonalUnitDeterminant_prefixValueUnits
#print axioms BONG.diagonalRepresents_values
#print axioms BONG.GoodBONG.fullPrefix_represents
#print axioms BONG.GoodBONG.isSpaceApproximation_prefixValueUnits
#print axioms BONG.GoodBONG.spaceApproximationRepresentationBridge_prefixValueUnits
#print axioms BONG.GoodBONG.isSpaceApproximation_prefixValueUnits_of_bridge

end BongTest.M211
