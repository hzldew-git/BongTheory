/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma310Approximation

/-!
# M212 factored Lemma 3.10 through arbitrary space approximations
-/

namespace BongTest.M212

open Bong
open Bong.Dyadic

#check DiagonalCodimensionOneCancellationLaws
#check BONG.GoodBONG.longTarget_iff_of_cancellation
#check BONG.GoodBONG.longSource_iff_of_cancellation
#check BONG.GoodBONG.beli2019Lemma218_target
#check BONG.GoodBONG.beli2019Lemma218_source
#check BONG.diagonalQuadratic_value_eq
#check BONG.coordinateChange
#check BONG.diagonalRepresents_values
#check BONG.GoodBONG.fullPrefix_represents
#check BONG.GoodBONG.spaceApproximationRepresentationBridge_prefixValueUnits
#check BONG.GoodBONG.centralPrefix_change_of_approximation
#check BONG.GoodBONG.centralTarget_iff_of_lemma218
#check BONG.GoodBONG.centralSource_iff_of_lemma218
#check BONG.GoodBONG.longPrefix_change_of_approximation
#check lemma310PrefixLawsOfApproximationLaws

#print axioms BONG.diagonalQuadratic_value_eq
#print axioms BONG.diagonalRepresents_values
#print axioms BONG.GoodBONG.fullPrefix_represents
#print axioms BONG.GoodBONG.centralPrefix_change_of_approximation
#print axioms BONG.GoodBONG.longPrefix_change_of_approximation
#print axioms lemma310PrefixLawsOfApproximationLaws

end BongTest.M212
