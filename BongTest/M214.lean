/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem
import Bong.Bong.DiagonalRepresentationParity

/-!
# M214 corrected Lemma 3.10 and extracted its generic parity foundation
-/

namespace BongTest.M214

open Bong
open Bong.Dyadic

#check EvenTruthParity.second_iff_third_of_first_fourth
#check EvenTruthParity.first_iff_third_of_second_fourth
#check diagonalUnitPrefix
#check DiagonalRepresentationParityLaws
#check DiagonalRepresentationParityLaws.caseI
#check DiagonalRepresentationParityLaws.caseII
#check DiagonalRepresentationParityLaws.caseIII
#check BONG.GoodBONG.beli2019Lemma218_target
#check BONG.GoodBONG.beli2019Lemma218_source
#check BONG.GoodBONG.centralTarget_iff_of_lemma218
#check BONG.GoodBONG.centralSource_iff_of_lemma218
#check BONG.GoodBONG.centralPrefix_change_of_approximation
#check BONG.GoodBONG.representationConditions_changeBONG_iff
#check beli2019Theorem21
#check beli2019Theorem21_prime

#print axioms EvenTruthParity.second_iff_third_of_first_fourth
#print axioms EvenTruthParity.first_iff_third_of_second_fourth

end BongTest.M214
