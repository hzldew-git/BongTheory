/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma73

/-!
# M221 Beli 2019 Lemma 7.3 smoke tests
-/

namespace BongTest.M221

open Bong
open Bong.Dyadic

#check RationalModEqTwo
#check RationalModEqTwo.refl
#check RationalModEqTwo.symm
#check RationalModEqTwo.trans
#check int_modEq_two_of_even_successive
#check rationalModEqTwo_of_successive
#check BONG.GoodBONG.alphaValue_le_twoE_iff_orderGap_le_twoE
#check BONG.GoodBONG.Lemma73StepConsequences
#check BONG.GoodBONG.beli2019Lemma73_step
#check BONG.GoodBONG.Lemma73LeftConsequences
#check BONG.GoodBONG.beli2019Lemma73_i
#check BONG.GoodBONG.Lemma73RightConsequences
#check BONG.GoodBONG.beli2019Lemma73_ii

#print axioms Bong.BONG.GoodBONG.beli2019Lemma73_step
#print axioms Bong.BONG.GoodBONG.beli2019Lemma73_i
#print axioms Bong.BONG.GoodBONG.beli2019Lemma73_ii

end BongTest.M221
