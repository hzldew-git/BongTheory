/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma517

/-!
# M172 Beli 2019 Lemma 5.17 smoke tests
-/

namespace BongTest.M172

open Bong
open Bong.Dyadic

#check BONG.GoodBONG.Beli2019Lemma517Data
#check BONG.GoodBONG.Beli2019Lemma517Data.min_prefixAlphaCap_eq_left
#check BONG.GoodBONG.Beli2019Lemma517Data.commonBound_of_leftCap
#check BONG.GoodBONG.Beli2019Lemma517PrefixData
#check BONG.GoodBONG.Beli2019Lemma517PrefixData.prefixExtensionHypothesis
#check BONG.GoodBONG.exists_goodBONG_with_ambientPrefix_of_lemma517

#print axioms BONG.GoodBONG.Beli2019Lemma517Data.commonBound_of_leftCap
#print axioms BONG.GoodBONG.exists_goodBONG_with_ambientPrefix_of_lemma517

end BongTest.M172
