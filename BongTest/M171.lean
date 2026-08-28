/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma513

/-!
# M171 Beli 2019 Lemma 5.13 smoke tests
-/

namespace BongTest.M171

open Bong
open Bong.Dyadic

#check BONG.GoodBONG.Beli2019Lemma513Data
#check BONG.GoodBONG.Beli2019Lemma513Bounds
#check BONG.GoodBONG.Beli2019Lemma513LocalData.prefixSum_succ_of_current_succ
#check BONG.GoodBONG.Beli2019Lemma513Data.common_or_prefixSum_succ
#check BONG.GoodBONG.representationDefectCondition_of_lemma513

#print axioms BONG.GoodBONG.Beli2019Lemma513LocalData.prefixSum_succ_of_current_succ
#print axioms BONG.GoodBONG.representationDefectCondition_of_lemma513

end BongTest.M171
