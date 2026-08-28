/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem

/-!
# M218 Beli 2019 Lemmas 2.20--2.21 smoke tests
-/

namespace BongTest.M218

open Bong
open Bong.Dyadic

#check BONG.GoodBONG.PrefixAgreement
#check BONG.GoodBONG.ScalarAgreement
#check GoodBONGDeepIntegralExtensionData
#check GoodBONGDeepIntegralExtensionLaws
#check GoodBONGSameRankIntegralImageData
#check exists_goodBONGSameRankIntegralImageData
#check BONG.GoodBONG.representationConditionsPrime_of_scalarAgreement
#check BONG.GoodBONG.representationConditionsPrime_of_prefixAgreement

#print axioms exists_goodBONGSameRankIntegralImageData
#print axioms BONG.GoodBONG.representationConditionsPrime_of_scalarAgreement
#print axioms BONG.GoodBONG.representationConditionsPrime_of_prefixAgreement
#print axioms beli2019_necessity

end BongTest.M218
