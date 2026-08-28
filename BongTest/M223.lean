/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma65

/-!
# M223 Beli 2019 Lemma 6.5 smoke tests
-/

namespace BongTest.M223

open Bong
open Bong.Dyadic

#check odd_add_of_modEq_add_one
#check BONG.GoodBONG.comparisonPrefixProduct_order_odd_of_modEq_add_one
#check BONG.GoodBONG.sourceNext_le_targetCurrent_of_halfGap_le_zero
#check BONG.GoodBONG.sourceNext_le_targetCurrent_of_primary_le_zero
#check BONG.GoodBONG.sourcePair_le_targetPair_of_secondary_le_zero
#check BONG.GoodBONG.beli2019Lemma65

#print axioms Bong.BONG.GoodBONG.beli2019Lemma65

end BongTest.M223
