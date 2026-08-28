/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma66

/-!
# M222 Beli 2019 Lemma 6.6 smoke tests
-/

namespace BongTest.M222

open Bong
open Bong.Dyadic

#check int_modEq_two_sum_Ico
#check int_modEq_two_of_even_sub
#check even_add_of_even_sub
#check BeliOrderSequence.closedSegmentSum
#check BeliOrderSequence.closedSegmentSum_pair
#check BeliOrderSequence.closedSegmentSum_add_two
#check BONG.GoodBONG.orderGap_even_of_nonpositive
#check BONG.GoodBONG.Lemma66EqualEndpointConsequences
#check BONG.GoodBONG.beli2019Lemma66_i
#check BONG.GoodBONG.beli2019Lemma66_ii

#print axioms Bong.BONG.GoodBONG.beli2019Lemma66_i
#print axioms Bong.BONG.GoodBONG.beli2019Lemma66_ii

end BongTest.M222
