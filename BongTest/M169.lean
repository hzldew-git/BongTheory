/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OddPrefixDefect

/-!
# M169 Beli 2019 Lemma 5.13(ii) arithmetic smoke tests
-/

namespace BongTest.M169

#check Bong.BONG.GoodBONG.ordUnit_prefixProduct_eq_orderSequence_prefixSum
#check Bong.BONG.GoodBONG.comparisonPrefixProduct_order_odd_of_prefixSum_succ
#check Bong.BONG.GoodBONG.comparisonPrefixProduct_order_odd_of_previous_prefix_eq
#check Bong.BONG.GoodBONG.truncatedPrefixDefect_nonneg
#check Bong.BONG.GoodBONG.truncatedPrefixDefect_eq_zero_of_odd_order
#check Bong.BONG.GoodBONG.truncatedPrefixDefect_eq_zero_of_prefixSum_succ

#print axioms
  Bong.BONG.GoodBONG.ordUnit_prefixProduct_eq_orderSequence_prefixSum
#print axioms
  Bong.BONG.GoodBONG.truncatedPrefixDefect_eq_zero_of_prefixSum_succ

end BongTest.M169
