/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019VolumeOrders

/-!
# M156 Beli 2019, volume-order smoke tests
-/

namespace BongTest.M156

#check Bong.BONG.volumeOrder_eq_ordUnit_valueProduct_all
#check Bong.BONG.ordUnit_valueProduct_eq_sum_order
#check Bong.BONG.volumeOrder_eq_sum_order
#check Bong.BONG.volumeOrder_eq_order_zero_add_sum_tail
#check Bong.BONG.sum_tail_order_eq_volumeOrder_sub_order_zero
#check Bong.BONG.GoodBONG.orderSequence_suffixSum_zero_eq_volumeOrder
#check Bong.BONG.GoodBONG.orderSequence_suffixSum_one_eq_volumeOrder_sub
#check Bong.BONG.GoodBONG.orderSequence_suffixSum_one_eq_sum_tail_order

#print axioms Bong.BONG.volumeOrder_eq_sum_order
#print axioms Bong.BONG.sum_tail_order_eq_volumeOrder_sub_order_zero
#print axioms Bong.BONG.GoodBONG.orderSequence_suffixSum_one_eq_volumeOrder_sub

end BongTest.M156
