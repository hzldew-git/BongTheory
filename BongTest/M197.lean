/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019IndexPOrderArithmetic

/-! # M197 Section 5 exceptional order-block smoke tests -/

namespace BongTest.M197

#check Bong.BeliOrderSequence.alternatingLowFirst
#check Bong.BeliOrderSequence.alternatingHighFirst
#check Bong.BeliOrderLE.alternating_shift_le
#check Bong.BeliOrderLE.indexP_unary_exceptional_block_le

#print axioms Bong.BeliOrderLE.alternating_shift_le
#print axioms Bong.BeliOrderLE.indexP_unary_exceptional_block_le

end BongTest.M197
