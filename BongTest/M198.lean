/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019IndexPOrderEndpoints

/-! # M198 Section 5 endpoint order-block smoke tests -/

namespace BongTest.M198

#check Bong.BeliOrderSequence.loweredLeftEndpoint
#check Bong.BeliOrderSequence.raisedRightEndpoint
#check Bong.BeliOrderLE.endpoint_raised_le
#check Bong.BeliOrderLE.indexP_unary_proper_block_le

#print axioms Bong.BeliOrderLE.endpoint_raised_le
#print axioms Bong.BeliOrderLE.indexP_unary_proper_block_le

end BongTest.M198
