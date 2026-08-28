/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AdjacentCappedDefect

/-!
# M182 smoke test

Checks Remark 1.1's capped adjacent-defect estimate, including endpoints.
-/

#check Bong.withTop_le_shift_add_min
#check Bong.BONG.GoodBONG.defectOrder_prefixPair_eq_adjacentDefect
#check Bong.BONG.GoodBONG.alpha_le_orderGap_add_cappedAdjacent

#print axioms Bong.BONG.GoodBONG.defectOrder_prefixPair_eq_adjacentDefect
#print axioms Bong.BONG.GoodBONG.alpha_le_orderGap_add_cappedAdjacent
