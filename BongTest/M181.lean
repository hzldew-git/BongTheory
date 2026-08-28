/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019CappedDefectMin

/-!
# M181 smoke test

Checks capped-defect domination and the source-prefix replacement form of
Beli (2019), Lemma 1.4(c).
-/

#check Bong.withTop_shifted_min_eq_of_domination
#check Bong.BONG.GoodBONG.truncatedPrefixDefect_comm
#check Bong.BONG.GoodBONG.truncatedPrefixDefect_add_two_domination
#check Bong.BONG.GoodBONG.truncatedPrefixDefect_add_two_domination_reverse
#check Bong.BONG.GoodBONG.shiftedTruncatedPrefixDefect_add_two_replace_of_cut_le

#print axioms Bong.withTop_shifted_min_eq_of_domination
#print axioms Bong.BONG.GoodBONG.shiftedTruncatedPrefixDefect_add_two_replace_of_cut_le
