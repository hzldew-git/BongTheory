/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma67Bounds

/-!
# M224 Beli 2019 Lemma 6.7 fixed-gap bounds
-/

namespace BongTest.M224

open Bong

#check BeliOrderSequence.segmentSum_singleton
#check BeliOrderLE.entryOrZero_le_add_two_of_totalGap
#check BeliOrderLE.prefixGap_bounds_of_totalGap
#check BeliOrderLE.prefixGap_trichotomy_of_totalGap
#check BeliOrderLE.prefix_suffix_eq_of_entryOrZero_eq_add_two
#check BONG.GoodBONG.targetOrder_le_sourceOrder_add_two_of_totalGap

#print axioms Bong.BeliOrderLE.prefix_suffix_eq_of_entryOrZero_eq_add_two

end BongTest.M224
