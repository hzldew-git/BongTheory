/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019DefectConditionBranches

/-!
# M170 Beli 2019 condition 2.1(ii) branch smoke tests
-/

namespace BongTest.M170

#check
  Bong.BONG.GoodBONG.truncatedPrefixDefect_eq_min_caps_of_common_approximation
#check Bong.BONG.GoodBONG.representationDefect_at_of_common_approximation
#check Bong.BONG.GoodBONG.representationDefect_at_of_prefixSum_succ
#check
  Bong.BONG.GoodBONG.representationDefectCondition_of_common_or_odd_branches

#print axioms
  Bong.BONG.GoodBONG.truncatedPrefixDefect_eq_min_caps_of_common_approximation
#print axioms
  Bong.BONG.GoodBONG.representationDefectCondition_of_common_or_odd_branches

end BongTest.M170
