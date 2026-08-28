/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrefixExtensionBaseAuto

/-!
# M164 Automatic one-vector prefix-extension smoke tests
-/

namespace BongTest.M164

#check
  Bong.BONG.GoodBONG.prescribedHeadCandidateWithTail_isGood_of_trigger_one_auto
#check Bong.BONG.GoodBONG.prescribedHeadGoodCandidateAuto
#check
  Bong.BONG.GoodBONG.exists_goodBONG_beginning_with_head_of_trigger_one_auto

#print axioms
  Bong.BONG.GoodBONG.prescribedHeadCandidateWithTail_isGood_of_trigger_one_auto
#print axioms
  Bong.BONG.GoodBONG.exists_goodBONG_beginning_with_head_of_trigger_one_auto

end BongTest.M164
