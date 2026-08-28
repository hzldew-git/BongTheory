/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrescribedHead

/-!
# M148 Beli 2019, prescribed-head construction smoke tests
-/

namespace BongTest.M148

#check Bong.Lattice.IsNormGenerator.of_le_of_normIdeal_eq
#check Bong.BONG.ofNormGenerator
#check Bong.BONG.head_ofNormGenerator
#check Bong.BONG.GoodBONG.prescribedHead_isNormGenerator
#check Bong.BONG.GoodBONG.prescribedHeadCandidate
#check Bong.BONG.GoodBONG.prescribedHeadCandidate_head
#check Bong.BONG.GoodBONG.prescribedHeadCandidateWithTail
#check Bong.BONG.GoodBONG.prescribedHeadCandidateWithTail_head
#check Bong.BONG.GoodBONG.prescribedHeadCandidateWithTail_tail

#print axioms Bong.Lattice.IsNormGenerator.of_le_of_normIdeal_eq
#print axioms Bong.BONG.head_ofNormGenerator
#print axioms Bong.BONG.GoodBONG.prescribedHead_isNormGenerator
#print axioms Bong.BONG.GoodBONG.prescribedHeadCandidate_head
#print axioms Bong.BONG.GoodBONG.prescribedHeadCandidateWithTail_head
#print axioms Bong.BONG.GoodBONG.prescribedHeadCandidateWithTail_tail

end BongTest.M148
