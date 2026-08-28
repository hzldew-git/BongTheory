/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AuxiliaryAlphaBounds

/-!
# M178 smoke test

Checks the endpoint-safe cap bounds following Definition 5 and the two defect
bounds used in the proof of Beli (2019), Lemma 2.16.
-/

#check Bong.BONG.GoodBONG.representationAlphaPrime_le_primaryLeftCap
#check Bong.BONG.GoodBONG.representationAlphaPrime_le_primaryRightCap
#check Bong.BONG.GoodBONG.representationAlphaPrime_le_secondaryLeftCap
#check Bong.BONG.GoodBONG.representationAlphaPrime_le_secondaryRightCap
#check Bong.BONG.GoodBONG.centralPreviousDefect_le_rightCap
#check Bong.BONG.GoodBONG.centralCurrentDefect_le_leftCap

#print axioms Bong.BONG.GoodBONG.representationAlphaPrime_le_primaryLeftCap
#print axioms Bong.BONG.GoodBONG.centralCurrentDefect_le_leftCap
