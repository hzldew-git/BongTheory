/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma27

/-!
# M183 smoke test

Checks Beli (2019), Lemma 2.7(i), including its `A'_i` normal form.
-/

#check Bong.BONG.GoodBONG.representationSecondaryPreviousDefect
#check Bong.BONG.GoodBONG.representationPrimaryDefect_le_secondaryAdjacentCut
#check Bong.BONG.GoodBONG.representationSecondaryDefect_replace_previous
#check Bong.BONG.GoodBONG.representationAlphaPrime_eq_min_primary_previous

#print axioms Bong.BONG.GoodBONG.representationSecondaryDefect_replace_previous
#print axioms Bong.BONG.GoodBONG.representationAlphaPrime_eq_min_primary_previous
