/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AuxiliaryAlpha

/-!
# M177 smoke test

Checks the Definition 5 auxiliary invariant `A'_i` and the decomposition of
`A_i` used at the start of the proof of Beli (2019), Lemma 2.16.
-/

#check Bong.BONG.GoodBONG.representationAlphaPrimeCandidates
#check Bong.BONG.GoodBONG.representationAlphaPrime
#check Bong.BONG.GoodBONG.representationAlphaPrime_le_primaryDefect
#check Bong.BONG.GoodBONG.representationAlphaPrime_le_secondaryDefect
#check Bong.BONG.GoodBONG.representationAlpha_eq_min_halfGap_prime
#check Bong.BONG.GoodBONG.representationAlpha_le_prime
#check Bong.BONG.GoodBONG.representationAlpha_eq_prime_of_prime_le_halfGap
#check Bong.BONG.GoodBONG.representationAlpha_eq_halfGap_of_halfGap_le_prime

#print axioms Bong.BONG.GoodBONG.representationAlpha_eq_min_halfGap_prime
#print axioms Bong.BONG.GoodBONG.representationAlpha_eq_prime_of_prime_le_halfGap
