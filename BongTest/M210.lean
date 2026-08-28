/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem

/-!
# M210 localized the remaining representation content of Lemma 3.10
-/

namespace BongTest.M210

open Bong
open Bong.Dyadic

#check BONG.GoodBONG.centralAdjustedAlpha_invariant
#check BONG.GoodBONG.centralAlphaTrigger_changeBONG_iff
#check BONG.GoodBONG.longRepresentationTrigger
#check BONG.GoodBONG.longRepresentationTrigger_changeBONG_iff
#check Beli2019Lemma310PrefixLaws
#check lemma310RepresentationLawsOfPrefixLaws
#check corollary311LawsOfLemma310
#check Lattice.IndexPChain.representationConditions
#check beli2019Theorem21_prime

#print axioms BONG.GoodBONG.centralAdjustedAlpha_invariant
#print axioms BONG.GoodBONG.centralAlphaTrigger_changeBONG_iff
#print axioms BONG.GoodBONG.longRepresentationTrigger_changeBONG_iff
#print axioms BONG.GoodBONG.representationConditions_changeBONG_iff
#print axioms Lattice.IndexPChain.representationConditions
#print axioms beli2019Theorem21_prime

end BongTest.M210
