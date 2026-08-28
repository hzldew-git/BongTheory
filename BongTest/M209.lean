/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem

/-!
# M209 proved the numerical part of Lemma 3.10 and derived Corollary 3.11
-/

namespace BongTest.M209

open Bong
open Bong.Dyadic

#check BONG.GoodBONG.representationOrderCondition_changeBONG_iff
#check BONG.GoodBONG.representationDefectCondition_changeBONG_iff
#check Beli2019Lemma310RepresentationLaws
#check BONG.GoodBONG.representationConditions_changeBONG_iff
#check corollary311LawsOfLemma310
#check Lattice.IndexPChain.representationConditions
#check beli2019Theorem21_prime

#print axioms BONG.GoodBONG.representationOrderCondition_changeBONG_iff
#print axioms BONG.GoodBONG.representationDefectCondition_changeBONG_iff
#print axioms BONG.GoodBONG.representationConditions_changeBONG_iff
#print axioms Lattice.IndexPChain.representationConditions
#print axioms beli2019Theorem21_prime

end BongTest.M209
