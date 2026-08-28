/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Necessity

/-!
# M174 Beli 2019 necessity-chain smoke tests
-/

namespace BongTest.M174

open Bong
open Bong.Dyadic

#check BONG.GoodBONG.Beli2019ReflexiveConditionsData
#check BONG.GoodBONG.Beli2019PrimeChainCertificate
#check BONG.GoodBONG.Beli2019PrimeChainCertificate.representationConditions
#check Beli2019Corollary311Laws
#check Beli2019SectionFiveLaws
#check Beli2019SectionFourLaws
#check Lattice.indexPChain_of_le
#check BONG.GoodBONG.representationConditions_of_lattice_le
#check BONG.GoodBONG.beli2019Lemma216
#check RepresentationConditions.toPrime

#print axioms BONG.GoodBONG.Beli2019PrimeChainCertificate.representationConditions
#print axioms BONG.GoodBONG.representationConditions_of_lattice_le
#print axioms RepresentationConditions.toPrime

end BongTest.M174
