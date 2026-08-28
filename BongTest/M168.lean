/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrefixConsequences

/-!
# M168 Corollary 5.10 scalar-consequence smoke tests
-/

namespace BongTest.M168

#check Bong.BONG.AmbientPrefixAgreement.value_eq
#check Bong.BONG.AmbientPrefixAgreement.valueUnit_eq
#check Bong.BONG.AmbientPrefixAgreement.prefixProduct_eq
#check Bong.BONG.GoodBONG.prefixValues_eq_of_ambientPrefixAgreement
#check Bong.BONG.GoodBONG.exists_goodBONG_with_ambientPrefix_and_prefixProduct

#print axioms Bong.BONG.AmbientPrefixAgreement.prefixProduct_eq
#print axioms Bong.BONG.GoodBONG.prefixValues_eq_of_ambientPrefixAgreement
#print axioms
  Bong.BONG.GoodBONG.exists_goodBONG_with_ambientPrefix_and_prefixProduct

end BongTest.M168
