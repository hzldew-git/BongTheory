/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem
import Bong.Bong.Beli2019FinalStep

/-!
# M175 Beli 2019 Sections 7--9 smoke tests
-/

namespace BongTest.M175

open Bong
open Bong.Dyadic

#check Beli2019NormReductionOutcome
#check Beli2019FinalStepOutcome
#check Beli2019SectionNineCase
#check Beli2019FinalStepData
#check Beli2019FinalStepData.sectionNine
#check Beli2019FinalStepData.descend
#check Beli2019FinalStepData.not_counterexample
#check Beli2019FinalStepData.represents
#check beli2019_sufficiency_complete
#check beli2019Theorem21
#check beli2019Theorem21_prime

#print axioms Beli2019FinalStepData.descend
#print axioms Beli2019FinalStepData.not_counterexample
#print axioms Beli2019FinalStepData.represents
#print axioms beli2019_sufficiency_complete
#print axioms beli2019Theorem21
#print axioms beli2019Theorem21_prime

end BongTest.M175
