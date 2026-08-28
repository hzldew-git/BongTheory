/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFive

/-!
# M173 Beli 2019 Section 5 smoke tests
-/

namespace BongTest.M173

open Bong
open Bong.Dyadic

#check Beli2019IndexPInclusion
#check BONG.GoodBONG.Beli2019SectionFiveDefectData
#check BONG.GoodBONG.Beli2019SectionFiveDefectData.defectCondition
#check BONG.GoodBONG.Beli2019SectionFiveCentralCertificate
#check BONG.GoodBONG.Beli2019SectionFiveLongCertificate
#check BONG.GoodBONG.Beli2019SectionFiveData
#check BONG.GoodBONG.Beli2019SectionFiveData.representationConditions
#check BONG.GoodBONG.Beli2019SectionFiveData.representationConditionsPrime

#print axioms BONG.GoodBONG.Beli2019SectionFiveDefectData.defectCondition
#print axioms BONG.GoodBONG.Beli2019SectionFiveData.representationConditions
#print axioms BONG.GoodBONG.Beli2019SectionFiveData.representationConditionsPrime

end BongTest.M173
