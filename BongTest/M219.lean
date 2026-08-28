/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019FinalStep

/-!
# M219 Beli 2019 rank-volume descent smoke tests
-/

namespace BongTest.M219

open Bong

#check Beli2019RankVolumeMeasure
#check Beli2019RankVolumeMeasure.Smaller
#check Beli2019RankVolumeMeasure.smaller_of_rank_lt
#check Beli2019RankVolumeMeasure.smaller_of_volumeGap_lt
#check Beli2019RankVolumeMeasure.smaller_wellFounded
#check beli2019ProblemSmaller_wellFounded
#check beli2019ProblemSmaller_of_rank_lt
#check beli2019ProblemSmaller_of_volumeGap_lt
#check Beli2019SectionNineCase
#check Beli2019FinalStepData.sectionNine

#print axioms Beli2019RankVolumeMeasure.smaller_wellFounded
#print axioms Beli2019FinalStepData.sectionNine
#print axioms Beli2019FinalStepData.not_counterexample

end BongTest.M219
