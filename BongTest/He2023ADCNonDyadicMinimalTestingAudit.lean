/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCNonDyadicMinimalTesting

/-! Focused kernel audit for non-dyadic Lemma 4.7(ii). -/

open Bong HeADC2025NonDyadicSystem

#check HeADC2025NonDyadicTestingIndex
#check card_heADC2025NonDyadicTestingIndex_one
#check card_heADC2025NonDyadicTestingIndex_two
#check card_heADC2025NonDyadicTestingIndex_of_three_le
#check HeADC2025NonDyadicSystem.IsNUniversal
#check HeADC2025NonDyadicSystem.IsLiteralMinimalUniversalityTestingFamily
#check MinimalTestingLaws.nonDyadicTestingFamily_isUniversalityTestingFamily
#check MinimalTestingLaws.heADC2025Lemma47ii

#print axioms MinimalTestingLaws.nonDyadicTestingFamily_isUniversalityTestingFamily
#print axioms MinimalTestingLaws.heADC2025Lemma47ii
#print axioms card_heADC2025NonDyadicTestingIndex_one
#print axioms card_heADC2025NonDyadicTestingIndex_two
#print axioms card_heADC2025NonDyadicTestingIndex_of_three_le
