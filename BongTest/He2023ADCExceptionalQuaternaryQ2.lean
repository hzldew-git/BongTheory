/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Papers.He2023ADC
import BongTest.Q2

/-! Concrete checks for He (2025), Lemma 6.12 over `ℚ_[2]`. -/

namespace BongTest.He2023ADCExceptionalQuaternaryQ2

open Bong Bong.Dyadic Bong.BONG.GoodBONG

noncomputable section

example : Lattice.IsNADC.{0, 0, 0}
    (heADCExceptionalQuaternaryForm (K := ℚ_[2]))
    (heADCExceptionalQuaternaryLattice (K := ℚ_[2])) 2 :=
  heADCExceptionalQuaternaryCandidate_is2ADC

example : ¬ Lattice.IsNADC.{0, 0, 0}
    (heADCExceptionalQuaternaryForm (K := ℚ_[2]))
    (heADCExceptionalQuaternaryLattice (K := ℚ_[2])) 3 :=
  heADCExceptionalQuaternaryCandidate_not_is3ADC

example : ¬ Lattice.IsOMaximal
    (heADCExceptionalQuaternaryForm (K := ℚ_[2]))
    (heADCExceptionalQuaternaryLattice (K := ℚ_[2])) :=
  heADCExceptionalQuaternaryCandidate_not_isOMaximal

#print axioms Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_is2ADC
#print axioms Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_not_is3ADC
#print axioms BongTest.Q2.q2DyadicContext

end

end BongTest.He2023ADCExceptionalQuaternaryQ2
