/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Papers.He2023ADC
import BongTest.Q2

/-! Concrete nonvacuity checks for the binary boundary over `ℚ_[2]`. -/

namespace BongTest.He2023ADCQuaternaryBoundaryQ2

open Bong Bong.Dyadic Bong.BONG.GoodBONG

noncomputable section

example : Lattice.IsNADC.{0, 0, 0}
    (heADCQuaternaryBoundaryForm (K := ℚ_[2]))
    (heADCQuaternaryBoundaryLattice (K := ℚ_[2])) 2 :=
  heADCQuaternaryBoundaryCandidate_is2ADC

example : ¬ Lattice.IsOMaximal
    (heADCQuaternaryBoundaryForm (K := ℚ_[2]))
    (heADCQuaternaryBoundaryLattice (K := ℚ_[2])) :=
  heADCQuaternaryBoundaryCandidate_not_isOMaximal

example : ¬ HeADC2025Lemma68ivBinaryStatement (K := ℚ_[2]) :=
  not_heADC2025Lemma68ivBinaryStatement

#print axioms Bong.BONG.GoodBONG.not_heADC2025Lemma68ivBinaryStatement
#print axioms BongTest.Q2.q2DyadicContext

end

end BongTest.He2023ADCQuaternaryBoundaryQ2
