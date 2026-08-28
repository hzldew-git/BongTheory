/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderReconstruction

/-!
# M142 Beli 2019, Corollary 5.8 smoke tests
-/

namespace BongTest.M142

open Bong

example {n k l : Nat} {x y : BeliOrderSequence n Int}
    (h : BeliOrderLE x y)
    (hplateau : y.IsMaximalInitialOddPlateau k)
    (hthreshold : BeliOrderSequence.IsMaximalTailOddBelowFirst x y l)
    (htail : x.suffixSum 1 = y.suffixSum 1) :
    BeliOrderSequence.NormGeneratorOrderFormula x y l :=
  h.normGeneratorOrderFormula k l hplateau hthreshold htail

#print axioms Bong.BeliOrderLE.normGeneratorOrderFormula

end BongTest.M142
