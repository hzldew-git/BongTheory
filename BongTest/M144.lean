/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MaximalIndices

/-!
# M144 Beli 2019, canonical Section 5 indices smoke tests
-/

namespace BongTest.M144

open Bong

example {n : Nat} (y : BeliOrderSequence n Int) (hn : 0 < n) :
    y.IsMaximalInitialOddPlateau (y.maximalInitialOddPlateauIndex hn) :=
  y.maximalInitialOddPlateauIndex_spec hn

example {n : Nat} (x y : BeliOrderSequence n Int) (hn : 0 < n) :
    BeliOrderSequence.IsMaximalTailOddBelowFirst x y
      (x.maximalTailOddBelowFirstIndex y) :=
  x.maximalTailOddBelowFirstIndex_spec y hn

#print axioms Bong.BeliOrderSequence.maximalInitialOddPlateauIndex_spec
#print axioms Bong.BeliOrderSequence.maximalTailOddBelowFirstIndex_spec

end BongTest.M144
