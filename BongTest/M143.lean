/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SecondOrderCriterion

/-!
# M143 Beli 2019, Corollary 5.9(i) order criterion smoke tests
-/

namespace BongTest.M143

open Bong

example {n k : Nat} {x y : BeliOrderSequence n Int}
    (h : BeliOrderLE x y) (hn : 2 ≤ n)
    (hplateau : y.IsMaximalInitialOddPlateau k)
    (htail : x.suffixSum 1 = y.suffixSum 1) :
    BeliOrderSequence.SecondOrderCriterion x y :=
  h.secondOrderCriterion k hn hplateau htail

#print axioms Bong.BeliOrderLE.secondOrderCriterion

end BongTest.M143
