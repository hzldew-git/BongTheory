/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019NormGeneratorOrders

/-!
# M141 Beli 2019, Lemma 5.7 order-profile smoke tests
-/

namespace BongTest.M141

open Bong

example {n k : Nat} {x y : BeliOrderSequence n Int}
    (h : BeliOrderLE x y)
    (hplateau : y.IsMaximalInitialOddPlateau k)
    (htail : x.suffixSum 1 = y.suffixSum 1) :
    BeliOrderSequence.NormGeneratorOrderProfile x y k :=
  h.normGeneratorOrderProfile k hplateau htail

#print axioms Bong.BeliOrderLE.normGeneratorOrderProfile

end BongTest.M141
