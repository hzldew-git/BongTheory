/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderSums

/-!
# M134 Beli 2019, Lemma 5.5(i) smoke tests
-/

namespace BongTest.M134

open Bong

example {m n k : Nat} {x : BeliOrderSequence m Int}
    {y : BeliOrderSequence n Int} (h : BeliOrderLE x y) (hk : k ≤ n) :
    x.prefixSum k ≤ y.prefixSum k :=
  h.prefixSum_le k hk

#print axioms Bong.BeliOrderSequence.prefixSum_add_two
#print axioms Bong.BeliOrderLE.prefixSum_le
#print axioms Bong.BONG.GoodBONG.orderPrefixSum_le_of_representationOrderCondition

end BongTest.M134
