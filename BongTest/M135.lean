/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderSumRigidity

/-!
# M135 Beli 2019, Lemma 5.5(ii)-(iii) smoke tests
-/

namespace BongTest.M135

open Bong

example {n d : Nat} {x y : BeliOrderSequence n Int}
    (h : BeliOrderLE x y) (hd : d ≤ n) :
    x.suffixLengthSum d ≤ y.suffixLengthSum d :=
  h.suffixLengthSum_le d hd

example {n : Nat} {x y : BeliOrderSequence n Int}
    (h : BeliOrderLE x y)
    (htotal : x.prefixSum n = y.prefixSum n) : x = y :=
  h.eq_of_totalPrefixSum_eq htotal

#print axioms Bong.BeliOrderLE.suffixLengthSum_le
#print axioms Bong.BeliOrderLE.eq_of_totalPrefixSum_eq
#print axioms
  Bong.BONG.GoodBONG.orderSequence_eq_of_representationOrderCondition_of_total_eq

end BongTest.M135
