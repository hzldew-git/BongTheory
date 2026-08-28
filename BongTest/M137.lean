/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019EqualityPropagation

/-!
# M137 Beli 2019, Lemma 5.6 pair-equality smoke tests
-/

namespace BongTest.M137

open Bong

example {m n a k : Nat} {x : BeliOrderSequence m Int}
    {y : BeliOrderSequence n Int} (h : BeliOrderLE x y)
    (ha : a ≤ n) (hk : k + 2 ≤ a) (heven : Even (a - k))
    (haeq : x.prefixSum a = y.prefixSum a) :
    x.entryOrZero k + x.entryOrZero (k + 1) =
      y.entryOrZero k + y.entryOrZero (k + 1) :=
  h.entryPair_eq_of_prefixSum_eq_of_evenGap a k ha hk heven haeq

example {n b k : Nat} {x y : BeliOrderSequence n Int}
    (h : BeliOrderLE x y) (hbk : b ≤ k) (hk : k + 2 ≤ n)
    (heven : Even (k - b))
    (hbeq : x.suffixSum b = y.suffixSum b) :
    x.entryOrZero k + x.entryOrZero (k + 1) =
      y.entryOrZero k + y.entryOrZero (k + 1) :=
  h.entryPair_eq_of_suffixSum_eq_of_evenGap b k hbk hk heven hbeq

#print axioms Bong.BeliOrderLE.prefixSum_eq_of_evenGap
#print axioms Bong.BeliOrderLE.entryPair_eq_of_prefixSum_eq_of_evenGap
#print axioms Bong.BeliOrderLE.suffixSum_eq_of_evenGap
#print axioms Bong.BeliOrderLE.entryPair_eq_of_suffixSum_eq_of_evenGap

end BongTest.M137
