/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SuffixMaximum

/-!
# M139 Beli 2019, Lemma 5.6(ii) maximum-formula smoke test
-/

namespace BongTest.M139

open Bong

example {n b k : Nat} {x y : BeliOrderSequence n Int}
    (h : BeliOrderLE x y) (hb0 : 0 < b) (hbk : b - 1 ≤ k)
    (hk : k < n) (heven : Even (k - (b - 1)))
    (hbeq : x.suffixSum b = y.suffixSum b) :
    y.entryOrZero k = max (x.entryOrZero k) (y.entryOrZero (b - 1)) :=
  h.entryOrZero_eq_max_of_suffixSum_eq_of_evenGap
    b k hb0 hbk hk heven hbeq

#print axioms Bong.BeliOrderLE.entryOrZero_eq_max_previous_of_suffix_and_pair_eq
#print axioms Bong.BeliOrderLE.entryOrZero_eq_max_of_suffixSum_eq_of_evenGap

end BongTest.M139
