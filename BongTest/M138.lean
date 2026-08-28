/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrefixMinimum

/-!
# M138 Beli 2019, Lemma 5.6(i) minimum-formula smoke test
-/

namespace BongTest.M138

open Bong

example {m n a k : Nat} {x : BeliOrderSequence m Int}
    {y : BeliOrderSequence n Int} (h : BeliOrderLE x y)
    (ha : a ≤ n) (haM : a < m) (hk : k ≤ a) (hkN : k < n)
    (heven : Even (a - k))
    (haeq : x.prefixSum a = y.prefixSum a) :
    x.entry k (hkN.trans_le h.rank) =
      min (y.entry k hkN) (x.entry a haM) :=
  h.entry_eq_min_of_prefixSum_eq_of_evenGap
    a k ha haM hk hkN heven haeq

#print axioms Bong.BeliOrderLE.entryOrZero_eq_min_next_of_prefix_and_pair_eq
#print axioms Bong.BeliOrderLE.entry_eq_min_of_prefixSum_eq_of_evenGap

end BongTest.M138
