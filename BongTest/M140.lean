/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019ExtremalDifference

/-!
# M140 Beli 2019, Lemma 5.6 extremal-difference smoke tests
-/

namespace BongTest.M140

open Bong

example {m n a c : Nat} {x : BeliOrderSequence m Int}
    {y : BeliOrderSequence n Int} (h : BeliOrderLE x y)
    (ha : a ≤ n) (haM : a < m) (hcA : c < a)
    (hc : BeliOrderSequence.IsFirstDifferenceAt x y c)
    (haeq : x.prefixSum a = y.prefixSum a) :
    Even (a - c) ∧ x.entryOrZero c < y.entryOrZero c := by
  have hp := h.firstDifference_profile a c ha haM hcA hc haeq
  exact ⟨hp.1, hp.2.1⟩

example {n b d : Nat} {x y : BeliOrderSequence n Int}
    (h : BeliOrderLE x y) (hb0 : 0 < b) (hbd : b ≤ d)
    (hd : BeliOrderSequence.IsLastDifferenceAt x y d)
    (hbeq : x.suffixSum b = y.suffixSum b) :
    Even (d - (b - 1)) ∧ x.entryOrZero d < y.entryOrZero d := by
  have hp := h.lastDifference_profile b d hb0 hbd hd hbeq
  exact ⟨hp.1, hp.2.1⟩

#print axioms Bong.BeliOrderLE.firstDifference_profile
#print axioms Bong.BeliOrderLE.lastDifference_profile

end BongTest.M140
