/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderGap

/-!
# M136 Beli 2019, Lemma 5.5(iv) smoke tests
-/

namespace BongTest.M136

open Bong

example {n i j : Nat} {x y : BeliOrderSequence n Int}
    (h : BeliOrderLE x y) {κ : Int}
    (htotal : x.prefixSum n + κ = y.prefixSum n)
    (hij : i ≤ j) (hj : j ≤ n) :
    y.segmentSum i j ≤ x.segmentSum i j + κ :=
  h.segmentSum_le_add_totalGap htotal i j hij hj

example {n i j : Nat} {x y : BeliOrderSequence n Int}
    (h : BeliOrderLE x y) {κ : Int}
    (htotal : x.prefixSum n + κ = y.prefixSum n)
    (hij : i ≤ j) (hj : j ≤ n) :
    x.segmentSum i j + κ = y.segmentSum i j ↔
      x.prefixSum i = y.prefixSum i ∧ x.suffixSum j = y.suffixSum j :=
  h.segmentSum_add_totalGap_eq_iff htotal i j hij hj

#print axioms Bong.BeliOrderLE.segmentSum_le_add_totalGap
#print axioms Bong.BeliOrderLE.segmentSum_add_totalGap_eq_iff
#print axioms Bong.BeliOrderLE.totalGap_nonneg

end BongTest.M136
