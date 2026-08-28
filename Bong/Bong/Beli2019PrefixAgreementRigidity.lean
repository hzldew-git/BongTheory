/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019EqualityPropagation
import Bong.Bong.Beli2019PrefixExtension

/-!
# Prefix rigidity for Beli's order relation

This file converts the two parity classes of Lemma 5.6(i) into coordinatewise
prefix agreement.  It is the combinatorial final step used in the proof of
Beli (2019), Lemma 5.17(ii).
-/

namespace Bong

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- If a Beli-ordered pair has the same sum through a positive prefix and
the same final entry of that prefix, then every entry in the prefix agrees.
The final entry supplies the second parity class missing from the two-step
prefix-sum propagation of Lemma 5.6(i). -/
theorem prefixAgreement_of_prefixSum_eq_of_last_eq
    {n : Nat} {x y : BeliOrderSequence n Gamma}
    (h : BeliOrderLE x y) (p : Nat) (hp : p ≤ n)
    (hsum : x.prefixSum p = y.prefixSum p)
    (hlast : 0 < p →
      x.entryOrZero (p - 1) = y.entryOrZero (p - 1)) :
    x.PrefixAgreement y p := by
  by_cases hpzero : p = 0
  · subst p
    exact
      { leftBound := by omega
        rightBound := by omega
        entry_eq := by
          intro j hj
          omega }
  have hppos : 0 < p := Nat.pos_of_ne_zero hpzero
  have hpred : p = (p - 1) + 1 := by omega
  have hsumPred : x.prefixSum (p - 1) = y.prefixSum (p - 1) := by
    have hsum' := hsum
    rw [hpred, x.prefixSum_succ, y.prefixSum_succ,
      hlast hppos] at hsum'
    exact add_right_cancel hsum'
  have hprefix (k : Nat) (hk : k ≤ p) :
      x.prefixSum k = y.prefixSum k := by
    rcases Nat.even_or_odd (p - k) with heven | hodd
    · exact h.prefixSum_eq_of_evenGap p k hp hk heven hsum
    · have hkPred : k ≤ p - 1 := by
        rcases hodd with ⟨r, hr⟩
        omega
      have hevenPred : Even ((p - 1) - k) := by
        rcases hodd with ⟨r, hr⟩
        refine ⟨r, ?_⟩
        omega
      exact h.prefixSum_eq_of_evenGap (p - 1) k
        (by omega) hkPred hevenPred hsumPred
  refine
    { leftBound := hp
      rightBound := hp
      entry_eq := ?_ }
  intro j hj
  have hbefore := hprefix j (by omega)
  have hafter := hprefix (j + 1) (by omega)
  rw [x.prefixSum_succ, y.prefixSum_succ, hbefore] at hafter
  exact add_left_cancel hafter

end BeliOrderLE

end Bong
