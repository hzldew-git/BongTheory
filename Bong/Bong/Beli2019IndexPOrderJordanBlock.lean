/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019IndexPOrderEndpoints

/-!
# Beli (2019), Section 5.4: comparison inside a common Jordan block

Inside a Jordan component, Lemma 2.13 writes the orders as an alternating
pair.  For the source and target of an index-uniformizer inclusion these
pairs have the same sum `2r`, while the first source entry is at most the
first target entry.  This is exactly the dichotomy in condition 2.1(i).
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- An odd-length sequence obtained by repeating the pair `(first, second)`
and ending with `first`. -/
def alternatingPair (first second : Gamma) (k : Nat) :
    BeliOrderSequence (2 * k + 1) Gamma where
  value i := if i.val % 2 = 0 then first else second
  twoStep := by
    intro i hi
    change (if i % 2 = 0 then first else second) ≤
      (if (i + 2) % 2 = 0 then first else second)
    have hmod : (i + 2) % 2 = i % 2 := by omega
    rw [hmod]

omit [AddCommGroup Gamma] [IsOrderedAddMonoid Gamma] in
@[simp]
theorem alternatingPair_entry (first second : Gamma) (k i : Nat)
    (hi : i < 2 * k + 1) :
    (alternatingPair first second k).entry i hi =
      if i % 2 = 0 then first else second :=
  rfl

end BeliOrderSequence

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Two alternating pairs of equal total are ordered whenever their first
entries are ordered. -/
theorem alternatingPair_le {sourceFirst sourceSecond targetFirst targetSecond : Gamma}
    (hfirst : sourceFirst ≤ targetFirst)
    (hsum : sourceFirst + sourceSecond = targetFirst + targetSecond)
    (k : Nat) :
    BeliOrderLE
      (BeliOrderSequence.alternatingPair sourceFirst sourceSecond k)
      (BeliOrderSequence.alternatingPair targetFirst targetSecond k) where
  rank := le_rfl
  compare := by
    intro i hi
    by_cases heven : i % 2 = 0
    · left
      simp only [BeliOrderSequence.alternatingPair_entry, heven, if_pos]
      exact hfirst
    · have hodd : i % 2 = 1 := by omega
      have hi0 : 0 < i := by omega
      have hiNext : i + 1 < 2 * k + 1 := by omega
      refine Or.inr ⟨hi0, hiNext, ?_⟩
      have hprevious : (i - 1) % 2 = 0 := by omega
      have hnext : (i + 1) % 2 = 0 := by omega
      simp only [BeliOrderSequence.alternatingPair_entry, hodd,
        hprevious, hnext, one_ne_zero, if_false, if_true]
      exact ((add_comm sourceSecond sourceFirst).trans hsum).le

/-- The common-Jordan-block calculation in Section 5.4.  The two alternating
pairs are `(v', 2r-v')` and `(v, 2r-v)`. -/
theorem indexP_common_jordan_block_le
    {sourceNorm targetNorm scale : Int}
    (hnorm : sourceNorm ≤ targetNorm) (k : Nat) :
    BeliOrderLE
      (BeliOrderSequence.alternatingPair
        sourceNorm (2 * scale - sourceNorm) k)
      (BeliOrderSequence.alternatingPair
        targetNorm (2 * scale - targetNorm) k) := by
  apply alternatingPair_le hnorm
  omega

end BeliOrderLE

end Bong
