/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019IndexPOrderArithmetic

/-!
# Beli (2019), Section 5.4: the proper exceptional block

In the proper unary subcase of the index-uniformizer calculation, the source
block has one lowered left endpoint and the target block has one raised right
endpoint.  Every other entry is the common scale order.  This file proves
that the comparison is coordinatewise, which is the first alternative in
condition 2.1(i).
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- A block of length `k + 2` whose left endpoint is `low` and whose other
entries are `middle`. -/
def loweredLeftEndpoint (low middle : Gamma) (hlm : low ≤ middle)
    (k : Nat) : BeliOrderSequence (k + 2) Gamma where
  value i := if i.val = 0 then low else middle
  twoStep := by
    intro i hi
    change (if i = 0 then low else middle) ≤
      (if i + 2 = 0 then low else middle)
    have hnext : i + 2 ≠ 0 := by omega
    rw [if_neg hnext]
    by_cases hi0 : i = 0
    · rw [if_pos hi0]
      exact hlm
    · rw [if_neg hi0]

/-- A block of length `k + 2` whose right endpoint is `high` and whose other
entries are `middle`. -/
def raisedRightEndpoint (middle high : Gamma) (hmh : middle ≤ high)
    (k : Nat) : BeliOrderSequence (k + 2) Gamma where
  value i := if i.val = k + 1 then high else middle
  twoStep := by
    intro i hi
    change (if i = k + 1 then high else middle) ≤
      (if i + 2 = k + 1 then high else middle)
    have hcurrent : i ≠ k + 1 := by omega
    rw [if_neg hcurrent]
    by_cases hlast : i + 2 = k + 1
    · rw [if_pos hlast]
      exact hmh
    · rw [if_neg hlast]

omit [AddCommGroup Gamma] [IsOrderedAddMonoid Gamma] in
@[simp]
theorem loweredLeftEndpoint_entry (low middle : Gamma)
    (hlm : low ≤ middle) (k i : Nat) (hi : i < k + 2) :
    (loweredLeftEndpoint low middle hlm k).entry i hi =
      if i = 0 then low else middle :=
  rfl

omit [AddCommGroup Gamma] [IsOrderedAddMonoid Gamma] in
@[simp]
theorem raisedRightEndpoint_entry (middle high : Gamma)
    (hmh : middle ≤ high) (k i : Nat) (hi : i < k + 2) :
    (raisedRightEndpoint middle high hmh k).entry i hi =
      if i = k + 1 then high else middle :=
  rfl

end BeliOrderSequence

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- The lowered-left block is below the raised-right block by the direct
coordinatewise branch of Beli's order relation. -/
theorem endpoint_raised_le {low middle high : Gamma}
    (hlm : low ≤ middle) (hmh : middle ≤ high) (k : Nat) :
    BeliOrderLE
      (BeliOrderSequence.loweredLeftEndpoint low middle hlm k)
      (BeliOrderSequence.raisedRightEndpoint middle high hmh k) where
  rank := le_rfl
  compare := by
    intro i hi
    left
    change (if i = 0 then low else middle) ≤
      (if i = k + 1 then high else middle)
    by_cases hi0 : i = 0
    · have hnotLast : i ≠ k + 1 := by omega
      rw [if_pos hi0, if_neg hnotLast]
      exact hlm
    · by_cases hlast : i = k + 1
      · rw [if_neg hi0, if_pos hlast]
        exact hmh
      · rw [if_neg hi0, if_neg hlast]

/-- The numerical proper block in Section 5.4: the source begins at `r - 2`,
the common middle order is `r - 1`, and the target ends at `r`. -/
theorem indexP_unary_proper_block_le (r : Int) (k : Nat) :
    BeliOrderLE
      (BeliOrderSequence.loweredLeftEndpoint
        (r - 2) (r - 1) (by omega) k)
      (BeliOrderSequence.raisedRightEndpoint
        (r - 1) r (by omega) k) :=
  endpoint_raised_le (by omega) (by omega) k

end BeliOrderLE

end Bong
