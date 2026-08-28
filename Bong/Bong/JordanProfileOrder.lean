/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemmas45To47

/-!
# Finite arithmetic for Jordan norm profiles

This file develops the finite-minimum calculation behind the invariant
`ord n(L^s)`.  It is deliberately independent of lattices: a Jordan family
is represented only by its scale orders and component norm orders.
-/

namespace Bong.JordanProfileOrder

open scoped BigOperators

/-- The alternating order attached to one Jordan component at a local
zero-based coordinate. -/
def localOrder (scale effective : Int) (i : Nat) : Int :=
  if scale = effective then scale
  else if Even i then effective else 2 * scale - effective

@[simp]
theorem localOrder_of_proper (scale : Int) (i : Nat) :
    localOrder scale scale i = scale := by
  simp [localOrder]

theorem localOrder_of_even {scale effective : Int} {i : Nat}
    (hne : scale ≠ effective) (hi : Even i) :
    localOrder scale effective i = effective := by
  simp [localOrder, hne, hi]

theorem localOrder_of_odd {scale effective : Int} {i : Nat}
    (hne : scale ≠ effective) (hi : ¬Even i) :
    localOrder scale effective i = 2 * scale - effective := by
  simp [localOrder, hne, hi]

/-- Shifting the local coordinate by an even number does not change the
alternating order.  This is the combinatorial core of concatenating two
improper equal-scale Jordan components. -/
theorem localOrder_add_left_of_even {scale effective : Int} {offset i : Nat}
    (hoffset : Even offset) :
    localOrder scale effective (offset + i) = localOrder scale effective i := by
  by_cases hproper : scale = effective
  · subst effective
    simp
  · simp [localOrder, hproper, Nat.even_add, hoffset]

/-- The alternating local order is two-periodic. -/
theorem localOrder_add_two (scale effective : Int) (i : Nat) :
    localOrder scale effective (i + 2) =
      localOrder scale effective i := by
  have htwo : Even (2 : Nat) := by norm_num
  simpa only [Nat.add_comm] using
    (localOrder_add_left_of_even
      (scale := scale) (effective := effective) (i := i) htwo)

/-- A proper component has constant local order, while an improper component
can be concatenated across an even-rank boundary. -/
theorem localOrder_add_left_of_proper_or_even
    {scale effective : Int} {offset i : Nat}
    (hboundary : scale = effective ∨ Even offset) :
    localOrder scale effective (offset + i) = localOrder scale effective i := by
  rcases hboundary with hproper | hoffset
  · subst effective
    simp
  · exact localOrder_add_left_of_even hoffset

theorem localOrder_even_of_scale_le {scale effective : Int} {i : Nat}
    (hscale : scale ≤ effective) (hi : Even i) :
    localOrder scale effective i = effective := by
  by_cases hproper : scale = effective
  · subst effective
    simp
  · exact localOrder_of_even hproper hi

theorem localOrder_odd_of_scale_le {scale effective : Int} {i : Nat}
    (hscale : scale ≤ effective) (hi : ¬Even i) :
    localOrder scale effective i = 2 * scale - effective := by
  by_cases hproper : scale = effective
  · subst effective
    simp [localOrder]
    omega
  · exact localOrder_of_odd hproper hi

/-- Every consecutive even/odd pair in one component has sum twice the
scale order, including the proper case. -/
theorem localOrder_even_add_next {scale effective : Int} {i : Nat}
    (hi : Even i) :
    localOrder scale effective i +
      localOrder scale effective (i + 1) = 2 * scale := by
  by_cases hproper : scale = effective
  · subst effective
    simp [localOrder]
    omega
  · have hodd : ¬Even (i + 1) := by
      intro hnext
      rcases hi with ⟨k, hk⟩
      rcases hnext with ⟨l, hl⟩
      omega
    rw [localOrder_of_even hproper hi,
      localOrder_of_odd hproper hodd]
    omega

/-- Every consecutive odd/even pair also has sum twice the scale. -/
theorem localOrder_previous_add_odd {scale effective : Int} {i : Nat}
    (hi : ¬Even i) (hi0 : 0 < i) :
    localOrder scale effective (i - 1) +
      localOrder scale effective i = 2 * scale := by
  have heven : Even (i - 1) := by
    rcases Nat.even_or_odd i with h | h
    · exact (hi h).elim
    · rcases h with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega
  have hnext : i - 1 + 1 = i := by omega
  simpa only [hnext] using
    (localOrder_even_add_next (scale := scale)
      (effective := effective) heven)

/-- Sum of the local Jordan orders strictly before a local coordinate. -/
def localPrefixSum (scale effective : Int) (length : Nat) : Int :=
  ∑ i ∈ Finset.range length, localOrder scale effective i

theorem localPrefixSum_add_two (scale effective : Int) (length : Nat) :
    localPrefixSum scale effective (length + 2) =
      localPrefixSum scale effective length +
        (localOrder scale effective length +
          localOrder scale effective (length + 1)) := by
  simp only [localPrefixSum, Finset.sum_range_succ]
  abel

/-- A whole number of alternating pairs contributes twice the scale per
pair, independently of the effective norm order. -/
theorem localPrefixSum_two_mul (scale effective : Int) (k : Nat) :
    localPrefixSum scale effective (2 * k) =
      (2 * (k : Int)) * scale := by
  induction k with
  | zero => simp [localPrefixSum]
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega,
        localPrefixSum_add_two, ih,
        localOrder_even_add_next (scale := scale)
          (effective := effective) (show Even (2 * k) by simp)]
      push_cast
      ring

/-- At an even local boundary, the preceding partial volume depends only on
the scale and the boundary length. -/
theorem localPrefixSum_of_even (scale effective : Int) {length : Nat}
    (hlength : Even length) :
    localPrefixSum scale effective length = (length : Int) * scale := by
  rcases hlength with ⟨k, hk⟩
  have hlength' : length = 2 * k := by omega
  rw [hlength', localPrefixSum_two_mul]
  push_cast
  rfl

/-- If two effective norm orders are ordered and the target local entry is
exactly one above the source entry, that entry must have even local parity;
therefore the preceding local prefix sums agree.  This is the arithmetic
core of Lemma 5.13(ii). -/
theorem localPrefixSum_eq_of_effective_le_of_current_succ
    {scale sourceEffective targetEffective : Int} {i : Nat}
    (hsourceScale : scale ≤ sourceEffective)
    (htargetScale : scale ≤ targetEffective)
    (heffective : sourceEffective ≤ targetEffective)
    (hcurrent : localOrder scale targetEffective i =
      localOrder scale sourceEffective i + 1) :
    localPrefixSum scale sourceEffective i =
      localPrefixSum scale targetEffective i := by
  by_cases heven : Even i
  · rw [localPrefixSum_of_even scale sourceEffective heven,
      localPrefixSum_of_even scale targetEffective heven]
  · rw [localOrder_odd_of_scale_le htargetScale heven,
      localOrder_odd_of_scale_le hsourceScale heven] at hcurrent
    omega

/-- At a fixed component scale, equality of one local profile entry forces
equality of the effective norm parameters, and hence equality of every local
prefix sum.  We use the successor prefix below in Lemma 5.17(ii), where the
current BONG coordinate belongs to the common prefix. -/
theorem effective_eq_of_localOrder_eq
    {scale sourceEffective targetEffective : Int} {i : Nat}
    (hsourceScale : scale ≤ sourceEffective)
    (htargetScale : scale ≤ targetEffective)
    (hcurrent : localOrder scale sourceEffective i =
      localOrder scale targetEffective i) :
    sourceEffective = targetEffective := by
  by_cases heven : Even i
  · rw [localOrder_even_of_scale_le hsourceScale heven,
      localOrder_even_of_scale_le htargetScale heven] at hcurrent
    exact hcurrent
  · rw [localOrder_odd_of_scale_le hsourceScale heven,
      localOrder_odd_of_scale_le htargetScale heven] at hcurrent
    omega

theorem localPrefixSum_succ_eq_of_localOrder_eq
    {scale sourceEffective targetEffective : Int} {i : Nat}
    (hsourceScale : scale ≤ sourceEffective)
    (htargetScale : scale ≤ targetEffective)
    (hcurrent : localOrder scale sourceEffective i =
      localOrder scale targetEffective i) :
    localPrefixSum scale sourceEffective (i + 1) =
      localPrefixSum scale targetEffective (i + 1) := by
  rw [effective_eq_of_localOrder_eq hsourceScale htargetScale hcurrent]

/-- At the last coordinate of a component, decreasing the effective norm
still gives the required order comparison when every source-improper
component has even rank.  A strict failure at an even last coordinate would
force the rank to be both even and odd. -/
theorem localOrder_le_of_effective_ge_at_last
    {scale sourceEffective targetEffective : Int} {localIndex rank : Nat}
    (hsourceScale : scale ≤ sourceEffective)
    (htargetScale : scale ≤ targetEffective)
    (heffective : targetEffective ≤ sourceEffective)
    (hparity : scale < sourceEffective → Even rank)
    (hlast : localIndex + 1 = rank) :
    localOrder scale sourceEffective localIndex ≤
      localOrder scale targetEffective localIndex := by
  by_cases heven : Even localIndex
  · by_cases heq : sourceEffective = targetEffective
    · rw [heq]
    · have hstrict : scale < sourceEffective := by
        have htargetLt : targetEffective < sourceEffective :=
          lt_of_le_of_ne heffective (Ne.symm heq)
        exact htargetScale.trans_lt htargetLt
      rcases hparity hstrict with ⟨k, hk⟩
      rcases heven with ⟨l, hl⟩
      omega
  · rw [localOrder_odd_of_scale_le hsourceScale heven,
      localOrder_odd_of_scale_le htargetScale heven]
    omega

/-- The adjusted contribution is monotone in the component norm order. -/
theorem adjustedAt_mono_norm {t : Nat} {scale norm norm' : Fin t → Int}
    {r : Int} {j : Fin t} (h : norm j ≤ norm' j) :
    adjustedAt scale norm r j ≤ adjustedAt scale norm' r j := by
  unfold adjustedAt
  split <;> omega

/-- Taking the minimum of two norm orders before adjustment is the same as
taking the minimum after adjustment. -/
theorem adjustedAt_min_norm {t : Nat} (scale : Fin t → Int)
    (u v r : Int) (j : Fin t) :
    (if scale j < r then min u v + 2 * (r - scale j) else min u v) =
      min (if scale j < r then u + 2 * (r - scale j) else u)
        (if scale j < r then v + 2 * (r - scale j) else v) := by
  split <;> omega

/-- The effective norm is no larger than any adjusted component
contribution. -/
theorem effectiveAt_le {t : Nat} (scale norm : Fin t → Int)
    (anchor j : Fin t) (r : Int) :
    effectiveAt scale norm anchor r ≤ adjustedAt scale norm r j := by
  exact Finset.inf'_le (f := adjustedAt scale norm r)
    (Finset.mem_univ j)

/-- A common lower bound for all adjusted contributions is a lower bound for
the effective norm. -/
theorem le_effectiveAt {t : Nat} (scale norm : Fin t → Int)
    (anchor : Fin t) (r x : Int)
    (h : ∀ j, x ≤ adjustedAt scale norm r j) :
    x ≤ effectiveAt scale norm anchor r := by
  apply Finset.le_inf'
  intro j _
  exact h j

/-- If a component norm order dominates its scale order, its adjusted
contribution at target scale `r` also dominates `r`. -/
theorem target_le_adjustedAt {t : Nat}
    (scale norm : Fin t → Int) (r : Int) (j : Fin t)
    (hscaleNorm : scale j ≤ norm j) :
    r ≤ adjustedAt scale norm r j := by
  unfold adjustedAt
  split <;> omega

/-- If every component norm order dominates its scale order, the effective
norm order at target scale `r` also dominates `r`. -/
theorem target_le_effectiveAt {t : Nat}
    (scale norm : Fin t → Int) (anchor : Fin t) (r : Int)
    (hscaleNorm : ∀ j, scale j ≤ norm j) :
    r ≤ effectiveAt scale norm anchor r := by
  apply le_effectiveAt
  intro j
  exact target_le_adjustedAt scale norm r j (hscaleNorm j)

/-- The `anchor` only supplies a proof that the finite family is nonempty;
the resulting minimum is independent of it. -/
theorem effectiveAt_anchor_irrel {t : Nat} (scale norm : Fin t → Int)
    (a b : Fin t) (r : Int) :
    effectiveAt scale norm a r = effectiveAt scale norm b r := by
  apply le_antisymm
  · apply le_effectiveAt
    intro j
    exact effectiveAt_le scale norm a j r
  · apply le_effectiveAt
    intro j
    exact effectiveAt_le scale norm b j r

/-- Pointwise domination of adjusted component contributions passes to the
effective minimum. -/
theorem effectiveAt_mono {t : Nat}
    {scale norm scale' norm' : Fin t → Int}
    (anchor anchor' : Fin t) (r : Int)
    (h : ∀ j, adjustedAt scale norm r j ≤
      adjustedAt scale' norm' r j) :
    effectiveAt scale norm anchor r ≤
      effectiveAt scale' norm' anchor' r := by
  apply le_effectiveAt
  intro j
  exact (effectiveAt_le scale norm anchor j r).trans (h j)

/-- The same comparison with possibly different target scales. -/
theorem effectiveAt_mono_cross {t : Nat}
    {scale norm scale' norm' : Fin t → Int}
    (anchor anchor' : Fin t) (r r' : Int)
    (h : ∀ j, adjustedAt scale norm r j ≤
      adjustedAt scale' norm' r' j) :
    effectiveAt scale norm anchor r ≤
      effectiveAt scale' norm' anchor' r' := by
  apply le_effectiveAt
  intro j
  exact (effectiveAt_le scale norm anchor j r).trans (h j)

/-- If every component norm order dominates its scale order, increasing the
target scale can only increase an adjusted contribution. -/
theorem adjustedAt_mono_target {t : Nat}
    (scale norm : Fin t → Int)
    {r r' : Int} (hrr' : r ≤ r') (j : Fin t) :
    adjustedAt scale norm r j ≤ adjustedAt scale norm r' j := by
  unfold adjustedAt
  split <;> split <;> omega

/-- Raising the target from `r` to `r'` increases one adjusted contribution
by at most twice the target difference. -/
theorem adjustedAt_target_le_add_two_mul_sub {t : Nat}
    (scale norm : Fin t → Int) {r r' : Int} (hrr' : r ≤ r')
    (j : Fin t) :
    adjustedAt scale norm r' j ≤
      adjustedAt scale norm r j + 2 * (r' - r) := by
  unfold adjustedAt
  split <;> split <;> omega

/-- If the distinguished component is already below both target scales,
an adjusted-order bound at the larger target propagates back to the smaller
target.  The distinguished contribution drops with the maximal slope two,
whereas every other contribution drops with slope at most two. -/
theorem adjustedAt_le_of_le_at_larger_target {t : Nat}
    (scale norm : Fin t → Int) (distinguished j : Fin t)
    {r r' : Int} (hscale : scale distinguished < r)
    (hrr' : r ≤ r')
    (h : adjustedAt scale norm r' distinguished ≤
      adjustedAt scale norm r' j) :
    adjustedAt scale norm r distinguished ≤
      adjustedAt scale norm r j := by
  have hscale' : scale distinguished < r' := hscale.trans_le hrr'
  simp only [adjustedAt, if_pos hscale, if_pos hscale'] at h ⊢
  by_cases hj : scale j < r
  · have hj' : scale j < r' := hj.trans_le hrr'
    rw [if_pos hj]
    rw [if_pos hj'] at h
    omega
  · rw [if_neg hj]
    by_cases hj' : scale j < r'
    · rw [if_pos hj'] at h
      omega
    · rw [if_neg hj'] at h
      omega

/-- Variant allowing the smaller target to equal the distinguished scale. -/
theorem adjustedAt_le_of_le_at_larger_target_of_scale_le {t : Nat}
    (scale norm : Fin t → Int) (distinguished j : Fin t)
    {r r' : Int} (hscale : scale distinguished ≤ r)
    (hrr' : r ≤ r')
    (h : adjustedAt scale norm r' distinguished ≤
      adjustedAt scale norm r' j) :
    adjustedAt scale norm r distinguished ≤
      adjustedAt scale norm r j := by
  rcases hscale.lt_or_eq with hlt | heq
  · exact adjustedAt_le_of_le_at_larger_target
      scale norm distinguished j hlt hrr' h
  · rw [← heq] at hrr' ⊢
    unfold adjustedAt at h ⊢
    rw [if_neg (lt_irrefl _)]
    by_cases hEq : scale distinguished = r'
    · subst r'
      simpa only [if_neg (lt_irrefl _)] using h
    · have hd' : scale distinguished < r' := lt_of_le_of_ne hrr' hEq
      rw [if_pos hd'] at h
      by_cases hj : scale j < scale distinguished
      · have hj' : scale j < r' := hj.trans hd'
        rw [if_pos hj]
        rw [if_pos hj'] at h
        omega
      · rw [if_neg hj]
        by_cases hj' : scale j < r'
        · rw [if_pos hj'] at h
          omega
        · rw [if_neg hj'] at h
          omega

/-- Effective norm order is monotone in the target scale. -/
theorem effectiveAt_mono_target {t : Nat}
    (scale norm : Fin t → Int)
    (anchor anchor' : Fin t) {r r' : Int} (hrr' : r ≤ r') :
    effectiveAt scale norm anchor r ≤
      effectiveAt scale norm anchor' r' := by
  apply le_effectiveAt
  intro j
  exact (effectiveAt_le scale norm anchor j r).trans
    (adjustedAt_mono_target scale norm hrr' j)

/-- Effective norm order has the same slope-two upper bound in the target
scale as each adjusted component contribution. -/
theorem effectiveAt_target_le_add_two_mul_sub {t : Nat}
    (scale norm : Fin t → Int) (anchor anchor' : Fin t)
    {r r' : Int} (hrr' : r ≤ r') :
    effectiveAt scale norm anchor' r' ≤
      effectiveAt scale norm anchor r + 2 * (r' - r) := by
  obtain ⟨j, _hj, hjmin⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (Fin t)))
    ⟨anchor, Finset.mem_univ anchor⟩ (adjustedAt scale norm r)
  calc
    effectiveAt scale norm anchor' r' ≤ adjustedAt scale norm r' j :=
      effectiveAt_le scale norm anchor' j r'
    _ ≤ adjustedAt scale norm r j + 2 * (r' - r) :=
      adjustedAt_target_le_add_two_mul_sub scale norm hrr' j
    _ = effectiveAt scale norm anchor r + 2 * (r' - r) := by
      exact congrArg (fun x ↦ x + 2 * (r' - r)) hjmin.symm

/-- In two finite families which agree away from one distinguished index,
a strict inequality between their effective minima forces the smaller
minimum to be the distinguished contribution. -/
theorem effectiveAt_eq_distinguished_of_lt {t : Nat}
    (scale norm scale' norm' : Fin t → Int)
    (anchor anchor' distinguished : Fin t) (r : Int)
    (hcommon : ∀ j, j ≠ distinguished →
      adjustedAt scale norm r j = adjustedAt scale' norm' r j)
    (hlt : effectiveAt scale norm anchor r <
      effectiveAt scale' norm' anchor' r) :
    effectiveAt scale norm anchor r =
    adjustedAt scale norm r distinguished := by
  have hdist : adjustedAt scale norm r distinguished <
      effectiveAt scale' norm' anchor' r := by
    by_contra hnot
    have hlarge_le_dist : effectiveAt scale' norm' anchor' r ≤
        adjustedAt scale norm r distinguished := le_of_not_gt hnot
    have hlarge_le_small : effectiveAt scale' norm' anchor' r ≤
        effectiveAt scale norm anchor r := by
      apply le_effectiveAt
      intro j
      by_cases hj : j = distinguished
      · subst j
        exact hlarge_le_dist
      · have hlarge := effectiveAt_le scale' norm' anchor' j r
        rw [← hcommon j hj] at hlarge
        exact hlarge
    exact (not_le_of_gt hlt) hlarge_le_small
  apply le_antisymm
  · exact effectiveAt_le scale norm anchor distinguished r
  · apply le_effectiveAt
    intro j
    by_cases hj : j = distinguished
    · subst j
      exact le_rfl
    · have hlarge : effectiveAt scale' norm' anchor' r ≤
          adjustedAt scale' norm' r j :=
        effectiveAt_le scale' norm' anchor' j r
      rw [← hcommon j hj] at hlarge
      exact hdist.le.trans hlarge

/-- Reindexing a finite component family does not change its effective
minimum. -/
theorem effectiveAt_comp_equiv {s t : Nat}
    (scale norm : Fin t → Int) (e : Fin s ≃ Fin t)
    (anchor : Fin s) (oldAnchor : Fin t) (r : Int) :
    effectiveAt (scale ∘ e) (norm ∘ e) anchor r =
      effectiveAt scale norm oldAnchor r := by
  apply le_antisymm
  · apply le_effectiveAt
    intro j
    calc
      effectiveAt (scale ∘ e) (norm ∘ e) anchor r ≤
          adjustedAt (scale ∘ e) (norm ∘ e) r (e.symm j) :=
        effectiveAt_le _ _ anchor (e.symm j) r
      _ = adjustedAt scale norm r j := by
        simp [adjustedAt]
  · apply le_effectiveAt
    intro j
    calc
      effectiveAt scale norm oldAnchor r ≤
          adjustedAt scale norm r (e j) :=
        effectiveAt_le _ _ oldAnchor (e j) r
      _ = adjustedAt (scale ∘ e) (norm ∘ e) r j := by
        rfl

/-- The scale family obtained by deleting the second member of an adjacent
pair. -/
def mergeScale {t : Nat} (scale : Fin (t + 1) → Int)
    (k : Fin t) : Fin t → Int :=
  fun j ↦ scale (k.succ.succAbove j)

/-- The corresponding norm family: at the retained first position the two
old norm orders are replaced by their minimum. -/
def mergeNorm {t : Nat} (norm : Fin (t + 1) → Int)
    (k : Fin t) : Fin t → Int :=
  fun j ↦ if j = k then min (norm k.castSucc) (norm k.succ)
    else norm (k.succ.succAbove j)

@[simp]
theorem mergeScale_self {t : Nat} (scale : Fin (t + 1) → Int)
    (k : Fin t) :
    mergeScale scale k k = scale k.castSucc := by
  simp [mergeScale]

@[simp]
theorem mergeNorm_self {t : Nat} (norm : Fin (t + 1) → Int)
    (k : Fin t) :
    mergeNorm norm k k = min (norm k.castSucc) (norm k.succ) := by
  simp [mergeNorm]

@[simp]
theorem mergeNorm_of_ne {t : Nat} (norm : Fin (t + 1) → Int)
    (k j : Fin t) (hjk : j ≠ k) :
    mergeNorm norm k j = norm (k.succ.succAbove j) := by
  simp [mergeNorm, hjk]

/-- At the retained position, adjustment turns the merged norm into the
minimum of the two old adjusted contributions. -/
theorem adjustedAt_merge_self {t : Nat}
    (scale norm : Fin (t + 1) → Int) (k : Fin t)
    (heq : scale k.castSucc = scale k.succ) (r : Int) :
    adjustedAt (mergeScale scale k) (mergeNorm norm k) r k =
      min (adjustedAt scale norm r k.castSucc)
        (adjustedAt scale norm r k.succ) := by
  simp only [adjustedAt, mergeScale_self, mergeNorm_self]
  rw [← heq]
  exact adjustedAt_min_norm (fun _ : Fin t ↦ scale k.castSucc)
    (norm k.castSucc) (norm k.succ) r k

/-- Away from the retained position, adjustment is unchanged. -/
theorem adjustedAt_merge_of_ne {t : Nat}
    (scale norm : Fin (t + 1) → Int) (k j : Fin t)
    (hjk : j ≠ k) (r : Int) :
    adjustedAt (mergeScale scale k) (mergeNorm norm k) r j =
      adjustedAt scale norm r (k.succ.succAbove j) := by
  simp [adjustedAt, mergeScale, mergeNorm, hjk]

/-- Amalgamating two equal-scale neighbours does not change the effective
norm order at any target scale. -/
theorem effectiveAt_merge {t : Nat}
    (scale norm : Fin (t + 1) → Int) (k : Fin t)
    (heq : scale k.castSucc = scale k.succ)
    (anchor : Fin t) (oldAnchor : Fin (t + 1)) (r : Int) :
    effectiveAt (mergeScale scale k) (mergeNorm norm k) anchor r =
      effectiveAt scale norm oldAnchor r := by
  apply le_antisymm
  · apply le_effectiveAt
    intro j
    by_cases hjRemoved : j = k.succ
    · subst j
      calc
        effectiveAt (mergeScale scale k) (mergeNorm norm k) anchor r ≤
            adjustedAt (mergeScale scale k) (mergeNorm norm k) r k :=
          effectiveAt_le _ _ anchor k r
        _ = min (adjustedAt scale norm r k.castSucc)
              (adjustedAt scale norm r k.succ) :=
          adjustedAt_merge_self scale norm k heq r
        _ ≤ adjustedAt scale norm r k.succ := min_le_right _ _
    · let j' : Fin t := k.predAbove j
      have hjMap : k.succ.succAbove j' = j := by
        exact Fin.succ_succAbove_predAbove hjRemoved
      by_cases hjk : j' = k
      · have hjFirst : j = k.castSucc := by
          rw [← hjMap, hjk, Fin.succAbove_succ_self]
        subst j'
        calc
          effectiveAt (mergeScale scale k) (mergeNorm norm k) anchor r ≤
              adjustedAt (mergeScale scale k) (mergeNorm norm k) r k :=
            effectiveAt_le _ _ anchor k r
          _ = min (adjustedAt scale norm r k.castSucc)
                (adjustedAt scale norm r k.succ) :=
            adjustedAt_merge_self scale norm k heq r
          _ ≤ adjustedAt scale norm r j := by
            rw [hjFirst]
            exact min_le_left _ _
      · calc
          effectiveAt (mergeScale scale k) (mergeNorm norm k) anchor r ≤
              adjustedAt (mergeScale scale k) (mergeNorm norm k) r j' :=
            effectiveAt_le _ _ anchor j' r
          _ = adjustedAt scale norm r (k.succ.succAbove j') :=
            adjustedAt_merge_of_ne scale norm k j' hjk r
          _ = adjustedAt scale norm r j := by rw [hjMap]
  · apply le_effectiveAt
    intro j
    by_cases hjk : j = k
    · subst j
      rw [adjustedAt_merge_self scale norm k heq r]
      exact le_min
        (effectiveAt_le scale norm oldAnchor k.castSucc r)
        (effectiveAt_le scale norm oldAnchor k.succ r)
    · rw [adjustedAt_merge_of_ne scale norm k j hjk r]
      exact effectiveAt_le scale norm oldAnchor
        (k.succ.succAbove j) r

end Bong.JordanProfileOrder
