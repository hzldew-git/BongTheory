/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenLeftCandidates

/-!
# Beli (2019), Lemma 7.9(ii), case 3: secondary-candidate arithmetic

The last candidate contains an adjacent order sum and a mixed prefix
defect.  This file separates the three numerical configurations used in
the paper: equal adjacent sums, and target sums one or two units larger.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Equal adjacent order sums and a two-unit mixed-prefix comparison give
the required secondary-candidate comparison. -/
theorem representationSecondaryDefect_le_add_two_of_orderSum_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hsum : b.order ⟨i.val, i.lt_large⟩ +
        b.order ⟨i.val + 1, hi.2⟩ =
      a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hi.2⟩)
    (hprefix : b.truncatedPrefixDefect c 1 (i.val + 2)
        (i.val - 2) ≤
      a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) +
        ((2 : ℚ) : WithTop ℚ)) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((2 : ℚ) : WithTop ℚ) := by
  unfold representationSecondaryDefect
  rw [hsum]
  have h := add_le_add_right hprefix
    ((((a.order ⟨i.val, i.lt_large⟩ +
      a.order ⟨i.val + 1, hi.2⟩ -
      c.order ⟨i.val - 2, by omega⟩ -
      c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ))
  simpa only [add_assoc] using h

/-- If the target adjacent sum is one unit larger, a target prefix bounded
by one is still within two units of every nonnegative source prefix. -/
theorem representationSecondaryDefect_le_add_two_of_orderSum_eq_add_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hsum : b.order ⟨i.val, i.lt_large⟩ +
        b.order ⟨i.val + 1, hi.2⟩ =
      a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hi.2⟩ + 1)
    (htarget : b.truncatedPrefixDefect c 1 (i.val + 2)
      (i.val - 2) ≤ ((1 : ℚ) : WithTop ℚ))
    (hsource : 0 ≤ a.truncatedPrefixDefect c 1 (i.val + 2)
      (i.val - 2)) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((2 : ℚ) : WithTop ℚ) := by
  have hcoefficientInt :
      b.order ⟨i.val, i.lt_large⟩ +
          b.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
          c.order ⟨i.val - 1, by omega⟩ =
        (a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
          c.order ⟨i.val - 1, by omega⟩) + 1 := by
    omega
  have hcoefficient :
      (((b.order ⟨i.val, i.lt_large⟩ +
        b.order ⟨i.val + 1, hi.2⟩ -
        c.order ⟨i.val - 2, by omega⟩ -
        c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) =
        (((a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          ((1 : ℚ) : WithTop ℚ) := by
    exact_mod_cast hcoefficientInt
  unfold representationSecondaryDefect
  rw [hcoefficient]
  let coefficient : WithTop ℚ :=
    (((a.order ⟨i.val, i.lt_large⟩ +
      a.order ⟨i.val + 1, hi.2⟩ -
      c.order ⟨i.val - 2, by omega⟩ -
      c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ)
  change (coefficient + 1) +
      b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) ≤
    (coefficient +
      a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2)) + 2
  calc
    _ ≤ (coefficient + 1) + 1 := by
      exact add_le_add_right htarget _
    _ = coefficient + 2 := by
      rw [add_assoc]
      norm_num
    _ ≤ (coefficient +
        a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2)) + 2 := by
      apply add_le_add_left
      exact le_add_of_nonneg_right hsource

/-- If the target adjacent sum is two units larger, an unshifted
mixed-prefix comparison supplies exactly the required two-unit bound. -/
theorem representationSecondaryDefect_le_add_two_of_orderSum_eq_add_two
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hsum : b.order ⟨i.val, i.lt_large⟩ +
        b.order ⟨i.val + 1, hi.2⟩ =
      a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hi.2⟩ + 2)
    (hprefix : b.truncatedPrefixDefect c 1 (i.val + 2)
        (i.val - 2) ≤
      a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2)) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((2 : ℚ) : WithTop ℚ) := by
  have hcoefficientInt :
      b.order ⟨i.val, i.lt_large⟩ +
          b.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
          c.order ⟨i.val - 1, by omega⟩ =
        (a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
          c.order ⟨i.val - 1, by omega⟩) + 2 := by
    omega
  have hcoefficient :
      (((b.order ⟨i.val, i.lt_large⟩ +
        b.order ⟨i.val + 1, hi.2⟩ -
        c.order ⟨i.val - 2, by omega⟩ -
        c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) =
        (((a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          ((2 : ℚ) : WithTop ℚ) := by
    exact_mod_cast hcoefficientInt
  unfold representationSecondaryDefect
  rw [hcoefficient]
  let coefficient : WithTop ℚ :=
    (((a.order ⟨i.val, i.lt_large⟩ +
      a.order ⟨i.val + 1, hi.2⟩ -
      c.order ⟨i.val - 2, by omega⟩ -
      c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ)
  change (coefficient + 2) +
      b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) ≤
    (coefficient +
      a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2)) + 2
  calc
    _ ≤ (coefficient + 2) +
        a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) :=
      add_le_add_right hprefix _
    _ = _ := by ac_rfl

/-- In the strict interior of the normalized left outer interval, the
adjacent source and target order sums agree. -/
theorem lemma79_even_leftOuter_secondary_le_add_two_of_prefix
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hfirst : O.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hbefore : i.val + 2 ≤ O.transition.lastZero)
    (hprefix : b.truncatedPrefixDefect c 1 (i.val + 2)
        (i.val - 2) ≤
      a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) +
        ((2 : ℚ) : WithTop ℚ)) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((2 : ℚ) : WithTop ℚ) := by
  rcases O.left_even_of_first_eq_zero hfirst with ⟨e, he⟩
  rcases hiEven with ⟨d, hd⟩
  have hpairParity : Even (O.transition.lastZero - i.val) :=
    ⟨e - d, by omega⟩
  have hpair := O.leftPairEq i.val hbefore hpairParity
  apply representationSecondaryDefect_le_add_two_of_orderSum_eq
    a b c i hi
  · rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hpair.symm
  · exact hprefix

end BONG.GoodBONG

end Bong
