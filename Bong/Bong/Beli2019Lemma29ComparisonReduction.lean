/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma29TargetReduction

/-!
# Beli (2019), Lemmas 2.7(iii) and 2.9: the comparison branch

When both crossing inequalities hold, Lemma 2.7(iii) replaces the interior
defect in `A'_i` by the comparison defect `d[a_(1,i)b_(1,i)]`.  If the
coefficient of that candidate is positive and condition (ii) bounds `A_i`
by the comparison defect, the replaced candidate is strictly larger than
`A_i` and can be deleted.  This is the branch of Lemma 2.9 used in
Lemma 9.3, Case 2(b).
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- The second application of capped Lemma 1.4(c) in Lemma 2.7(iii).
Multiplying the right prefix by its next two entries changes the sign from
`-1` to `1` inside an outer minimum. -/
theorem shiftedTruncatedPrefixDefect_right_add_two_neg_replace_of_cut_le
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i j : Nat) (y : ℚ) (z : WithTop ℚ)
    (hcut : z ≤ (y : WithTop ℚ) +
      b.truncatedPrefixDefect b (-1) j (j + 2)) :
    min ((y : WithTop ℚ) +
        a.truncatedPrefixDefect b (-1) i j) z =
      min ((y : WithTop ℚ) +
        a.truncatedPrefixDefect b 1 i (j + 2)) z := by
  have hforward :
      min (b.truncatedPrefixDefect b (-1) j (j + 2))
          (a.truncatedPrefixDefect b (-1) i j) ≤
        a.truncatedPrefixDefect b 1 i (j + 2) := by
    have h := a.truncatedPrefixDefect_domination b b
      (-1) (-1) i j (j + 2)
    simpa only [neg_mul_neg, one_mul, min_comm] using h
  have hreverse :
      min (b.truncatedPrefixDefect b (-1) j (j + 2))
          (a.truncatedPrefixDefect b 1 i (j + 2)) ≤
        a.truncatedPrefixDefect b (-1) i j := by
    have h := a.truncatedPrefixDefect_domination b b
      1 (-1) i (j + 2) j
    rw [b.truncatedPrefixDefect_comm b (-1) (j + 2) j] at h
    simpa only [one_mul, min_comm] using h
  exact withTop_shifted_min_eq_of_domination y z
    (b.truncatedPrefixDefect b (-1) j (j + 2))
    (a.truncatedPrefixDefect b (-1) i j)
    (a.truncatedPrefixDefect b 1 i (j + 2))
    hforward hreverse hcut

/-- The Lemma 2.7(iii) replacement candidate
`R_(i+1)+R_(i+2)-S_(i-1)-S_i+d[a_(1,i)b_(1,i)]`. -/
noncomputable def representationSecondaryComparisonDefect
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) : WithTop ℚ :=
  (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
    a.truncatedPrefixDefect b 1 i.val i.val

set_option maxHeartbeats 800000 in
/-- Lemma 2.7(iii), in the normal form for Definition 5's `A'_i`. -/
theorem representationAlphaPrime_eq_min_primary_comparison
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hleft : b.order ⟨i.val - 2, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val, i.lt_large⟩)
    (hright : b.order ⟨i.val - 1, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val + 1, hi.2⟩) :
    a.representationAlphaPrime b i =
      min (a.representationPrimaryDefect b i)
        (a.representationSecondaryComparisonDefect b i hi) := by
  let shift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  have hprevious := by
    letI : Beli2006AlphaLaws.{u, v} K := alphaV
    exact a.representationAlphaPrime_eq_min_primary_previous b i hi hleft
  have hcut := by
    letI : Beli2006AlphaLaws.{u, w} K := alphaW
    exact a.representationPrimaryDefect_le_secondaryTargetAdjacentCut
      b i hi hright
  have hreplace :=
    a.shiftedTruncatedPrefixDefect_right_add_two_neg_replace_of_cut_le b
      i.val (i.val - 2) shift (a.representationPrimaryDefect b i) (by
        simpa only [shift, show i.val - 2 + 2 = i.val by omega] using hcut)
  calc
    a.representationAlphaPrime b i =
        min (a.representationPrimaryDefect b i)
          (a.representationSecondaryPreviousDefect b i hi) := hprevious
    _ = min (a.representationSecondaryPreviousDefect b i hi)
          (a.representationPrimaryDefect b i) := min_comm _ _
    _ = min ((shift : WithTop ℚ) +
          a.truncatedPrefixDefect b 1 i.val i.val)
          (a.representationPrimaryDefect b i) := by
      simpa only [representationSecondaryPreviousDefect, shift,
        show i.val - 2 + 2 = i.val by omega] using hreplace
    _ = min (a.representationPrimaryDefect b i)
          (a.representationSecondaryComparisonDefect b i hi) := by
      rw [min_comm]
      rfl

/-- A positive translate of `D` cannot realize a minimum which is at most
`D`.  This is the order-theoretic step in Lemma 2.9. -/
theorem min_shift_eq_left_of_pos_of_min_le
    (z D : WithTop ℚ) (y : ℚ) (hy : 0 < y)
    (hmin : min z ((y : WithTop ℚ) + D) ≤ D) :
    min z ((y : WithTop ℚ) + D) = z := by
  by_cases htop : D = ⊤
  · simp [htop]
  · have hDlt : D < (y : WithTop ℚ) + D := by
      rw [← WithTop.coe_untop D htop, ← WithTop.coe_add]
      exact WithTop.coe_lt_coe.mpr (by linarith)
    have hnotSecondary : ¬(y : WithTop ℚ) + D ≤
        min z ((y : WithTop ℚ) + D) := by
      intro hle
      exact (not_le_of_gt hDlt) (hle.trans hmin)
    have hz : z ≤ (y : WithTop ℚ) + D := by
      by_contra hnot
      have hsecondaryLe : (y : WithTop ℚ) + D ≤ z := le_of_not_ge hnot
      have heq : min z ((y : WithTop ℚ) + D) =
          (y : WithTop ℚ) + D := min_eq_right hsecondaryLe
      apply hnotSecondary
      rw [heq]
    exact min_eq_left hz

set_option maxHeartbeats 800000 in
/-- Lemma 2.9 in the double-crossing case.  Under condition (ii), a
positive secondary order shift makes the secondary comparison candidate
redundant, leaving exactly the half-gap and primary candidates. -/
theorem representationAlpha_eq_min_halfGap_primary_of_comparison
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hleft : b.order ⟨i.val - 2, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val, i.lt_large⟩)
    (hright : b.order ⟨i.val - 1, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val + 1, hi.2⟩)
    (hshift : 0 <
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩)
    (hcomparison : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b 1 i.val i.val) :
    a.representationAlpha b i =
      min (a.representationHalfGap b i)
        (a.representationPrimaryDefect b i) := by
  let shift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let D := a.truncatedPrefixDefect b 1 i.val i.val
  let z := min (a.representationHalfGap b i)
    (a.representationPrimaryDefect b i)
  have hnormal : a.representationAlpha b i =
      min z ((shift : WithTop ℚ) + D) := by
    have hprime :=
      a.representationAlphaPrime_eq_min_primary_comparison
        (alphaV := alphaV) (alphaW := alphaW) b i hi hleft hright
    rw [a.representationAlpha_eq_min_halfGap_prime b i, hprime]
    simp only [representationSecondaryComparisonDefect, shift, D, z,
      min_assoc]
  have hshiftQ : (0 : ℚ) < shift := by
    dsimp only [shift]
    exact_mod_cast hshift
  have hminLe : min z ((shift : WithTop ℚ) + D) ≤ D := by
    rw [← hnormal]
    exact hcomparison
  rw [hnormal, min_shift_eq_left_of_pos_of_min_le z D shift hshiftQ hminLe]

end BONG.GoodBONG

end Bong
