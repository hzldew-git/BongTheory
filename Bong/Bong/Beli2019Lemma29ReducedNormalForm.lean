/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma29TargetReduction

/-!
# Beli (2019), Definition 6 and Remark 2.8

This file records the reduced invariant `\overline A_i` from Definition 6.
At an interior boundary it is the minimum of the half-gap, primary,
source-alpha, and target-alpha candidates.  The two remarks after the
definition remove one alpha candidate when the corresponding crossing
inequality holds.

These are formulae for the reduced invariant itself.  Lemma 2.9, which
identifies it with `A_i` under condition 2.1(ii), remains a separate result.
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

/-- Beli (2019), Definition 6: the reduced representation invariant
`\overline A_i` at an interior boundary. -/
noncomputable def representationAlphaReduced
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1) : WithTop ℚ :=
  min (a.representationHalfGap b i)
    (min (a.representationPrimaryDefect b i)
      (min (a.representationSecondarySourceAlpha b i hi)
        (a.representationSecondaryTargetAlpha b i hi hsmall)))

/-- Definition 6's primed reduced invariant, obtained from
`representationAlphaReduced` by omitting the half-gap candidate. -/
noncomputable def representationAlphaPrimeReduced
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1) : WithTop ℚ :=
  min (a.representationPrimaryDefect b i)
    (min (a.representationSecondarySourceAlpha b i hi)
      (a.representationSecondaryTargetAlpha b i hi hsmall))

/-- The unprimed reduced invariant has the same half-gap decomposition as
the original representation invariant. -/
theorem representationAlphaReduced_eq_min_halfGap_primeReduced
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1) :
    a.representationAlphaReduced b i hi hsmall =
      min (a.representationHalfGap b i)
        (a.representationAlphaPrimeReduced b i hi hsmall) := by
  rfl

/-- Remark 2.8: if `R_(i+1) ≥ S_(i-1)`, the source-alpha candidate is
no smaller than the primary candidate and can be deleted. -/
theorem representationPrimaryDefect_le_secondarySourceAlpha_of_cross
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hcross : b.order ⟨i.val - 2, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val, i.lt_large⟩) :
    a.representationPrimaryDefect b i ≤
      a.representationSecondarySourceAlpha b i hi := by
  let next : Fin m := ⟨i.val, by omega⟩
  let primaryShift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let sourceShift : ℚ :=
    ((2 * a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  have hdefect :
      a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) ≤
        (a.alphaValue next : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_leftCap b (-1)
      (i.val + 1) (i.val - 1)
    rw [a.prefixAlphaCap_of_internal (by omega) hi.2] at hcap
    simpa only [next, show i.val + 1 - 1 = i.val by omega] using hcap
  have hshift : primaryShift ≤ sourceShift := by
    dsimp only [primaryShift, sourceShift]
    norm_cast
    omega
  unfold representationPrimaryDefect representationSecondarySourceAlpha
  calc
    (((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) ≤
      (primaryShift : WithTop ℚ) +
        (a.alphaValue next : WithTop ℚ) := by
      simpa only [primaryShift] using add_le_add le_rfl hdefect
    _ ≤ (sourceShift : WithTop ℚ) +
        (a.alphaValue next : WithTop ℚ) :=
      add_le_add (by exact_mod_cast hshift) le_rfl
    _ = (((2 * a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        (a.alphaValue ⟨i.val, by omega⟩ : WithTop ℚ) := by
      rfl

/-- Remark 2.8, target form: if `R_(i+2) ≥ S_i`, the target-alpha
candidate is no smaller than the primary candidate. -/
theorem representationPrimaryDefect_le_secondaryTargetAlpha_of_cross_local
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1)
    (hcross : b.order ⟨i.val - 1, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val + 1, hi.2⟩) :
    a.representationPrimaryDefect b i ≤
      a.representationSecondaryTargetAlpha b i hi hsmall := by
  let previous : Fin n := ⟨i.val - 2, by omega⟩
  let primaryShift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let targetShift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      2 * b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  have hdefect :
      a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) ≤
        (b.alphaValue previous : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_rightCap b (-1)
      (i.val + 1) (i.val - 1)
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    simpa only [previous, show i.val - 1 - 1 = i.val - 2 by omega]
      using hcap
  have hshift : primaryShift ≤ targetShift := by
    dsimp only [primaryShift, targetShift]
    norm_cast
    omega
  unfold representationPrimaryDefect representationSecondaryTargetAlpha
  calc
    (((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) ≤
      (primaryShift : WithTop ℚ) +
        (b.alphaValue previous : WithTop ℚ) := by
      simpa only [primaryShift] using add_le_add le_rfl hdefect
    _ ≤ (targetShift : WithTop ℚ) +
        (b.alphaValue previous : WithTop ℚ) :=
      add_le_add (by exact_mod_cast hshift) le_rfl
    _ = (((a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hi.2⟩ -
        2 * b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        (b.alphaValue ⟨i.val - 2, by omega⟩ : WithTop ℚ) := by
      rfl

/-- Definition 6 after deleting the source-alpha candidate. -/
theorem representationAlphaReduced_eq_min_halfGap_primary_target_of_cross
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1)
    (hcross : b.order ⟨i.val - 2, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val, i.lt_large⟩) :
    a.representationAlphaReduced b i hi hsmall =
      min (a.representationHalfGap b i)
        (min (a.representationPrimaryDefect b i)
          (a.representationSecondaryTargetAlpha b i hi hsmall)) := by
  have hsource :=
    a.representationPrimaryDefect_le_secondarySourceAlpha_of_cross
      b i hi hcross
  unfold representationAlphaReduced
  have hinner :
      min (a.representationPrimaryDefect b i)
          (min (a.representationSecondarySourceAlpha b i hi)
            (a.representationSecondaryTargetAlpha b i hi hsmall)) =
        min (a.representationPrimaryDefect b i)
          (a.representationSecondaryTargetAlpha b i hi hsmall) := by
    rw [← min_assoc, min_eq_left hsource]
  rw [hinner]

/-- Definition 6 after deleting the target-alpha candidate. -/
theorem representationAlphaReduced_eq_min_halfGap_primary_source_of_cross
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1)
    (hcross : b.order ⟨i.val - 1, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val + 1, hi.2⟩) :
    a.representationAlphaReduced b i hi hsmall =
      min (a.representationHalfGap b i)
        (min (a.representationPrimaryDefect b i)
          (a.representationSecondarySourceAlpha b i hi)) := by
  have htarget :=
    a.representationPrimaryDefect_le_secondaryTargetAlpha_of_cross_local
      b i hi hsmall hcross
  unfold representationAlphaReduced
  have hinner :
      min (a.representationPrimaryDefect b i)
          (min (a.representationSecondarySourceAlpha b i hi)
            (a.representationSecondaryTargetAlpha b i hi hsmall)) =
        min (a.representationPrimaryDefect b i)
          (a.representationSecondarySourceAlpha b i hi) := by
    rw [min_comm (a.representationSecondarySourceAlpha b i hi),
      ← min_assoc, min_eq_left htarget]
  rw [hinner]

/-- Definition 6's primed invariant after deleting the source-alpha
candidate. -/
theorem representationAlphaPrimeReduced_eq_min_primary_target_of_cross
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1)
    (hcross : b.order ⟨i.val - 2, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val, i.lt_large⟩) :
    a.representationAlphaPrimeReduced b i hi hsmall =
      min (a.representationPrimaryDefect b i)
        (a.representationSecondaryTargetAlpha b i hi hsmall) := by
  have hsource :=
    a.representationPrimaryDefect_le_secondarySourceAlpha_of_cross
      b i hi hcross
  unfold representationAlphaPrimeReduced
  rw [← min_assoc, min_eq_left hsource]

/-- Definition 6's primed invariant after deleting the target-alpha
candidate. -/
theorem representationAlphaPrimeReduced_eq_min_primary_source_of_cross
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1)
    (hcross : b.order ⟨i.val - 1, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val + 1, hi.2⟩) :
    a.representationAlphaPrimeReduced b i hi hsmall =
      min (a.representationPrimaryDefect b i)
        (a.representationSecondarySourceAlpha b i hi) := by
  have htarget :=
    a.representationPrimaryDefect_le_secondaryTargetAlpha_of_cross_local
      b i hi hsmall hcross
  unfold representationAlphaPrimeReduced
  rw [min_comm (a.representationSecondarySourceAlpha b i hi),
    ← min_assoc, min_eq_left htarget]

/-- If both crossing inequalities hold, both alpha candidates are redundant
in Definition 6's primed invariant. -/
theorem representationAlphaPrimeReduced_eq_primary_of_crosses
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1)
    (hleft : b.order ⟨i.val - 2, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val, i.lt_large⟩)
    (hright : b.order ⟨i.val - 1, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val + 1, hi.2⟩) :
    a.representationAlphaPrimeReduced b i hi hsmall =
      a.representationPrimaryDefect b i := by
  rw [a.representationAlphaPrimeReduced_eq_min_primary_target_of_cross
    b i hi hsmall hleft]
  have htarget :=
    a.representationPrimaryDefect_le_secondaryTargetAlpha_of_cross_local
      b i hi hsmall hright
  rw [min_eq_left htarget]

/-- If both crossing inequalities hold, both alpha candidates are
redundant and the reduced invariant has only its half-gap and primary
candidates. -/
theorem representationAlphaReduced_eq_min_halfGap_primary_of_crosses
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1)
    (hleft : b.order ⟨i.val - 2, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val, i.lt_large⟩)
    (hright : b.order ⟨i.val - 1, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val + 1, hi.2⟩) :
    a.representationAlphaReduced b i hi hsmall =
      min (a.representationHalfGap b i)
        (a.representationPrimaryDefect b i) := by
  rw [a.representationAlphaReduced_eq_min_halfGap_primary_target_of_cross
    b i hi hsmall hleft]
  have htarget :=
    a.representationPrimaryDefect_le_secondaryTargetAlpha_of_cross_local
      b i hi hsmall hright
  rw [min_eq_left htarget]

end BONG.GoodBONG

end Bong
