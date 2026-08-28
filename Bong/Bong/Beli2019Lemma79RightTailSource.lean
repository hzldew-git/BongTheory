/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma63Right
import Bong.Bong.Beli2019Lemma79TypeIRightSourceSecondary
import Bong.Bong.Beli2019Remark616RightMixedGeneral

/-!
# Beli (2019), Lemma 7.9(ii): the unchanged right tail

After the last unequal order, the source and intermediate BONGs have the
same order suffix.  Lemma 6.3 identifies every later mixed alpha with the
intermediate alpha, and Remark 6.16 then compares the mixed prefixes in the
primary and secondary candidates.  Thus all three candidates for the new
representation alpha are bounded by their source counterparts.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Remark 6.16 immediately bounds a changed mixed prefix by the
corresponding source mixed prefix. -/
theorem truncatedPrefixDefect_le_source_of_rightAlpha
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (j : RepresentationIndex (n + 2) (n + 2))
    (hAlpha : a.representationAlphaValue b j =
      b.alphaValue ⟨j.val - 1, by
        have hjPos := j.pos
        have hjLarge := j.lt_large
        omega⟩)
    (epsilon : Kˣ) (k : Nat) :
    b.truncatedPrefixDefect c epsilon j.val k ≤
      a.truncatedPrefixDefect c epsilon j.val k := by
  have hformula := beli2019Remark616_rightMixedPrefix_at
    a b c hdefect j hAlpha epsilon k
  rw [hformula]
  exact min_le_left _ _

/-- Equal current source orders identify the two half-gap candidates. -/
theorem lemma79_rightTail_halfGap_eq_sourceHalfGap
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hcurrent : a.orderSequence.entryOrZero i.val =
      b.orderSequence.entryOrZero i.val) :
    b.representationHalfGap c i = a.representationHalfGap c i := by
  have horder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hcurrent
  unfold representationHalfGap
  rw [horder]

/-- On an unchanged suffix, the comparison primary candidate is bounded by
the corresponding source candidate. -/
theorem lemma79_rightTail_primary_le_sourcePrimary
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hsuffix : ∀ k, i.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i := by
  have hcurrent := hsuffix i.val le_rfl i.lt_large
  have horder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hcurrent
  have hprefix :
      b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
        a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
    by_cases hfull : i.val + 1 = n + 2
    · simpa only [hfull] using
        (truncatedPrefixDefect_fullLeft_change
          a b c (-1) (i.val - 1)).le
    · have hfarBound : i.val + 1 < n + 2 := by
        have hiLarge := i.lt_large
        omega
      let farIdx : RepresentationIndex (n + 2) (n + 2) :=
        ⟨i.val + 1, by omega, hfarBound, hfarBound.le⟩
      have hfarSuffix : ∀ k, farIdx.val ≤ k → k < n + 2 →
          a.orderSequence.entryOrZero k =
            b.orderSequence.entryOrZero k := by
        intro k hk hkn
        exact hsuffix k (by simp only [farIdx] at hk ⊢; omega) hkn
      have hAlpha := a.beli2019Lemma63_sameRank_right_value
        b hdefect farIdx hfarSuffix
      simpa only [farIdx] using
        (truncatedPrefixDefect_le_source_of_rightAlpha
          a b c hdefect farIdx hAlpha (-1) (i.val - 1))
  unfold representationPrimaryDefect
  rw [horder]
  exact add_le_add_right hprefix _

/-- On an unchanged suffix, the comparison secondary candidate is bounded
by the corresponding source candidate. -/
theorem lemma79_rightTail_secondary_le_sourceSecondary
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hsuffix : ∀ k, i.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi := by
  have hcurrent := hsuffix i.val le_rfl i.lt_large
  have hnext := hsuffix (i.val + 1) (by omega) hi.2
  have hcurrentOrder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hcurrent
  have hnextOrder : a.order ⟨i.val + 1, hi.2⟩ =
      b.order ⟨i.val + 1, hi.2⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hnext
  have hprefix :
      b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) ≤
        a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) := by
    by_cases hfull : i.val + 2 = n + 2
    · simpa only [hfull] using
        (truncatedPrefixDefect_fullLeft_change
          a b c 1 (i.val - 2)).le
    · have hfarBound : i.val + 2 < n + 2 := by omega
      let farIdx : RepresentationIndex (n + 2) (n + 2) :=
        ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
      have hfarSuffix : ∀ k, farIdx.val ≤ k → k < n + 2 →
          a.orderSequence.entryOrZero k =
            b.orderSequence.entryOrZero k := by
        intro k hk hkn
        exact hsuffix k (by simp only [farIdx] at hk ⊢; omega) hkn
      have hAlpha := a.beli2019Lemma63_sameRank_right_value
        b hdefect farIdx hfarSuffix
      simpa only [farIdx] using
        (truncatedPrefixDefect_le_source_of_rightAlpha
          a b c hdefect farIdx hAlpha 1 (i.val - 2))
  unfold representationSecondaryDefect
  rw [hcurrentOrder, hnextOrder]
  exact add_le_add_right hprefix _

set_option maxHeartbeats 2000000 in
-- Candidate minima contain proof-dependent secondary terms.
/-- The representation alpha for the comparison pair is no larger than the
source representation alpha at every boundary in an unchanged suffix. -/
theorem lemma79_rightTail_alpha_le_sourceAlpha
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hsuffix : ∀ k, i.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) := by
  have hhalf := lemma79_rightTail_halfGap_eq_sourceHalfGap
    a b c i (hsuffix i.val le_rfl i.lt_large)
  have hprimary := lemma79_rightTail_primary_le_sourcePrimary
    a b c hdefect i hsuffix
  rw [b.coe_representationAlphaValue c i,
    a.coe_representationAlphaValue c i,
    b.representationAlpha_eq_min_halfGap_prime c i,
    a.representationAlpha_eq_min_halfGap_prime c i]
  apply min_le_min hhalf.le
  by_cases hi : 1 < i.val ∧ i.val + 1 < n + 2
  · rw [b.representationAlphaPrime_eq_min_primary_secondary c i hi,
      a.representationAlphaPrime_eq_min_primary_secondary c i hi]
    exact min_le_min hprimary
      (lemma79_rightTail_secondary_le_sourceSecondary
        a b c hdefect i hi hsuffix)
  · rw [b.representationAlphaPrime_eq_primary_of_not_interior c i hi,
      a.representationAlphaPrime_eq_primary_of_not_interior c i hi]
    exact hprimary

end BONG.GoodBONG

end Bong
