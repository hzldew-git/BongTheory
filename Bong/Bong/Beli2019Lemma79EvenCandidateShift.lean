/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenBetaReduction

/-!
# Beli (2019), Lemma 7.9(ii), case 3: shifted candidate assembly

The inequality `B_i <= C_i + 2` is proved in the paper by comparing the
half-gap, primary, and secondary candidates separately.  The first theorem
below packages this order-theoretic assembly for an arbitrary shift.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Candidatewise shifted bounds induce the same shifted bound between the
two representation invariants. -/
theorem representationAlphaValue_le_add_of_candidate_bounds
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (shift : WithTop ℚ)
    (hhalf : b.representationHalfGap c i ≤
      a.representationHalfGap c i + shift)
    (hprimary : b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i + shift)
    (hsecondary : ∀ hi : 1 < i.val ∧ i.val + 1 < n + 2,
      b.representationSecondaryDefect c i hi ≤
        a.representationSecondaryDefect c i hi + shift) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) + shift := by
  rw [b.coe_representationAlphaValue c i,
    a.coe_representationAlphaValue c i,
    b.representationAlpha_eq_min_halfGap_prime c i,
    a.representationAlpha_eq_min_halfGap_prime c i]
  by_cases hi : 1 < i.val ∧ i.val + 1 < n + 2
  · rw [b.representationAlphaPrime_eq_min_primary_secondary c i hi,
      a.representationAlphaPrime_eq_min_primary_secondary c i hi]
    simpa only [min_add] using
      min_le_min hhalf (min_le_min hprimary (hsecondary hi))
  · rw [b.representationAlphaPrime_eq_primary_of_not_interior c i hi,
      a.representationAlphaPrime_eq_primary_of_not_interior c i hi]
    simpa only [min_add] using min_le_min hhalf hprimary

/-- The paper's three `+2` candidate comparisons, together with
`beta_i = alpha_i + 2`, prove the scalar beta estimate. -/
theorem lemma79_even_beta_bound_of_candidate_shifts
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (halpha : b.alphaValue ⟨i.val - 1, by
        have hp := i.pos
        have hb := i.lt_large
        omega⟩ =
      a.alphaValue ⟨i.val - 1, by
        have hp := i.pos
        have hb := i.lt_large
        omega⟩ + 2)
    (hhalf : b.representationHalfGap c i ≤
      a.representationHalfGap c i + ((2 : ℚ) : WithTop ℚ))
    (hprimary : b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i + ((2 : ℚ) : WithTop ℚ))
    (hsecondary : ∀ hi : 1 < i.val ∧ i.val + 1 < n + 2,
      b.representationSecondaryDefect c i hi ≤
        a.representationSecondaryDefect c i hi +
          ((2 : ℚ) : WithTop ℚ)) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by
        have hp := i.pos
        have hb := i.lt_large
        omega⟩ := by
  apply lemma79_even_beta_bound_of_comparison_shift
    a b c hdefectAC i
  · exact representationAlphaValue_le_add_of_candidate_bounds
      a b c i ((2 : ℚ) : WithTop ℚ) hhalf hprimary hsecondary
  · exact halpha

end BONG.GoodBONG

end Bong
