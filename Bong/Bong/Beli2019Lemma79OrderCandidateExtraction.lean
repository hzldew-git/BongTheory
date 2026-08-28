/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIIComparisonDefect

/-!
# Beli (2019), Lemma 7.9(i): extracting the active candidate

Once the comparison-prefix defect bounds `A_i` and the half-gap candidate
is too large, the auxiliary minimum `A'_i` supplies either the primary
defect candidate or, at an interior boundary, the secondary candidate.
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

/-- If `A_i` is at most `C` but the half-gap candidate is larger than `C`,
then the reduced invariant `A'_i` is at most `C`. -/
theorem representationAlphaPrime_le_of_alphaValue_le_of_lt_halfGap
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) (C : WithTop ℚ)
    (hAlpha : (a.representationAlphaValue b i : WithTop ℚ) ≤ C)
    (hHalf : C < a.representationHalfGap b i) :
    a.representationAlphaPrime b i ≤ C := by
  have hAlpha' : a.representationAlpha b i ≤ C := by
    rw [← a.coe_representationAlphaValue b i]
    exact hAlpha
  rw [a.representationAlpha_eq_min_halfGap_prime b i] at hAlpha'
  rcases min_le_iff.mp hAlpha' with hhalf | hprime
  · exact False.elim ((not_le_of_gt hHalf) hhalf)
  · exact hprime

/-- Under the same hypotheses, one of the explicit defect candidates in
`A'_i` is at most `C`.  The existential secondary alternative records its
interiority proof because that proof is part of the candidate's type. -/
theorem representationDefectCandidate_le_of_alphaValue_le_of_lt_halfGap
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) (C : WithTop ℚ)
    (hAlpha : (a.representationAlphaValue b i : WithTop ℚ) ≤ C)
    (hHalf : C < a.representationHalfGap b i) :
    a.representationPrimaryDefect b i ≤ C ∨
      ∃ hi : 1 < i.val ∧ i.val + 1 < m + 1,
        a.representationSecondaryDefect b i hi ≤ C := by
  have hprime := a.representationAlphaPrime_le_of_alphaValue_le_of_lt_halfGap
    b i C hAlpha hHalf
  by_cases hi : 1 < i.val ∧ i.val + 1 < m + 1
  · rw [a.representationAlphaPrime_eq_min_primary_secondary b i hi]
      at hprime
    rcases min_le_iff.mp hprime with hprimary | hsecondary
    · exact Or.inl hprimary
    · exact Or.inr ⟨hi, hsecondary⟩
  · rw [a.representationAlphaPrime_eq_primary_of_not_interior b i hi]
      at hprime
    exact Or.inl hprime

end BONG.GoodBONG

end Bong
