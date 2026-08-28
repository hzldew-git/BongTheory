/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma214Previous

/-!
# Beli (2019), Lemma 2.16 at ordinary central indices

Lemma 2.14 handles either strict half-gap truncation.  If neither adjacent
invariant is truncated, the actual `A`-sum is the auxiliary `A'`-sum, whose
equivalence with the revised defect sum was proved separately.
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

/-- Lemma 2.16 at a central index whose current representation invariant is
ordinary rather than the exceptional terminal expression. -/
theorem centralAlphaTrigger_iff_defectTrigger_of_ordinary
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hRank : n ≤ m) (horder : a.RepresentationOrderCondition b hRank)
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hi : i.val ≤ n + 1) :
    a.centralAlphaTrigger b i ↔ a.centralDefectTrigger b i := by
  constructor
  · intro h
    unfold centralAlphaTrigger at h
    rcases h with ⟨hcross, hsum⟩
    unfold centralDefectTrigger
    refine ⟨hcross, ?_⟩
    have hactual :
        ((2 * (ramificationIndex K : ℚ) +
          (a.order ⟨i.val - 1, by
            have := i.one_lt
            have := i.lt_large
            omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
          a.representationAlpha b i.previous +
            ((((b.order ⟨i.val - 1, by
                have := i.one_lt
                have := hi
                omega⟩ : Int) : ℚ) : WithTop ℚ) +
              a.representationAlpha b (i.current hi)) := by
      unfold centralAdjustedAlpha at hsum
      rw [dif_pos hi, a.coe_representationAlphaValue b i.previous,
        a.coe_representationAlphaValue b (i.current hi)] at hsum
      exact hsum
    have hactualLeft :
        ((2 * (ramificationIndex K : ℚ) +
          (a.order ⟨i.val - 1, by
            have := i.one_lt
            have := i.lt_large
            omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
          (a.representationAlpha b i.previous +
            (((b.order ⟨i.val - 1, by
              have := i.one_lt
              have := hi
              omega⟩ : Int) : ℚ) : WithTop ℚ)) +
            a.representationAlpha b (i.current hi) := by
      simpa only [add_assoc] using hactual
    apply (a.centralAlphaPrimeTrigger_iff_defectSum
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b i hi hcross).mp
    exact hactualLeft.trans_le (add_le_add
      (add_le_add (a.representationAlpha_le_prime b i.previous) le_rfl)
      (a.representationAlpha_le_prime b (i.current hi)))
  · intro h
    unfold centralDefectTrigger at h
    rcases h with ⟨hcross, hsum⟩
    by_cases hprevious : a.representationAlpha b i.previous =
        a.representationAlphaPrime b i.previous
    · by_cases hcurrent : a.representationAlpha b (i.current hi) =
          a.representationAlphaPrime b (i.current hi)
      · have hprime :=
          (a.centralAlphaPrimeTrigger_iff_defectSum
            (sourceLaws := sourceLaws) (targetLaws := targetLaws)
            b i hi hcross).mpr hsum
        unfold centralAlphaTrigger
        refine ⟨hcross, ?_⟩
        unfold centralAdjustedAlpha
        rw [dif_pos hi, a.coe_representationAlphaValue b i.previous,
          a.coe_representationAlphaValue b (i.current hi), hprevious,
          hcurrent]
        simpa only [add_assoc] using hprime
      · letI : Beli2006AlphaLaws.{u, w} K := targetLaws
        exact a.centralAlphaTrigger_of_current_alpha_ne_prime
          b hRank horder hdefect i hi hcurrent
    · letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
      exact a.centralAlphaTrigger_of_previous_alpha_ne_prime
        b hRank horder hdefect i hi hprevious

end BONG.GoodBONG

end Bong
