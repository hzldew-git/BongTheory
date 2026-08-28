/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019CappedIntegrality
import Bong.Bong.Beli2019Lemma79EvenBetaReduction

/-!
# Beli (2019), Lemma 7.9(ii), case 3: target integrality split

The representation alpha is bounded by the target-side primary coefficient.
A nonintegral target self-prefix is above `2e`; in the integral branch, a
strict inequality one unit below the primary coefficient rounds up to the
desired bound.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- The target-side primary coefficient bounds the representation alpha. -/
theorem lemma79_even_representationAlphaValue_le_primaryCoefficient
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      ((((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) : WithTop ℚ) +
        (c.alphaValue (evenTargetPreviousAlphaIndex i) : WithTop ℚ)) := by
  calc
    (b.representationAlphaValue c i : WithTop ℚ) ≤
        ((((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) : WithTop ℚ) +
          c.prefixAlphaCap (i.val - 1)) :=
      lemma79_representationAlphaValue_le_primaryRightCap b c i
    _ = _ := by rw [evenTarget_prefixAlphaCap c i hiTwo]

/-- The nonintegral target self-prefix branch is immediate from the `2e`
bound on the representation alpha. -/
theorem lemma79_even_targetCapped_of_not_integral
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hi := i.lt_large
          omega⟩ ≤
      2 * (ramificationIndex K : Int))
    (hnot : ¬ IsWithTopRationalInteger
      (c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val := by
  exact (representationAlphaValue_le_twoE_of_crossGap_le
    b c i hcross).trans
      (c.twoE_lt_alternatingSelfCapped_of_not_integral
        ((-1) ^ (i.val / 2)) i.val i.pos i.lt_large hnot).le

/-- In the integral branch, strict domination above one less than the
primary coefficient rounds to the full primary coefficient. -/
theorem lemma79_even_targetCapped_of_integral_strict_primary
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val)
    (hintegral : IsWithTopRationalInteger
      (c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val))
    (halphaIntegral : IsRationalInteger
      (c.alphaValue (evenTargetPreviousAlphaIndex i)))
    (hstrict :
      ((show ℚ from
          ((b.order ⟨i.val, i.lt_large⟩ -
            c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) - 1) : WithTop ℚ) <
        c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val := by
  let primary : ℚ :=
    ((b.order ⟨i.val, i.lt_large⟩ -
      c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
      c.alphaValue (evenTargetPreviousAlphaIndex i)
  have hprimaryIntegral : IsRationalInteger primary := by
    exact halphaIntegral.intCast_add
      (b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousIndex i))
  have hprimaryCapped : (primary : WithTop ℚ) ≤
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val := by
    apply hintegral.coe_le_of_sub_one_lt hprimaryIntegral
    simpa only [primary] using hstrict
  exact (lemma79_even_representationAlphaValue_le_primaryCoefficient
    b c i hiTwo).trans hprimaryCapped

end BONG.GoodBONG

end Bong
