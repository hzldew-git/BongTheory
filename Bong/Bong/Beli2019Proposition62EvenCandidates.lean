/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Proposition62OrderReduction

/-!
# Beli (2019), Proposition 6.2: even-candidate reduction

This file names the two alternatives at a noninitial even coordinate of the
`W`-sequence.  Conditions 2.1(i) and 2.1(ii), Lemma 2.7(i), and the two
candidate calculations show that either one of those alternatives holds or
the primary defect candidate realizes `A_i`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The direct alternative at the even `W`-coordinate belonging to `i`. -/
noncomputable def representationWeightEvenDirect
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1)) : Prop :=
  (a.order ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
      a.alphaValue ⟨i.val - 1, by
        have := i.pos
        have := i.lt_large
        omega⟩ ≤
    (b.order ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
      b.alphaValue ⟨i.val - 1, by
        have := i.pos
        have := i.lt_large
        omega⟩

/-- The pair alternative at a noninitial even `W`-coordinate. -/
noncomputable def representationWeightEvenPair
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 1 < i.val) : Prop :=
  (a.order ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
      (a.order ⟨i.val, i.lt_large⟩ : ℚ) ≤
    2 * (b.order ⟨i.val - 1,
      (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
      b.alphaValue ⟨i.val - 1, by
        have := i.pos
        have := i.lt_large
        omega⟩ -
      b.alphaValue ⟨i.val - 2, by
        have := i.lt_large
        omega⟩

/-- The half-gap branch gives the direct even comparison. -/
theorem representationWeightEvenDirect_of_halfGap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hcurrent : a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ ≤
      b.order ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩)
    (hhalf : a.representationAlpha b i =
      a.representationHalfGap b i) :
    a.representationWeightEvenDirect b i := by
  exact a.weightSequence_even_direct_of_halfGap b hdefect i hcurrent hhalf

/-- The replaced secondary branch gives the pair comparison. -/
theorem representationWeightEvenPair_of_secondaryPrevious
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < n + 1)
    (hsecondary : a.representationAlpha b i =
      a.representationSecondaryPreviousDefect b i hi)
    (hshift : 0 <
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by omega⟩ -
        b.order ⟨i.val - 1, by omega⟩) :
    a.representationWeightEvenPair b i hi.1 := by
  exact a.weightSequence_even_pair_of_secondaryPrevious b hdefect i hi
    hsecondary hshift

/-- Candidate reduction for the noninitial even part of Proposition 6.2. -/
theorem representationWeightEven_direct_or_pair_or_primary
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 1 < i.val) :
    a.representationWeightEvenDirect b i ∨
      a.representationWeightEvenPair b i hi ∨
        a.representationAlpha b i = a.representationPrimaryDefect b i := by
  by_cases hdirect : a.representationWeightEvenDirect b i
  · exact Or.inl hdirect
  by_cases hpair : a.representationWeightEvenPair b i hi
  · exact Or.inr (Or.inl hpair)
  have hpairLt :
      2 * (b.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : ℚ) +
          b.alphaValue ⟨i.val - 1, by
            have := i.pos
            have := i.lt_large
            omega⟩ -
          b.alphaValue ⟨i.val - 2, by
            have := i.lt_large
            omega⟩ <
        (a.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : ℚ) + (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
    exact lt_of_not_ge hpair
  have hb := a.order_bounds_of_weightPair_lt b horder i hi hpairLt
  have hcurrent := hb.1
  have hcross := hb.2.1
  have hstrict := hb.2.2
  have hhalfFalse
      (hhalf : a.representationAlpha b i =
        a.representationHalfGap b i) : False := by
    apply hdirect
    exact a.representationWeightEvenDirect_of_halfGap b hdefect i
      hcurrent hhalf
  by_cases hinterior : i.val + 1 < n + 1
  · let hiInterior : 1 < i.val ∧ i.val + 1 < n + 1 :=
      ⟨hi, hinterior⟩
    have hnormal : a.representationAlpha b i =
        min (a.representationHalfGap b i)
          (min (a.representationPrimaryDefect b i)
            (a.representationSecondaryPreviousDefect b i hiInterior)) := by
      rw [a.representationAlpha_eq_min_halfGap_prime b i,
        a.representationAlphaPrime_eq_min_primary_previous b i hiInterior
          hcross.le]
    rcases min_choice (a.representationHalfGap b i)
        (min (a.representationPrimaryDefect b i)
          (a.representationSecondaryPreviousDefect b i hiInterior)) with
      hhalf | hprime
    · exact False.elim (hhalfFalse (hnormal.trans hhalf))
    · rcases min_choice (a.representationPrimaryDefect b i)
          (a.representationSecondaryPreviousDefect b i hiInterior) with
        hprimary | hsecondary
      · exact Or.inr (Or.inr (hnormal.trans (hprime.trans hprimary)))
      · have htwo : a.order ⟨i.val - 1, by omega⟩ ≤
            a.order ⟨i.val + 1, hinterior⟩ := by
          let p : Fin (n + 1) := ⟨i.val - 1, by omega⟩
          have hp : p.val + 2 < n + 1 := by
            simp only [p]
            omega
          have := a.good p hp
          unfold order
          simpa only [p, show i.val - 1 + 2 = i.val + 1 by omega]
            using this
        have hshift : 0 <
            a.order ⟨i.val, i.lt_large⟩ +
                a.order ⟨i.val + 1, hinterior⟩ -
              b.order ⟨i.val - 2, by omega⟩ -
                b.order ⟨i.val - 1, by omega⟩ := by
          omega
        apply False.elim
        apply hpair
        exact a.representationWeightEvenPair_of_secondaryPrevious b hdefect i
          hiInterior (hnormal.trans (hprime.trans hsecondary)) hshift
  · have hprime : a.representationAlphaPrime b i =
        a.representationPrimaryDefect b i :=
      a.representationAlphaPrime_eq_primary_of_not_interior b i
        (by omega)
    have hnormal : a.representationAlpha b i =
        min (a.representationHalfGap b i)
          (a.representationPrimaryDefect b i) := by
      rw [a.representationAlpha_eq_min_halfGap_prime b i, hprime]
    rcases min_choice (a.representationHalfGap b i)
        (a.representationPrimaryDefect b i) with hhalf | hprimary
    · exact False.elim (hhalfFalse (hnormal.trans hhalf))
    · exact Or.inr (Or.inr (hnormal.trans hprimary))

end BONG.GoodBONG

end Bong
