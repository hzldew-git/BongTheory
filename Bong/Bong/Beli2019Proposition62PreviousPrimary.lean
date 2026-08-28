/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Proposition62PrimaryDescent

/-!
# Beli (2019), Proposition 6.2: the preceding primary candidate

After descending from a primary `A_i`, the half-gap candidate for `A_(i-1)`
would force the direct even comparison.  Its secondary-current candidate is
strictly larger than the descended cross defect.  Consequently, if both even
comparison alternatives fail, the preceding invariant is primary as well.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

set_option maxHeartbeats 800000 in
-- Candidate normal forms and nested `WithTop` arithmetic need extra elaboration time.
/-- If `A_i` is primary while both even comparison alternatives fail, then
`A_(i-1)` is also primary. -/
theorem representationAlpha_previous_eq_primary
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 1 < i.val)
    (hprimary : a.representationAlpha b i =
      a.representationPrimaryDefect b i)
    (hdirect : ¬a.representationWeightEvenDirect b i)
    (hpair : ¬a.representationWeightEvenPair b i hi) :
    a.representationAlpha b (previousRepresentationIndex i hi) =
      a.representationPrimaryDefect b
        (previousRepresentationIndex i hi) := by
  let j := previousRepresentationIndex i hi
  change a.representationAlpha b j = a.representationPrimaryDefect b j
  have hjval : j.val = i.val - 1 := rfl
  let p : Fin n := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  have hpSucc : p.succ = ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have hpCast : p.castSucc = ⟨i.val - 1,
      (Nat.sub_le _ _).trans_lt i.lt_large⟩ := by
    apply Fin.ext
    rfl
  let D := a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1)
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
  have hcross := hb.2.1
  have hstrict := hb.2.2
  have hprevious := a.representationAlpha_previous_le_primaryCross
    b hdefect i hi hprimary hdirect
  change a.representationAlpha b j ≤ D at hprevious
  have hright := a.representationAlpha_le_rightAlpha b hdefect i
  rw [hprimary] at hright
  have hDne : D ≠ ⊤ := by
    intro htop
    unfold representationPrimaryDefect at hright
    rw [← hpSucc, ← hpCast] at hright
    change (((((a.order p.succ - b.order p.castSucc : Int) : ℚ) :
      WithTop ℚ) + D) ≤ (b.alphaValue p : WithTop ℚ)) at hright
    rw [htop] at hright
    apply b.alpha_ne_top p
    rw [← b.coe_alphaValue p]
    exact top_unique hright
  have hhalfFalse
      (hhalf : a.representationAlpha b j =
        a.representationHalfGap b j) : False := by
    have hlower :
        (((a.order p.succ - b.order p.castSucc : Int) : ℚ) : WithTop ℚ) +
            a.representationAlpha b j ≤
          (b.alphaValue p : WithTop ℚ) := by
      calc
        (((a.order p.succ - b.order p.castSucc : Int) : ℚ) : WithTop ℚ) +
              a.representationAlpha b j ≤
            (((a.order p.succ - b.order p.castSucc : Int) : ℚ) :
              WithTop ℚ) +
              D := by gcongr
        _ = a.representationPrimaryDefect b i := by
          unfold representationPrimaryDefect
          rw [hpSucc, hpCast]
        _ = a.representationAlpha b i := hprimary.symm
        _ ≤ (b.alphaValue p : WithTop ℚ) :=
          a.representationAlpha_le_rightAlpha b hdefect i
    rw [hhalf] at hlower
    unfold representationHalfGap at hlower
    simp only [j, previousRepresentationIndex] at hlower
    simp only [show i.val - 1 - 1 = i.val - 2 by omega] at hlower
    norm_cast at hlower
    rw [Rat.divInt_eq_div] at hlower
    push_cast at hlower
    rw [hpSucc, hpCast] at hlower
    have halpha := a.alphaValue_le_halfGapValue p
    unfold halfGapValue orderGap at halpha
    push_cast at halpha
    rw [hpSucc, hpCast] at halpha
    have hcrossQ :
        (b.order ⟨i.val - 2, by
          have := i.lt_large
          omega⟩ : ℚ) <
          (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
      exact_mod_cast hcross
    have hdirectQ : (a.order p.castSucc : ℚ) + a.alphaValue p ≤
        (b.order p.castSucc : ℚ) + b.alphaValue p := by
      rw [hpCast]
      linarith
    apply hdirect
    simpa only [representationWeightEvenDirect, p, Fin.castSucc_mk]
      using hdirectQ
  have hcrossPrevious :
      b.order ⟨j.val - 1, by
          simp only [j, previousRepresentationIndex]
          have := i.lt_large
          omega⟩ ≤
        a.order ⟨j.val + 1, by
          simp only [j, previousRepresentationIndex]
          have := i.lt_large
          omega⟩ := by
    simpa only [j, previousRepresentationIndex,
      show i.val - 1 - 1 = i.val - 2 by omega,
      show i.val - 1 + 1 = i.val by omega] using hcross.le
  by_cases hinterior : 1 < j.val ∧ j.val + 1 < n + 1
  · have hnormal : a.representationAlpha b j =
        min (a.representationHalfGap b j)
          (min (a.representationPrimaryDefect b j)
            (a.representationSecondaryCurrentDefect b j hinterior)) := by
      rw [a.representationAlpha_eq_min_halfGap_prime b j,
        a.representationAlphaPrime_eq_min_primary_current b j hinterior
          hcrossPrevious]
    rcases min_choice (a.representationHalfGap b j)
        (min (a.representationPrimaryDefect b j)
          (a.representationSecondaryCurrentDefect b j hinterior)) with
      hhalf | hprime
    · exact False.elim (hhalfFalse (hnormal.trans hhalf))
    · rcases min_choice (a.representationPrimaryDefect b j)
          (a.representationSecondaryCurrentDefect b j hinterior) with
        hprimaryPrevious | hsecondary
      · exact hnormal.trans (hprime.trans hprimaryPrevious)
      · have htwo : b.order ⟨i.val - 3, by omega⟩ ≤
            b.order ⟨i.val - 1, by omega⟩ := by
          let t : Fin (n + 1) := ⟨i.val - 3, by omega⟩
          have ht : t.val + 2 < n + 1 := by
            simp only [t]
            omega
          have := b.good t ht
          unfold order
          simpa only [t, show i.val - 3 + 2 = i.val - 1 by omega]
            using this
        have hcoefficient : 0 <
            a.order ⟨j.val, j.lt_large⟩ +
                a.order ⟨j.val + 1, hinterior.2⟩ -
              b.order ⟨j.val - 2, by omega⟩ -
                b.order ⟨j.val - 1, by omega⟩ := by
          simp only [j, previousRepresentationIndex,
            show i.val - 1 + 1 = i.val by omega,
            show i.val - 1 - 2 = i.val - 3 by omega,
            show i.val - 1 - 1 = i.val - 2 by omega]
          omega
        have hsecondaryLe :
            a.representationSecondaryCurrentDefect b j hinterior ≤ D := by
          have hsecondaryEq : a.representationAlpha b j =
              a.representationSecondaryCurrentDefect b j hinterior :=
            hnormal.trans (hprime.trans hsecondary)
          simpa only [hsecondaryEq] using hprevious
        unfold representationSecondaryCurrentDefect at hsecondaryLe
        simp only [j, previousRepresentationIndex,
          show i.val - 1 + 1 = i.val by omega,
          show i.val - 1 + 2 = i.val + 1 by omega,
          show i.val - 1 - 2 = i.val - 3 by omega,
          show i.val - 1 - 1 = i.val - 2 by omega] at hsecondaryLe
        change (((((a.order ⟨i.val - 1, by omega⟩ +
            a.order ⟨i.val, i.lt_large⟩ -
            b.order ⟨i.val - 3, by omega⟩ -
            b.order ⟨i.val - 2, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
              D) ≤ D) at hsecondaryLe
        rw [← WithTop.coe_untop D hDne] at hsecondaryLe
        norm_cast at hsecondaryLe
        have hcoefficientQ : (0 : ℚ) <
            ((a.order ⟨j.val, j.lt_large⟩ +
              a.order ⟨j.val + 1, hinterior.2⟩ -
              b.order ⟨j.val - 2, by omega⟩ -
              b.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) := by
          exact_mod_cast hcoefficient
        simp only [j, previousRepresentationIndex,
          show i.val - 1 + 1 = i.val by omega,
          show i.val - 1 - 2 = i.val - 3 by omega,
          show i.val - 1 - 1 = i.val - 2 by omega] at hcoefficientQ
        linarith
  · have hprime : a.representationAlphaPrime b j =
        a.representationPrimaryDefect b j :=
      a.representationAlphaPrime_eq_primary_of_not_interior b j hinterior
    have hnormal : a.representationAlpha b j =
        min (a.representationHalfGap b j)
          (a.representationPrimaryDefect b j) := by
      rw [a.representationAlpha_eq_min_halfGap_prime b j, hprime]
    rcases min_choice (a.representationHalfGap b j)
        (a.representationPrimaryDefect b j) with hhalf | hprimaryPrevious
    · exact False.elim (hhalfFalse (hnormal.trans hhalf))
    · exact hnormal.trans hprimaryPrevious

end BONG.GoodBONG

end Bong
