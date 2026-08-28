/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma29TargetReduction
import Bong.Bong.Beli2019Lemma79OrderCandidateExtraction

/-!
# Beli (2019), Lemma 7.9(ii): strict primary-candidate reduction

This file packages the Section 2.7--2.9 argument used at the type-I
gap-two boundary.  When both cross-order inequalities hold and the
secondary coefficient is positive, condition 2.1(ii) prevents the
secondary candidate from lying strictly below the primary candidate.
Thus an alpha value below its half-gap forces the primary candidate to
have that same value.
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

set_option maxHeartbeats 1000000 in
-- The dependent prefix caps require several `WithTop` normalizations.
/-- If `S_i <= R_(i+2)`, the primary candidate is bounded by the
target-alpha candidate occurring in the reduced invariant. -/
theorem representationPrimaryDefect_le_secondaryTargetAlpha_of_cross
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1)
    (hcross : b.order ⟨i.val - 1, by omega⟩ <=
      a.order ⟨i.val + 1, hi.2⟩) :
    a.representationPrimaryDefect b i <=
      a.representationSecondaryTargetAlpha b i hi hsmall := by
  let previous : Fin n := ⟨i.val - 2, by omega⟩
  let primaryShift : Rat :=
    ((a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 1, by omega⟩ : Int) : Rat)
  let targetShift : Rat :=
    ((a.order ⟨i.val, i.lt_large⟩ +
      a.order ⟨i.val + 1, hi.2⟩ -
      2 * b.order ⟨i.val - 1, by omega⟩ : Int) : Rat)
  have hcap : b.prefixAlphaCap (i.val - 1) =
      (b.alphaValue previous : WithTop Rat) := by
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
    congr 1
  have hdefect : a.truncatedPrefixDefect b (-1)
      (i.val + 1) (i.val - 1) <=
      (b.alphaValue previous : WithTop Rat) := by
    rw [← hcap]
    exact a.truncatedPrefixDefect_le_rightCap b (-1)
      (i.val + 1) (i.val - 1)
  have hshift : primaryShift <= targetShift := by
    dsimp only [primaryShift, targetShift]
    have hshiftInt :
        a.order ⟨i.val, i.lt_large⟩ -
            b.order ⟨i.val - 1, by omega⟩ <=
          a.order ⟨i.val, i.lt_large⟩ +
            a.order ⟨i.val + 1, hi.2⟩ -
            2 * b.order ⟨i.val - 1, by omega⟩ := by
      omega
    exact_mod_cast hshiftInt
  unfold representationPrimaryDefect representationSecondaryTargetAlpha
  calc
    (((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : Rat) :
          WithTop Rat) +
        a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) <=
      (primaryShift : WithTop Rat) +
        (b.alphaValue previous : WithTop Rat) := by
          simpa only [primaryShift] using
            add_le_add (le_refl (primaryShift : WithTop Rat)) hdefect
    _ <= (targetShift : WithTop Rat) +
        (b.alphaValue previous : WithTop Rat) :=
      add_le_add (WithTop.coe_le_coe.mpr hshift) le_rfl
    _ = (((a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hi.2⟩ -
          2 * b.order ⟨i.val - 1, by omega⟩ : Int) : Rat) :
          WithTop Rat) +
        (b.alphaValue ⟨i.val - 2, by omega⟩ : WithTop Rat) := by
      rfl

/-- Below the half-gap, the Section 2.9 reduction forces the primary
candidate to be no larger than the realized alpha value. -/
theorem representationPrimaryDefect_le_of_alphaValue_eq_of_lt_halfGap
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) (C : Rat)
    (hvalue : a.representationAlphaValue b i = C)
    (hhalf : (C : WithTop Rat) < a.representationHalfGap b i)
    (hcomparison : (C : WithTop Rat) <=
      a.truncatedPrefixDefect b 1 i.val i.val)
    (hsmall : forall hi : 1 < i.val ∧ i.val + 1 < m + 1,
      i.val < n + 1)
    (hpreviousCross : forall hi : 1 < i.val ∧ i.val + 1 < m + 1,
      b.order ⟨i.val - 2, by omega⟩ <=
        a.order ⟨i.val, i.lt_large⟩)
    (hcurrentCross : forall hi : 1 < i.val ∧ i.val + 1 < m + 1,
      b.order ⟨i.val - 1, by omega⟩ <=
        a.order ⟨i.val + 1, hi.2⟩)
    (hshift : forall hi : 1 < i.val ∧ i.val + 1 < m + 1,
      0 < a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by omega⟩ -
        b.order ⟨i.val - 1, by omega⟩) :
    a.representationPrimaryDefect b i <= (C : WithTop Rat) := by
  have hAlpha : a.representationAlpha b i = (C : WithTop Rat) := by
    calc
      a.representationAlpha b i =
          (a.representationAlphaValue b i : WithTop Rat) :=
        (a.coe_representationAlphaValue b i).symm
      _ = (C : WithTop Rat) := by exact_mod_cast hvalue
  have hprimeLe : a.representationAlphaPrime b i <=
      (C : WithTop Rat) :=
    a.representationAlphaPrime_le_of_alphaValue_le_of_lt_halfGap
      b i (C : WithTop Rat) (by
        rw [hvalue]) hhalf
  have hCLePrime : (C : WithTop Rat) <=
      a.representationAlphaPrime b i := by
    calc
      (C : WithTop Rat) = a.representationAlpha b i := hAlpha.symm
      _ = min (a.representationHalfGap b i)
          (a.representationAlphaPrime b i) :=
        a.representationAlpha_eq_min_halfGap_prime b i
      _ <= a.representationAlphaPrime b i := min_le_right _ _
  have hprime : a.representationAlphaPrime b i =
      (C : WithTop Rat) := le_antisymm hprimeLe hCLePrime
  by_cases hi : 1 < i.val ∧ i.val + 1 < m + 1
  · by_contra hprimaryNot
    have hCPrimary : (C : WithTop Rat) <
        a.representationPrimaryDefect b i :=
      lt_of_not_ge hprimaryNot
    have hmin : min (a.representationPrimaryDefect b i)
        (a.representationSecondaryDefect b i hi) =
        (C : WithTop Rat) := by
      calc
        min (a.representationPrimaryDefect b i)
            (a.representationSecondaryDefect b i hi) =
            a.representationAlphaPrime b i :=
          (a.representationAlphaPrime_eq_min_primary_secondary
            b i hi).symm
        _ = (C : WithTop Rat) := hprime
    have hsecondaryLe : a.representationSecondaryDefect b i hi <=
        (C : WithTop Rat) := by
      by_contra hsecondaryNot
      have hCSecondary : (C : WithTop Rat) <
          a.representationSecondaryDefect b i hi :=
        lt_of_not_ge hsecondaryNot
      have hlt := lt_min hCPrimary hCSecondary
      rw [hmin] at hlt
      exact (lt_irrefl _ hlt).elim
    have hsecondaryPrimary : a.representationSecondaryDefect b i hi <=
        a.representationPrimaryDefect b i :=
      hsecondaryLe.trans hCPrimary.le
    letI : Beli2006AlphaLaws.{u, v} K := alphaV
    have hreplace := a.representationSecondaryDefect_replace_previous
      b i hi (hpreviousCross hi)
    have hpreviousMin : min
        (a.representationSecondaryPreviousDefect b i hi)
        (a.representationPrimaryDefect b i) <= (C : WithTop Rat) := by
      calc
        min (a.representationSecondaryPreviousDefect b i hi)
            (a.representationPrimaryDefect b i) =
            min (a.representationSecondaryDefect b i hi)
              (a.representationPrimaryDefect b i) := hreplace.symm
        _ = a.representationSecondaryDefect b i hi :=
          min_eq_left hsecondaryPrimary
        _ <= (C : WithTop Rat) := hsecondaryLe
    have hpreviousLe : a.representationSecondaryPreviousDefect b i hi <=
        (C : WithTop Rat) := by
      by_contra hpreviousNot
      have hCPrevious : (C : WithTop Rat) <
          a.representationSecondaryPreviousDefect b i hi :=
        lt_of_not_ge hpreviousNot
      exact (not_le_of_gt (lt_min hCPrevious hCPrimary)) hpreviousMin
    have hsmall' : i.val < n + 1 := hsmall hi
    letI : Beli2006AlphaLaws.{u, w} K := alphaW
    have htargetLe :=
      a.representationSecondaryTargetAlpha_le_of_previous_le_comparison
        b i hi hsmall' C hpreviousLe hcomparison (hshift hi)
    have hprimaryTarget :=
      a.representationPrimaryDefect_le_secondaryTargetAlpha_of_cross
        b i hi hsmall' (hcurrentCross hi)
    exact (not_le_of_gt hCPrimary) (hprimaryTarget.trans htargetLe)
  · rw [a.representationAlphaPrime_eq_primary_of_not_interior
      b i hi] at hprime
    exact hprime.le

end BONG.GoodBONG

end Bong
