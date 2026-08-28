/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixProfile
import Bong.Bong.Beli2019Lemma79DefectOneCap
import Bong.Bong.Beli2019Lemma79EvenCandidateShift
import Bong.Bong.Beli2019Lemma79EvenTargetParity

/-!
# Beli (2019), Lemma 7.9(ii), case 6: one-unit candidate shifts

On the case-6 parity class the current target order is one above the
source order.  This file records the resulting one-unit comparisons for
the half-gap, primary, and secondary candidates.  It also isolates the two
short closing arguments used when the third alpha is positive or zero.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- A one-unit increase of the current order increases the half-gap
candidate by at most one. -/
theorem representationHalfGap_le_add_one_of_order_eq_add_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (horder : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 1) :
    b.representationHalfGap c i ≤
      a.representationHalfGap c i + ((1 : ℚ) : WithTop ℚ) := by
  unfold representationHalfGap
  norm_cast
  simp only [Rat.divInt_eq_div]
  have horderQ : (b.order ⟨i.val, i.lt_large⟩ : ℚ) =
      (a.order ⟨i.val, i.lt_large⟩ : ℚ) + 1 := by
    exact_mod_cast horder
  push_cast at horderQ ⊢
  linarith

/-- A one-unit order shift and a decreasing mixed prefix give the
one-unit primary-candidate comparison. -/
theorem representationPrimaryDefect_le_add_one_of_order_eq_add_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (horder : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 1)
    (hprefix : b.truncatedPrefixDefect c (-1) (i.val + 1)
        (i.val - 1) ≤
      a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i + ((1 : ℚ) : WithTop ℚ) := by
  have hiPrevious : i.val - 1 < n + 2 := by
    have hiBound := i.lt_large
    omega
  have hcoefficientInt :
      b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, hiPrevious⟩ =
        (a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, hiPrevious⟩) + 1 := by
    omega
  have hcoefficient :
      (((b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) : WithTop ℚ) =
        (((a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) : WithTop ℚ) +
          ((1 : ℚ) : WithTop ℚ) := by
    exact_mod_cast hcoefficientInt
  unfold representationPrimaryDefect
  rw [hcoefficient]
  let coefficient : WithTop ℚ :=
    (((a.order ⟨i.val, i.lt_large⟩ -
      c.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) : WithTop ℚ)
  change (coefficient + 1) +
      b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
    (coefficient +
      a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)) + 1
  calc
    _ ≤ (coefficient + 1) +
        a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
      simpa only [add_comm] using add_le_add_right hprefix
        (coefficient + 1)
    _ = _ := by ac_rfl

/-- Equal adjacent order sums transport a one-unit mixed-prefix comparison
to the secondary candidates. -/
theorem representationSecondaryDefect_le_add_one_of_orderSum_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hsum : b.order ⟨i.val, i.lt_large⟩ +
        b.order ⟨i.val + 1, hi.2⟩ =
      a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hi.2⟩)
    (hprefix : b.truncatedPrefixDefect c 1 (i.val + 2)
        (i.val - 2) ≤
      a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) +
        ((1 : ℚ) : WithTop ℚ)) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((1 : ℚ) : WithTop ℚ) := by
  unfold representationSecondaryDefect
  rw [hsum]
  let coefficient : WithTop ℚ :=
    (((a.order ⟨i.val, i.lt_large⟩ +
      a.order ⟨i.val + 1, hi.2⟩ -
      c.order ⟨i.val - 2, by omega⟩ -
      c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ)
  change coefficient +
      b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) ≤
    (coefficient +
      a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2)) +
        ((1 : ℚ) : WithTop ℚ)
  calc
    _ ≤ coefficient +
        (a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) +
          ((1 : ℚ) : WithTop ℚ)) :=
      by
        simpa only [add_comm] using
          add_le_add_left hprefix coefficient
    _ = _ := by ac_rfl

/-- If the target adjacent order sum is one larger, an unshifted mixed
prefix comparison gives the one-unit secondary-candidate bound. -/
theorem representationSecondaryDefect_le_add_one_of_orderSum_eq_add_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hsum : b.order ⟨i.val, i.lt_large⟩ +
        b.order ⟨i.val + 1, hi.2⟩ =
      a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hi.2⟩ + 1)
    (hprefix : b.truncatedPrefixDefect c 1 (i.val + 2)
        (i.val - 2) ≤
      a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2)) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((1 : ℚ) : WithTop ℚ) := by
  have hcoefficientInt :
      b.order ⟨i.val, i.lt_large⟩ +
          b.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
          c.order ⟨i.val - 1, by omega⟩ =
        (a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
          c.order ⟨i.val - 1, by omega⟩) + 1 := by
    omega
  have hcoefficient :
      (((b.order ⟨i.val, i.lt_large⟩ +
        b.order ⟨i.val + 1, hi.2⟩ -
        c.order ⟨i.val - 2, by omega⟩ -
        c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) =
        (((a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          ((1 : ℚ) : WithTop ℚ) := by
    exact_mod_cast hcoefficientInt
  unfold representationSecondaryDefect
  rw [hcoefficient]
  let coefficient : WithTop ℚ :=
    (((a.order ⟨i.val, i.lt_large⟩ +
      a.order ⟨i.val + 1, hi.2⟩ -
      c.order ⟨i.val - 2, by omega⟩ -
      c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ)
  change (coefficient + 1) +
      b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) ≤
    (coefficient +
      a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2)) + 1
  calc
    _ ≤ (coefficient + 1) +
        a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) := by
      simpa only [add_comm] using
        add_le_add_right hprefix (coefficient + 1)
    _ = _ := by ac_rfl

/-- The three one-unit candidate comparisons assemble to the corresponding
comparison of representation alphas. -/
theorem lemma79_caseSix_alpha_le_add_one_of_candidate_bounds
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hhalf : b.representationHalfGap c i ≤
      a.representationHalfGap c i + ((1 : ℚ) : WithTop ℚ))
    (hprimary : b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i + ((1 : ℚ) : WithTop ℚ))
    (hsecondary : ∀ hi : 1 < i.val ∧ i.val + 1 < n + 2,
      b.representationSecondaryDefect c i hi ≤
        a.representationSecondaryDefect c i hi +
          ((1 : ℚ) : WithTop ℚ)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) +
        ((1 : ℚ) : WithTop ℚ) := by
  exact representationAlphaValue_le_add_of_candidate_bounds
    a b c i ((1 : ℚ) : WithTop ℚ) hhalf hprimary hsecondary

/-- In the first parity branch of case 6, odd source-comparison order makes
the old defect zero.  A one-unit alpha shift and positive adjacent caps
then close condition (ii) for the target pair. -/
theorem lemma79_caseSix_of_alphaShift_even_and_sourceOdd
    [Beli2006AlphaLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hshift : (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) +
        ((1 : ℚ) : WithTop ℚ))
    (hbeta : b.alphaValue ⟨i.val - 1, by
      have hiBound := i.lt_large
      omega⟩ = 1)
    (hgamma : (1 : ℚ) ≤ c.alphaValue ⟨i.val - 1, by
      have hiBound := i.lt_large
      omega⟩)
    (hbcEven : Even
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (hacOdd : Odd
      (ordUnit K (a.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hsourceZero :=
    a.truncatedPrefixDefect_eq_zero_of_odd_order_general
      c 1 i.val i.val (by simpa only [one_mul] using hacOdd)
  have hsourceAlphaNonpos :
      (a.representationAlphaValue c i : WithTop ℚ) ≤ 0 := by
    exact (hdefectAC i).trans_eq hsourceZero
  have htargetAlphaOneTop :
      (b.representationAlphaValue c i : WithTop ℚ) ≤ 1 := by
    calc
      (b.representationAlphaValue c i : WithTop ℚ) ≤
          (a.representationAlphaValue c i : WithTop ℚ) + 1 := hshift
      _ ≤ 0 + 1 := by
        simpa only [add_comm] using
          add_le_add_right hsourceAlphaNonpos (1 : WithTop ℚ)
      _ = 1 := by norm_num
  have htargetAlphaOne : b.representationAlphaValue c i ≤ 1 := by
    exact WithTop.coe_le_coe.mp htargetAlphaOneTop
  apply b.lemma79_ii_of_alpha_le_one_and_even c i htargetAlphaOne
  · rw [hbeta]
  · exact hgamma
  · exact hbcEven

/-- If the third alpha vanishes and the target current order is no larger
than the third current order, P2 forces the half-gap candidate to be
nonpositive, closing condition (ii) directly. -/
theorem lemma79_caseSix_of_gamma_eq_zero_and_current_order
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hcurrent : b.order ⟨i.val, i.lt_large⟩ ≤
      c.order ⟨i.val, i.lt_large⟩)
    (hgamma : c.alphaValue ⟨i.val - 1, by
      have hiBound := i.lt_large
      omega⟩ = 0) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hiPrevious : i.val - 1 < n + 2 := by
    have hiBound := i.lt_large
    omega
  have hiAlphaPrevious : i.val - 1 < n + 1 := by
    have hiBound := i.lt_large
    omega
  let previous : Fin (n + 1) := ⟨i.val - 1, hiAlphaPrevious⟩
  have hpreviousSucc : previous.succ = ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    simp only [previous, Fin.succ_mk]
    exact Nat.sub_add_cancel i.pos
  have hpreviousCast : previous.castSucc =
      ⟨i.val - 1, hiPrevious⟩ := by
    apply Fin.ext
    rfl
  have hgap := (c.alpha_p2 previous).2.mp (by
    simpa only [previous] using hgamma)
  rw [orderGap, hpreviousSucc, hpreviousCast] at hgap
  have hnext : b.order ⟨i.val, i.lt_large⟩ -
      c.order ⟨i.val - 1, hiPrevious⟩ ≤
        -(2 * (ramificationIndex K : Int)) := by
    omega
  have hhalf : b.representationHalfGap c i ≤ 0 := by
    unfold representationHalfGap
    norm_cast
    simp only [Rat.divInt_eq_div]
    have hnextQ :
        ((b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) ≤
            -(2 * (ramificationIndex K : ℚ)) := by
      exact_mod_cast hnext
    linarith
  calc
    (b.representationAlphaValue c i : WithTop ℚ) =
        b.representationAlpha c i := b.coe_representationAlphaValue c i
    _ ≤ b.representationHalfGap c i :=
      b.representationAlpha_le_halfGap c i
    _ ≤ 0 := hhalf
    _ ≤ b.truncatedPrefixDefect c 1 i.val i.val :=
      b.truncatedPrefixDefect_nonneg c 1 i.val i.val

end BONG.GoodBONG

end Bong
