/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenAlphaShiftLeftOuter

/-!
# Beli (2019), Lemma 7.9(ii), case 3: left candidate comparisons

On the normalized left outer interval, the current intermediate order is
one above the original order.  This bounds the half-gap candidate by a
shift of two.  If the next intermediate alpha is at most one, its endpoint
cap gives the same bound for the primary defect candidate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- An order shift by at most four bounds the half-gap candidate by a
two-unit shift. -/
theorem representationHalfGap_le_add_two_of_order_le_add_four
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (horder : b.order ⟨i.val, i.lt_large⟩ ≤
      a.order ⟨i.val, i.lt_large⟩ + 4) :
    b.representationHalfGap c i ≤
      a.representationHalfGap c i + ((2 : ℚ) : WithTop ℚ) := by
  unfold representationHalfGap
  norm_cast
  simp only [Rat.divInt_eq_div]
  have horderQ : (b.order ⟨i.val, i.lt_large⟩ : ℚ) ≤
      (a.order ⟨i.val, i.lt_large⟩ : ℚ) + 4 := by
    exact_mod_cast horder
  push_cast at horderQ ⊢
  linarith

/-- A one-unit order shift and an endpoint alpha at most one bound the
primary candidate by a two-unit shift. -/
theorem representationPrimaryDefect_le_add_two_of_order_eq_add_one
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (horder : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 1)
    (halpha : b.alphaValue ⟨i.val, by omega⟩ ≤ 1) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i +
        ((2 : ℚ) : WithTop ℚ) := by
  have hprefix := b.truncatedPrefixDefect_le_leftCap
    c (-1) (i.val + 1) (i.val - 1)
  rw [b.prefixAlphaCap_of_internal (by omega) hiNext] at hprefix
  have hprefixOne :
      b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
        ((1 : ℚ) : WithTop ℚ) :=
    hprefix.trans (by exact_mod_cast halpha)
  have hsourceNonnegative := a.truncatedPrefixDefect_nonneg
    c (-1) (i.val + 1) (i.val - 1)
  have hcoefficientInt :
      b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by
            have hp := i.pos
            have hb := i.lt_large
            omega⟩ =
        (a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by
            have hp := i.pos
            have hb := i.lt_large
            omega⟩) + 1 := by
    omega
  have hcoefficient :
      (((b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hp := i.pos
          have hb := i.lt_large
          omega⟩ : Int) : ℚ) : WithTop ℚ) =
        (((a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by
            have hp := i.pos
            have hb := i.lt_large
            omega⟩ : Int) : ℚ) : WithTop ℚ) +
          ((1 : ℚ) : WithTop ℚ) := by
    exact_mod_cast hcoefficientInt
  unfold representationPrimaryDefect
  rw [hcoefficient]
  calc
    _ ≤ ((((a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by
            have hp := i.pos
            have hb := i.lt_large
            omega⟩ : Int) : ℚ) : WithTop ℚ) +
        ((1 : ℚ) : WithTop ℚ)) + ((1 : ℚ) : WithTop ℚ) :=
      by
        have h := add_le_add_left hprefixOne
          ((((a.order ⟨i.val, i.lt_large⟩ -
            c.order ⟨i.val - 1, by
              have hp := i.pos
              have hb := i.lt_large
              omega⟩ : Int) : ℚ) : WithTop ℚ) +
            ((1 : ℚ) : WithTop ℚ))
        simpa only [add_comm] using h
    _ = (((a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by
            have hp := i.pos
            have hb := i.lt_large
            omega⟩ : Int) : ℚ) : WithTop ℚ) +
        ((2 : ℚ) : WithTop ℚ) := by
      rw [show ((2 : ℚ) : WithTop ℚ) =
        ((1 : ℚ) : WithTop ℚ) + ((1 : ℚ) : WithTop ℚ) by
          norm_num]
      ac_rfl
    _ ≤ ((((a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by
            have hp := i.pos
            have hb := i.lt_large
            omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)) +
          ((2 : ℚ) : WithTop ℚ) := by
      apply add_le_add_left
      exact le_add_of_nonneg_right hsourceNonnegative

/-- The half-gap comparison on a normalized no-gap left outer interval. -/
theorem lemma79_even_leftOuter_halfGap_le_add_two
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hfirst : O.first = 0)
    (hnoTwo : ∀ k, k < n + 2 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val) (hleft : i.val ≤ O.transition.lastZero) :
    b.representationHalfGap c i ≤
      a.representationHalfGap c i + ((2 : ℚ) : WithTop ℚ) := by
  have ha := O.source_leftEven_eq_first hfirst i.val hleft hiEven
  have hb := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo i.val hleft hiEven
  apply representationHalfGap_le_add_two_of_order_le_add_four a b c i
  rw [← a.orderSequence_entryOrZero_eq_order,
    ← b.orderSequence_entryOrZero_eq_order]
  change b.orderSequence.entryOrZero i.val ≤
    a.orderSequence.entryOrZero i.val + 4
  omega

/-- The primary comparison on a normalized no-gap left outer interval. -/
theorem lemma79_even_leftOuter_primary_le_add_two
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hfirst : O.first = 0)
    (hnoTwo : ∀ k, k < n + 2 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (hiEven : Even i.val) (hleft : i.val ≤ O.transition.lastZero)
    (halpha : b.alphaValue ⟨i.val, by omega⟩ ≤ 1) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i +
        ((2 : ℚ) : WithTop ℚ) := by
  have ha := O.source_leftEven_eq_first hfirst i.val hleft hiEven
  have hb := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo i.val hleft hiEven
  apply representationPrimaryDefect_le_add_two_of_order_eq_add_one
    a b c i hiNext
  · rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    change b.orderSequence.entryOrZero i.val =
      a.orderSequence.entryOrZero i.val + 1
    omega
  · exact halpha

end BONG.GoodBONG

end Bong
