/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912AnisotropicRepresentation

/-!
# Beli (2019), Lemma 9.12: anisotropic mixed-defect bounds

This file formalizes the two complementary integral defect depths occurring
after a failed scalar inequality.  Discreteness of raw defects and alpha
invariants upgrades the strict `threshold - 1` inequalities to capped
mixed-prefix bounds at the threshold itself.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG.Beli2019Lemma910Data

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {Q : Lattice K U}
  {N : Nat} {c : GoodBONG s Q (N + 3)}

/-- The two complementary integral depths alternating along the failure
prefix. -/
noncomputable def failureThreshold (A₁ : Int) (k : Nat) : Int :=
  if k % 2 = 0 then A₁ + 1
  else 2 * (ramificationIndex K : Int) - (A₁ + 1)

@[simp]
theorem failureThreshold_of_even (A₁ : Int) (k : Nat)
    (hk : k % 2 = 0) :
    failureThreshold (K := K) A₁ k = A₁ + 1 := by
  simp [failureThreshold, hk]

@[simp]
theorem failureThreshold_of_odd (A₁ : Int) (k : Nat)
    (hk : k % 2 = 1) :
    failureThreshold (K := K) A₁ k =
      2 * (ramificationIndex K : Int) - (A₁ + 1) := by
  simp [failureThreshold, hk]

theorem failureThreshold_even
    {A₁ : Int} (P : Beli2019Lemma912ComparisonFirstAlphaProfile
      (K := K) c A₁) (k : Nat) :
    Even (failureThreshold (K := K) A₁ k) := by
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [failureThreshold_of_even (K := K) A₁ k hk]
    exact P.first_even
  · rw [failureThreshold_of_odd (K := K) A₁ k hk]
    exact P.complement_even

theorem failureThreshold_pos
    {A₁ : Int} (P : Beli2019Lemma912ComparisonFirstAlphaProfile
      (K := K) c A₁) (k : Nat) :
    0 < failureThreshold (K := K) A₁ k := by
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [failureThreshold_of_even (K := K) A₁ k hk]
    exact P.first_pos
  · rw [failureThreshold_of_odd (K := K) A₁ k hk]
    exact P.complement_pos

theorem failureThreshold_lt_twoE
    {A₁ : Int} (P : Beli2019Lemma912ComparisonFirstAlphaProfile
      (K := K) c A₁) (k : Nat) :
    failureThreshold (K := K) A₁ k <
      2 * (ramificationIndex K : Int) := by
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [failureThreshold_of_even (K := K) A₁ k hk]
    exact P.first_lt_twoE
  · rw [failureThreshold_of_odd (K := K) A₁ k hk]
    exact P.complement_lt_twoE

theorem failureThreshold_add_next
    (A₁ : Int) (k : Nat) :
    failureThreshold (K := K) A₁ k +
        failureThreshold (K := K) A₁ (k + 1) =
      2 * (ramificationIndex K : Int) := by
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · have hnext : (k + 1) % 2 = 1 := by omega
    rw [failureThreshold_of_even (K := K) A₁ k hk,
      failureThreshold_of_odd (K := K) A₁ (k + 1) hnext]
    omega
  · have hnext : (k + 1) % 2 = 0 := by omega
    rw [failureThreshold_of_odd (K := K) A₁ k hk,
      failureThreshold_of_even (K := K) A₁ (k + 1) hnext]
    omega

/-- The failed scalar lower bound is one less than the first alternating
threshold at the failure boundary. -/
theorem failureShift_eq_threshold_sub_one
    {R₁ R₂ A₁ : Int}
    (target : GoodBONG q L (N + 3))
    (c : GoodBONG s Q (N + 3))
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (O : Beli2019Lemma912FailureAlternatingOrders target c R₁ R₂ i)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K) :
    (((target.order ⟨i.val, i.lt_large⟩ -
        target.order (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
      (A₁ : ℚ)) =
      ((failureThreshold (K := K) A₁ (i.val - 1) - 1 : Int) : ℚ) := by
  have hone : target.order (⟨1, by omega⟩ : Fin (N + 3)) = R₂ + 2 :=
    O.target_odd (⟨1, by omega⟩ : Fin (N + 3))
      (show 1 ≤ i.val by omega) (by norm_num)
  rcases Nat.mod_two_eq_zero_or_one i.val with hmod | hmod
  · have hprevious : (i.val - 1) % 2 = 1 := by omega
    rw [O.target_even ⟨i.val, i.lt_large⟩ le_rfl hmod, hone,
      failureThreshold_of_odd (K := K) A₁ (i.val - 1) hprevious]
    push_cast at hformula ⊢
    linarith
  · have hprevious : (i.val - 1) % 2 = 0 := by omega
    rw [O.target_odd ⟨i.val, i.lt_large⟩ le_rfl hmod, hone,
      failureThreshold_of_even (K := K) A₁ (i.val - 1) hprevious]
    push_cast
    ring

/-- After removing the primary order shift, the same failed scalar lower
bound is one less than the complementary threshold. -/
theorem failureShift_eq_orderDifference_add_previousThreshold_sub_one
    {R₁ R₂ A₁ : Int}
    (source : GoodBONG q L (N + 3))
    (target : GoodBONG r M (N + 3))
    (c : GoodBONG s Q (N + 3))
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (O : Beli2019Lemma912FailureAlternatingOrders target c R₁ R₂ i)
    (hcurrent : source.order ⟨i.val, i.lt_large⟩ =
      target.order ⟨i.val, i.lt_large⟩)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K) :
    (((target.order ⟨i.val, i.lt_large⟩ -
        target.order (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
      (A₁ : ℚ)) =
      (((source.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) +
        ((failureThreshold (K := K) A₁ (i.val - 2) - 1 : Int) : ℚ)) := by
  have hone : target.order (⟨1, by omega⟩ : Fin (N + 3)) = R₂ + 2 :=
    O.target_odd (⟨1, by omega⟩ : Fin (N + 3))
      (show 1 ≤ i.val by omega) (by norm_num)
  rcases Nat.mod_two_eq_zero_or_one i.val with hmod | hmod
  · have hprevious : (i.val - 1) % 2 = 1 := by omega
    have hbefore : (i.val - 2) % 2 = 0 := by omega
    rw [hcurrent, O.target_even ⟨i.val, i.lt_large⟩ le_rfl hmod,
      O.comparison_odd
        ⟨i.val - 1, by have := i.lt_large; omega⟩
        (by change i.val - 1 + 1 ≤ i.val; omega) hprevious,
      hone, failureThreshold_of_even (K := K) A₁ (i.val - 2) hbefore]
    push_cast
    ring
  · have hprevious : (i.val - 1) % 2 = 0 := by omega
    have hbefore : (i.val - 2) % 2 = 1 := by omega
    rw [hcurrent, O.target_odd ⟨i.val, i.lt_large⟩ le_rfl hmod,
      O.comparison_even
        ⟨i.val - 1, by have := i.lt_large; omega⟩
        (by change i.val - 1 + 1 ≤ i.val; omega) hprevious,
      hone, failureThreshold_of_odd (K := K) A₁ (i.val - 2) hbefore]
    push_cast at hformula ⊢
    linarith

/-- The two capped mixed defects at the failure boundary reach the two
complementary alternating thresholds. -/
structure Beli2019Lemma912TopMixedDefectBounds
    (source : GoodBONG q L (N + 3))
    (c : GoodBONG s Q (N + 3)) (A₁ : Int)
    (i : RepresentationIndex (N + 3) (N + 3)) : Prop where
  diagonal :
    (((failureThreshold (K := K) A₁ (i.val - 1) : Int) : ℚ) :
        WithTop ℚ) ≤
      source.truncatedPrefixDefect c 1 i.val i.val
  shifted :
    (((failureThreshold (K := K) A₁ (i.val - 2) : Int) : ℚ) :
        WithTop ℚ) ≤
      source.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)

set_option maxHeartbeats 1200000 in
-- Four discrete alpha/defect roundings are combined with dependent prefix caps.
/-- A failed scalar inequality forces both top mixed-prefix defect bounds. -/
theorem topMixedDefectBounds
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, z} K]
    [comparisonParity : Beli2009AlphaParityLaws.{u, z} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (hdefectSource :
      (a.castLength hlength).RepresentationDefectCondition c)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hfailure :
      (((E.bong.castLength hlength).order ⟨i.val, i.lt_large⟩ -
          (E.bong.castLength hlength).order
            (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          (A₁ : ℚ) <
        (E.bong.castLength hlength).representationAlphaValue c i)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (P : Beli2019Lemma912ComparisonFirstAlphaProfile c A₁)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K) :
    Beli2019Lemma912TopMixedDefectBounds
      (a.castLength hlength) c A₁ i := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  let first := failureThreshold (K := K) A₁ (i.val - 1)
  let second := failureThreshold (K := K) A₁ (i.val - 2)
  let shift : ℚ :=
    ((target.order ⟨i.val, i.lt_large⟩ -
      target.order (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) + (A₁ : ℚ)
  have hcomparison := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    exact E.representationAlphaValue_le_source
      a c D horders hlength hdefectSourceTarget i hiTwo
  have hcomparisonTop :
      (target.representationAlphaValue c i : WithTop ℚ) ≤
        (source.representationAlphaValue c i : WithTop ℚ) := by
    exact_mod_cast hcomparison
  have hfailureTop : (shift : WithTop ℚ) <
      (target.representationAlphaValue c i : WithTop ℚ) := by
    apply WithTop.coe_lt_coe.mpr
    simpa only [shift] using hfailure
  have hsourceStrict : (shift : WithTop ℚ) <
      (source.representationAlphaValue c i : WithTop ℚ) :=
    hfailureTop.trans_le hcomparisonTop
  have hshiftFirst : shift = ((first - 1 : Int) : ℚ) := by
    exact failureShift_eq_threshold_sub_one
      target c i hiTwo O hformula
  have hfirstStrict : ((((first - 1 : Int) : ℚ) : WithTop ℚ)) <
      source.truncatedPrefixDefect c 1 i.val i.val := by
    rw [← hshiftFirst]
    exact hsourceStrict.trans_le (hdefectSource i)
  have hfirstRawStrict : ((((first - 1 : Int) : ℚ) : WithTop ℚ)) <
      defectOrder (K := K)
        ((1 : Kˣ) * source.prefixProduct i.val * c.prefixProduct i.val) :=
    hfirstStrict.trans_le
      (source.truncatedPrefixDefect_le_defect c 1 i.val i.val)
  have hfirstRaw : (((first : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K)
        ((1 : Kˣ) * source.prefixProduct i.val * c.prefixProduct i.val) := by
    simpa only [show first - 1 + 1 = first by omega] using
      intCast_add_one_le_defectOrder_of_lt
        ((1 : Kˣ) * source.prefixProduct i.val * c.prefixProduct i.val)
          (first - 1) hfirstRawStrict
  have hleftAlphaUpper := source.representationAlpha_le_leftAlpha
    c hdefectSource i
  rw [← source.coe_representationAlphaValue c i] at hleftAlphaUpper
  have hleftAlphaStrict : ((first - 1 : Int) : ℚ) <
      source.alphaValue ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
    apply WithTop.coe_lt_coe.mp
    rw [← hshiftFirst]
    exact hsourceStrict.trans_le hleftAlphaUpper
  have hleftAlpha : (first : ℚ) ≤
      source.alphaValue ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
    have hround := by
      letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
      letI : Beli2009AlphaParityLaws.{u, v} K := sourceParity
      exact source.intCast_add_one_le_alphaValue_of_lt_of_le_twoE
        ⟨i.val - 1, by have := i.lt_large; omega⟩ (first - 1)
          (by have := failureThreshold_lt_twoE P (i.val - 1); omega)
          hleftAlphaStrict
    simpa only [show first - 1 + 1 = first by omega] using hround
  have hrightAlphaUpper := source.representationAlpha_le_rightAlpha
    c hdefectSource i
  rw [← source.coe_representationAlphaValue c i] at hrightAlphaUpper
  have hrightAlphaStrict : ((first - 1 : Int) : ℚ) <
      c.alphaValue ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
    apply WithTop.coe_lt_coe.mp
    rw [← hshiftFirst]
    exact hsourceStrict.trans_le hrightAlphaUpper
  have hrightAlpha : (first : ℚ) ≤
      c.alphaValue ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
    have hround := by
      letI : Beli2006AlphaLaws.{u, z} K := comparisonLaws
      letI : Beli2009AlphaParityLaws.{u, z} K := comparisonParity
      exact c.intCast_add_one_le_alphaValue_of_lt_of_le_twoE
        ⟨i.val - 1, by have := i.lt_large; omega⟩ (first - 1)
          (by have := failureThreshold_lt_twoE P (i.val - 1); omega)
          hrightAlphaStrict
    simpa only [show first - 1 + 1 = first by omega] using hround
  have hfirstBound : ((first : ℚ) : WithTop ℚ) ≤
      source.truncatedPrefixDefect c 1 i.val i.val := by
    unfold truncatedPrefixDefect
    apply le_min hfirstRaw
    apply le_min
    · rw [source.prefixAlphaCap_of_internal i.pos i.lt_large]
      exact_mod_cast hleftAlpha
    · rw [c.prefixAlphaCap_of_internal i.pos i.lt_large]
      exact_mod_cast hrightAlpha
  have hsourceCurrent : source.order ⟨i.val, i.lt_large⟩ =
      target.order ⟨i.val, i.lt_large⟩ :=
    (E.order_castLength_eq_source_of_two_le
      a D horders hlength ⟨i.val, i.lt_large⟩ hiTwo).symm
  have hshiftSecond : shift =
      (((source.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) +
        ((second - 1 : Int) : ℚ)) := by
    exact failureShift_eq_orderDifference_add_previousThreshold_sub_one
      source target c i hiTwo O hsourceCurrent hformula
  have hprimaryUpper := source.representationAlpha_le_primary c i
  rw [← source.coe_representationAlphaValue c i] at hprimaryUpper
  have hprimaryStrict := hsourceStrict.trans_le hprimaryUpper
  unfold representationPrimaryDefect at hprimaryStrict
  rw [hshiftSecond] at hprimaryStrict
  let coefficient : WithTop ℚ :=
    (((source.order ⟨i.val, i.lt_large⟩ -
      c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) : WithTop ℚ)
  have hsecondStrict : ((((second - 1 : Int) : ℚ) : WithTop ℚ)) <
      source.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
    apply (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp
    change coefficient + ((((second - 1 : Int) : ℚ) : WithTop ℚ)) <
      coefficient +
        source.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)
    exact hprimaryStrict
  have hsecondRawStrict : ((((second - 1 : Int) : ℚ) : WithTop ℚ)) <
      defectOrder (K := K)
        ((-1 : Kˣ) * source.prefixProduct (i.val + 1) *
          c.prefixProduct (i.val - 1)) :=
    hsecondStrict.trans_le
      (source.truncatedPrefixDefect_le_defect c (-1)
        (i.val + 1) (i.val - 1))
  have hsecondRaw : (((second : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K)
        ((-1 : Kˣ) * source.prefixProduct (i.val + 1) *
          c.prefixProduct (i.val - 1)) := by
    simpa only [show second - 1 + 1 = second by omega] using
      intCast_add_one_le_defectOrder_of_lt
        ((-1 : Kˣ) * source.prefixProduct (i.val + 1) *
          c.prefixProduct (i.val - 1)) (second - 1) hsecondRawStrict
  have hsecondLeftCap : ((second : ℚ) : WithTop ℚ) ≤
      source.prefixAlphaCap (i.val + 1) := by
    by_cases hfull : i.val + 1 = N + 3
    · rw [hfull, source.prefixAlphaCap_last]
      exact le_top
    · have hinterior : i.val + 1 < N + 3 := by
        have := i.lt_large
        omega
      rw [source.prefixAlphaCap_of_internal (by omega) hinterior]
      have halphaStrict : ((second - 1 : Int) : ℚ) <
          source.alphaValue ⟨i.val, by have := hinterior; omega⟩ := by
        apply WithTop.coe_lt_coe.mp
        have hcap := source.truncatedPrefixDefect_le_leftCap c (-1)
          (i.val + 1) (i.val - 1)
        rw [source.prefixAlphaCap_of_internal (by omega) hinterior] at hcap
        exact hsecondStrict.trans_le hcap
      have halpha : (second : ℚ) ≤
          source.alphaValue ⟨i.val, by have := hinterior; omega⟩ := by
        have hround := by
          letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
          letI : Beli2009AlphaParityLaws.{u, v} K := sourceParity
          exact source.intCast_add_one_le_alphaValue_of_lt_of_le_twoE
            ⟨i.val, by have := hinterior; omega⟩ (second - 1)
              (by have := failureThreshold_lt_twoE P (i.val - 2); omega)
              halphaStrict
        simpa only [show second - 1 + 1 = second by omega] using hround
      exact_mod_cast halpha
  have hsecondRightCap : ((second : ℚ) : WithTop ℚ) ≤
      c.prefixAlphaCap (i.val - 1) := by
    rw [c.prefixAlphaCap_of_internal (by omega) (by
      have := i.lt_large
      omega)]
    have halphaStrict : ((second - 1 : Int) : ℚ) <
        c.alphaValue ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
      apply WithTop.coe_lt_coe.mp
      have hcap := source.truncatedPrefixDefect_le_rightCap c (-1)
        (i.val + 1) (i.val - 1)
      rw [c.prefixAlphaCap_of_internal (by omega) (by
        have := i.lt_large
        omega)] at hcap
      exact hsecondStrict.trans_le hcap
    have halpha : (second : ℚ) ≤
        c.alphaValue ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
      have hround := by
        letI : Beli2006AlphaLaws.{u, z} K := comparisonLaws
        letI : Beli2009AlphaParityLaws.{u, z} K := comparisonParity
        exact c.intCast_add_one_le_alphaValue_of_lt_of_le_twoE
          ⟨i.val - 2, by have := i.lt_large; omega⟩ (second - 1)
            (by have := failureThreshold_lt_twoE P (i.val - 2); omega)
            halphaStrict
      simpa only [show second - 1 + 1 = second by omega] using hround
    exact_mod_cast halpha
  have hsecondBound : ((second : ℚ) : WithTop ℚ) ≤
      source.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
    unfold truncatedPrefixDefect
    exact le_min hsecondRaw (le_min hsecondLeftCap hsecondRightCap)
  exact ⟨by simpa only [first] using hfirstBound,
    by simpa only [second] using hsecondBound⟩

end BONG.GoodBONG.Beli2019Lemma910Data

end Bong
