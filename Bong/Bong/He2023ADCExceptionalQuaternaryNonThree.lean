/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCExceptionalQuaternaryTesting

/-!
# The exceptional quaternary lattice is not 3-ADC

This file formalizes He (2025), Lemma 6.12(ii).  A maximal ternary test
with order profile `0,-2e,1` is selected by the two-column ambient-space
alternative.  At the terminal representation index, its full mixed defect
is zero while the comparison invariant is at least one half, contradicting
condition (ii) of Theorem 3.6.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {W : Type u} [AddCommGroup W] [Module K W]
  {r : QuadraticSpace K W} {M : Lattice K W}

/-- The common maximal ternary profile used in Lemma 6.12(ii). -/
def HeADCExceptionalTernaryTestOrders (b : GoodBONG r M 3) : Prop :=
  ∀ i, b.order i = (![0, -(2 * (ramificationIndex K : Int)), 1] : Fin 3 → Int) i

/-- The full mixed prefix at the terminal comparison index has odd order
and therefore zero defect. -/
theorem heADCExceptional_ternaryTerminalDefect_zero (b : GoodBONG r M 3)
    (hb : HeADCExceptionalTernaryTestOrders b) :
    (heADCExceptionalQuaternaryCandidate (K := K)).truncatedPrefixDefect b 1 3 3 = 0 := by
  let a := heADCExceptionalQuaternaryCandidate (K := K)
  apply a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed b 1 3 3
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  rw [ordUnit_mul, ordUnit_mul, hone,
    a.ordUnit_prefixProduct_eq_orderSequence_prefixSum 3 (by omega),
    b.ordUnit_prefixProduct_eq_orderSequence_prefixSum 3 (by omega)]
  simp only [BeliOrderSequence.prefixSum_succ, BeliOrderSequence.prefixSum_zero,
    BeliOrderSequence.entryOrZero_of_lt _ (by decide : 0 < 4),
    BeliOrderSequence.entryOrZero_of_lt _ (by decide : 1 < 4),
    BeliOrderSequence.entryOrZero_of_lt _ (by decide : 2 < 4),
    BeliOrderSequence.entryOrZero_of_lt _ (by decide : 0 < 3),
    BeliOrderSequence.entryOrZero_of_lt _ (by decide : 1 < 3),
    BeliOrderSequence.entryOrZero_of_lt _ (by decide : 2 < 3)]
  change Odd (0 + (0 + a.order 0 + a.order 1 + a.order 2) +
    (0 + b.order 0 + b.order 1 + b.order 2))
  rw [heADCExceptionalQuaternaryCandidate_orders,
    heADCExceptionalQuaternaryCandidate_orders,
    heADCExceptionalQuaternaryCandidate_orders, hb, hb, hb]
  simp

/-- The preceding mixed defect in the primary comparison candidate is at
least `2e`. -/
theorem heADCExceptional_ternaryPreviousDefect_ge_twoE (b : GoodBONG r M 3)
    (hM : Lattice.IsIntegral r M) (hb : HeADCExceptionalTernaryTestOrders b) :
    (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) ≤
      (heADCExceptionalQuaternaryCandidate (K := K)).truncatedPrefixDefect
        b (-1) 4 2 := by
  let a := heADCExceptionalQuaternaryCandidate (K := K)
  let E : WithTop ℚ := ((2 * (ramificationIndex K : ℚ) : ℚ) : ℚ)
  have hbOne : b.order (1 : Fin 3) = -(2 * (ramificationIndex K : Int)) := by
    simpa using hb 1
  have hbPrefix : E ≤ defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) := by
    simpa [E, BONG.signedEvenPrefixProduct, GoodBONG.prefixProduct] using
      b.heADCEvenEndpoint_signedPrefix_defect 0 (by omega) hM hbOne
  have haPrefix : E ≤ defectOrder (K := K) (a.prefixProduct 4) := by
    rw [heADCExceptionalQuaternaryCandidate_fullDefect]
  have hraw : E ≤ defectOrder (K := K)
      ((-1 : Kˣ) * a.prefixProduct 4 * b.prefixProduct 2) := by
    calc
      E ≤ min (defectOrder (K := K) (a.prefixProduct 4))
          (defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2)) :=
        le_min haPrefix hbPrefix
      _ ≤ defectOrder (K := K)
          (a.prefixProduct 4 * ((-1 : Kˣ) * b.prefixProduct 2)) :=
        defectOrder_mul_ge_min _ _
      _ = defectOrder (K := K)
          ((-1 : Kˣ) * a.prefixProduct 4 * b.prefixProduct 2) := by
        congr 1
        ac_rfl
  have hgap : 2 * (ramificationIndex K : Int) < b.orderGap (1 : Fin 2) := by
    unfold orderGap
    change 2 * (ramificationIndex K : Int) < b.order (2 : Fin 3) - b.order (1 : Fin 3)
    rw [show b.order 2 = 1 by simpa using hb 2,
      show b.order 1 = -(2 * (ramificationIndex K : Int)) by simpa using hb 1]
    omega
  have halpha : 2 * (ramificationIndex K : ℚ) < b.alphaValue (1 : Fin 2) :=
    ((b.heADC2025Proposition33 1).compareTwoE.1).mp hgap
  unfold truncatedPrefixDefect
  rw [a.prefixAlphaCap_last, b.prefixAlphaCap_of_internal (by omega) (by omega)]
  exact le_min hraw (le_min le_top (WithTop.coe_le_coe.mpr halpha.le))

/-- At the terminal index, the comparison invariant is at least one half. -/
theorem heADCExceptional_ternaryTerminalAlpha_ge_half (b : GoodBONG r M 3)
    (hM : Lattice.IsIntegral r M) (hb : HeADCExceptionalTernaryTestOrders b) :
    (((1 / 2 : ℚ) : ℚ) : WithTop ℚ) ≤
      ((heADCExceptionalQuaternaryCandidate (K := K)).representationAlphaValue b
        ⟨3, by omega, by omega, le_rfl⟩ : ℚ) := by
  let a := heADCExceptionalQuaternaryCandidate (K := K)
  let i : RepresentationIndex 4 3 := ⟨3, by omega, by omega, le_rfl⟩
  change (((1 / 2 : ℚ) : ℚ) : WithTop ℚ) ≤
    ((a.representationAlphaValue b i : ℚ) : WithTop ℚ)
  have hprevious := heADCExceptional_ternaryPreviousDefect_ge_twoE b hM hb
  have hhalf : a.representationHalfGap b i = (((1 / 2 : ℚ) : ℚ) : WithTop ℚ) := by
    unfold representationHalfGap
    simp only [i]
    rw [heADCExceptionalQuaternaryCandidate_orders, hb]
    apply congrArg ((↑) : ℚ → WithTop ℚ)
    push_cast
    ring
  have hprimary : (((1 / 2 : ℚ) : ℚ) : WithTop ℚ) ≤
      a.representationPrimaryDefect b i := by
    unfold representationPrimaryDefect
    simp only [i]
    rw [heADCExceptionalQuaternaryCandidate_orders, hb]
    calc
      (((1 / 2 : ℚ) : ℚ) : WithTop ℚ) ≤
          ((((2 - 2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) :
            WithTop ℚ) +
            (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ)) := by
        rw [← WithTop.coe_add]
        apply WithTop.coe_le_coe.mpr
        push_cast
        linarith
      _ ≤ ((((2 - 2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) :
          WithTop ℚ) + a.truncatedPrefixDefect b (-1) 4 2) :=
        by
          simpa only [add_comm] using
            (add_le_add_left hprevious
              (((2 - 2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) : WithTop ℚ))
  rw [coe_representationAlphaValue, a.representationAlpha_eq_min_halfGap_prime b i,
    a.representationAlphaPrime_eq_primary_of_not_interior b i (by simp [i]), hhalf]
  exact le_min le_rfl hprimary

/-- No ternary lattice with the published maximal test profile can be
integrally represented by the exceptional candidate. -/
theorem heADCExceptionalQuaternaryCandidate_not_represents_ternaryProfile
    (b : GoodBONG r M 3) (hM : Lattice.IsIntegral r M)
    (hb : HeADCExceptionalTernaryTestOrders b) :
    ¬ Lattice.Represents (heADCExceptionalQuaternaryForm (K := K)) r
      (heADCExceptionalQuaternaryLattice (K := K)) M := by
  intro hrep
  let a := heADCExceptionalQuaternaryCandidate (K := K)
  let i : RepresentationIndex 4 3 := ⟨3, by omega, by omega, le_rfl⟩
  have hconditions := (heADC2025Theorem36Published (by omega) hrep.ambient a b).mp hrep
  have hzero := heADCExceptional_ternaryTerminalDefect_zero b hb
  have hhalf := heADCExceptional_ternaryTerminalAlpha_ge_half b hM hb
  have hfalse : (((1 / 2 : ℚ) : ℚ) : WithTop ℚ) ≤ 0 := by
    calc
      (((1 / 2 : ℚ) : ℚ) : WithTop ℚ) ≤
          (a.representationAlphaValue b i : WithTop ℚ) := hhalf
      _ ≤ a.truncatedPrefixDefect b 1 3 3 := hconditions.defectCondition i
      _ = 0 := hzero
  norm_num at hfalse

/-- He (2025), Lemma 6.12(ii): the exceptional quaternary lattice is not 3-ADC. -/
theorem heADCExceptionalQuaternaryCandidate_not_is3ADC :
    ¬ Lattice.IsNADC.{u, u, u} (heADCExceptionalQuaternaryForm (K := K))
      (heADCExceptionalQuaternaryLattice (K := K)) 3 := by
  intro hADC
  let a := heADCExceptionalQuaternaryCandidate (K := K)
  let epsilon : Kˣ := 1
  have hepsilon : IsValuationUnit K (epsilon : K) := by simp [epsilon, IsValuationUnit]
  let c := epsilon * uniformizerPowerUnit K 1
  let first := heADCW1Odd 0 c
  let second := heADCW2Odd 0 c
  have hpair := heADC2025Proposition42iOdd (K := K) 0 c
  have hchoice := heADC2025Lemma45iCodimensionOne first second hpair a.valueUnit
  rcases hchoice with ⟨hfirst, _⟩ | ⟨_, hsecond⟩
  · let b := heADCMaximalGoodBONG first
    have hrep := (a.heADCMaximal_represents_iff_diagonalRepresents hADC first).mpr hfirst
    have hprofileRaw := (heADC2025Lemma412iiiFirstPublished epsilon hepsilon 0 b
      (heHuOMaximalLattice_isOMaximal first).isIntegral
      (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
    have hprofile : HeADCExceptionalTernaryTestOrders b := by
      intro i
      have h := hprofileRaw i
      fin_cases i <;> simpa [heADCMaximalOrderProfile, b, first, c] using h
    exact heADCExceptionalQuaternaryCandidate_not_represents_ternaryProfile b
      (heHuOMaximalLattice_isOMaximal first).isIntegral hprofile hrep
  · let b := heADCMaximalGoodBONG second
    have hrep := (a.heADCMaximal_represents_iff_diagonalRepresents hADC second).mpr hsecond
    have hprofileRaw := (heADC2025Lemma412iiiSecondPublished epsilon hepsilon 0 b
      (heHuOMaximalLattice_isOMaximal second).isIntegral
      (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
    have hprofile : HeADCExceptionalTernaryTestOrders b := by
      intro i
      have h := hprofileRaw i
      fin_cases i <;> simpa [heADCMaximalOrderProfile, b, second, c] using h
    exact heADCExceptionalQuaternaryCandidate_not_represents_ternaryProfile b
      (heHuOMaximalLattice_isOMaximal second).isIntegral hprofile hrep

end BONG.GoodBONG

end Bong
