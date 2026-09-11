/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCQuaternaryBoundaryTesting
import Bong.Bong.He2023ADCOddMaximalStructure

/-!
# The second-column quaternary boundary lattice is not 3-ADC

The published proof of He (2025), Theorem 7.1, excludes only the exceptional
first-column lattice from Lemma 6.12. The separate second-column 2-ADC
boundary must also be excluded. For either maximal ternary ambient space,
the terminal mixed defect is zero while the comparison invariant is at least
one half.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {W : Type u} [AddCommGroup W] [Module K W]
  {r : QuadraticSpace K W} {M : Lattice K W}

/-- The two possible maximal ternary order profiles for a unit parameter. -/
def HeADCBoundaryTernaryTestOrders (b : GoodBONG r M 3) : Prop :=
  b.order 0 = 0 ∧
    (b.order 1 = -(2 * (ramificationIndex K : Int)) ∨
      b.order 1 = 2 - 2 * (ramificationIndex K : Int)) ∧
    b.order 2 = 0

/-- The terminal mixed product has odd order for either unit-parameter
maximal ternary profile. -/
theorem heADCBoundary_ternaryTerminalDefect_zero (b : GoodBONG r M 3)
    (hb : HeADCBoundaryTernaryTestOrders b) :
    (heADCQuaternaryBoundaryCandidate (K := K)).truncatedPrefixDefect b 1 3 3 = 0 := by
  let a := heADCQuaternaryBoundaryCandidate (K := K)
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
  have haZero : a.order 0 = 0 := by
    simpa using heADCQuaternaryBoundaryCandidate_orders (K := K) 0
  have haOne : a.order 1 = -(2 * (ramificationIndex K : Int)) := by
    simpa using heADCQuaternaryBoundaryCandidate_orders (K := K) 1
  have haTwo : a.order 2 = 1 := by
    simpa using heADCQuaternaryBoundaryCandidate_orders (K := K) 2
  rw [haZero, haOne, haTwo, hb.1, hb.2.2]
  rcases hb.2.1 with hstandard | hraised
  · rw [hstandard]
    refine ⟨-(2 * ramificationIndex K), ?_⟩
    norm_num
    ring
  · rw [hraised]
    refine ⟨1 - 2 * ramificationIndex K, ?_⟩
    norm_num
    ring

/-- The preceding mixed defect is bounded below by `2e-1`. This single
bound covers both maximal unit-parameter ternary profiles. -/
theorem heADCBoundary_ternaryPreviousDefect_ge_twoE_sub_one
    (b : GoodBONG r M 3)
    (hcapped : (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) ≤
      b.heADCAdjacentCappedDefect 0) :
    (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) ≤
      (heADCQuaternaryBoundaryCandidate (K := K)).truncatedPrefixDefect
        b (-1) 4 2 := by
  let a := heADCQuaternaryBoundaryCandidate (K := K)
  let T : WithTop ℚ := ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : ℚ)
  let E : WithTop ℚ := ((2 * (ramificationIndex K : ℚ) : ℚ) : ℚ)
  have hcapped' : T ≤ b.truncatedPrefixDefect b (-1) 0 2 := by
    simpa [T, heADCAdjacentCappedDefect, heHuAdjacentCappedDefect] using hcapped
  have hbRaw' := hcapped'.trans (b.truncatedPrefixDefect_le_defect b (-1) 0 2)
  have hbRaw : T ≤ defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) := by
    simpa [GoodBONG.prefixProduct, BONG.prefixProduct] using hbRaw'
  have hbCap : T ≤ b.prefixAlphaCap 2 :=
    hcapped'.trans (b.truncatedPrefixDefect_le_rightCap b (-1) 0 2)
  have hTE : T ≤ E := by
    apply WithTop.coe_le_coe.mpr
    linarith
  have haRaw : E ≤ defectOrder (K := K) (a.prefixProduct 4) := by
    rw [heADCQuaternaryBoundaryCandidate_fullDefect]
  have hraw : T ≤ defectOrder (K := K)
      ((-1 : Kˣ) * a.prefixProduct 4 * b.prefixProduct 2) := by
    calc
      T ≤ min (defectOrder (K := K) (a.prefixProduct 4))
          (defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2)) :=
        le_min (hTE.trans haRaw) hbRaw
      _ ≤ defectOrder (K := K)
          (a.prefixProduct 4 * ((-1 : Kˣ) * b.prefixProduct 2)) :=
        defectOrder_mul_ge_min _ _
      _ = defectOrder (K := K)
          ((-1 : Kˣ) * a.prefixProduct 4 * b.prefixProduct 2) := by
        congr 1
        ac_rfl
  unfold truncatedPrefixDefect
  rw [a.prefixAlphaCap_last]
  exact le_min hraw (le_min le_top hbCap)

/-- The comparison invariant at the terminal representation index is at
least one half. -/
theorem heADCBoundary_ternaryTerminalAlpha_ge_half (b : GoodBONG r M 3)
    (hb : HeADCBoundaryTernaryTestOrders b)
    (hcapped : (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) ≤
      b.heADCAdjacentCappedDefect 0) :
    (((1 / 2 : ℚ) : ℚ) : WithTop ℚ) ≤
      ((heADCQuaternaryBoundaryCandidate (K := K)).representationAlphaValue b
        ⟨3, by omega, by omega, le_rfl⟩ : ℚ) := by
  let a := heADCQuaternaryBoundaryCandidate (K := K)
  let i : RepresentationIndex 4 3 := ⟨3, by omega, by omega, le_rfl⟩
  change (((1 / 2 : ℚ) : ℚ) : WithTop ℚ) ≤
    ((a.representationAlphaValue b i : ℚ) : WithTop ℚ)
  have hprevious := heADCBoundary_ternaryPreviousDefect_ge_twoE_sub_one b hcapped
  have hbTwo : b.order (⟨3 - 1, by omega⟩ : Fin 3) = 0 := by
    simpa using hb.2.2
  have hhalf : a.representationHalfGap b i = (((3 / 2 : ℚ) : ℚ) : WithTop ℚ) := by
    unfold representationHalfGap
    simp only [i]
    rw [heADCQuaternaryBoundaryCandidate_orders, hbTwo]
    apply congrArg ((↑) : ℚ → WithTop ℚ)
    push_cast
    ring
  have hprimary : (((1 / 2 : ℚ) : ℚ) : WithTop ℚ) ≤
      a.representationPrimaryDefect b i := by
    unfold representationPrimaryDefect
    simp only [i]
    rw [heADCQuaternaryBoundaryCandidate_orders, hbTwo]
    calc
      (((1 / 2 : ℚ) : ℚ) : WithTop ℚ) ≤
          ((((3 - 2 * (ramificationIndex K : Int) - 0 : Int) : ℚ) :
            WithTop ℚ) +
            (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) := by
        rw [← WithTop.coe_add]
        apply WithTop.coe_le_coe.mpr
        push_cast
        linarith
      _ ≤ ((((3 - 2 * (ramificationIndex K : Int) - 0 : Int) : ℚ) :
          WithTop ℚ) + a.truncatedPrefixDefect b (-1) 4 2) := by
        simpa only [add_comm] using
          (add_le_add_left hprevious
            (((3 - 2 * (ramificationIndex K : Int) - 0 : Int) : ℚ) : WithTop ℚ))
  rw [coe_representationAlphaValue, a.representationAlpha_eq_min_halfGap_prime b i,
    a.representationAlphaPrime_eq_primary_of_not_interior b i (by simp [i]), hhalf]
  exact le_min (by norm_num) hprimary

/-- No maximal ternary lattice with either unit-parameter profile is
integrally represented by the boundary candidate under the stated capped
defect lower bound. -/
theorem heADCQuaternaryBoundaryCandidate_not_represents_ternaryProfile
    (b : GoodBONG r M 3) (hb : HeADCBoundaryTernaryTestOrders b)
    (hcapped : (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) ≤
      b.heADCAdjacentCappedDefect 0) :
    ¬ Lattice.Represents (heADCQuaternaryBoundaryForm (K := K)) r
      (heADCQuaternaryBoundaryLattice (K := K)) M := by
  intro hrep
  let a := heADCQuaternaryBoundaryCandidate (K := K)
  let i : RepresentationIndex 4 3 := ⟨3, by omega, by omega, le_rfl⟩
  have hconditions := (heADC2025Theorem36Published (by omega) hrep.ambient a b).mp hrep
  have hzero := heADCBoundary_ternaryTerminalDefect_zero b hb
  have hhalf := heADCBoundary_ternaryTerminalAlpha_ge_half b hb hcapped
  have hfalse : (((1 / 2 : ℚ) : ℚ) : WithTop ℚ) ≤ 0 := by
    calc
      (((1 / 2 : ℚ) : ℚ) : WithTop ℚ) ≤
          (a.representationAlphaValue b i : WithTop ℚ) := hhalf
      _ ≤ a.truncatedPrefixDefect b 1 3 3 := hconditions.defectCondition i
      _ = 0 := hzero
  norm_num at hfalse

/-- The omitted second-column boundary in the printed proof of Theorem 7.1
is also not 3-ADC. -/
theorem heADCQuaternaryBoundaryCandidate_not_is3ADC :
    ¬ Lattice.IsNADC.{u, u, u} (heADCQuaternaryBoundaryForm (K := K))
      (heADCQuaternaryBoundaryLattice (K := K)) 3 := by
  intro hADC
  let a := heADCQuaternaryBoundaryCandidate (K := K)
  let epsilon : Kˣ := 1
  have hepsilon : IsValuationUnit K (epsilon : K) := by
    simp [epsilon, IsValuationUnit]
  let first := heADCW1Odd 0 epsilon
  let second := heADCW2Odd 0 epsilon
  have hpair := heADC2025Proposition42iOdd (K := K) 0 epsilon
  have hchoice := heADC2025Lemma45iCodimensionOne first second hpair a.valueUnit
  rcases hchoice with ⟨hfirst, _⟩ | ⟨_, hsecond⟩
  · let b := heADCMaximalGoodBONG first
    have hmax := heHuOMaximalLattice_isOMaximal first
    have hrep := (a.heADCMaximal_represents_iff_diagonalRepresents hADC first).mpr hfirst
    have hprofileRaw := (heADC2025Lemma412iPublished epsilon hepsilon 0 b
      hmax.isIntegral (QuadraticSpace.isIsometric_refl _)).mp
        (Lattice.isIsometric_refl _ _)
    have hbZero : b.order 0 = 0 := by
      have h := hprofileRaw 0
      simpa [heADCMaximalOrderProfile, b, first, epsilon] using h
    have hbOne : b.order 1 = -(2 * (ramificationIndex K : Int)) := by
      have h := hprofileRaw 1
      simpa [heADCMaximalOrderProfile, b, first, epsilon] using h
    have hbTwo : b.order 2 = 0 := by
      have h := hprofileRaw 2
      simpa [heADCMaximalOrderProfile, b, first, epsilon] using h
    have hb : HeADCBoundaryTernaryTestOrders b := by
      exact ⟨hbZero, Or.inl hbOne, hbTwo⟩
    have hstructure := heADC2025Proposition413 0 b hmax
    have hstandard := hstructure.standardTail hbOne
    have hthreshold :
        (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) ≤
          b.heADCAdjacentCappedDefect 0 := by
      calc
        (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) ≤
            (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) := by
          apply WithTop.coe_le_coe.mpr
          linarith
        _ ≤ b.heADCAdjacentCappedDefect 0 := hstandard.2.2.2
    exact heADCQuaternaryBoundaryCandidate_not_represents_ternaryProfile b hb
      hthreshold hrep
  · let b := heADCMaximalGoodBONG second
    have hmax := heHuOMaximalLattice_isOMaximal second
    have hrep := (a.heADCMaximal_represents_iff_diagonalRepresents hADC second).mpr hsecond
    have hprofileRaw := (heADC2025Lemma412iiPublished epsilon hepsilon 0 b
      hmax.isIntegral (QuadraticSpace.isIsometric_refl _)).mp
        (Lattice.isIsometric_refl _ _)
    have hbZero : b.order 0 = 0 := by
      have h := hprofileRaw 0
      simpa [heADCMaximalOrderProfile, b, second, epsilon] using h
    have hbOne : b.order 1 = 2 - 2 * (ramificationIndex K : Int) := by
      have h := hprofileRaw 1
      simpa [heADCMaximalOrderProfile, b, second, epsilon] using h
    have hbTwo : b.order 2 = 0 := by
      have h := hprofileRaw 2
      simpa [heADCMaximalOrderProfile, b, second, epsilon] using h
    have hb : HeADCBoundaryTernaryTestOrders b := by
      exact ⟨hbZero, Or.inr hbOne, hbTwo⟩
    have hstructure := heADC2025Proposition413 0 b hmax
    have hraised := hstructure.raisedTail hbOne
    have hthreshold :
        (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) ≤
          b.heADCAdjacentCappedDefect 0 := by
      exact le_of_eq hraised.2.2.1.symm
    exact heADCQuaternaryBoundaryCandidate_not_represents_ternaryProfile b hb
      hthreshold hrep

end BONG.GoodBONG

end Bong
