/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328ScaledCoefficientShift

/-!
# The zero-left specialization of O'Meara 93:19

The determinant correction in 93:28 applies 93:19 to the plane
`A(0,-lambda)` and a represented norm generator `delta` of the next
modular component.  This file constructs that specialization and proves
that the binary exchange complement has exactly the old tail norm ideal.
The latter fact is needed to install the output as a Jordan component,
not merely as an abstract modular complement.
-/

namespace Bong

open Dyadic Module

namespace Lattice.Omeara9319ExchangeSetup

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {s : Kˣ}

/-- The exact scalar setup used to replace `A(0,-lambda)` by
`A(delta,-lambda)`. -/
noncomputable def zeroLeft
    (hL : IsModular q L s) (hpos : 0 < finrank K V)
    (lambda : K) (hlambda : lambda ∈ IntegerRing K)
    (hscale : IsInMaximalIdeal K (s : K))
    (delta : Kˣ) (hdelta : (delta : K) ∈ normGroupSet q L) :
    Omeara9319ExchangeSetup q L s :=
  ofRepresentedScalar hL hpos 0 (-lambda) (delta : K)
    (IntegerRing K).zero_mem ((IntegerRing K).neg_mem lambda hlambda)
    hscale (by simpa [IsValuationUnit]) hdelta

@[simp]
theorem zeroLeft_alpha
    (hL : IsModular q L s) (hpos : 0 < finrank K V)
    (lambda : K) (hlambda : lambda ∈ IntegerRing K)
    (hscale : IsInMaximalIdeal K (s : K))
    (delta : Kˣ) (hdelta : (delta : K) ∈ normGroupSet q L) :
    (zeroLeft hL hpos lambda hlambda hscale delta hdelta).alpha = 0 := rfl

@[simp]
theorem zeroLeft_beta
    (hL : IsModular q L s) (hpos : 0 < finrank K V)
    (lambda : K) (hlambda : lambda ∈ IntegerRing K)
    (hscale : IsInMaximalIdeal K (s : K))
    (delta : Kˣ) (hdelta : (delta : K) ∈ normGroupSet q L) :
    (zeroLeft hL hpos lambda hlambda hscale delta hdelta).beta =
      -lambda := rfl

@[simp]
theorem zeroLeft_delta
    (hL : IsModular q L s) (hpos : 0 < finrank K V)
    (lambda : K) (hlambda : lambda ∈ IntegerRing K)
    (hscale : IsInMaximalIdeal K (s : K))
    (delta : Kˣ) (hdelta : (delta : K) ∈ normGroupSet q L) :
    (zeroLeft hL hpos lambda hlambda hscale delta hdelta).delta =
      (delta : K) := rfl

/-- In the zero-left specialization the new displayed coefficient is
literally `delta`. -/
theorem zeroLeft_newCoefficient
    (hL : IsModular q L s) (hpos : 0 < finrank K V)
    (lambda : K) (hlambda : lambda ∈ IntegerRing K)
    (hscale : IsInMaximalIdeal K (s : K))
    (delta : Kˣ) (hdelta : (delta : K) ∈ normGroupSet q L) :
    let E := zeroLeft hL hpos lambda hlambda hscale delta hdelta
    E.alpha + (s : K) * E.gamma = (delta : K) := by
  let E := zeroLeft hL hpos lambda hlambda hscale delta hdelta
  change E.alpha + (s : K) * E.gamma = (delta : K)
  rw [show E.alpha = 0 by rfl, zero_add, ← E.delta_eq]
  rfl

/-- The old general plane in the zero-left setup is the coordinate swap of
the one-parameter plane `A(-lambda,0)`, with the harmless scale-one
rescaling made explicit. -/
noncomputable def zeroLeftOldPlaneToNegativeCoefficient
    (hL : IsModular q L s) (hpos : 0 < finrank K V)
    (lambda : K) (hlambda : lambda ∈ IntegerRing K)
    (hscale : IsInMaximalIdeal K (s : K))
    (delta : Kˣ) (hdelta : (delta : K) ∈ normGroupSet q L) :
    let E := zeroLeft hL hpos lambda hlambda hscale delta hdelta
    Isometry E.oldPlane
      ((QuadraticSpace.omearaPlane (-lambda)).rescaleUnit (1 : Kˣ))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
  let E := zeroLeft hL hpos lambda hlambda hscale delta hdelta
  let swap := omearaGeneralPlaneSwapLatticeIsometry
    (0 : K) (-lambda) (by simp)
  let identify := omearaGeneralPlaneZeroRightLatticeIsometry (-lambda)
  let addScale :=
    (Isometry.rescaleUnitOne (QuadraticSpace.omearaPlane (-lambda))
      (hyperbolicPlaneLattice (K := K))).symm
  have h : Isometry
      (QuadraticSpace.omearaGeneralPlane 0 (-lambda) (by simp))
      ((QuadraticSpace.omearaPlane (-lambda)).rescaleUnit (1 : Kˣ))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) :=
    swap.trans (identify.trans addScale)
  simpa only [E, Omeara9319ExchangeSetup.oldPlane,
    zeroLeft_alpha, zeroLeft_beta] using h

private theorem mul_integral_mem_principalIdeal
    (delta x c : K) (hx : x ∈ principalIdeal (K := K) delta)
    (hc : c ∈ IntegerRing K) :
    x * c ∈ principalIdeal (K := K) delta := by
  let cO : IntegerRing K := ⟨c, hc⟩
  have h := (principalIdeal (K := K) delta).smul_mem cO hx
  change c * x ∈ principalIdeal (K := K) delta at h
  simpa only [mul_comm] using h

/-- If a 93:19 exchange kills the first coefficient of the displayed
unimodular plane, its binary complement has no values outside the old
tail norm ideal.  This is the estimate needed in 93:28, Step 6: unlike
the zero-left determinant correction, the exchanged binary complement
need not itself represent a generator of that ideal. -/
theorem exchangeComplement_normIdeal_le_of_newCoefficient_zero
    (E : Omeara9319ExchangeSetup q L s)
    (hL : IsModular q L s) (hpos : 0 < finrank K V)
    (delta : Kˣ) (hdelta : IsNormGeneratorValue q L delta)
    (hzero : E.alpha + (s : K) * E.gamma = 0)
    (halpha : E.alpha ∈ principalIdeal (K := K) (delta : K))
    (hbetaScaleSq : E.beta * (s : K) ^ 2 ∈
      principalIdeal (K := K) (delta : K)) :
    normIdeal E.exchangeComplement
        (hyperbolicPlaneLattice (K := K)) ≤
      principalIdeal (K := K) (delta : K) := by
  have htwoScale : principalIdeal (K := K) (2 * (s : K)) ≤
      principalIdeal (K := K) (delta : K) := by
    rw [← hdelta.2,
      ← twoScaleIdeal_eq_principalIdeal_two_mul_of_modular hL hpos]
    exact twoScaleIdeal_le_normIdeal q L
  have htwoS : (2 : K) * (s : K) ∈
      principalIdeal (K := K) (delta : K) :=
    htwoScale (generator_mem_principalIdeal ((2 : K) * (s : K)))
  have holdIntegral : E.alpha * E.beta - 1 ∈ IntegerRing K := by
    exact (IntegerRing K).sub_mem
      ((IntegerRing K).toSubring.mul_mem E.alpha_integral E.beta_integral)
      (IntegerRing K).one_mem
  have hnegScaleGamma : -(s : K) * E.gamma = E.alpha := by
    calc
      -(s : K) * E.gamma = -((s : K) * E.gamma) := by ring
      _ = E.alpha := neg_eq_of_add_eq_zero_left hzero
  apply normIdeal_le_of_quadratic_mem
  intro x hx
  have hxCoordinates := (mem_omearaPlaneLattice_iff x).mp hx
  let x0 : IntegerRing K := ⟨x 0, hxCoordinates.1⟩
  let x1 : IntegerRing K := ⟨x 1, hxCoordinates.2⟩
  have hfirst : (-(s : K) * E.gamma) * x 0 ^ 2 ∈
      principalIdeal (K := K) (delta : K) := by
    rw [hnegScaleGamma]
    exact mul_integral_mem_principalIdeal (delta : K)
      E.alpha (x 0 ^ 2) halpha
        ((IntegerRing K).toSubring.pow_mem hxCoordinates.1 2)
  have hcross :
      ((2 : K) * (s : K)) *
          ((E.alpha * E.beta - 1) * (x 0 * x 1)) ∈
        principalIdeal (K := K) (delta : K) := by
    exact mul_integral_mem_principalIdeal (delta : K)
      ((2 : K) * (s : K))
      ((E.alpha * E.beta - 1) * (x 0 * x 1)) htwoS
      ((IntegerRing K).toSubring.mul_mem holdIntegral
        ((IntegerRing K).toSubring.mul_mem hxCoordinates.1 hxCoordinates.2))
  have hlast :
      (E.beta * (s : K) ^ 2) *
          ((E.alpha * E.beta - 1) * x 1 ^ 2) ∈
        principalIdeal (K := K) (delta : K) := by
    exact mul_integral_mem_principalIdeal (delta : K)
      (E.beta * (s : K) ^ 2)
      ((E.alpha * E.beta - 1) * x 1 ^ 2) hbetaScaleSq
      ((IntegerRing K).toSubring.mul_mem holdIntegral
        ((IntegerRing K).toSubring.pow_mem hxCoordinates.2 2))
  have hformula : E.exchangeComplement.quadratic x =
      (-(s : K) * E.gamma) * x 0 ^ 2 +
        ((2 : K) * (s : K)) *
          ((E.alpha * E.beta - 1) * (x 0 * x 1)) +
        (E.beta * (s : K) ^ 2) *
          ((E.alpha * E.beta - 1) * x 1 ^ 2) := by
    change E.exchangeComplement.bilin x x = _
    unfold exchangeComplement
    rw [QuadraticSpace.omearaExchangeComplement_bilin_apply]
    ring
  rw [hformula]
  exact (principalIdeal (K := K) (delta : K)).add_mem
    ((principalIdeal (K := K) (delta : K)).add_mem hfirst hcross) hlast

/-- Norm-ideal preservation for a zero-left exchange under the exact
scalar hypotheses used in the calculation.  Unlike the convenient
`zeroLeft` constructor below, this form also applies when the modular scale
is a unit and the exchanged determinant is known directly. -/
theorem exchangeComplement_normIdeal_eq_of_zeroLeft
    (E : Omeara9319ExchangeSetup q L s)
    (hL : IsModular q L s) (hpos : 0 < finrank K V)
    (lambda : K) (delta : Kˣ)
    (hdelta : IsNormGeneratorValue q L delta)
    (halpha : E.alpha = 0) (hbeta : E.beta = -lambda)
    (hdeltaEq : (s : K) * E.gamma = (delta : K))
    (hlambdaScaleSqDelta : lambda * (s : K) ^ 2 ∈
      principalIdeal (K := K) (delta : K)) :
    normIdeal E.exchangeComplement (hyperbolicPlaneLattice (K := K)) =
      principalIdeal (K := K) (delta : K) := by
  have htwoScale : principalIdeal (K := K) (2 * (s : K)) ≤
      principalIdeal (K := K) (delta : K) := by
    rw [← hdelta.2,
      ← twoScaleIdeal_eq_principalIdeal_two_mul_of_modular hL hpos]
    exact twoScaleIdeal_le_normIdeal q L
  have htwoS : (2 : K) * (s : K) ∈
      principalIdeal (K := K) (delta : K) :=
    htwoScale (generator_mem_principalIdeal ((2 : K) * (s : K)))
  apply le_antisymm
  · apply normIdeal_le_of_quadratic_mem
    intro x hx
    have hxCoordinates := (mem_omearaPlaneLattice_iff x).mp hx
    let x0 : IntegerRing K := ⟨x 0, hxCoordinates.1⟩
    let x1 : IntegerRing K := ⟨x 1, hxCoordinates.2⟩
    have hdeltaTerm : -(delta : K) * x 0 ^ 2 ∈
        principalIdeal (K := K) (delta : K) := by
      let c : IntegerRing K := -(x0 ^ 2)
      have h := (principalIdeal (K := K) (delta : K)).smul_mem c
        (generator_mem_principalIdeal (delta : K))
      change (-(x 0 ^ 2)) * (delta : K) ∈
        principalIdeal (K := K) (delta : K) at h
      convert h using 1 <;> ring
    have hcrossTerm : -(2 : K) * (s : K) * (x 0 * x 1) ∈
        principalIdeal (K := K) (delta : K) := by
      let c : IntegerRing K := -(x0 * x1)
      have h := (principalIdeal (K := K) (delta : K)).smul_mem c htwoS
      change (-(x 0 * x 1)) * ((2 : K) * (s : K)) ∈
        principalIdeal (K := K) (delta : K) at h
      convert h using 1 <;> ring
    have hlambdaTerm : lambda * (s : K) ^ 2 * x 1 ^ 2 ∈
        principalIdeal (K := K) (delta : K) := by
      exact mul_integral_mem_principalIdeal (delta : K)
        (lambda * (s : K) ^ 2) (x 1 ^ 2) hlambdaScaleSqDelta
          ((IntegerRing K).toSubring.pow_mem hxCoordinates.2 2)
    have hnegDeltaEq : -(s : K) * E.gamma = -(delta : K) := by
      rw [neg_mul, hdeltaEq]
    have hformula : E.exchangeComplement.quadratic x =
        -(delta : K) * x 0 ^ 2 -
          (2 : K) * (s : K) * (x 0 * x 1) +
          lambda * (s : K) ^ 2 * x 1 ^ 2 := by
      change E.exchangeComplement.bilin x x = _
      unfold exchangeComplement
      rw [QuadraticSpace.omearaExchangeComplement_bilin_apply,
        halpha, hbeta, hnegDeltaEq]
      ring
    rw [hformula]
    convert (principalIdeal (K := K) (delta : K)).add_mem
      ((principalIdeal (K := K) (delta : K)).add_mem
        hdeltaTerm hcrossTerm) hlambdaTerm using 1 <;> ring
  · change Submodule.span (IntegerRing K) {(delta : K)} ≤
      normIdeal E.exchangeComplement (hyperbolicPlaneLattice (K := K))
    rw [Submodule.span_singleton_le_iff_mem]
    let e0 : Fin 2 → K := ![1, 0]
    have he0 : e0 ∈ hyperbolicPlaneLattice (K := K) := by
      rw [mem_omearaPlaneLattice_iff]
      simp [e0]
    have hnegDeltaEq : -(s : K) * E.gamma = -(delta : K) := by
      rw [neg_mul, hdeltaEq]
    have hvalue : E.exchangeComplement.quadratic e0 = -(delta : K) := by
      change E.exchangeComplement.bilin e0 e0 = _
      unfold exchangeComplement
      rw [QuadraticSpace.omearaExchangeComplement_bilin_apply,
        hnegDeltaEq]
      simp [e0]
    have hneg := quadratic_mem_normIdeal_of_mem E.exchangeComplement
      (hyperbolicPlaneLattice (K := K)) he0
    rw [hvalue] at hneg
    simpa only [neg_neg] using
      (normIdeal E.exchangeComplement
        (hyperbolicPlaneLattice (K := K))).neg_mem hneg

/-- The exchange complement contains `-delta` and every one of its values
lies in `delta O`; hence its norm ideal is exactly the old tail norm ideal.

Only the term `lambda * s^2` occurs in the quadratic polynomial of the
exchange complement.  Thus the sharp hypothesis is membership of that
scaled term in `delta O`; requiring `lambda` itself to lie there would be
unnecessarily strong in the adjacent-norm-order case of 93:28, Step 6. -/
theorem zeroLeft_exchangeComplement_normIdeal_eq
    (hL : IsModular q L s) (hpos : 0 < finrank K V)
    (lambda : K) (hlambda : lambda ∈ IntegerRing K)
    (hscale : IsInMaximalIdeal K (s : K))
    (delta : Kˣ) (hdelta : IsNormGeneratorValue q L delta)
    (hlambdaScaleSqDelta : lambda * (s : K) ^ 2 ∈
      principalIdeal (K := K) (delta : K)) :
    let E := zeroLeft hL hpos lambda hlambda hscale delta hdelta.1
    normIdeal E.exchangeComplement (hyperbolicPlaneLattice (K := K)) =
      principalIdeal (K := K) (delta : K) := by
  let E := zeroLeft hL hpos lambda hlambda hscale delta hdelta.1
  have hsIntegral : (s : K) ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 (le_of_lt hscale)
  have htwoScale : principalIdeal (K := K) (2 * (s : K)) ≤
      principalIdeal (K := K) (delta : K) := by
    rw [← hdelta.2,
      ← twoScaleIdeal_eq_principalIdeal_two_mul_of_modular hL hpos]
    exact twoScaleIdeal_le_normIdeal q L
  have htwoS : (2 : K) * (s : K) ∈
      principalIdeal (K := K) (delta : K) :=
    htwoScale (generator_mem_principalIdeal ((2 : K) * (s : K)))
  apply le_antisymm
  · apply normIdeal_le_of_quadratic_mem
    intro x hx
    have hxCoordinates := (mem_omearaPlaneLattice_iff x).mp hx
    let x0 : IntegerRing K := ⟨x 0, hxCoordinates.1⟩
    let x1 : IntegerRing K := ⟨x 1, hxCoordinates.2⟩
    have hdeltaTerm : -(delta : K) * x 0 ^ 2 ∈
        principalIdeal (K := K) (delta : K) := by
      let c : IntegerRing K := -(x0 ^ 2)
      have h := (principalIdeal (K := K) (delta : K)).smul_mem c
        (generator_mem_principalIdeal (delta : K))
      change (-(x 0 ^ 2)) * (delta : K) ∈
        principalIdeal (K := K) (delta : K) at h
      convert h using 1 <;> ring
    have hcrossTerm : -(2 : K) * (s : K) * (x 0 * x 1) ∈
        principalIdeal (K := K) (delta : K) := by
      let c : IntegerRing K := -(x0 * x1)
      have h := (principalIdeal (K := K) (delta : K)).smul_mem c htwoS
      change (-(x 0 * x 1)) * ((2 : K) * (s : K)) ∈
        principalIdeal (K := K) (delta : K) at h
      convert h using 1 <;> ring
    have hlambdaTerm : lambda * (s : K) ^ 2 * x 1 ^ 2 ∈
        principalIdeal (K := K) (delta : K) := by
      exact mul_integral_mem_principalIdeal (delta : K)
        (lambda * (s : K) ^ 2) (x 1 ^ 2) hlambdaScaleSqDelta
          ((IntegerRing K).toSubring.pow_mem hxCoordinates.2 2)
    have hformula : E.exchangeComplement.quadratic x =
        -(delta : K) * x 0 ^ 2 -
          (2 : K) * (s : K) * (x 0 * x 1) +
          lambda * (s : K) ^ 2 * x 1 ^ 2 := by
      change E.exchangeComplement.bilin x x = _
      unfold exchangeComplement
      rw [QuadraticSpace.omearaExchangeComplement_bilin_apply]
      have hnew := zeroLeft_newCoefficient hL hpos lambda hlambda
        hscale delta hdelta.1
      have hdeltaEq : (s : K) * E.gamma = (delta : K) := by
        simpa only [zeroLeft_alpha, zero_add] using hnew
      have hnegDeltaEq : -(s : K) * E.gamma = -(delta : K) := by
        rw [neg_mul, hdeltaEq]
      rw [show E.alpha = 0 by simp [E], show E.beta = -lambda by simp [E],
        hnegDeltaEq]
      ring
    rw [hformula]
    convert (principalIdeal (K := K) (delta : K)).add_mem
      ((principalIdeal (K := K) (delta : K)).add_mem
        hdeltaTerm hcrossTerm) hlambdaTerm using 1 <;> ring
  · change Submodule.span (IntegerRing K) {(delta : K)} ≤
      normIdeal E.exchangeComplement (hyperbolicPlaneLattice (K := K))
    rw [Submodule.span_singleton_le_iff_mem]
    let e0 : Fin 2 → K := ![1, 0]
    have he0 : e0 ∈ hyperbolicPlaneLattice (K := K) := by
      rw [mem_omearaPlaneLattice_iff]
      simp [e0]
    have hvalue : E.exchangeComplement.quadratic e0 = -(delta : K) := by
      change E.exchangeComplement.bilin e0 e0 = _
      unfold exchangeComplement
      rw [QuadraticSpace.omearaExchangeComplement_bilin_apply]
      have hdeltaEq : (s : K) * E.gamma = (delta : K) := by
        have hnew := zeroLeft_newCoefficient hL hpos lambda hlambda
          hscale delta hdelta.1
        simpa only [zeroLeft_alpha, zero_add] using hnew
      have hnegDeltaEq : -(s : K) * E.gamma = -(delta : K) := by
        rw [neg_mul, hdeltaEq]
      rw [hnegDeltaEq]
      simp [e0]
    have hneg := quadratic_mem_normIdeal_of_mem E.exchangeComplement
      (hyperbolicPlaneLattice (K := K)) he0
    rw [hvalue] at hneg
    simpa only [neg_neg] using
      (normIdeal E.exchangeComplement
        (hyperbolicPlaneLattice (K := K))).neg_mem hneg

end Lattice.Omeara9319ExchangeSetup

end Bong
