/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaEvenPlaneNormalization
import Bong.Lattice.OmearaGeneralPlaneChangeOfComplement
import Bong.Lattice.OmearaHighRankModularSplitting

/-!
# Combining two general O'Meara planes

This is the final integral calculation in O'Meara 93:18(v), without the
temporary zero-right-coefficient simplification.  Starting with

`A(alpha,beta) orthogonal A(gamma,delta) orthogonal R`,

add `c` times the first vector of the second plane to the first vector of
the first plane.  O'Meara 82:15a changes the first coefficient to
`alpha + gamma*c^2` and constructs an integral orthogonal complement.  If
`alpha = gamma*c^2`, `alpha` is in the maximal ideal, and `beta = 2*zeta`,
the new plane is `A(2*alpha,2*zeta)` and O'Meara 93:11 makes it hyperbolic.

No assertion is made that the new complement is the old second plane; the
change-of-complement theorem constructs the correct integral complement.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The vector `c*e_0` in the first factor of a displayed second plane. -/
private def secondPlaneSquareVector
    {W : Type w} [AddCommGroup W] [Module K W]
    (c : K) : (Fin 2 → K) × W :=
  (![c, 0], 0)

private theorem secondPlaneSquareVector_mem
    {W : Type w} [AddCommGroup W] [Module K W]
    (M : Lattice K W) (c : K) (hc : c ∈ IntegerRing K) :
    secondPlaneSquareVector (W := W) c ∈
      product (hyperbolicPlaneLattice (K := K)) M := by
  rw [mem_product_iff, mem_omearaPlaneLattice_iff]
  exact ⟨⟨by simpa [secondPlaneSquareVector] using hc,
    by simp [secondPlaneSquareVector]⟩, M.zero_mem⟩

private theorem secondPlaneSquareVector_quadratic
    {W : Type w} [AddCommGroup W] [Module K W]
    (gamma delta : K) (hnondegenerate : gamma * delta ≠ 1)
    (r : QuadraticSpace K W) (c : K) :
    ((QuadraticSpace.omearaGeneralPlane gamma delta hnondegenerate)
        |>.orthogonalSum r).quadratic
      (secondPlaneSquareVector (W := W) c) = gamma * c ^ 2 := by
  rw [QuadraticSpace.quadratic,
    QuadraticSpace.orthogonalSum_bilin_apply,
    QuadraticSpace.omearaGeneralPlane_bilin_apply]
  simp [secondPlaneSquareVector]
  ring

/-- A maximal-ideal first half and an integral second half make the
determinant of `A(2*eta,2*zeta)` a valuation unit. -/
private theorem deepEvenPlane_determinant_isValuationUnit
    (eta zeta : K) (heta : IsInMaximalIdeal K eta)
    (hzeta : zeta ∈ IntegerRing K) :
    IsValuationUnit K (((2 : K) * eta) * ((2 : K) * zeta) - 1) := by
  have hfourZeta : (4 : K) * zeta ∈ IntegerRing K :=
    (IntegerRing K).toSubring.mul_mem (by norm_num) hzeta
  have hproductMax : IsInMaximalIdeal K (eta * ((4 : K) * zeta)) :=
    isInMaximalIdeal_mul_isIntegral K heta
      ((mem_integerRing_iff K).1 hfourZeta)
  have hnegMax : IsInMaximalIdeal K (-(eta * ((4 : K) * zeta))) := by
    simpa only [IsInMaximalIdeal, ord_neg] using hproductMax
  have hone := isValuationUnit_one_add_of_isInMaximalIdeal hnegMax
  have hrewrite :
      ((2 : K) * eta) * ((2 : K) * zeta) - 1 =
        -(1 + -(eta * ((4 : K) * zeta))) := by ring
  rw [hrewrite, IsValuationUnit, ord_neg]
  exact hone

/-- General-plane form of the last calculation in O'Meara 93:18(v).
The supplied isometry displays two nested unimodular planes.  The first
coefficients differ by an integral square, while the right coefficient of
the first plane is merely even.  The result is a genuine displayed
hyperbolic summand, with the complement constructed by 82:15a. -/
noncomputable def Omeara9318vData.ofGeneralTwoPlaneDisplayedIsometryOfSquareRelated
    {W : Type w} [AddCommGroup W] [Module K W]
    (hmodular : IsModular q L (1 : Kˣ))
    (alpha beta gamma delta c zeta : K)
    (hfirst : alpha * beta ≠ 1)
    (hsecond : gamma * delta ≠ 1)
    (halphaIntegral : alpha ∈ IntegerRing K)
    (hzeta : zeta ∈ IntegerRing K)
    (hc : c ∈ IntegerRing K)
    (halphaMaximal : IsInMaximalIdeal K alpha)
    (hrelated : alpha = gamma * c ^ 2)
    (hbeta : beta = (2 : K) * zeta)
    (r : QuadraticSpace K W) (M : Lattice K W)
    (displayed : Isometry q
      ((QuadraticSpace.omearaGeneralPlane alpha beta hfirst).orthogonalSum
        ((QuadraticSpace.omearaGeneralPlane gamma delta hsecond)
          |>.orthogonalSum r))
      L
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K)) M))) :
    Omeara9318vData q L (1 : Kˣ) := by
  let first := QuadraticSpace.omearaGeneralPlane alpha beta hfirst
  let second := QuadraticSpace.omearaGeneralPlane gamma delta hsecond
  let tail := second.orthogonalSum r
  let tailLattice := product (hyperbolicPlaneLattice (K := K)) M
  let z : (Fin 2 → K) × W := secondPlaneSquareVector (W := W) c
  have hz : z ∈ tailLattice :=
    secondPlaneSquareVector_mem M c hc
  have hqz : tail.quadratic z = gamma * c ^ 2 := by
    exact secondPlaneSquareVector_quadratic gamma delta hsecond r c
  have hnewCoefficient : alpha + tail.quadratic z = (2 : K) * alpha := by
    rw [hqz, ← hrelated]
    ring
  have hbetaIntegral : beta ∈ IntegerRing K := by
    rw [hbeta]
    exact (IntegerRing K).toSubring.mul_mem (by norm_num) hzeta
  have hnewIntegral : alpha + tail.quadratic z ∈ IntegerRing K := by
    rw [hnewCoefficient]
    exact (IntegerRing K).toSubring.mul_mem (by norm_num) halphaIntegral
  have hnewDetUnit : IsValuationUnit K
      ((alpha + tail.quadratic z) * beta - 1) := by
    rw [hnewCoefficient, hbeta]
    exact deepEvenPlane_determinant_isValuationUnit
      alpha zeta halphaMaximal hzeta
  have hambient : IsModular (first.orthogonalSum tail)
      (product (hyperbolicPlaneLattice (K := K)) tailLattice)
      (1 : Kˣ) := by
    exact hmodular.mapLatticeIsometry displayed
  let C := omearaGeneralPlaneChangeOfComplement
    tail tailLattice alpha beta hfirst z halphaIntegral hbetaIntegral hz
      hnewIntegral hnewDetUnit hambient
  have hnewNondegenerate :
      ((2 : K) * alpha) * ((2 : K) * zeta) ≠ 1 := by
    exact sub_ne_zero.mp
      (omearaExchange_ne_zero_of_isValuationUnit
        (deepEvenPlane_determinant_isValuationUnit
          alpha zeta halphaMaximal hzeta))
  let normalizeRaw := Classical.choice
    (omeara9311_deep_even_plane_isIsometric
      alpha zeta halphaIntegral halphaMaximal hzeta hnewNondegenerate)
  let normalize : Isometry
      (QuadraticSpace.omearaGeneralPlane
        (alpha + tail.quadratic z) beta
          (sub_ne_zero.mp
            (omearaExchange_ne_zero_of_isValuationUnit hnewDetUnit)))
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
    simpa only [hnewCoefficient, hbeta] using normalizeRaw
  let toChanged := displayed.trans C.displayedIsometry
  let hyperbolicDisplayed := toChanged.trans
    (normalize.orthogonalProductBasic
      (Isometry.refl (C.decomposition.component 1).space
        (C.decomposition.component 1).lattice))
  exact Omeara9318vData.ofDisplayedIsometry
    (C.decomposition.component 1).space
    (C.decomposition.component 1).lattice hmodular hyperbolicDisplayed

end Lattice

end Bong
