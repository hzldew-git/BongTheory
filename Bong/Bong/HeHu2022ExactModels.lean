/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022SectionTwo
import Bong.Bong.BeliLemma43ConstructionProof
import Bong.Bong.BeliUniversalPreliminaries
import Bong.Bong.Beli2019VolumeOrders
import Bong.Bong.BeliUniversalLemma44
import Bong.Bong.MonotoneDiagonalization
import Bong.Lattice.BasisIsometry

/-!
# Exact good-BONG models for He--Hu (2024)

The explicit lattices in Table 2 are most faithfully represented by their
displayed good-BONG coefficient sequences.  This file packages Beli's exact
diagonal realization together with the lattice, the good BONG, its values,
orders, integrality criterion, and volume order.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG.GoodBONG

/-- Reindexing only the length of a good BONG preserves every displayed
value unit. -/
@[simp]
theorem valueUnit_castLength_heHu
    {V : Type u} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {m n : Nat}
    (b : GoodBONG q L m) (h : m = n) (i : Fin n) :
    (b.castLength h).valueUnit i =
      b.valueUnit ⟨i.val, by omega⟩ := by
  subst n
  rfl

/-- Reindexing only the length also preserves every prefix product. -/
@[simp]
theorem prefixProduct_castLength_heHu
    {V : Type u} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {m n : Nat}
    (b : GoodBONG q L m) (h : m = n) (i : Nat) :
    (b.castLength h).prefixProduct i = b.prefixProduct i := by
  subst n
  rfl

end BONG.GoodBONG

/-- Beli's constructive exact realization of an admissible good-BONG
coefficient sequence. -/
noncomputable def heHuExactRealization {n : Nat} (a : Fin n → Kˣ)
    (hadj : BONG.CoefficientAdjacentAdmissible a)
    (hweak : BONG.CoefficientWeakTwoStep (K := K) a) :
    BONG.DiagonalBONGRealization a :=
  BONG.diagonalBONGRealizationOfCriteria a hadj hweak

/-- The quadratic lattice denoted by `≺ a₁,…,aₙ ≻` relative to the
displayed good BONG. -/
noncomputable def heHuExactModel {n : Nat} (a : Fin n → Kˣ)
    (hadj : BONG.CoefficientAdjacentAdmissible a)
    (hweak : BONG.CoefficientWeakTwoStep (K := K) a) :
    Lattice.QuadraticLatticeModel (K := K) where
  Carrier := Fin n → K
  form := BONG.coefficientDiagonalSpace a
  lattice := (heHuExactRealization a hadj hweak).lattice

/-- The exact good BONG carried by `heHuExactModel`. -/
noncomputable def heHuExactGoodBONG {n : Nat} (a : Fin n → Kˣ)
    (hadj : BONG.CoefficientAdjacentAdmissible a)
    (hweak : BONG.CoefficientWeakTwoStep (K := K) a) :
    BONG.GoodBONG (BONG.coefficientDiagonalSpace a)
      (heHuExactRealization a hadj hweak).lattice n := by
  exact
    { toBONG := (heHuExactRealization a hadj hweak).bong
      good := (heHuExactRealization a hadj hweak).isGood hweak }

@[simp]
theorem heHuExactModel_rank {n : Nat} (a : Fin n → Kˣ)
    (hadj : BONG.CoefficientAdjacentAdmissible a)
    (hweak : BONG.CoefficientWeakTwoStep (K := K) a) :
    (heHuExactModel a hadj hweak).rank = n := by
  change finrank K (Fin n → K) = n
  exact finrank_fin_fun K

@[simp]
theorem heHuExactGoodBONG_valueUnit {n : Nat} (a : Fin n → Kˣ)
    (hadj : BONG.CoefficientAdjacentAdmissible a)
    (hweak : BONG.CoefficientWeakTwoStep (K := K) a) (i : Fin n) :
    (heHuExactGoodBONG a hadj hweak).valueUnit i = a i := by
  exact (heHuExactRealization a hadj hweak).valueUnit_eq i

@[simp]
theorem heHuExactGoodBONG_order {n : Nat} (a : Fin n → Kˣ)
    (hadj : BONG.CoefficientAdjacentAdmissible a)
    (hweak : BONG.CoefficientWeakTwoStep (K := K) a) (i : Fin n) :
    (heHuExactGoodBONG a hadj hweak).order i = ordUnit K (a i) := by
  exact (heHuExactRealization a hadj hweak).order_eq i

/-- Pointwise multiplication of a monotone exact good-BONG row by squares
of valuation units gives an isometric integral lattice.  Monotonicity turns
both recursively constructed BONG lattices into their displayed basis
lattices; the unit square roots then give an integral diagonal change of
basis. -/
theorem heHuExactModel_isIsometric_of_pointwise_unit_square {n : Nat}
    (source target scale : Fin (n + 1) → Kˣ)
    (hsourceAdj : BONG.CoefficientAdjacentAdmissible source)
    (hsourceWeak : BONG.CoefficientWeakTwoStep (K := K) source)
    (htargetAdj : BONG.CoefficientAdjacentAdmissible target)
    (htargetWeak : BONG.CoefficientWeakTwoStep (K := K) target)
    (hsourceMono : ∀ i j, i ≤ j →
      ordUnit K (source i) ≤ ordUnit K (source j))
    (htargetMono : ∀ i j, i ≤ j →
      ordUnit K (target i) ≤ ordUnit K (target j))
    (hscaleUnit : ∀ i, IsValuationUnit K (scale i : K))
    (hcoeff : ∀ i, source i = target i * scale i ^ 2) :
    Lattice.IsIsometric
      (BONG.coefficientDiagonalSpace source)
      (BONG.coefficientDiagonalSpace target)
      (heHuExactRealization source hsourceAdj hsourceWeak).lattice
      (heHuExactRealization target htargetAdj htargetWeak).lattice := by
  let bs := heHuExactGoodBONG source hsourceAdj hsourceWeak
  let bt := heHuExactGoodBONG target htargetAdj htargetWeak
  let scaledBasis := bt.toBONG.basis.unitsSMul scale
  have hgram : ∀ i j,
      (BONG.coefficientDiagonalSpace target).bilin
          (scaledBasis i) (scaledBasis j) =
        (BONG.coefficientDiagonalSpace source).bilin
          (bs.toBONG.basis i) (bs.toBONG.basis j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      have hsourceValue :
          (BONG.coefficientDiagonalSpace source).quadratic
              (bs.toBONG.basis i) = (source i : K) := by
        rw [show bs.toBONG.basis i = bs.toBONG.ambientVector i by rfl,
          bs.toBONG.quadratic_ambientVector]
        change bs.value i = (source i : K)
        exact congrArg Units.val
          (heHuExactGoodBONG_valueUnit source hsourceAdj hsourceWeak i)
      have htargetValue :
          (BONG.coefficientDiagonalSpace target).quadratic
              (bt.toBONG.basis i) = (target i : K) := by
        rw [show bt.toBONG.basis i = bt.toBONG.ambientVector i by rfl,
          bt.toBONG.quadratic_ambientVector]
        change bt.value i = (target i : K)
        exact congrArg Units.val
          (heHuExactGoodBONG_valueUnit target htargetAdj htargetWeak i)
      have hcoeffField := congrArg Units.val (hcoeff i)
      change (source i : K) = (target i : K) * (scale i : K) ^ 2
        at hcoeffField
      change (BONG.coefficientDiagonalSpace target).quadratic
          (scaledBasis i) =
        (BONG.coefficientDiagonalSpace source).quadratic
          (bs.toBONG.basis i)
      rw [show scaledBasis i = (scale i : K) • bt.toBONG.basis i by
        simp [scaledBasis, Basis.unitsSMul_apply, Units.smul_def],
        QuadraticSpace.quadratic_smul, htargetValue, hsourceValue,
        hcoeffField]
      ring
    · have hsourceZero :=
        (LinearMap.BilinForm.iIsOrtho_def.mp
          bs.toBONG.ambientVector_iIsOrtho) i j hij
      have htargetZero :=
        (LinearMap.BilinForm.iIsOrtho_def.mp
          bt.toBONG.ambientVector_iIsOrtho) i j hij
      rw [show scaledBasis i = (scale i : K) • bt.toBONG.basis i by
        simp [scaledBasis, Basis.unitsSMul_apply, Units.smul_def],
        show scaledBasis j = (scale j : K) • bt.toBONG.basis j by
          simp [scaledBasis, Basis.unitsSMul_apply, Units.smul_def],
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
        show (BONG.coefficientDiagonalSpace target).bilin
            (bt.toBONG.basis i) (bt.toBONG.basis j) = 0 by
          simpa only [BONG.ambientVector] using htargetZero,
        show (BONG.coefficientDiagonalSpace source).bilin
            (bs.toBONG.basis i) (bs.toBONG.basis j) = 0 by
          simpa only [BONG.ambientVector] using hsourceZero]
      simp
  have hiso := Lattice.basisLattice_isIsometric_of_gram_eq
    (BONG.coefficientDiagonalSpace source)
    (BONG.coefficientDiagonalSpace target)
    bs.toBONG.basis scaledBasis hgram
  have hsourceLattice :
      (heHuExactRealization source hsourceAdj hsourceWeak).lattice =
        Lattice.basisLattice bs.toBONG.basis := by
    apply bs.toBONG.lattice_eq_basisLattice_of_order_monotone
    intro i j hij
    change bs.order i ≤ bs.order j
    rw [show bs.order i = ordUnit K (source i) by
      exact heHuExactGoodBONG_order source hsourceAdj hsourceWeak i,
      show bs.order j = ordUnit K (source j) by
        exact heHuExactGoodBONG_order source hsourceAdj hsourceWeak j]
    exact hsourceMono i j hij
  have htargetLattice :
      (heHuExactRealization target htargetAdj htargetWeak).lattice =
        Lattice.basisLattice bt.toBONG.basis := by
    apply bt.toBONG.lattice_eq_basisLattice_of_order_monotone
    intro i j hij
    change bt.order i ≤ bt.order j
    rw [show bt.order i = ordUnit K (target i) by
      exact heHuExactGoodBONG_order target htargetAdj htargetWeak i,
      show bt.order j = ordUnit K (target j) by
        exact heHuExactGoodBONG_order target htargetAdj htargetWeak j]
    exact htargetMono i j hij
  have hscaledLattice : Lattice.basisLattice scaledBasis =
      Lattice.basisLattice bt.toBONG.basis := by
    exact Lattice.basisLattice_unitsSMul_eq bt.toBONG.basis scale hscaleUnit
  rw [← hsourceLattice, hscaledLattice, ← htargetLattice] at hiso
  exact hiso

/-- A nonempty exact model is integral precisely when its first displayed
BONG order is nonnegative. -/
theorem heHuExactModel_isIntegral_iff {n : Nat}
    (a : Fin (n + 1) → Kˣ)
    (hadj : BONG.CoefficientAdjacentAdmissible a)
    (hweak : BONG.CoefficientWeakTwoStep (K := K) a) :
    Lattice.IsIntegral (BONG.coefficientDiagonalSpace a)
        (heHuExactRealization a hadj hweak).lattice ↔
      0 ≤ ordUnit K (a 0) := by
  let b := heHuExactGoodBONG a hadj hweak
  have h := b.toBONG.beliUniversalLemma22
  rw [h]
  change 0 ≤ b.order 0 ↔ 0 ≤ ordUnit K (a 0)
  rw [heHuExactGoodBONG_order]

/-- The volume order of an exact model is the sum of its displayed
`R_i` invariants. -/
theorem heHuExactModel_volumeOrder {n : Nat} (a : Fin n → Kˣ)
    (hadj : BONG.CoefficientAdjacentAdmissible a)
    (hweak : BONG.CoefficientWeakTwoStep (K := K) a) :
    Lattice.volumeOrder (BONG.coefficientDiagonalSpace a)
        (heHuExactRealization a hadj hweak).lattice =
      ∑ i, ordUnit K (a i) := by
  let b := heHuExactGoodBONG a hadj hweak
  calc
    Lattice.volumeOrder (BONG.coefficientDiagonalSpace a)
        (heHuExactRealization a hadj hweak).lattice =
        ∑ i, b.toBONG.order i := b.toBONG.volumeOrder_eq_sum_order
    _ = ∑ i, ordUnit K (a i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      change b.order i = ordUnit K (a i)
      exact heHuExactGoodBONG_order a hadj hweak i

end Bong
