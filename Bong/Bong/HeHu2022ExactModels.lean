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
