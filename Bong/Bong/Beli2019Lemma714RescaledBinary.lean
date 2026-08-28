/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714BoundaryOrders
import Bong.Bong.Rescale
import Bong.Lattice.DeterminantBasis

/-!
# Beli (2019), Lemma 7.14(ii): the rescaled binary block

The binary part of the non-norm-generator lattice is
`J' = \mathfrak p J`.  This file constructs its good BONG directly by
globally rescaling the original binary BONG.  Thus its vectors are literally
`π x₁, π x₂`, its values are `π² a₁, π² a₂`, and its volume order is four
larger than that of `J`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {J : Lattice K V}

/-- The concrete good BONG on the uniformly rescaled binary lattice
`\mathfrak p J`. -/
noncomputable def lemma714RescaledBinary (j : GoodBONG q J 2) :
    GoodBONG q (Lattice.rescale (uniformizerUnit K) J) 2 :=
  j.rescale (uniformizerUnit K)

/-- Its two ambient vectors are exactly `πx₁, πx₂`. -/
@[simp]
theorem lemma714RescaledBinary_ambientVector
    (j : GoodBONG q J 2) (i : Fin 2) :
    (j.lemma714RescaledBinary).toBONG.ambientVector i =
      uniformizer K • j.toBONG.ambientVector i := by
  simpa [lemma714RescaledBinary, coe_uniformizerUnit] using
    BONG.GoodBONG.ambientVector_rescale (uniformizerUnit K) j i

/-- Its displayed BONG values are `π²a_i`. -/
@[simp]
theorem lemma714RescaledBinary_value
    (j : GoodBONG q J 2) (i : Fin 2) :
    j.lemma714RescaledBinary.value i =
      uniformizer K ^ 2 * j.value i := by
  simpa [lemma714RescaledBinary, coe_uniformizerUnit] using
    BONG.GoodBONG.value_rescale (uniformizerUnit K) j i

/-- Both displayed orders rise by exactly two. -/
@[simp]
theorem lemma714RescaledBinary_order
    (j : GoodBONG q J 2) (i : Fin 2) :
    j.lemma714RescaledBinary.order i = j.order i + 2 := by
  rw [lemma714RescaledBinary, BONG.GoodBONG.order_rescale]
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    simpa [uniformizerPowerUnit] using
      (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
  omega

/-- Uniform rescaling multiplies both binary values by the same square, so
the normalized endpoint square class is unchanged. -/
@[simp]
theorem lemma714RescaledBinary_binaryUnitSquareClass
    (j : GoodBONG q J 2) :
    j.lemma714RescaledBinary.toBONG.binaryUnitSquareClass =
      j.toBONG.binaryUnitSquareClass := by
  unfold BONG.binaryUnitSquareClass BONG.binaryParameter
    BONG.GoodBONG.lemma714RescaledBinary
  change unitSquareClass K
      ((j.toBONG.rescale (uniformizerUnit K)).valueUnit 1 /
        (j.toBONG.rescale (uniformizerUnit K)).valueUnit 0) = _
  rw [BONG.valueUnit_rescale, BONG.valueUnit_rescale]
  congr 1
  simp

/-- The rescaled binary block is a literal sublattice of the original
binary block. -/
theorem lemma714RescaledBinary_lattice_le (j : GoodBONG q J 2) :
    Lattice.rescale (uniformizerUnit K) J ≤ J := by
  apply Lattice.rescale_le_self_of_mem_integerRing
  rw [coe_uniformizerUnit, mem_integerRing_iff, Dyadic.IsIntegral,
    ord_uniformizer]
  norm_num

/-- Scaling a rank-two lattice by the uniformizer raises its volume order
by four. -/
theorem lemma714RescaledBinary_volumeOrder
    (j : GoodBONG q J 2) :
    Lattice.volumeOrder q (Lattice.rescale (uniformizerUnit K) J) =
      Lattice.volumeOrder q J + 4 := by
  rw [Lattice.volumeOrder_rescale]
  have hdim := j.toBONG.length_eq_finrank
  have hdimInt : (Module.finrank K V : Int) = 2 := by
    exact_mod_cast hdim.symm
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    simpa [uniformizerPowerUnit] using
      (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
  rw [hdimInt, hpi]
  norm_num

/-- In particular the rescaled binary block is strict in volume. -/
theorem lemma714RescaledBinary_volumeOrder_lt
    (j : GoodBONG q J 2) :
    Lattice.volumeOrder q J <
      Lattice.volumeOrder q (Lattice.rescale (uniformizerUnit K) J) := by
  rw [j.lemma714RescaledBinary_volumeOrder]
  omega

end BONG.GoodBONG

end Bong
