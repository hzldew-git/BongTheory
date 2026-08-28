/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.JordanReverseDualInvariants
import Bong.Lattice.ProductDefectRescale

/-!
# Boundary ideals of the reverse-dual Jordan chain

This file completes the ideal-theoretic part of O'Meara 93:24.  The two
fundamental indices at a boundary are exchanged by reverse duality.  The
intermediate scaled boundary ideal acquires the predicted square factor,
which is cancelled exactly by the outer scale normalization.  Thus the
actual fundamental boundary ideal `f_i` is unchanged at the reversed cut.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

@[simp]
theorem rev_boundaryLeftIndex (i : Fin t) :
    Fin.rev (boundaryLeftIndex i) =
      boundaryRightIndex (Fin.rev i) := by
  apply Fin.ext
  simp [boundaryLeftIndex, boundaryRightIndex]

@[simp]
theorem rev_boundaryRightIndex (i : Fin t) :
    Fin.rev (boundaryRightIndex i) =
      boundaryLeftIndex (Fin.rev i) := by
  apply Fin.ext
  simp [boundaryLeftIndex, boundaryRightIndex]

/-- The norm-order sum at a reverse-dual boundary is obtained by subtracting
twice the sum of the two old scale orders. -/
theorem reverseDual_boundaryNormOrderSum
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    J.reverseDual.boundaryNormOrderSum i =
      J.boundaryNormOrderSum (Fin.rev i) -
        2 * (J.fundamentalScaleOrder
              (boundaryLeftIndex (Fin.rev i)) +
          J.fundamentalScaleOrder
              (boundaryRightIndex (Fin.rev i))) := by
  unfold boundaryNormOrderSum
  rw [J.reverseDual_fundamentalNormGenerator_order,
    J.reverseDual_fundamentalNormGenerator_order,
    rev_boundaryLeftIndex, rev_boundaryRightIndex]
  ring

/-- Reverse duality preserves the parity of every boundary norm-order sum. -/
theorem reverseDual_boundaryNormOrderSum_even_iff
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    Even (J.reverseDual.boundaryNormOrderSum i) ↔
      Even (J.boundaryNormOrderSum (Fin.rev i)) := by
  rw [J.reverseDual_boundaryNormOrderSum i]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m + J.fundamentalScaleOrder
        (boundaryLeftIndex (Fin.rev i)) +
      J.fundamentalScaleOrder (boundaryRightIndex (Fin.rev i)), ?_⟩
    omega
  · rintro ⟨m, hm⟩
    refine ⟨m - J.fundamentalScaleOrder
        (boundaryLeftIndex (Fin.rev i)) -
      J.fundamentalScaleOrder (boundaryRightIndex (Fin.rev i)), ?_⟩
    omega

/-- The product-defect summand at a reverse-dual boundary has the common
inverse-square factor of the two old scales. -/
theorem reverseDual_boundaryProductDefectSum
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    J.reverseDual.boundaryProductDefectSum i =
      Lattice.scalarIdeal
        ((((J.scaleGenerator (boundaryRightIndex (Fin.rev i)))⁻¹ *
          (J.scaleGenerator (boundaryLeftIndex (Fin.rev i)))⁻¹) ^ 2 : Kˣ) : K)
        (J.boundaryProductDefectSum (Fin.rev i)) := by
  let j : Fin t := Fin.rev i
  let li : Fin (t + 1) := boundaryLeftIndex j
  let ri : Fin (t + 1) := boundaryRightIndex j
  let c : Kˣ := (J.scaleGenerator ri)⁻¹
  let d : Kˣ := (J.scaleGenerator li)⁻¹
  have hleft : Fin.rev (boundaryLeftIndex i) = ri := by
    simp only [rev_boundaryLeftIndex, ri, j]
  have hright : Fin.rev (boundaryRightIndex i) = li := by
    simp only [rev_boundaryRightIndex, li, j]
  unfold boundaryProductDefectSum
  calc
    Lattice.productDefectSum
        (J.reverseDual.fundamentalNormGroup (boundaryLeftIndex i))
        (J.reverseDual.fundamentalNormGroup (boundaryRightIndex i)) =
      Lattice.scalarIdeal (((c * d) ^ 2 : Kˣ) : K)
        (Lattice.productDefectSum
          (J.fundamentalNormGroup ri) (J.fundamentalNormGroup li)) := by
      apply Lattice.productDefectSum_eq_scalarIdeal_of_sq_scaled c d
      · intro z
        have h := J.mem_reverseDual_fundamentalNormGroup_iff
          (boundaryLeftIndex i) z
        rw [hleft] at h
        have hc : (c ^ 2)⁻¹ = J.scaleGenerator ri ^ 2 := by
          dsimp only [c]
          group
        rw [hc]
        exact h
      · intro z
        have h := J.mem_reverseDual_fundamentalNormGroup_iff
          (boundaryRightIndex i) z
        rw [hright] at h
        have hd : (d ^ 2)⁻¹ = J.scaleGenerator li ^ 2 := by
          dsimp only [d]
          group
        rw [hd]
        exact h
    _ = Lattice.scalarIdeal (((c * d) ^ 2 : Kˣ) : K)
        (Lattice.productDefectSum
          (J.fundamentalNormGroup li) (J.fundamentalNormGroup ri)) := by
      rw [Lattice.productDefectSum_comm]
    _ = Lattice.scalarIdeal
        ((((J.scaleGenerator (boundaryRightIndex (Fin.rev i)))⁻¹ *
          (J.scaleGenerator (boundaryLeftIndex (Fin.rev i)))⁻¹) ^ 2 : Kˣ) : K)
        (Lattice.productDefectSum
          (J.fundamentalNormGroup (boundaryLeftIndex (Fin.rev i)))
          (J.fundamentalNormGroup (boundaryRightIndex (Fin.rev i))) ) := by
      rfl

/-- The dyadic parity summand has the same inverse-square covariance as the
product-defect summand. -/
theorem reverseDual_boundaryParityIdeal
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    J.reverseDual.boundaryParityIdeal i =
      Lattice.scalarIdeal
        ((((J.scaleGenerator (boundaryRightIndex (Fin.rev i)))⁻¹ *
          (J.scaleGenerator (boundaryLeftIndex (Fin.rev i)))⁻¹) ^ 2 : Kˣ) : K)
        (J.boundaryParityIdeal (Fin.rev i)) := by
  let li : Fin (t + 1) := boundaryLeftIndex (Fin.rev i)
  let ri : Fin (t + 1) := boundaryRightIndex (Fin.rev i)
  let c : Kˣ := (J.scaleGenerator ri)⁻¹
  let d : Kˣ := (J.scaleGenerator li)⁻¹
  unfold boundaryParityIdeal
  rw [Lattice.twiceIdeal_powerIdeal, Lattice.twiceIdeal_powerIdeal,
    Lattice.scalarIdeal_powerIdeal_units,
    J.reverseDual_boundaryNormOrderSum i,
    J.reverseDual_fundamentalScaleOrder,
    rev_boundaryLeftIndex, ordUnit_pow, ordUnit_mul,
    ordUnit_inv, ordUnit_inv]
  congr 1
  unfold fundamentalScaleOrder
  omega

/-- The intermediate ideal `s_i² f_i` has the common inverse-square
factor of the two adjacent old scales. -/
theorem reverseDual_scaledFundamentalIdeal
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    J.reverseDual.scaledFundamentalIdeal i =
      Lattice.scalarIdeal
        ((((J.scaleGenerator (boundaryRightIndex (Fin.rev i)))⁻¹ *
          (J.scaleGenerator (boundaryLeftIndex (Fin.rev i)))⁻¹) ^ 2 : Kˣ) : K)
        (J.scaledFundamentalIdeal (Fin.rev i)) := by
  have heven := J.reverseDual_boundaryNormOrderSum_even_iff i
  unfold scaledFundamentalIdeal
  by_cases h : Even (J.boundaryNormOrderSum (Fin.rev i))
  · have hdual : Even (J.reverseDual.boundaryNormOrderSum i) := heven.2 h
    rw [if_pos hdual, if_pos h, Lattice.scalarIdeal_sup,
      J.reverseDual_boundaryProductDefectSum i,
      J.reverseDual_boundaryParityIdeal i]
  · have hdual : ¬ Even (J.reverseDual.boundaryNormOrderSum i) := by
      exact fun h' ↦ h (heven.1 h')
    rw [if_neg hdual, if_neg h,
      J.reverseDual_boundaryProductDefectSum i]

/-- O'Meara 93:24: the actual fundamental ideal is invariant at the
reversed boundary. -/
@[simp]
theorem reverseDual_fundamentalIdeal
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) :
    J.reverseDual.fundamentalIdeal i =
      J.fundamentalIdeal (Fin.rev i) := by
  let li : Fin (t + 1) := boundaryLeftIndex (Fin.rev i)
  let ri : Fin (t + 1) := boundaryRightIndex (Fin.rev i)
  let c : Kˣ := (J.scaleGenerator ri)⁻¹
  let d : Kˣ := (J.scaleGenerator li)⁻¹
  unfold fundamentalIdeal
  rw [J.reverseDual_scaledFundamentalIdeal i,
    Lattice.scalarIdeal_scalarIdeal_eq,
    J.reverseDual_scaleGenerator, rev_boundaryLeftIndex]
  change Lattice.scalarIdeal
      (((((J.scaleGenerator ri)⁻¹)⁻¹ ^ 2 : Kˣ) : K) *
        (((c * d) ^ 2 : Kˣ) : K))
      (J.scaledFundamentalIdeal (Fin.rev i)) =
    Lattice.scalarIdeal ((((J.scaleGenerator li)⁻¹ ^ 2 : Kˣ) : K))
      (J.scaledFundamentalIdeal (Fin.rev i))
  congr 1
  norm_cast
  dsimp only [c, d]
  simp [mul_pow, mul_comm]

end Lattice.JordanDecomposition

end Bong
