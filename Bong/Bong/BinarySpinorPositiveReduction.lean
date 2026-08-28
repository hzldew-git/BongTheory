/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryReflectionCoordinates
import Bong.Bong.BinaryShearIsometry
import Bong.Lattice.DeterminantProjection

/-!
# Reduction of nonnegative binary spinor calculations to a diagonal model

When the binary parameter has nonnegative order, every admissible shear is
integral.  Hence the standard binary lattice can be sheared integrally to the
diagonal model `X² + aY²`.  This is the normalization used in Xu's binary
spinor-norm calculations.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- An admissible binary shear is integral when the determinant parameter
has nonnegative order. -/
theorem binaryShear_mem_integerRing_of_parameterOrder_nonneg
    (a : Kˣ) (c : K)
    (hR : 0 ≤ ordUnit K a)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    c ∈ IntegerRing K := by
  have ha : (a : K) ∈ IntegerRing K := by
    rw [mem_integerRing_iff]
    change (0 : WithTop Int) ≤ ord K (a : K)
    rw [← coe_ordUnit]
    exact_mod_cast hR
  apply Lattice.mem_integerRing_of_sq_mem_integerRing
  change c ^ 2 ∈ (IntegerRing K).toSubring
  have hsub := (IntegerRing K).sub_mem hdiag ha
  simpa only [add_sub_cancel_right] using hsub

/-- Integral shear equivalence without an ambient common rescaling. -/
theorem binaryModel_isIsometric_of_shear_sub_integral
    (a : Kˣ) (c c' : K)
    (hsub : c - c' ∈ IntegerRing K) :
    Lattice.IsIsometric
      (QuadraticSpace.binaryModel a c)
      (QuadraticSpace.binaryModel a c')
      (binaryModelLattice (K := K))
      (binaryModelLattice (K := K)) := by
  simpa [QuadraticSpace.rescaleUnit] using
    (rescaledBinaryModel_isIsometric_of_shear_sub_integral
      (K := K) (1 : Kˣ) a c c' hsub)

/-- For nonnegative parameter order, the proper spinor image of an
admissible binary model equals that of the diagonal model. -/
theorem spinorNormImage_binaryModel_eq_diagonal_of_parameterOrder_nonneg
    (a : Kˣ) (c : K)
    (hR : 0 ≤ ordUnit K a)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) =
      Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) := by
  have hc : c ∈ IntegerRing K :=
    binaryShear_mem_integerRing_of_parameterOrder_nonneg a c hR hdiag
  have hsub : c - 0 ∈ IntegerRing K := by simpa using hc
  rcases binaryModel_isIsometric_of_shear_sub_integral a c 0 hsub with ⟨e⟩
  exact Lattice.spinorNormImage_eq_of_isometry e

/-- A binary BONG with nonnegative order gap has the proper spinor image of
the diagonal model `X² + aY²`. -/
theorem spinorNormImage_eq_diagonal_of_binaryOrderGap_nonneg
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2) (hR : 0 ≤ b.binaryOrderGap) :
    Lattice.spinorNormImage (q := q) (L := L) =
      Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel b.binaryParameter 0)
        (L := binaryModelLattice (K := K)) := by
  rw [b.spinorNormImage_eq_binaryModel]
  apply spinorNormImage_binaryModel_eq_diagonal_of_parameterOrder_nonneg
  · change 0 ≤ b.binaryParameterOrder
    rwa [b.binaryParameterOrder_eq_orderGap]
  · exact b.binaryModelCoefficient_isAdmissibleWitness.1
  · exact b.binaryModelCoefficient_isAdmissibleWitness.2

end BONG

end Bong
