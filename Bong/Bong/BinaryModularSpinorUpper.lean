/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.BinaryDiagonalEvenSpinorUpper
import Bong.Bong.BinaryReflectionCoordinates

/-!
# Quadratic-norm containment for sheared binary models

The quadratic value of the binary model with parameter `a` and shear `c` is

`(x + c y)^2 + a y^2`.

Consequently every reflection value, and hence every proper integral spinor
class, is a norm from the quadratic algebra with parameter `-a`.  Unlike the
positive-order arguments, this calculation does not diagonalize the lattice
and therefore applies unchanged to the modular (negative-order) branch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Every nonzero value of a sheared binary model is a quadratic norm from
the negative of its parameter. -/
theorem squareClass_binaryModelValue_mem_quadraticNorm
    (a : Kˣ) (c : K) {z : Fin 2 → K}
    (hz : (QuadraticSpace.binaryModel a c).IsAnisotropic z) :
    squareClass K
        (Units.mk0 ((QuadraticSpace.binaryModel a c).quadratic z) hz) ∈
      quadraticNormSquareClassSubgroup K (-a) := by
  let x : K := z 0 + c * z 1
  let y : K := z 1
  have hvalue :
      (QuadraticSpace.binaryModel a c).quadratic z =
        x ^ 2 + (a : K) * y ^ 2 := by
    rw [QuadraticSpace.binaryModel_quadratic_apply]
    simp only [x, y]
    ring
  have hnonzero : x ^ 2 + (a : K) * y ^ 2 ≠ 0 := by
    rw [← hvalue]
    exact hz
  have hnorm := squareClass_diagonalValue_mem_quadraticNorm
    (K := K) a hnonzero
  have hclass :
      squareClass K
          (Units.mk0 (x ^ 2 + (a : K) * y ^ 2) hnonzero) =
        squareClass K
          (Units.mk0 ((QuadraticSpace.binaryModel a c).quadratic z) hz) := by
    congr 1
    apply Units.ext
    simpa only [Units.val_mk0] using hvalue.symm
  rwa [hclass] at hnorm

/-- The proper spinor image of every admissible sheared binary model is
contained in the quadratic norm square-class subgroup of `-a`. -/
theorem spinorNormImage_binaryModel_le_quadraticNorm
    (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) ⊆
      (quadraticNormSquareClassSubgroup K (-a) : Set (SquareClass K)) := by
  intro A hA
  rw [spinorNormImage_binaryModel_eq_primitiveReflectionClassSet
    a c htwo hdiag] at hA
  rcases hA with
    ⟨z, hz, _hzMem, _hzPrimitive, _hfirst, _hsecond, hclass⟩
  have hnorm := squareClass_binaryModelValue_mem_quadraticNorm
    (K := K) a c hz
  rwa [hclass] at hnorm

/-- Intrinsic form of quadratic-norm containment for an arbitrary binary
BONG, including the improper modular branch. -/
theorem spinorNormImage_le_quadraticNorm
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2) :
    Lattice.spinorNormImage (q := q) (L := L) ⊆
      (quadraticNormSquareClassSubgroup K (-b.binaryParameter) :
        Set (SquareClass K)) := by
  rw [b.spinorNormImage_eq_binaryModel]
  exact spinorNormImage_binaryModel_le_quadraticNorm
    b.binaryParameter b.binaryModelCoefficient
    b.binaryModelCoefficient_isAdmissibleWitness.1
    b.binaryModelCoefficient_isAdmissibleWitness.2

end BONG

end Bong
