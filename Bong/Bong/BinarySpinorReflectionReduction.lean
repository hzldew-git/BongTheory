/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryModelIsometry
import Bong.Lattice.BinarySpinorRescale
import Bong.Lattice.SpinorNormIsometry

/-!
# Reduction of binary BONG spinor norms to the explicit model

Every binary BONG lattice is isometric to a scalar multiple of its explicit
binary Gram model.  Proper binary spinor norms are invariant under both that
lattice isometry and the common scalar multiple.  Hence the remaining local
calculation can be carried out entirely in the standard lattice `O^2` with
the explicit form `binaryModel`.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- The first standard vector gives an integral reflection in the explicit
binary model attached to a binary BONG. -/
theorem binaryModelFirst_isIntegralReflection (b : BONG V q L 2) :
    Lattice.IsIntegralReflection
      (q := QuadraticSpace.binaryModel b.binaryParameter
        b.binaryModelCoefficient)
      (L := binaryModelLattice (K := K))
      (binaryModelFirst_isAnisotropic b.binaryParameter
        b.binaryModelCoefficient) := by
  exact (binaryModelFirst_isNormGenerator b.binaryParameter
      b.binaryModelCoefficient
      b.binaryModelCoefficient_isAdmissibleWitness.1
      b.binaryModelCoefficient_isAdmissibleWitness.2).isIntegralReflection
    (binaryModelFirst_isAnisotropic b.binaryParameter
      b.binaryModelCoefficient)

/-- A binary BONG has exactly the proper spinor-norm image of its unscaled
explicit binary model.  This removes both the ambient lattice and the first
BONG value from the local spinor calculation. -/
theorem spinorNormImage_eq_binaryModel (b : BONG V q L 2) :
    Lattice.spinorNormImage (q := q) (L := L) =
      Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel b.binaryParameter
          b.binaryModelCoefficient)
        (L := binaryModelLattice (K := K)) := by
  calc
    Lattice.spinorNormImage (q := q) (L := L) =
        Lattice.spinorNormImage
          (q := b.normalizedBinaryModelSpace)
          (L := binaryModelLattice (K := K)) :=
      (Lattice.spinorNormImage_eq_of_isometry
        b.normalizedBinaryModelLatticeIsometry).symm
    _ = Lattice.spinorNormImage
          (q := QuadraticSpace.binaryModel b.binaryParameter
            b.binaryModelCoefficient)
          (L := binaryModelLattice (K := K)) := by
      exact Lattice.spinorNormImage_rescaleUnit_of_finrank_eq_two
        (q := QuadraticSpace.binaryModel b.binaryParameter
          b.binaryModelCoefficient)
        (L := binaryModelLattice (K := K))
        (b.valueUnit 0) (by simp)
        (binaryModelFirst_isAnisotropic b.binaryParameter
          b.binaryModelCoefficient)
        b.binaryModelFirst_isIntegralReflection

end BONG

end Bong
