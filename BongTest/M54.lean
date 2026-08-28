/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryIntegralSquare

/-!
# M54 integral-square binary sublattice smoke tests
-/

namespace BongTest.M54

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b : BONG V q L 2) (s : Kˣ)
    (hs : (s : K) ∈ IntegerRing K) :
    (b.binaryIntegralSquareSubBONG s hs).binaryParameter =
      b.binaryParameter * s ^ 2 :=
  b.binaryIntegralSquareSubBONG_binaryParameter s hs

example (b : BONG V q L 2) (s : Kˣ)
    (hs : (s : K) ∈ IntegerRing K) :
    Lattice.spinorNormImage
        (q := q) (L := b.binaryIntegralSquareSubLattice s hs) ⊆
      Lattice.spinorNormImage (q := q) (L := L) :=
  b.spinorNormImage_binaryIntegralSquareSubLattice_subset s hs

#print axioms Bong.Lattice.rescale_le_self_of_mem_integerRing
#print axioms Bong.BONG.binaryIntegralSquareSubBONG_binaryParameter
#print axioms Bong.BONG.spinorNormImage_binaryIntegralSquareSubLattice_subset
#print axioms Bong.BONG.exists_binaryBONG_parameter_mul_integral_square

end

end BongTest.M54
