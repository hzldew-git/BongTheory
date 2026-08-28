/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BasisLattice
import Bong.Lattice.AdaptedBasis

/-!
# An integral basis adapted to a binary BONG

For a binary BONG, the exact projection sequence supplies an integral basis
whose first vector is the BONG head and whose second vector projects exactly
to the unary BONG tail.  This is the basis used in the strict-negative
modularity calculation.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- An integral basis of a binary BONG lattice adapted to its recursive
projection. -/
noncomputable def binaryIntegralBasis (b : BONG V q L 2) :
    Basis (Unit ⊕ Fin 1) (IntegerRing K) L.toSubmodule :=
  Lattice.adaptedIntegralBasisOfProjectedBasis L b.head
    b.head_isNormGenerator b.head_isAnisotropic
    b.tail.integralBasisFinOne

/-- The second vector of the adapted binary integral basis. -/
noncomputable def binarySecondVector (b : BONG V q L 2) : V :=
  b.binaryIntegralBasis (Sum.inr 0)

@[simp]
theorem coe_binaryIntegralBasis_inl (b : BONG V q L 2) (i : Unit) :
    ((b.binaryIntegralBasis (Sum.inl i) : L.toSubmodule) : V) =
      b.head := by
  exact Lattice.adaptedIntegralBasisOfProjectedBasis_inl
    L b.head b.head_isNormGenerator b.head_isAnisotropic
      b.tail.integralBasisFinOne i

theorem binarySecondVector_mem (b : BONG V q L 2) :
    b.binarySecondVector ∈ L :=
  (b.binaryIntegralBasis (Sum.inr 0)).property

theorem coe_binaryIntegralBasis_inr (b : BONG V q L 2) (i : Fin 1) :
    ((b.binaryIntegralBasis (Sum.inr i) : L.toSubmodule) : V) =
      b.binarySecondVector := by
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  rfl

/-- The second adapted vector projects to the recursive unary BONG head. -/
theorem projectionToOrthogonal_binarySecondVector
    (b : BONG V q L 2) :
    q.projectionToOrthogonal b.head b.head_isAnisotropic
        b.binarySecondVector = b.tail.head := by
  have h :=
    Lattice.projectionMap_adaptedIntegralBasisOfProjectedBasis_inr
      L b.head b.head_isNormGenerator b.head_isAnisotropic
      b.tail.integralBasisFinOne 0
  have hcoe := congrArg
    (fun z : (L.projectedLattice q b.head
      b.head_isAnisotropic).toSubmodule =>
        (z : q.vectorOrthogonal b.head)) h
  change
    q.projectionToOrthogonal b.head b.head_isAnisotropic
        ((b.binaryIntegralBasis (Sum.inr 0) : L.toSubmodule) : V) =
      ((b.tail.integralBasisFinOne 0 :
        (L.projectedLattice q b.head
          b.head_isAnisotropic).toSubmodule) :
            q.vectorOrthogonal b.head) at hcoe
  rw [b.tail.coe_integralBasisFinOne_zero] at hcoe
  change
    q.projectionToOrthogonal b.head b.head_isAnisotropic
        ((b.binaryIntegralBasis (Sum.inr 0) : L.toSubmodule) : V) =
      b.tail.head
  exact hcoe

/-- The projected quadratic value of the second adapted vector is exactly
the second BONG value. -/
theorem quadratic_projection_binarySecondVector
    (b : BONG V q L 2) :
    q.quadratic
        (q.orthogonalProjection b.head b.binarySecondVector) =
      b.value 1 := by
  have hp := congrArg
    (fun z : q.vectorOrthogonal b.head => q.quadratic (z : V))
    b.projectionToOrthogonal_binarySecondVector
  calc
    q.quadratic
        (q.orthogonalProjection b.head b.binarySecondVector) =
        q.quadratic
          (q.projectionToOrthogonal b.head b.head_isAnisotropic
            b.binarySecondVector : V) := rfl
    _ = q.quadratic (b.tail.head : V) := hp
    _ = (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
          b.tail.head := rfl
    _ = b.tail.value 0 :=
      b.tail.value_zero_eq_quadratic_head.symm
    _ = b.value 1 := b.value_tail 0

end BONG

end Bong
