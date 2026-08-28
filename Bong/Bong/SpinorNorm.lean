/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Basic
import Bong.Lattice.SpinorNorm

/-!
# Spinor norms along a recursive BONG

The recursive tail of a BONG is the projected lattice at its first norm
generator.  The Section 2.5 embedding therefore applies at every recursive
step.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : ℕ}

/-- The integral orthogonal group of a BONG tail embeds in that of the head. -/
noncomputable def tailAutomorphismHom (b : BONG V q L (n + 1)) :
    Lattice.IntegralOrthogonalGroup
        (q.orthogonalSpace b.head b.head_isAnisotropic)
        (L.projectedLattice q b.head b.head_isAnisotropic) →*
      Lattice.IntegralOrthogonalGroup q L :=
  Lattice.projectedAutomorphismHom b.head_isNormGenerator

/-- The tail orthogonal-group embedding is injective. -/
theorem tailAutomorphismHom_injective (b : BONG V q L (n + 1)) :
    Function.Injective b.tailAutomorphismHom :=
  Lattice.projectedAutomorphismHom_injective b.head_isNormGenerator

/-- One recursive tail step can only decrease the spinor-norm image. -/
theorem spinorNormImage_tail_subset (b : BONG V q L (n + 1)) :
    Lattice.spinorNormImage
        (q := q.orthogonalSpace b.head b.head_isAnisotropic)
        (L := L.projectedLattice q b.head b.head_isAnisotropic) ⊆
      Lattice.spinorNormImage (q := q) (L := L) :=
  Lattice.spinorNormImage_projectedLattice_subset
    b.head_isNormGenerator

/-- Extension along the BONG head preserves the integral spinor norm. -/
theorem integralSpinorNorm_tailAutomorphismHom
    (b : BONG V q L (n + 1))
    (f : Lattice.IntegralOrthogonalGroup
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic)) :
    Lattice.integralSpinorNorm (b.tailAutomorphismHom f) =
      Lattice.integralSpinorNorm f :=
  Lattice.integralSpinorNorm_extendProjectedAutomorphism
    b.head_isNormGenerator f

end BONG

end Bong
