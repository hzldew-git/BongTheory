/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryAutomorphism
import Bong.Lattice.SpinorNorm

/-!
# Spinor-norm inclusion for nested binary lattices

The orthogonal-group inclusion from Beli 2003, Lemma 3.2(i), keeps the
underlying ambient isometry unchanged.  It therefore keeps the Wall spinor
norm unchanged and induces inclusion of integral spinor-norm images.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

namespace Lattice

/-- Restricting the same binary ambient automorphism to the larger lattice
does not alter its spinor norm. -/
theorem integralSpinorNorm_binaryInclusionHom
    (b : BONG V q L 2) (c : BONG V q M 2)
    (hhead : b.head = c.head) (hLM : L ≤ M)
    (f : IntegralOrthogonalGroup q L) :
    integralSpinorNorm
        (IntegralOrthogonalGroup.binaryInclusionHom
          b c hhead hLM f) =
      integralSpinorNorm f := by
  rfl

/-- Beli 2003, Lemma 3.2(i), at the level of spinor-norm images. -/
theorem spinorNormImage_subset_of_binary_commonHead
    (b : BONG V q L 2) (c : BONG V q M 2)
    (hhead : b.head = c.head) (hLM : L ≤ M) :
    spinorNormImage (q := q) (L := L) ⊆
      spinorNormImage (q := q) (L := M) := by
  rintro _ ⟨f, rfl⟩
  let included : IntegralRotation q M :=
    ⟨IntegralOrthogonalGroup.binaryInclusionHom
        b c hhead hLM f.toIntegralOrthogonalGroup,
      f.det_eq_one⟩
  refine ⟨included, ?_⟩
  exact integralSpinorNorm_binaryInclusionHom b c hhead hLM
    f.toIntegralOrthogonalGroup

end Lattice

end Bong
