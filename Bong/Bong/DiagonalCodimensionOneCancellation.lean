/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalRepresentationParity

/-!
# Cancellation for codimension-one diagonal representations

This file isolates the paper-independent Witt-cancellation input needed when
an equal-rank diagonal space embeds in a one-dimensional extension.  The
determinant condition is stated as equality of square classes.
-/

namespace Bong

universe u

namespace DiagonalRepresents

variable {K : Type u} [Field K]

/-- A representation between equal finite dimensions is reversible. -/
theorem symm_of_sameRank {n : Nat} {a b : Fin n → K}
    (h : DiagonalRepresents a b) : DiagonalRepresents b a := by
  rcases h with ⟨f, hf, hq⟩
  let e : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    LinearEquiv.ofBijective f
      ⟨hf, LinearMap.surjective_of_injective hf⟩
  refine ⟨e.symm.toLinearMap, e.symm.injective, ?_⟩
  intro y
  have hy := hq (e.symm y)
  have hmap : f (e.symm y) = y := by
    change e (e.symm y) = y
    exact e.apply_symm_apply y
  rw [hmap] at hy
  exact hy.symm

end DiagonalRepresents

/-- Witt cancellation for a diagonal codimension-one extension.

If `candidate` embeds in an extension of `base` by one anisotropic line and
their determinants have the same square class, then the two equal-rank
diagonal spaces are isometric.  The reverse representation follows from
`DiagonalRepresents.symm_of_sameRank`.
-/
class DiagonalCodimensionOneCancellationLaws
    (K : Type u) [Field K] [CharZero K] : Prop where
  cancel
    {n : Nat} (base candidate : Fin n → Kˣ)
    (extended : Fin (n + 1) → Kˣ)
    (hprefix : diagonalUnitPrefix extended = base)
    (hrep : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients candidate)
      (BONG.GoodBONG.diagonalUnitCoefficients extended))
    (hsquare : IsSquare
      (BONG.GoodBONG.diagonalUnitDeterminant candidate *
        BONG.GoodBONG.diagonalUnitDeterminant base)) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients candidate)
      (BONG.GoodBONG.diagonalUnitCoefficients base)

end Bong
