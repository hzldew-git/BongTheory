/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalHasseSymbol

/-!
# Classification of diagonal quadratic spaces over a dyadic local field

The standard local classification says that two nondegenerate diagonal
quadratic spaces of the same dimension are isometric when their determinant
square classes and Hasse invariants agree.  Mathlib does not currently expose
this local theorem, so the converse direction is isolated here as one generic
trust boundary.  The forward invariance direction remains the separate,
weaker `DiagonalIsometryInvariantLaws` interface.
-/

namespace Bong

open Dyadic

universe u

/-- Local classification of nondegenerate diagonal quadratic forms by
dimension, determinant square class, and Hasse invariant. -/
class DyadicDiagonalClassificationLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  represents_of_invariants {n : Nat} (a b : Fin n → Kˣ)
    (determinant_square :
      IsSquare (BONG.GoodBONG.diagonalUnitDeterminant a *
        BONG.GoodBONG.diagonalUnitDeterminant b))
    (hasse_eq : diagonalHasseSymbol K a = diagonalHasseSymbol K b) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients a)
      (BONG.GoodBONG.diagonalUnitCoefficients b)

end Bong
