/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalHasseSymbol

/-!
# The obstruction to representing a line by a ternary diagonal form

Over a dyadic local field, failure of a nondegenerate ternary form to
represent a nonzero scalar has two consequences: the ternary form is
anisotropic, and the signed product of its determinant with that scalar is
a square.  Equivalently, adjoining the negative scalar produces the unique
possible anisotropic quaternary determinant class.

This local quadratic-space theorem is kept as an explicit, paper-independent
trust boundary until it is derived from the foundational Witt theory.
-/

namespace Bong

open Dyadic

universe u

/-- The local-field obstruction to unary representation by a ternary
diagonal form.  This interface contains no lattice, BONG, or Beli-specific
data. -/
class DyadicTernaryRepresentationObstructionLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  obstruction (a : Fin 3 → Kˣ) (b : Kˣ)
    (hnot : ¬DiagonalRepresents
      (fun _ : Fin 1 ↦ (b : K))
      (BONG.GoodBONG.diagonalUnitCoefficients a)) :
    DiagonalAnisotropic (BONG.GoodBONG.diagonalUnitCoefficients a) ∧
      IsSquare ((-1 : Kˣ) *
        BONG.GoodBONG.diagonalUnitDeterminant a * b)
  /-- The converse geometric implication used in Beli's Lemma 9.6: once
  the line is represented, the exceptional signed determinant square class
  forces the ternary form to be isotropic.  This is the Witt-decomposition
  half of the same paper-independent ternary classification theorem. -/
  isotropic_of_represents_and_signedDeterminantSquare
      (a : Fin 3 → Kˣ) (b : Kˣ)
      (hrep : DiagonalRepresents
        (fun _ : Fin 1 ↦ (b : K))
        (BONG.GoodBONG.diagonalUnitCoefficients a))
      (hsquare : IsSquare ((-1 : Kˣ) *
        BONG.GoodBONG.diagonalUnitDeterminant a * b)) :
      DiagonalIsotropic (BONG.GoodBONG.diagonalUnitCoefficients a)

end Bong
