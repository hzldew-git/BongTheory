/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019CanonicalApproximation

/-!
# Codimension-two diagonal representations over dyadic local fields

For two nondegenerate quadratic spaces whose dimensions differ by two, the
only automatic-existence exception is the negative-square determinant class.
This is a standard local quadratic-space theorem, independent of BONGs and of
Beli's representation criterion.  It is isolated here because the required
local Witt-classification result is not currently available in mathlib.
-/

namespace Bong

open BONG.GoodBONG

universe u

/-- The standard local-field codimension-two representation theorem.

The determinant of a diagonal form is used only modulo squares, so the product
of the two determinants represents their quotient.  Outside the negative
square class, every source form embeds in the target form. -/
class DyadicDiagonalCodimensionTwoLaws
    (K : Type u) [Field K] [CharZero K] : Prop where
  represents_of_not_negative_determinant_square
    {m r : Nat} (source : Fin m → Kˣ) (target : Fin r → Kˣ)
    (hrank : r = m + 2)
    (hdet : ¬ IsSquare
      (-diagonalUnitDeterminant target *
        diagonalUnitDeterminant source)) :
    DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients target)

/-- Public form of the codimension-two local theorem. -/
theorem diagonalRepresents_of_not_negative_determinant_square
    {K : Type u} [Field K] [CharZero K]
    [DyadicDiagonalCodimensionTwoLaws K]
    {m r : Nat} (source : Fin m → Kˣ) (target : Fin r → Kˣ)
    (hrank : r = m + 2)
    (hdet : ¬ IsSquare
      (-diagonalUnitDeterminant target *
        diagonalUnitDeterminant source)) :
    DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients target) :=
  DyadicDiagonalCodimensionTwoLaws.represents_of_not_negative_determinant_square
    source target hrank hdet

end Bong
