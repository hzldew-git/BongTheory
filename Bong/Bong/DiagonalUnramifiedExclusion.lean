/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalRepresentationParity
import Bong.Dyadic.UnramifiedNorm

/-!
# Excluding mixed unramified endpoint classes

This file combines the four-space parity cycle with the norm group of the
unramified quadratic extension.  Two equal-rank diagonal spaces that both
embed in the same one-dimensional extension cannot occupy opposite
discriminant classes when their common codimension-one comparison produces
an odd complementary determinant.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [discriminant : DyadicDiscriminantClassLaws K]
  [DyadicUnramifiedNormLaws K]
  [HilbertSymbolLaws K]
  [DiagonalRepresentationParityLaws K]

/-- The case-III parity cycle excludes two simultaneous codimension-one
representations when the equal-rank determinant comparison is in the
discriminant class and the complementary determinant has odd order. -/
theorem not_both_diagonalRepresented_of_unramified_twist
    {i j k l : Nat} (a : Fin i → Kˣ) (b : Fin j → Kˣ)
    (c : Fin k → Kˣ) (hba : j + 1 = i) (hcb : k = j)
    (hlc : l + 1 = k)
    (hcommon : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients
        (diagonalUnitTake c l (by omega)))
      (BONG.GoodBONG.diagonalUnitCoefficients b))
    (hmixed : IsSquare
      ((BONG.GoodBONG.diagonalUnitDeterminant b *
          BONG.GoodBONG.diagonalUnitDeterminant c) *
        discriminant.discriminantUnit))
    (hodd : Odd (ordUnit K
      (-BONG.GoodBONG.diagonalUnitDeterminant a *
        BONG.GoodBONG.diagonalUnitDeterminant
          (diagonalUnitTake c l (by omega))))) :
    ¬(DiagonalRepresents
        (BONG.GoodBONG.diagonalUnitCoefficients b)
        (BONG.GoodBONG.diagonalUnitCoefficients a) ∧
      DiagonalRepresents
        (BONG.GoodBONG.diagonalUnitCoefficients c)
        (BONG.GoodBONG.diagonalUnitCoefficients a)) := by
  rintro ⟨hb, hc⟩
  have hcycle := DiagonalRepresentationParityLaws.caseIII
    a b c hba hcb hlc
  have hhilbert := hcycle.all_triple_consequences.1 hb hcommon hc
  exact
    (hilbertSymbol_ne_one_of_isSquare_mul_discriminant_of_odd_order
      hmixed hodd) hhilbert

end Bong
