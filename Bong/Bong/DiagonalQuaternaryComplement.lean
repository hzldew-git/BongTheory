/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalHasseSymbol

/-!
# Ternary complements in quaternary spaces over dyadic local fields

Every nondegenerate quaternary quadratic space over a nonarchimedean local
field represents every nonzero scalar.  Orthogonal splitting then supplies a
nondegenerate ternary complement.  The local universality theorem is not yet
available in mathlib, so this file records precisely that paper-independent
input as an explicit interface.
-/

namespace Bong

open Dyadic

universe u

/-- The standard local-field universality and orthogonal-splitting theorem
for nondegenerate quaternary diagonal forms.

This is an explicit trust boundary until quaternary universality over dyadic
local fields is derived from the local norm theorem in the foundational
layer.  It contains no BONG- or Beli-specific data. -/
class DyadicQuaternaryComplementLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  complement (b : Kˣ) (base : Fin 4 → Kˣ) :
    ∃ c : Fin 3 → Kˣ,
      DiagonalRepresents
        (BONG.GoodBONG.diagonalUnitCoefficients (Fin.cons b c))
        (BONG.GoodBONG.diagonalUnitCoefficients base)

/-- Every unit-valued quaternary diagonal form has a ternary complement to
any prescribed nonzero line. -/
theorem diagonalQuaternary_hasComplement
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [DyadicQuaternaryComplementLaws K]
    (b : Kˣ) (base : Fin 4 → Kˣ) :
    ∃ c : Fin 3 → Kˣ,
      DiagonalRepresents
        (BONG.GoodBONG.diagonalUnitCoefficients (Fin.cons b c))
        (BONG.GoodBONG.diagonalUnitCoefficients base) :=
  DyadicQuaternaryComplementLaws.complement b base

end Bong
