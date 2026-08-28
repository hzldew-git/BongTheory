/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Dyadic local fields

This file records the ambient data used by the BONG development.  A
`DyadicContext K` consists of a nonarchimedean local field of characteristic zero,
a normalized additive valuation with values in `WithTop ℤ`, and the condition
that `2` has positive valuation.

The compatibility field prevents the additive valuation from drifting away from
the valuative relation that controls the topology and the valuation ring.
-/

namespace Bong

/-- The normalized valued-field data used throughout the BONG development. -/
class DyadicContext (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] extends IsNonarchimedeanLocalField K where
  /-- The normalized additive valuation. -/
  ord : AddValuation K (WithTop ℤ)
  /-- `ord` induces the valuative relation already carried by `K`. -/
  ordCompatible : (AddValuation.toValuation ord).Compatible
  /-- A chosen uniformizer, used to make later constructions deterministic. -/
  uniformizer : K
  /-- The chosen uniformizer has additive valuation one. -/
  ordUniformizer : ord uniformizer = 1
  /-- Dyadicity: the rational integer `2` lies in the maximal ideal. -/
  ordTwoPos : 0 < ord (2 : K)

namespace DyadicContext

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K]

instance : IsNonarchimedeanLocalField K :=
  DyadicContext.toIsNonarchimedeanLocalField

instance : (AddValuation.toValuation (DyadicContext.ord (K := K))).Compatible :=
  DyadicContext.ordCompatible

end DyadicContext

end Bong
