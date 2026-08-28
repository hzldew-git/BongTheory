/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Jordan

/-!
# Raw Jordan decompositions

O'Meara's recursive extraction first produces unary or binary modular blocks
whose scales are nondecreasing.  Equal-scale neighbours are amalgamated only
afterward.  This structure records precisely that intermediate object.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- The unamalgamated output of O'Meara 91C. -/
structure RawJordanDecomposition (q : QuadraticSpace K V)
    (L : Lattice K V) (t : Nat) extends OrthogonalDecomposition q L t where
  scaleGenerator : Fin t → Kˣ
  normGenerator : Fin t → Kˣ
  modular : ∀ i, IsModular (component i).space (component i).lattice
    (scaleGenerator i)
  scaleIdeal_eq : ∀ i,
    scaleIdeal (component i).space (component i).lattice =
      principalIdeal (K := K) (scaleGenerator i : K)
  normIdeal_eq : ∀ i,
    normIdeal (component i).space (component i).lattice =
      principalIdeal (K := K) (normGenerator i : K)
  rank_one_or_two : ∀ i,
    finrank K (component i).carrier = 1 ∨
      finrank K (component i).carrier = 2
  scaleOrder_mono : ∀ {i j : Fin t}, i < j →
    ordUnit K (scaleGenerator i) ≤ ordUnit K (scaleGenerator j)

end Lattice

end Bong
