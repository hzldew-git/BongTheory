/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.JordanAmalgamation
import Bong.Lattice.OmearaRawJordan

/-!
# O'Meara's Jordan decomposition theorem

This file completes the construction in O'Meara, Section 91C.  The recursive
unary-or-binary modular splitting is flattened, and consecutive components of
equal scale are amalgamated.  The result has strictly increasing scales.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- O'Meara 91C: every quadratic lattice has a finite Jordan decomposition
with strictly increasing modular scales. -/
theorem exists_omearaJordanDecomposition
    (q : QuadraticSpace K V) (L : Lattice K V) :
    ∃ (s : Nat), Nonempty (JordanDecomposition q L s) := by
  let R := omearaRawJordanDecomposition q L
  exact (WeakJordanDecomposition.ofRaw R).exists_jordan

/-- A chosen Jordan decomposition supplied by O'Meara 91C. -/
noncomputable def omearaJordanDecomposition
    (q : QuadraticSpace K V) (L : Lattice K V) :
    Σ s : Nat, JordanDecomposition q L s :=
  (WeakJordanDecomposition.ofRaw
    (omearaRawJordanDecomposition q L)).jordanWitness

end Lattice

end Bong
