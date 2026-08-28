/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.DeterminantBasis

/-!
# Volume of a modular lattice

The volume order of an `a`-modular rank-`n` lattice is `n * ord(a)`.  This is
deduced from the rescaling and integral-duality formulas for lattice volume.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- The volume order of an `a`-modular lattice is its rank times the order of
`a`. -/
theorem IsModular.volumeOrder_eq {q : QuadraticSpace K V}
    {L : Lattice K V} {a : Kˣ} (hmodular : IsModular q L a) :
    volumeOrder q L = (finrank K V : Int) * ordUnit K a := by
  have h := congrArg (volumeOrder q) hmodular
  rw [volumeOrder_dualLattice, volumeOrder_rescale,
    ordUnit_inv] at h
  ring_nf at h ⊢
  omega

end Lattice

end Bong
