/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Isometry
import Bong.Lattice.NormGenerator

/-!
# Norm generators under lattice isometries

An isometry preserves lattice membership, quadratic values, and the norm
ideal.  It therefore preserves the property of being a norm generator in
both directions.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- A lattice isometry carries a norm generator to a norm generator. -/
theorem IsNormGenerator.mapLatticeIsometry {x : V}
    (generator : IsNormGenerator q L x)
    (f : Isometry q r L M) :
    IsNormGenerator r M (f.toLinearEquiv x) := by
  constructor
  · exact (f.map_mem x).1 generator.mem
  · calc
      normIdeal r M =
          normIdeal r (map f.toLinearEquiv L) :=
        congrArg (normIdeal r) f.map_eq.symm
      _ = normIdeal q L :=
        normIdeal_map_isometry f.toQuadraticSpaceIsometry L
      _ = principalIdeal (K := K) (q.quadratic x) :=
        generator.normIdeal_eq
      _ = principalIdeal (K := K)
          (r.quadratic (f.toLinearEquiv x)) := by
        have hquad : r.quadratic (f.toLinearEquiv x) =
            q.quadratic x := f.map_bilin x x
        rw [hquad]

/-- Being a norm generator is invariant under a lattice isometry. -/
theorem isNormGenerator_map_iff (f : Isometry q r L M) (x : V) :
    IsNormGenerator r M (f.toLinearEquiv x) ↔
      IsNormGenerator q L x := by
  constructor
  · intro h
    have hback := h.mapLatticeIsometry f.symm
    simpa [Isometry.symm] using hback
  · intro h
    exact h.mapLatticeIsometry f

end Lattice

end Bong
