/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ModularCriterion

/-!
# M44 scale-and-volume modularity smoke tests
-/

namespace BongTest.M44

open Bong Bong.Dyadic Module

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

example (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.principalIdeal (K := K) (a : K)) :
    Lattice.rescale a⁻¹ L ≤ Lattice.dualLattice q L :=
  Lattice.rescale_inv_le_dualLattice_of_scaleIdeal_le q L a hscale

example (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.principalIdeal (K := K) (a : K))
    (hvolume : Lattice.volumeOrder q L =
      (finrank K V : Int) * ordUnit K a) :
    Lattice.IsModular q L a :=
  Lattice.isModular_of_scaleIdeal_le_of_volumeOrder_eq
    q L a hscale hvolume

#print axioms Bong.Lattice.volumeIdeal_eq_of_volumeOrder_eq
#print axioms Bong.Lattice.eq_of_le_of_volumeOrder_eq
#print axioms Bong.Lattice.rescale_inv_le_dualLattice_of_scaleIdeal_le
#print axioms Bong.Lattice.isModular_of_scaleIdeal_le_of_volumeOrder_eq

end

end BongTest.M44
