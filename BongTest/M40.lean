/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryModular

/-!
# M40 diagonal modularity smoke tests
-/

namespace BongTest.M40

open Bong Bong.Dyadic Module

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

example (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0) :
    Lattice.IsModular q (Lattice.basisLattice basis)
        (Units.mk0 (q.quadratic (basis 0)) hne0) ↔
      ord K (q.quadratic (basis 0)) =
        ord K (q.quadratic (basis 1)) :=
  Lattice.isModular_basisLattice_fin_two_iff_ord_eq
    q basis horth hne0 hne1

#print axioms Bong.Lattice.rescale_basisLattice
#print axioms Bong.Lattice.basisLattice_unitsSMul_eq
#print axioms Bong.Lattice.dualBasis_eq_unitsSMul_of_iIsOrtho
#print axioms Bong.Lattice.isModular_basisLattice_iff_orders_eq
#print axioms Bong.Lattice.isModular_basisLattice_fin_two_iff_ord_eq

end

end BongTest.M40
