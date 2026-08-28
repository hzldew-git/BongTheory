/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.OrthogonalBasis
import Bong.Lattice.DiagonalModular

/-!
# Modular diagonal binary lattices

An anisotropic orthogonal binary basis with equal diagonal orders generates a
modular lattice.  This is the diagonal boundary case of Beli (2003),
Lemma 3.3(i).
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- An anisotropic orthogonal binary basis with equal diagonal orders gives a
modular basis lattice, with either diagonal value as scale generator. -/
theorem isModular_basisLattice_fin_two_of_ord_eq
    (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0)
    (horder : ord K (q.quadratic (basis 0)) =
      ord K (q.quadratic (basis 1))) :
    IsModular q (basisLattice basis)
      (Units.mk0 (q.quadratic (basis 0)) hne0) := by
  let hne : ∀ i : Fin 2, q.quadratic (basis i) ≠ 0 := by
    intro i
    cases i using Fin.cases with
    | zero => exact hne0
    | succ i => simpa [Subsingleton.elim i 0] using hne1
  apply isModular_basisLattice_of_iIsOrtho_of_orders_eq
    q basis horth hne
      (Units.mk0 (q.quadratic (basis 0)) hne0)
  intro i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      apply WithTop.coe_injective
      rw [coe_ordUnit, coe_ordUnit]
      exact horder.symm

/-- For an anisotropic orthogonal binary basis, modularity at the first
diagonal value is equivalent to equality of the two diagonal orders. -/
theorem isModular_basisLattice_fin_two_iff_ord_eq
    (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0) :
    IsModular q (basisLattice basis)
        (Units.mk0 (q.quadratic (basis 0)) hne0) ↔
      ord K (q.quadratic (basis 0)) =
        ord K (q.quadratic (basis 1)) := by
  constructor
  · intro hmodular
    let hne : ∀ i : Fin 2, q.quadratic (basis i) ≠ 0 := by
      intro i
      cases i using Fin.cases with
      | zero => exact hne0
      | succ i => simpa [Subsingleton.elim i 0] using hne1
    have h := orders_eq_of_isModular_basisLattice_of_iIsOrtho
      q basis horth hne
        (Units.mk0 (q.quadratic (basis 0)) hne0) hmodular (1 : Fin 2)
    have h' : ord K (q.quadratic (basis 1)) =
        ord K (q.quadratic (basis 0)) := by
      simpa [coe_ordUnit] using
        congrArg ((↑) : Int → WithTop Int) h
    exact h'.symm
  · exact isModular_basisLattice_fin_two_of_ord_eq
      q basis horth hne0 hne1

end Lattice

namespace BONG

/-- In the equal-order case, the ordered orthogonal BONG constructed from the
basis lies on a modular lattice. -/
theorem isModular_ofOrthogonalBasisFinTwoOfOrdEq
    (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0)
    (horder : ord K (q.quadratic (basis 0)) =
      ord K (q.quadratic (basis 1))) :
    Lattice.IsModular q (Lattice.basisLattice basis)
      (Units.mk0 (q.quadratic (basis 0)) hne0) :=
  Lattice.isModular_basisLattice_fin_two_of_ord_eq
    q basis horth hne0 hne1 horder

end BONG

end Bong
