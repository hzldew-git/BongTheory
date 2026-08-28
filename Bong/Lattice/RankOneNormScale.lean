/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ModularScale
import Bong.Lattice.NormGeneratorValues
import Bong.Lattice.OrthogonalBasis

/-!
# Norm and scale in rank one

For a one-dimensional lattice the chosen integral basis is automatically
orthogonal.  Consequently its norm and scale ideals are equal.  This is the
rank-one local calculation used for the unary component in Beli's Section 5.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- In dimension one every lattice has the same norm and scale ideal. -/
theorem normIdeal_eq_scaleIdeal_of_finrank_eq_one
    (q : QuadraticSpace K V) (L : Lattice K V)
    (hfin : finrank K V = 1) :
    normIdeal q L = scaleIdeal q L := by
  let e : Fin (finrank K V) ≃ Fin 1 := finCongr hfin
  let b : Basis (Fin 1) K V := L.standardAmbientBasis.reindex e
  have hb : basisLattice b = L := by
    calc
      basisLattice b = basisLattice L.standardAmbientBasis :=
        basisLattice_reindex L.standardAmbientBasis e
      _ = L := by
        apply Lattice.ext
        exact L.toSubmodule_eq_span_standardAmbientBasis.symm
  have horth : q.bilin.iIsOrtho b := by
    rw [LinearMap.BilinForm.iIsOrtho_def]
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  rw [← hb, normIdeal_basisLattice_of_iIsOrtho q b horth,
    scaleIdeal_basisLattice_of_iIsOrtho q b horth]

/-- For a rank-one modular lattice, any generators chosen for the norm and
scale ideals have the same valuation. -/
theorem ordUnit_normGenerator_eq_scaleGenerator_of_finrank_eq_one
    (q : QuadraticSpace K V) (L : Lattice K V) (a b : Kˣ)
    (hfin : finrank K V = 1)
    (hmodular : IsModular q L a)
    (hnorm : normIdeal q L = principalIdeal (K := K) (b : K)) :
    ordUnit K b = ordUnit K a := by
  have hpositive : 0 < finrank K V := by omega
  apply (principalIdeal_eq_iff_ordUnit_eq b a).mp
  exact hnorm.symm.trans
    ((normIdeal_eq_scaleIdeal_of_finrank_eq_one q L hfin).trans
      (hmodular.scaleIdeal_eq_principal hpositive))

end Lattice

end Bong
