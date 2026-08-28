/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalDecompositionDual

namespace Bong

open Dyadic Module

namespace Lattice.OrthogonalDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The rank of the ambient space is the sum of the ranks of all components
of a finite orthogonal decomposition. -/
theorem finrank_eq_sum_components
    (D : OrthogonalDecomposition q L t) :
    finrank K V = ∑ i, finrank K (D.component i).carrier := by
  classical
  letI (i : Fin t) : Fintype (D.component i).lattice.BasisIndex :=
    Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis D.componentAmbientBasis,
    Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact Module.finrank_eq_card_basis
    (D.component i).lattice.ambientBasis |>.symm

end Lattice.OrthogonalDecomposition

end Bong
