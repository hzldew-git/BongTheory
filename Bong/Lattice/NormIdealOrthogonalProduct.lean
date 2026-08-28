/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Product
import Bong.Lattice.NormGenerator
import Bong.QuadraticSpace.OrthogonalSum

/-!
# Norm ideals of orthogonal products

The norm ideal of a concrete orthogonal product is the sum of the norm
ideals of its two factors.  This belongs to the lattice-theoretic core and
is used independently of any paper-specific argument.
-/

namespace Bong

open Dyadic

universe u v w

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The norm ideal of an orthogonal product is the sum of the component
norm ideals. -/
theorem normIdeal_orthogonalProduct :
    normIdeal (q.orthogonalSum r) (product L M) =
      normIdeal q L ⊔ normIdeal r M := by
  apply le_antisymm
  · apply normIdeal_le_of_quadratic_mem
    intro z hzProduct
    have hz := mem_product_iff.mp hzProduct
    have hx : q.quadratic z.1 ∈ normIdeal q L :=
      quadratic_mem_normIdeal_of_mem q L hz.1
    have hy : r.quadratic z.2 ∈ normIdeal r M :=
      quadratic_mem_normIdeal_of_mem r M hz.2
    rw [QuadraticSpace.orthogonalSum_quadratic_apply]
    exact (normIdeal q L ⊔ normIdeal r M).add_mem
      ((show normIdeal q L ≤ normIdeal q L ⊔ normIdeal r M from
        _root_.le_sup_left) hx)
      ((show normIdeal r M ≤ normIdeal q L ⊔ normIdeal r M from
        _root_.le_sup_right) hy)
  · have hleft : normIdeal q L ≤
        normIdeal (q.orthogonalSum r) (product L M) := by
      apply normIdeal_le_of_quadratic_mem
      intro x hx
      have hmem : ((x : V), (0 : W)) ∈ product L M :=
        inl_mem_product_iff.mpr hx
      have hvalue := quadratic_mem_normIdeal_of_mem
        (q.orthogonalSum r) (product L M) hmem
      simpa using hvalue
    have hright : normIdeal r M ≤
        normIdeal (q.orthogonalSum r) (product L M) := by
      apply normIdeal_le_of_quadratic_mem
      intro y hy
      have hmem : ((0 : V), (y : W)) ∈ product L M :=
        inr_mem_product_iff.mpr hy
      have hvalue := quadratic_mem_normIdeal_of_mem
        (q.orthogonalSum r) (product L M) hmem
      simpa using hvalue
    exact _root_.sup_le hleft hright

end Lattice
end Bong
