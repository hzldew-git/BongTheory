/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Representation
import Bong.Bong.Beli2009JordanIdeals
import Bong.Lattice.Jordan
import Bong.Lattice.ModularIsometry

/-!
# Norm groups under integral representations

An integral isometric embedding carries pairings, quadratic values, the
scale ideal, and hence O'Meara's scalar norm group into the target lattice.
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

namespace Representation

/-- An integral isometric embedding carries the scale ideal into the target
scale ideal. -/
theorem scaleIdeal_le (f : Representation q r L M) :
    scaleIdeal q L ≤ scaleIdeal r M := by
  rw [scaleIdeal, Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  have h := bilin_mem_scaleIdeal r M
    ⟨f.toLinearMap p.1, f.map_mem p.1.property⟩
    ⟨f.toLinearMap p.2, f.map_mem p.2.property⟩
  rw [f.map_bilin] at h
  exact h

/-- An integral isometric embedding carries O'Meara's scalar norm group
into the target norm group. -/
theorem normGroupSet_subset (f : Representation q r L M) :
    normGroupSet q L ⊆ normGroupSet r M := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  refine ⟨f.toLinearMap x, f.map_mem hx, y, ?_, ?_⟩
  · exact Submodule.map_mono f.scaleIdeal_le hy
  · rw [f.map_quadratic]

end Representation

namespace Isometry

/-- Rescaling the source and target lattices by the same scalar preserves an
integral isometry. -/
noncomputable def rescaleLattices
    (f : Isometry q r L M) (a : Kˣ) :
    Isometry q r (rescale a L) (rescale a M) := by
  have hmap : map f.toLinearEquiv (rescale a L) = rescale a M := by
    rw [map_rescale, f.map_eq]
  exact
    { toLinearEquiv := f.toLinearEquiv
      map_bilin := f.map_bilin
      map_mem := fun x => by
        rw [← hmap]
        exact (map_mem_map_iff f.toLinearEquiv (rescale a L) x).symm }

end Isometry

namespace QuadraticSublattice

/-- The inclusion of a nondegenerate quadratic subspace is an integral
representation whenever the displayed internal lattice maps into the
ambient lattice. -/
noncomputable def inclusionRepresentation
    (C : QuadraticSublattice q) (A : Lattice K C.carrier)
    (M : Lattice K V)
    (hmem : ∀ x : C.carrier, x ∈ A → (x : V) ∈ M) :
    Representation C.space q A M where
  toLinearMap := Submodule.subtype C.carrier
  injective := Subtype.val_injective
  map_bilin _ _ := rfl
  map_mem := fun hx => hmem _ hx

end QuadraticSublattice

end Lattice

end Bong
