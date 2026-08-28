/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma710DualProduct
import Bong.Bong.MaximalNormSplittingDual

/-!
# Beli (2019), Lemma 7.10: swapping the orthogonal factors

Reverse duality reverses the complete BONG sequence.  Consequently the
right factor of an orthogonal product occurs first in the dual endpoint
argument.  This file supplies the explicit factor-swap isometry, its action
on product lattices and dual lattices, and the swapped reverse-dual BONG used
in the general case of Lemma 7.10.
-/

namespace Bong

open Dyadic

universe u v w

namespace QuadraticSpace

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

/-- Swapping the two coordinates is an isometry from `q ⊥ r` to
`r ⊥ q`. -/
def orthogonalSumSwapIsometry (q : QuadraticSpace K V)
    (r : QuadraticSpace K W) :
    Isometry (q.orthogonalSum r) (r.orthogonalSum q) where
  toLinearEquiv := LinearEquiv.prodComm K V W
  map_bilin x y := by
    change r.bilin x.2 y.2 + q.bilin x.1 y.1 =
      q.bilin x.1 y.1 + r.bilin x.2 y.2
    exact add_comm _ _

@[simp]
theorem orthogonalSumSwapIsometry_apply
    (q : QuadraticSpace K V) (r : QuadraticSpace K W) (z : V × W) :
    (orthogonalSumSwapIsometry q r).toLinearEquiv z = (z.2, z.1) :=
  rfl

end QuadraticSpace

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The image of a lattice after exchanging the two orthogonal factors. -/
noncomputable def swapLattice (N : Lattice K (V × W)) :
    Lattice K (W × V) :=
  map (LinearEquiv.prodComm K V W) N

/-- The factor-swap isometry bundled with the image lattice. -/
noncomputable def orthogonalSumSwapLatticeIsometry
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (N : Lattice K (V × W)) :
    Isometry (q.orthogonalSum r) (r.orthogonalSum q) N
      (swapLattice N) where
  toLinearEquiv := LinearEquiv.prodComm K V W
  map_bilin := (QuadraticSpace.orthogonalSumSwapIsometry q r).map_bilin
  map_mem z := (map_mem_map_iff
    (LinearEquiv.prodComm K V W) N z).symm

@[simp]
theorem orthogonalSumSwapLatticeIsometry_apply
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (N : Lattice K (V × W)) (z : V × W) :
    (orthogonalSumSwapLatticeIsometry q r N).toLinearEquiv z =
      (z.2, z.1) :=
  rfl

/-- Swapping a concrete product lattice exchanges its two factors. -/
@[simp]
theorem swapLattice_product :
    swapLattice (product L M) = product M L := by
  apply Lattice.ext
  ext z
  change z ∈ map (LinearEquiv.prodComm K V W) (product L M) ↔
    z ∈ product M L
  rw [mem_map_iff, mem_product_iff, mem_product_iff]
  simp only [LinearEquiv.symm_prodComm, LinearEquiv.prodComm_apply]
  exact and_comm

/-- A product identity after factor swap reflects to the original product
identity. -/
theorem eq_product_of_swapLattice_eq {N : Lattice K (V × W)}
    (h : swapLattice N = product M L) : N = product L M := by
  apply Lattice.ext
  ext z
  calc
    z ∈ N ↔
        (LinearEquiv.prodComm K V W) z ∈ swapLattice N :=
      (map_mem_map_iff (LinearEquiv.prodComm K V W) N z).symm
    _ ↔ (LinearEquiv.prodComm K V W) z ∈ product M L := by
      rw [h]
    _ ↔ z ∈ product L M := by
      exact and_comm

end Lattice

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {N : Lattice K (V × W)} {n : Nat}
  [BONGReverseDualLaws.{u, max v w} K]

/-- Reverse duality followed by exchange of the orthogonal factors.  The
ambient vectors, reciprocal values, and negated reversed orders are all
recorded explicitly for the index calculations in Lemma 7.10. -/
theorem exists_swappedReverseDual_with_values
    (b : BONG.GoodBONG (q.orthogonalSum r) N n) :
    ∃ c : BONG.GoodBONG (r.orthogonalSum q)
        (Lattice.dualLattice (r.orthogonalSum q)
          (Lattice.swapLattice N)) n,
      (∀ i, c.toBONG.ambientVector i =
        (LinearEquiv.prodComm K V W) (b.toBONG.reverseDualVector i)) ∧
      (∀ i, c.value i =
        ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K)) ∧
      ∀ i, c.order i = -b.order (Fin.rev i) := by
  rcases b.exists_reverseDual with ⟨c, hc⟩
  let f := Lattice.orthogonalSumSwapLatticeIsometry q r N
  let d := c.mapLatticeIsometry f.dual
  have hd : ∀ i, d.toBONG.ambientVector i =
      (LinearEquiv.prodComm K V W)
        (b.toBONG.reverseDualVector i) := by
    intro i
    change (c.toBONG.mapLatticeIsometry f.dual).ambientVector i = _
    rw [BONG.ambientVector_mapLatticeIsometry, hc i]
    rfl
  refine ⟨d, hd, ?_, ?_⟩
  · intro i
    change d.toBONG.value i =
      ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K)
    rw [← d.toBONG.quadratic_ambientVector i, hd i]
    calc
      (r.orthogonalSum q).quadratic
          ((LinearEquiv.prodComm K V W)
            (b.toBONG.reverseDualVector i)) =
          (q.orthogonalSum r).quadratic
            (b.toBONG.reverseDualVector i) :=
        (QuadraticSpace.orthogonalSumSwapIsometry q r).map_quadratic _
      _ = ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K) :=
        b.toBONG.quadratic_reverseDualVector i
  · intro i
    change d.toBONG.order i = -b.toBONG.order (Fin.rev i)
    apply WithTop.coe_injective
    rw [BONG.coe_order]
    have hvalue : d.toBONG.value i =
        ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K) := by
      rw [← d.toBONG.quadratic_ambientVector i, hd i]
      calc
        (r.orthogonalSum q).quadratic
            ((LinearEquiv.prodComm K V W)
              (b.toBONG.reverseDualVector i)) =
            (q.orthogonalSum r).quadratic
              (b.toBONG.reverseDualVector i) :=
          (QuadraticSpace.orthogonalSumSwapIsometry q r).map_quadratic _
        _ = ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K) :=
          b.toBONG.quadratic_reverseDualVector i
    rw [hvalue]
    change ord K (((b.toBONG.valueUnit (Fin.rev i))⁻¹ : Kˣ) : K) = _
    rw [← coe_ordUnit, ordUnit_inv,
      ← b.toBONG.order_eq_ordUnit]

end BONG.GoodBONG

end Bong
