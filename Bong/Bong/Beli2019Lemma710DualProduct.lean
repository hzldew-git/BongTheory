/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma710RightEnd
import Bong.Bong.GoodMap
import Bong.Bong.MaximalNormSplittingDual
import Bong.Bong.Structural
import Bong.Lattice.DualIsometry

/-!
# Beli (2019), Lemma 7.10: duals of orthogonal products

The general case of Lemma 7.10 is reduced to the right-end case by reversing
and dualizing the relevant good BONGs.  This file proves the underlying
integral identity: the dual of a concrete orthogonal-product lattice is the
product of the two component dual lattices.
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

/-- Integral duality commutes with the concrete orthogonal product. -/
theorem dualLattice_orthogonalProduct :
    dualLattice (q.orthogonalSum r) (product L M) =
      product (dualLattice q L) (dualLattice r M) := by
  apply Lattice.ext
  ext z
  change z ∈ dualLattice (q.orthogonalSum r) (product L M) ↔
    z ∈ product (dualLattice q L) (dualLattice r M)
  rw [mem_dualLattice_iff, mem_product_iff]
  constructor
  · intro hz
    constructor
    · rw [mem_dualLattice_iff]
      intro x hx
      have h := hz (x, 0) (inl_mem_product_iff.mpr hx)
      simpa [QuadraticSpace.orthogonalSum_bilin_apply] using h
    · rw [mem_dualLattice_iff]
      intro y hy
      have h := hz (0, y) (inr_mem_product_iff.mpr hy)
      simpa [QuadraticSpace.orthogonalSum_bilin_apply] using h
  · rintro ⟨hzLeft, hzRight⟩ y hy
    rw [mem_dualLattice_iff] at hzLeft hzRight
    have hleft := hzLeft y.1 (fst_mem_of_mem_product hy)
    have hright := hzRight y.2 (snd_mem_of_mem_product hy)
    rw [QuadraticSpace.orthogonalSum_bilin_apply]
    exact (IntegerRing K).add_mem _ _ hleft hright

/-- The dual-product identity bundled in the direction needed to transport
a reverse-dual BONG into the concrete product of the component duals. -/
noncomputable def dualOrthogonalProductIsometry :
    Isometry (q.orthogonalSum r) (q.orthogonalSum r)
      (dualLattice (q.orthogonalSum r) (product L M))
      (product (dualLattice q L) (dualLattice r M)) :=
  Isometry.ofLatticeEq (q.orthogonalSum r)
    dualLattice_orthogonalProduct

end Lattice

namespace BONG.GoodBONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  [BONGReverseDualLaws.{u, max v w} K]

/-- Reverse duality followed by the concrete dual-product identification.
The result lives on the product of the component dual lattices, rather than
merely on the dual of the ambient orthogonal product. -/
theorem exists_reverseDualOrthogonalProduct_with_values
    (b : BONG.GoodBONG (q.orthogonalSum r) (Lattice.product L M) n) :
    ∃ c : BONG.GoodBONG (q.orthogonalSum r)
        (Lattice.product (Lattice.dualLattice q L)
          (Lattice.dualLattice r M)) n,
      (∀ i, c.toBONG.ambientVector i = b.toBONG.reverseDualVector i) ∧
      (∀ i, c.value i =
        ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K)) ∧
      ∀ i, c.order i = -b.order (Fin.rev i) := by
  rcases b.exists_reverseDual with ⟨c, hc⟩
  let f := Lattice.dualOrthogonalProductIsometry
    (q := q) (r := r) (L := L) (M := M)
  let d := c.mapLatticeIsometry f
  have hd : ∀ i, d.toBONG.ambientVector i =
      b.toBONG.reverseDualVector i := by
    intro i
    change (c.toBONG.mapLatticeIsometry f).ambientVector i = _
    rw [BONG.ambientVector_mapLatticeIsometry, hc i]
    simp [f, Lattice.dualOrthogonalProductIsometry]
  refine ⟨d, hd, ?_, ?_⟩
  · intro i
    change d.toBONG.value i =
      ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K)
    rw [← d.toBONG.quadratic_ambientVector i, hd i]
    exact b.toBONG.quadratic_reverseDualVector i
  · intro i
    change d.toBONG.order i = -b.toBONG.order (Fin.rev i)
    apply WithTop.coe_injective
    rw [BONG.coe_order]
    have hvalue : d.toBONG.value i =
        ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K) := by
      rw [← d.toBONG.quadratic_ambientVector i, hd i]
      exact b.toBONG.quadratic_reverseDualVector i
    rw [hvalue]
    change ord K (((b.toBONG.valueUnit (Fin.rev i))⁻¹ : Kˣ) : K) = _
    rw [← coe_ordUnit, ordUnit_inv, ← b.toBONG.order_eq_ordUnit]

/-- The vector-only form of reverse duality on an orthogonal product. -/
theorem exists_reverseDualOrthogonalProduct
    (b : BONG.GoodBONG (q.orthogonalSum r) (Lattice.product L M) n) :
    ∃ c : BONG.GoodBONG (q.orthogonalSum r)
        (Lattice.product (Lattice.dualLattice q L)
          (Lattice.dualLattice r M)) n,
      ∀ i, c.toBONG.ambientVector i = b.toBONG.reverseDualVector i := by
  rcases b.exists_reverseDualOrthogonalProduct_with_values with
    ⟨c, hc, _, _⟩
  exact ⟨c, hc⟩

omit [BONGReverseDualLaws.{u, max v w} K] in
/-- A right-end identity proved after reverse duality reflects to the
original lattices.  This is the first half of the general `u < n` argument
in Lemma 7.10: the prefix here is the reversed unchanged suffix from the
paper.  The conditional endpoint hypothesis includes the empty-prefix
boundary handled by `beli2019Lemma710RightEnd_all_of_good`. -/
theorem beli2019Lemma710DualRightEnd_all_of_good
    {rightLength baseTail s : Nat} {N : Lattice K (V × W)}
    (leftDual : BONG.GoodBONG q (Lattice.dualLattice q L) n)
    (hs : 1 ≤ s) (hsRank : s - 1 ≤ n)
    (rightDual : BONG W r (Lattice.dualLattice r M)
      (rightLength + 1))
    (seed : BONG.OrthogonalPrefixSeed r (Lattice.dualLattice r M)
      (baseTail + 1) (steps := s - 1) leftDual.toBONG)
    (hlast : ∀ hsTwo : 2 ≤ s,
      leftDual.order ⟨s - 2, by omega⟩ ≤ rightDual.order 0)
    (targetDual : BONG.GoodBONG (q.orthogonalSum r)
      (Lattice.dualLattice (q.orthogonalSum r) N)
      ((baseTail + 1) + (s - 1)))
    (leftVectors : ∀ i : Fin (s - 1),
      targetDual.toBONG.ambientVector
          (BONG.orthogonalProductLeftIndex (baseTail + 1) i) =
        (leftDual.toBONG.ambientVector (seed.sourceIndex i), 0))
    (rightVectors : ∀ j : Fin (baseTail + 1),
      targetDual.toBONG.ambientVector
          (BONG.orthogonalProductRightIndex (s - 1) j) =
        seed.baseAmbientVector j) :
    N = Lattice.product L M := by
  have hdual :
      Lattice.dualLattice (q.orthogonalSum r) N =
        Lattice.product (Lattice.dualLattice q L)
          (Lattice.dualLattice r M) :=
    leftDual.beli2019Lemma710RightEnd_all_of_good s hs hsRank
      rightDual seed hlast targetDual.toBONG targetDual.good
      leftVectors rightVectors
  have hdualProduct :
      Lattice.dualLattice (q.orthogonalSum r) N =
        Lattice.dualLattice (q.orthogonalSum r)
          (Lattice.product L M) := by
    calc
      Lattice.dualLattice (q.orthogonalSum r) N =
          Lattice.product (Lattice.dualLattice q L)
            (Lattice.dualLattice r M) := hdual
      _ = Lattice.dualLattice (q.orthogonalSum r)
          (Lattice.product L M) :=
        (Lattice.dualLattice_orthogonalProduct
          (q := q) (r := r) (L := L) (M := M)).symm
  exact Lattice.eq_of_dualLattice_eq hdualProduct

omit [BONGReverseDualLaws.{u, max v w} K] in
/-- Step-count form of the reverse-dual endpoint reflection theorem. -/
theorem beli2019Lemma710DualRightEnd_steps_of_good
    {rightLength baseTail steps : Nat} {N : Lattice K (V × W)}
    (leftDual : BONG.GoodBONG q (Lattice.dualLattice q L) n)
    (hsteps : steps ≤ n)
    (rightDual : BONG W r (Lattice.dualLattice r M)
      (rightLength + 1))
    (seed : BONG.OrthogonalPrefixSeed r (Lattice.dualLattice r M)
      (baseTail + 1) (steps := steps) leftDual.toBONG)
    (hlast : ∀ hpos : 0 < steps,
      leftDual.order ⟨steps - 1, by omega⟩ ≤ rightDual.order 0)
    (targetDual : BONG.GoodBONG (q.orthogonalSum r)
      (Lattice.dualLattice (q.orthogonalSum r) N)
      ((baseTail + 1) + steps))
    (leftVectors : ∀ i : Fin steps,
      targetDual.toBONG.ambientVector
          (BONG.orthogonalProductLeftIndex (baseTail + 1) i) =
        (leftDual.toBONG.ambientVector (seed.sourceIndex i), 0))
    (rightVectors : ∀ j : Fin (baseTail + 1),
      targetDual.toBONG.ambientVector
          (BONG.orthogonalProductRightIndex steps j) =
        seed.baseAmbientVector j) :
    N = Lattice.product L M := by
  have hdual :
      Lattice.dualLattice (q.orthogonalSum r) N =
        Lattice.product (Lattice.dualLattice q L)
          (Lattice.dualLattice r M) :=
    leftDual.beli2019Lemma710RightEnd_steps_of_good hsteps rightDual
      seed hlast targetDual.toBONG targetDual.good leftVectors rightVectors
  apply Lattice.eq_of_dualLattice_eq
  calc
    Lattice.dualLattice (q.orthogonalSum r) N =
        Lattice.product (Lattice.dualLattice q L)
          (Lattice.dualLattice r M) := hdual
    _ = Lattice.dualLattice (q.orthogonalSum r)
        (Lattice.product L M) :=
      (Lattice.dualLattice_orthogonalProduct
        (q := q) (r := r) (L := L) (M := M)).symm

end BONG.GoodBONG

end Bong
