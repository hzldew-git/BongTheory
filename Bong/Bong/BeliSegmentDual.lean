/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.MaximalNormSplittingDual
import Bong.Bong.SegmentTransport

/-!
# Integral duality for consecutive BONG segments

Passing to a consecutive segment commutes with normalized dual vectors.  If a
second segment realizes the reversed dual vectors, it is canonically
isometric to the integral dual of the original segment.  This is the
lattice-theoretic duality used in Beli (2003), Lemmas 4.8--4.9.
-/

namespace Bong

open Dyadic

namespace BONG.SegmentWitness

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n m start dualStart length : Nat}
  {bound : start + length ≤ n}
  {dualBound : dualStart + length ≤ m}
  {b : BONG V q L n} {c : BONG W r M m}

/-- Passing to a consecutive segment commutes with normalized dual vectors,
after inclusion of the segment carrier into the parent space. -/
@[simp]
theorem coe_dualVector_eq
    (w : SegmentWitness b start length bound) (i : Fin length) :
    (w.bong.dualVector i : V) = b.dualVector (w.sourceIndex i) := by
  rw [BONG.dualVector, BONG.dualVector, w.valueUnit_eq]
  change ((b.valueUnit (w.sourceIndex i))⁻¹ : K) •
      (w.bong.ambientVector i : V) =
    ((b.valueUnit (w.sourceIndex i))⁻¹ : K) •
      b.ambientVector (w.sourceIndex i)
  rw [w.ambientVector_eq]
  congr 1

/-- The reverse-dual vector of a segment is the parent dual vector at the
reversed local segment index. -/
@[simp]
theorem coe_reverseDualVector_eq
    (w : SegmentWitness b start length bound) (i : Fin length) :
    (w.bong.reverseDualVector i : V) =
      b.dualVector (w.sourceIndex (Fin.rev i)) := by
  rw [BONG.reverseDualVector, w.coe_dualVector_eq]

/-- For a prefix segment, reversing inside the segment agrees with taking
the suffix of the reversed parent sequence. -/
theorem coe_reverseDualVector_prefix_eq
    {prefixBound : 0 + length ≤ n}
    (w : SegmentWitness b 0 length prefixBound) (i : Fin length) :
    (w.bong.reverseDualVector i : V) =
      b.reverseDualVector
        ⟨n - length + i.val, by omega⟩ := by
  rw [w.coe_reverseDualVector_eq, BONG.reverseDualVector]
  congr 1
  apply Fin.ext
  simp only [sourceIndex_val, Nat.zero_add, Fin.rev]
  omega

/-- A consecutive segment in a reverse-dual BONG is the integral dual of
the corresponding original segment. -/
noncomputable def segmentDualLatticeIsometry
    [BONGReverseDualLaws.{u, v} K]
    (original : SegmentWitness b start length bound)
    (originalGood : b.IsGood)
    (dual : SegmentWitness c dualStart length dualBound)
    (ambient : q.Isometry r)
    (dualVectors : ∀ i : Fin length,
      (dual.bong.ambientVector i : W) =
        ambient.toLinearEquiv
          (original.bong.reverseDualVector i : V)) :
    Lattice.Isometry
      (q.restrict original.carrier original.nondegenerate)
      (r.restrict dual.carrier dual.nondegenerate)
      (Lattice.dualLattice
        (q.restrict original.carrier original.nondegenerate)
        original.lattice)
      dual.lattice := by
  let originalSegment := original.toGoodBONG originalGood
  choose reverseDual reverseDualVectors using
    originalSegment.exists_reverseDual
  let f : original.carrier ≃ₗ[K] dual.carrier :=
    reverseDual.toBONG.basis.equiv dual.bong.basis (Equiv.refl (Fin length))
  have hgram : ∀ i j : Fin length,
      (r.restrict dual.carrier dual.nondegenerate).bilin
          (dual.bong.basis i) (dual.bong.basis j) =
        (q.restrict original.carrier original.nondegenerate).bilin
          (reverseDual.toBONG.basis i) (reverseDual.toBONG.basis j) := by
    intro i j
    change r.bilin (dual.bong.ambientVector i : W)
        (dual.bong.ambientVector j : W) =
      q.bilin (reverseDual.toBONG.ambientVector i : original.carrier)
        (reverseDual.toBONG.ambientVector j : original.carrier)
    rw [dualVectors i, dualVectors j, ambient.map_bilin,
      reverseDualVectors i, reverseDualVectors j]
    change q.bilin (original.bong.reverseDualVector i : V)
        (original.bong.reverseDualVector j : V) =
      q.bilin (original.bong.reverseDualVector i : V)
        (original.bong.reverseDualVector j : V)
    rfl
  let restricted :
      (q.restrict original.carrier original.nondegenerate).Isometry
        (r.restrict dual.carrier dual.nondegenerate) :=
    { toLinearEquiv := f
      map_bilin := by
        intro x y
        have hforms :
            (r.restrict dual.carrier dual.nondegenerate).bilin.comp
                f.toLinearMap f.toLinearMap =
              (q.restrict original.carrier original.nondegenerate).bilin := by
          apply LinearMap.BilinForm.ext_basis reverseDual.toBONG.basis
          intro i j
          rw [LinearMap.BilinForm.comp_apply]
          simpa [f, Module.Basis.equiv] using hgram i j
        exact DFunLike.congr_fun (DFunLike.congr_fun hforms x) y }
  let mapped := reverseDual.toBONG.map restricted
  have mappedVectors : ∀ i : Fin length,
      mapped.ambientVector i = dual.bong.ambientVector i := by
    intro i
    rw [BONG.ambientVector_map]
    change f (reverseDual.toBONG.basis i) = dual.bong.basis i
    simp [f, Module.Basis.equiv]
  have hmap :
      Lattice.map restricted.toLinearEquiv
          (Lattice.dualLattice
            (q.restrict original.carrier original.nondegenerate)
            original.lattice) =
        dual.lattice :=
    mapped.lattice_eq_of_ambientVector_eq dual.bong mappedVectors
  exact
    { toLinearEquiv := restricted.toLinearEquiv
      map_bilin := restricted.map_bilin
      map_mem := by
        intro x
        rw [← hmap, Lattice.map_mem_map_iff] }

/-- The segment reverse-dual isometry is the canonical basis map on every
normalized reversed dual vector. -/
@[simp]
theorem segmentDualLatticeIsometry_apply_reverseDualVector
    [BONGReverseDualLaws.{u, v} K]
    (original : SegmentWitness b start length bound)
    (originalGood : b.IsGood)
    (dual : SegmentWitness c dualStart length dualBound)
    (ambient : q.Isometry r)
    (dualVectors : ∀ i : Fin length,
      (dual.bong.ambientVector i : W) =
        ambient.toLinearEquiv
          (original.bong.reverseDualVector i : V))
    (i : Fin length) :
    (segmentDualLatticeIsometry original originalGood dual ambient
      dualVectors).toLinearEquiv (original.bong.reverseDualVector i) =
      dual.bong.ambientVector i := by
  let originalSegment := original.toGoodBONG originalGood
  let reverseDual :=
    Classical.choose originalSegment.exists_reverseDual
  have reverseDualVectors :=
    Classical.choose_spec originalSegment.exists_reverseDual
  change (reverseDual.toBONG.basis.equiv dual.bong.basis
      (Equiv.refl (Fin length))) (original.bong.reverseDualVector i) =
    dual.bong.ambientVector i
  have hreverse := reverseDualVectors i
  change reverseDual.toBONG.ambientVector i =
    original.bong.reverseDualVector i at hreverse
  rw [← hreverse]
  change (reverseDual.toBONG.basis.equiv dual.bong.basis
      (Equiv.refl (Fin length))) (reverseDual.toBONG.basis i) =
    dual.bong.basis i
  simp [Module.Basis.equiv]

end BONG.SegmentWitness

end Bong
