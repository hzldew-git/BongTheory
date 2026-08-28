/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Representation
import Bong.Lattice.OrthogonalDecompositionVolume
import Bong.Lattice.ProjectionScaling
import Bong.Lattice.VolumeRigidity

/-!
# Equal-rank rigidity of integral representations

An injective integral representation between full lattices of the same
ambient dimension identifies the source with a sublattice of the target.
If their volume orders agree, full-lattice volume rigidity makes that
inclusion an equality.  Thus the representation is already an integral
isometry.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The image lattice of an integral representation lies in its target
lattice. -/
theorem Representation.map_le
    (f : Representation q r L M)
    [FiniteDimensional K V] [FiniteDimensional K W]
    (hfinrank : finrank K V = finrank K W) :
    map (f.toQuadraticSpaceIsometryOfFinrankEq hfinrank).toLinearEquiv L ≤ M := by
  intro y hy
  change y ∈ map
    (f.toQuadraticSpaceIsometryOfFinrankEq hfinrank).toLinearEquiv L at hy
  change y ∈ M
  rw [mem_map_iff] at hy
  have hmem := f.map_mem hy
  have heq : f.toLinearMap
      ((f.toQuadraticSpaceIsometryOfFinrankEq hfinrank).toLinearEquiv.symm y) = y := by
    change (f.toQuadraticSpaceIsometryOfFinrankEq hfinrank).toLinearEquiv
      ((f.toQuadraticSpaceIsometryOfFinrankEq hfinrank).toLinearEquiv.symm y) = y
    exact LinearEquiv.apply_symm_apply _ y
  rw [heq] at hmem
  exact hmem

/-- An equal-rank integral representation with equal volume order is an
integral isometry. -/
noncomputable def Representation.toIsometryOfFinrankEqOfVolumeOrderEq
    (f : Representation q r L M)
    [FiniteDimensional K V] [FiniteDimensional K W]
    (hfinrank : finrank K V = finrank K W)
    (hvolume : volumeOrder q L = volumeOrder r M) :
    Isometry q r L M := by
  let e : QuadraticSpace.Isometry q r :=
    f.toQuadraticSpaceIsometryOfFinrankEq hfinrank
  let image : Lattice K W := map e.toLinearEquiv L
  have hle : image ≤ M := by
    simpa only [image, e] using f.map_le hfinrank
  have himageVolume : volumeOrder r image = volumeOrder q L := by
    exact (volumeOrder_eq_of_isometry (Isometry.toMap q e L)).symm
  have hmap : image = M :=
    eq_of_le_of_volumeOrder_eq r image M hle
      (himageVolume.trans hvolume)
  exact Isometry.ofMapEq q e L M hmap

/-- Proposition-valued form of equal-rank representation rigidity. -/
theorem Represents.isIsometric_of_finrank_eq_of_volumeOrder_eq
    (h : Represents r q M L)
    [FiniteDimensional K V] [FiniteDimensional K W]
    (hfinrank : finrank K V = finrank K W)
    (hvolume : volumeOrder q L = volumeOrder r M) :
    IsIsometric q r L M := by
  rcases h with ⟨f⟩
  exact ⟨f.toIsometryOfFinrankEqOfVolumeOrderEq hfinrank hvolume⟩

end Lattice

end Bong
