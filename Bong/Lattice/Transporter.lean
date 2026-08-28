/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.SectionTwo
import Bong.Lattice.Isometry
import Bong.QuadraticSpace.OrthogonalExtension

/-!
# Transporting isometries through norm-generator projections

This file proves the automorphism case of Beli (2003), Corollary 2.4 and
Section 2.5: every integral isometry of the projected lattice extends, by
fixing a norm generator, to an integral isometry of the original lattice.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {x : V}
  {anisotropic : q.IsAnisotropic x}

/-- Projection of an image lattice is the image of its projection. -/
theorem projectedLattice_map_orthogonalExtension
    (f : QuadraticSpace.Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)) :
    projectedLattice q
        (map (QuadraticSpace.orthogonalExtensionLinearEquiv f) L)
        x anisotropic =
      map f.toLinearEquiv (projectedLattice q L x anisotropic) := by
  apply Lattice.ext
  ext y
  change y ∈ projectedLattice q
      (map (QuadraticSpace.orthogonalExtensionLinearEquiv f) L)
        x anisotropic ↔
    y ∈ map f.toLinearEquiv (projectedLattice q L x anisotropic)
  rw [mem_projectedLattice_iff, mem_map_iff]
  constructor
  · rintro ⟨z, hz, hprojection⟩
    have hw :
        (QuadraticSpace.orthogonalExtensionLinearEquiv f).symm z ∈ L := by
      simpa only [mem_map_iff] using hz
    let w := (QuadraticSpace.orthogonalExtensionLinearEquiv f).symm z
    have hzw : QuadraticSpace.orthogonalExtensionLinearEquiv f w = z := by
      exact (QuadraticSpace.orthogonalExtensionLinearEquiv f).apply_symm_apply z
    have htail :
        q.projectionToOrthogonal x anisotropic w =
          f.toLinearEquiv.symm y := by
      apply f.toLinearEquiv.injective
      rw [f.toLinearEquiv.apply_symm_apply]
      rw [← hprojection, ← hzw]
      exact (QuadraticSpace.projectionToOrthogonal_orthogonalExtensionLinearEquiv
        f w).symm
    rw [← htail]
    exact projection_mem_projectedLattice q L x anisotropic hw
  · intro hy
    rcases (mem_projectedLattice_iff q L x anisotropic
      (f.toLinearEquiv.symm y)).1 hy with ⟨w, hw, hprojection⟩
    refine ⟨QuadraticSpace.orthogonalExtensionLinearEquiv f w, ?_, ?_⟩
    · exact (map_mem_map_iff
        (QuadraticSpace.orthogonalExtensionLinearEquiv f) L w).2 hw
    · rw [QuadraticSpace.projectionToOrthogonal_orthogonalExtensionLinearEquiv]
      rw [hprojection, f.toLinearEquiv.apply_symm_apply]

/--
Beli's Corollary 2.4: an isometry between projected lattices extends by the
identity on their common norm-generator line.
-/
noncomputable def Isometry.extendProjectedIsometry
    (generatorL : IsNormGenerator q L x)
    (generatorM : IsNormGenerator q M x)
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)
      (projectedLattice q L x anisotropic)
      (projectedLattice q M x anisotropic)) :
    Isometry q q L M := by
  let ambient := QuadraticSpace.orthogonalExtensionIsometry
    f.toQuadraticSpaceIsometry
  let e := ambient.toLinearEquiv
  let imageLattice := map e L
  have hfix : e x = x := by
    exact QuadraticSpace.orthogonalExtensionLinearEquiv_apply_distinguished
      f.toQuadraticSpaceIsometry
  have hnorm : normIdeal q imageLattice = normIdeal q L := by
    exact normIdeal_map_isometry ambient L
  have hnormTarget : normIdeal q imageLattice = normIdeal q M :=
    hnorm.trans (generatorL.normIdeal_eq.trans generatorM.normIdeal_eq.symm)
  have hxImage : x ∈ imageLattice := by
    have hx := (map_mem_map_iff e L x).2 generatorL.mem
    simpa only [hfix] using hx
  have generatorImage : IsNormGenerator q imageLattice x :=
    ⟨hxImage, hnorm.trans generatorL.normIdeal_eq⟩
  have hprojection :
      projectedLattice q imageLattice x anisotropic =
        projectedLattice q M x anisotropic := by
    change projectedLattice q
        (map (QuadraticSpace.orthogonalExtensionLinearEquiv
          f.toQuadraticSpaceIsometry) L) x anisotropic = _
    rw [projectedLattice_map_orthogonalExtension]
    exact f.map_eq
  have hImage : imageLattice = M :=
    eq_of_normIdeal_eq_of_projectedLattice_eq q imageLattice M x
      generatorImage generatorM anisotropic hnormTarget hprojection
  have hImageMap : map e L = M := by
    simpa only [imageLattice] using hImage
  exact
    { toLinearEquiv := e
      map_bilin := ambient.map_bilin
      map_mem := fun y => by
        have hy := (map_mem_map_iff e L y).symm
        simpa only [hImageMap] using hy }

/-- The automorphism specialization of Beli's Corollary 2.4 and Section 2.5. -/
noncomputable def Isometry.extendProjectedAutomorphism
    (generator : IsNormGenerator q L x)
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)
      (projectedLattice q L x anisotropic)
      (projectedLattice q L x anisotropic)) :
    Isometry q q L L :=
  f.extendProjectedIsometry generator generator

/-- The extended automorphism fixes the chosen norm generator. -/
@[simp]
theorem Isometry.extendProjectedAutomorphism_apply_distinguished
    (generator : IsNormGenerator q L x)
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)
      (projectedLattice q L x anisotropic)
      (projectedLattice q L x anisotropic)) :
    (f.extendProjectedAutomorphism generator).toLinearEquiv x = x := by
  exact QuadraticSpace.orthogonalExtensionLinearEquiv_apply_distinguished
    f.toQuadraticSpaceIsometry

/-- The extended automorphism induces the original map after projection. -/
theorem Isometry.projection_extendProjectedAutomorphism
    (generator : IsNormGenerator q L x)
    (f : Isometry (q.orthogonalSpace x anisotropic)
      (q.orthogonalSpace x anisotropic)
      (projectedLattice q L x anisotropic)
      (projectedLattice q L x anisotropic)) (y : V) :
    q.projectionToOrthogonal x anisotropic
        ((f.extendProjectedAutomorphism generator).toLinearEquiv y) =
      f.toLinearEquiv (q.projectionToOrthogonal x anisotropic y) := by
  exact QuadraticSpace.projectionToOrthogonal_orthogonalExtensionLinearEquiv
    f.toQuadraticSpaceIsometry y

end Lattice

end Bong
