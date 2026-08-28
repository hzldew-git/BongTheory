/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.OrthogonalExtension

/-!
# Preimages of projected sublattices

Given `x ∈ L` and a full sublattice `N ≤ pr_(x^⊥) L`, this file constructs
the full lattice of vectors of `L` whose projection lies in `N`.  This is the
one-step construction in Beli (2003), Lemma 2.7(ii).
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/--
The inverse image in `L` of a full sublattice of its orthogonal projection.
-/
noncomputable def projectionPreimage (q : QuadraticSpace K V)
    (L : Lattice K V) (x : V) (anisotropic : q.IsAnisotropic x)
    (hxL : x ∈ L) (N : Lattice K (q.vectorOrthogonal x))
    (hN : N ≤ projectedLattice q L x anisotropic) : Lattice K V where
  toSubmodule := L.toSubmodule ⊓ N.toSubmodule.comap
    ((q.projectionToOrthogonal x anisotropic).restrictScalars (IntegerRing K))
  fg := L.fg.of_le inf_le_left
  span_eq_top := by
    let P : Submodule (IntegerRing K) V :=
      L.toSubmodule ⊓ N.toSubmodule.comap
        ((q.projectionToOrthogonal x anisotropic).restrictScalars
          (IntegerRing K))
    let S : Submodule K V := Submodule.span K (P : Set V)
    have hxP : x ∈ P := by
      refine ⟨hxL, ?_⟩
      change q.projectionToOrthogonal x anisotropic x ∈ N
      have hzero : q.projectionToOrthogonal x anisotropic x = 0 := by
        apply Subtype.ext
        exact q.orthogonalProjection_self anisotropic
      rw [hzero]
      exact N.zero_mem
    have hxS : x ∈ S := Submodule.subset_span hxP
    have hNtoS : (N.toSubmodule : Set (q.vectorOrthogonal x)) ⊆
        (S.comap (Submodule.subtype (q.vectorOrthogonal x)) :
          Set (q.vectorOrthogonal x)) := by
      intro z hz
      have hzProjected : z ∈ projectedLattice q L x anisotropic := hN hz
      rcases (mem_projectedLattice_iff q L x anisotropic z).1 hzProjected with
        ⟨y, hyL, hprojection⟩
      have hyP : y ∈ P := by
        refine ⟨hyL, ?_⟩
        change q.projectionToOrthogonal x anisotropic y ∈ N
        rw [hprojection]
        exact hz
      have hyS : y ∈ S := Submodule.subset_span hyP
      change (z : V) ∈ S
      have hcoerce : (z : V) =
          y - (q.bilin x y / q.quadratic x) • x := by
        rw [← hprojection]
        exact q.orthogonalProjection_apply x y
      rw [hcoerce]
      exact S.sub_mem hyS (S.smul_mem _ hxS)
    have hspanN : Submodule.span K (N.toSubmodule : Set _) ≤
        S.comap (Submodule.subtype (q.vectorOrthogonal x)) :=
      Submodule.span_le.2 hNtoS
    rw [N.span_eq_top] at hspanN
    apply top_unique
    intro y _
    change y ∈ S
    have hprojectionS :
        (q.projectionToOrthogonal x anisotropic y : V) ∈ S := by
      have hp := hspanN
        (show q.projectionToOrthogonal x anisotropic y ∈
          (⊤ : Submodule K (q.vectorOrthogonal x)) by trivial)
      exact hp
    have hlineS : q.lineProjection x y ∈ S := by
      rw [q.lineProjection_apply]
      exact S.smul_mem _ hxS
    rw [← q.lineProjection_add_orthogonalProjection x y]
    exact S.add_mem hlineS hprojectionS

@[simp]
theorem mem_projectionPreimage_iff (q : QuadraticSpace K V)
    (L : Lattice K V) (x : V) (anisotropic : q.IsAnisotropic x)
    (hxL : x ∈ L) (N : Lattice K (q.vectorOrthogonal x))
    (hN : N ≤ projectedLattice q L x anisotropic) (y : V) :
    y ∈ projectionPreimage q L x anisotropic hxL N hN ↔
      y ∈ L ∧ q.projectionToOrthogonal x anisotropic y ∈ N :=
  Iff.rfl

/-- A projection preimage is a sublattice of the original lattice. -/
theorem projectionPreimage_le (q : QuadraticSpace K V)
    (L : Lattice K V) (x : V) (anisotropic : q.IsAnisotropic x)
    (hxL : x ∈ L) (N : Lattice K (q.vectorOrthogonal x))
    (hN : N ≤ projectedLattice q L x anisotropic) :
    projectionPreimage q L x anisotropic hxL N hN ≤ L := by
  intro y hy
  exact hy.1

/-- The distinguished vector belongs to every projection preimage. -/
theorem mem_projectionPreimage (q : QuadraticSpace K V)
    (L : Lattice K V) (x : V) (anisotropic : q.IsAnisotropic x)
    (hxL : x ∈ L) (N : Lattice K (q.vectorOrthogonal x))
    (hN : N ≤ projectedLattice q L x anisotropic) :
    x ∈ projectionPreimage q L x anisotropic hxL N hN := by
  rw [mem_projectionPreimage_iff]
  refine ⟨hxL, ?_⟩
  have hzero : q.projectionToOrthogonal x anisotropic x = 0 := by
    apply Subtype.ext
    exact q.orthogonalProjection_self anisotropic
  rw [hzero]
  exact N.zero_mem

/-- Projecting the inverse-image lattice recovers the selected sublattice. -/
theorem projectedLattice_projectionPreimage (q : QuadraticSpace K V)
    (L : Lattice K V) (x : V) (anisotropic : q.IsAnisotropic x)
    (hxL : x ∈ L) (N : Lattice K (q.vectorOrthogonal x))
    (hN : N ≤ projectedLattice q L x anisotropic) :
    projectedLattice q
        (projectionPreimage q L x anisotropic hxL N hN) x anisotropic = N := by
  apply Lattice.ext
  ext y
  change y ∈ projectedLattice q
      (projectionPreimage q L x anisotropic hxL N hN) x anisotropic ↔ y ∈ N
  rw [mem_projectedLattice_iff]
  constructor
  · rintro ⟨z, hz, hprojection⟩
    rw [mem_projectionPreimage_iff] at hz
    rw [← hprojection]
    exact hz.2
  · intro hy
    have hyProjected : y ∈ projectedLattice q L x anisotropic := hN hy
    rcases (mem_projectedLattice_iff q L x anisotropic y).1 hyProjected with
      ⟨z, hzL, hprojection⟩
    refine ⟨z, ?_, hprojection⟩
    rw [mem_projectionPreimage_iff]
    exact ⟨hzL, hprojection.symm ▸ hy⟩

/-- A norm generator remains a norm generator in every projection preimage. -/
theorem isNormGenerator_projectionPreimage (q : QuadraticSpace K V)
    (L : Lattice K V) (x : V) (generator : IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x)
    (N : Lattice K (q.vectorOrthogonal x))
    (hN : N ≤ projectedLattice q L x anisotropic) :
    IsNormGenerator q
      (projectionPreimage q L x anisotropic generator.mem N hN) x := by
  refine ⟨mem_projectionPreimage q L x anisotropic generator.mem N hN, ?_⟩
  apply le_antisymm
  · exact (normIdeal_mono q
      (projectionPreimage_le q L x anisotropic generator.mem N hN)).trans_eq
        generator.normIdeal_eq
  · rw [principalIdeal, Submodule.span_le]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact quadratic_mem_normIdeal_of_mem q
      (projectionPreimage q L x anisotropic generator.mem N hN)
      (mem_projectionPreimage q L x anisotropic generator.mem N hN)

/-- Taking the inverse image of the entire projected lattice changes nothing. -/
@[simp]
theorem projectionPreimage_projectedLattice (q : QuadraticSpace K V)
    (L : Lattice K V) (x : V) (anisotropic : q.IsAnisotropic x)
    (hxL : x ∈ L) :
    projectionPreimage q L x anisotropic hxL
      (projectedLattice q L x anisotropic) (fun _ hy => hy) = L := by
  apply Lattice.ext
  ext y
  change y ∈ projectionPreimage q L x anisotropic hxL
      (projectedLattice q L x anisotropic) (fun _ hy => hy) ↔ y ∈ L
  rw [mem_projectionPreimage_iff]
  simp only [and_iff_left_iff_imp]
  intro hy
  exact projection_mem_projectedLattice q L x anisotropic hy

end Lattice

end Bong
