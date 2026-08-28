/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.SpinorNorm
import Bong.Lattice.ModularIsometry

/-!
# Spinor norms under lattice isometry and integral duality

The Wall determinant is invariant under conjugation by a quadratic-space
isometry.  Consequently integral spinor-norm images are invariant under
lattice isometry.  We also show that an integral automorphism preserves the
integral dual lattice, so a lattice and its dual have the same spinor image.
-/

namespace Bong

open Module

namespace QuadraticSpace

universe u v w

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}

/-- Conjugate an orthogonal automorphism through an ambient isometry. -/
def Isometry.conjugate (e : q.Isometry r) (f : q.Isometry q) : r.Isometry r :=
  e.symm.trans (f.trans e)

omit [CharZero K] in
@[simp]
theorem Isometry.conjugate_apply (e : q.Isometry r) (f : q.Isometry q)
    (y : W) :
    (e.conjugate f).toLinearEquiv y =
      e.toLinearEquiv (f.toLinearEquiv (e.toLinearEquiv.symm y)) :=
  rfl

omit [CharZero K] in
theorem residualLinearMap_conjugate_apply
    (e : q.Isometry r) (f : q.Isometry q) (x : V) :
    residualLinearMap (e.conjugate f) (e.toLinearEquiv x) =
      e.toLinearEquiv (residualLinearMap f x) := by
  simp only [residualLinearMap_apply, Isometry.conjugate_apply,
    e.toLinearEquiv.symm_apply_apply, map_sub]

/-- The residual spaces of conjugate isometries are canonically equivalent. -/
noncomputable def residualSpaceConjugateEquiv
    (e : q.Isometry r) (f : q.Isometry q) :
    residualSpace f ≃ₗ[K] residualSpace (e.conjugate f) where
  toFun y := by
    refine ⟨e.toLinearEquiv (y : V), ?_⟩
    rcases y.property with ⟨x, hx⟩
    refine ⟨e.toLinearEquiv x, ?_⟩
    rw [residualLinearMap_conjugate_apply]
    exact congrArg e.toLinearEquiv hx
  invFun z := by
    refine ⟨e.toLinearEquiv.symm (z : W), ?_⟩
    rcases z.property with ⟨y, hy⟩
    refine ⟨e.toLinearEquiv.symm y, ?_⟩
    have htransport :
        residualLinearMap f (e.toLinearEquiv.symm y) =
          e.toLinearEquiv.symm
            (residualLinearMap (e.conjugate f) y) := by
      apply e.toLinearEquiv.injective
      rw [e.toLinearEquiv.apply_symm_apply]
      simpa only [e.toLinearEquiv.apply_symm_apply] using
        (residualLinearMap_conjugate_apply e f
          (e.toLinearEquiv.symm y)).symm
    exact htransport.trans (congrArg e.toLinearEquiv.symm hy)
  left_inv y := by
    apply Subtype.ext
    exact e.toLinearEquiv.symm_apply_apply (y : V)
  right_inv z := by
    apply Subtype.ext
    exact e.toLinearEquiv.apply_symm_apply (z : W)
  map_add' x y := by
    apply Subtype.ext
    exact e.toLinearEquiv.map_add (x : V) (y : V)
  map_smul' a x := by
    apply Subtype.ext
    exact e.toLinearEquiv.map_smul a (x : V)

@[simp]
theorem coe_residualSpaceConjugateEquiv
    (e : q.Isometry r) (f : q.Isometry q) (y : residualSpace f) :
    ((residualSpaceConjugateEquiv e f y : residualSpace (e.conjugate f)) : W) =
      e.toLinearEquiv (y : V) :=
  rfl

theorem residualSpaceConjugateEquiv_residualMap
    (e : q.Isometry r) (f : q.Isometry q) (x : V) :
    residualSpaceConjugateEquiv e f (residualMap f x) =
      residualMap (e.conjugate f) (e.toLinearEquiv x) := by
  apply Subtype.ext
  exact (residualLinearMap_conjugate_apply e f x).symm

/-- The Wall form is transported literally to the Wall form of the
conjugate isometry. -/
theorem wallForm_conjugate
    (e : q.Isometry r) (f : q.Isometry q)
    (y z : residualSpace f) :
    wallForm (e.conjugate f) (residualSpaceConjugateEquiv e f y)
        (residualSpaceConjugateEquiv e f z) =
      wallForm f y z := by
  rcases residualMap_surjective f y with ⟨x, rfl⟩
  rw [residualSpaceConjugateEquiv_residualMap,
    wallForm_residualMap_left, wallForm_residualMap_left]
  change 2 * r.bilin (e.toLinearEquiv x) (e.toLinearEquiv (z : V)) =
    2 * q.bilin x (z : V)
  rw [e.map_bilin]

/-- The Wall spinor norm is invariant under isometric conjugation. -/
theorem spinorNorm_conjugate [FiniteDimensional K V] [FiniteDimensional K W]
    (e : q.Isometry r) (f : q.Isometry q) :
    spinorNorm (e.conjugate f) = spinorNorm f := by
  let E := residualSpaceConjugateEquiv e f
  let b := wallBasis f
  let c := b.map E
  have hfin : Module.finrank K (residualSpace (e.conjugate f)) =
      Module.finrank K (residualSpace f) := E.symm.finrank_eq
  have hmatrix : LinearMap.BilinForm.toMatrix c (wallForm (e.conjugate f)) =
      LinearMap.BilinForm.toMatrix b (wallForm f) := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, c, Basis.map_apply]
    exact wallForm_conjugate e f (b i) (b j)
  rw [spinorNorm_eq_basisDeterminantOfFinrankEq (e.conjugate f) hfin c,
    spinorNorm_eq_basisDeterminant f b]
  apply congrArg (Dyadic.squareClass K)
  apply Units.ext
  exact congrArg Matrix.det hmatrix

end QuadraticSpace

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- Conjugate an integral orthogonal automorphism through a lattice isometry. -/
noncomputable def Isometry.conjugateAutomorphism
    (e : Isometry q r L M) (f : IntegralOrthogonalGroup q L) :
    IntegralOrthogonalGroup r M where
  toLinearEquiv :=
    (e.toQuadraticSpaceIsometry.conjugate f.toQuadraticSpaceIsometry).toLinearEquiv
  map_bilin :=
    (e.toQuadraticSpaceIsometry.conjugate f.toQuadraticSpaceIsometry).map_bilin
  map_mem y := by
    change y ∈ M ↔
      e.toLinearEquiv
          (f.toLinearEquiv (e.toLinearEquiv.symm y)) ∈ M
    calc
      y ∈ M ↔ e.toLinearEquiv.symm y ∈ L := by
        simpa using (e.map_mem (e.toLinearEquiv.symm y)).symm
      _ ↔ f.toLinearEquiv (e.toLinearEquiv.symm y) ∈ L :=
        f.map_mem (e.toLinearEquiv.symm y)
      _ ↔ e.toLinearEquiv
          (f.toLinearEquiv (e.toLinearEquiv.symm y)) ∈ M :=
        e.map_mem _

/-- Conjugation through a lattice isometry preserves the integral spinor
norm. -/
theorem integralSpinorNorm_conjugateAutomorphism
    (e : Isometry q r L M) (f : IntegralOrthogonalGroup q L) :
    integralSpinorNorm (e.conjugateAutomorphism f) =
      integralSpinorNorm f := by
  letI : Module.Finite K V := L.moduleFinite
  letI : Module.Finite K W := M.moduleFinite
  exact QuadraticSpace.spinorNorm_conjugate
    e.toQuadraticSpaceIsometry f.toQuadraticSpaceIsometry

/-- Conjugating a proper integral rotation through a lattice isometry
preserves properness. -/
noncomputable def IntegralRotation.conjugateAutomorphism
    (e : Isometry q r L M) (f : IntegralRotation q L) :
    IntegralRotation r M where
  toIntegralOrthogonalGroup :=
    e.conjugateAutomorphism f.toIntegralOrthogonalGroup
  det_eq_one := by
    change LinearEquiv.det
        ((e.toLinearEquiv.symm.trans
          f.toIntegralOrthogonalGroup.toLinearEquiv).trans
            e.toLinearEquiv) = 1
    rw [LinearEquiv.det_conj, f.det_eq_one]

/-- Conjugation through a lattice isometry preserves the spinor norm of a
proper integral rotation. -/
theorem IntegralRotation.spinorNorm_conjugateAutomorphism
    (e : Isometry q r L M) (f : IntegralRotation q L) :
    (f.conjugateAutomorphism e).spinorNorm = f.spinorNorm :=
  integralSpinorNorm_conjugateAutomorphism e
    f.toIntegralOrthogonalGroup

/-- Integral spinor-norm images are invariant under lattice isometry. -/
theorem spinorNormImage_eq_of_isometry (e : Isometry q r L M) :
    spinorNormImage (q := q) (L := L) =
      spinorNormImage (q := r) (L := M) := by
  apply Set.Subset.antisymm
  · rintro a ⟨f, rfl⟩
    exact ⟨f.conjugateAutomorphism e,
      f.spinorNorm_conjugateAutomorphism e⟩
  · rintro a ⟨f, rfl⟩
    exact ⟨f.conjugateAutomorphism e.symm,
      f.spinorNorm_conjugateAutomorphism e.symm⟩

/-- The determinant-`-1` spinor image is invariant under lattice isometry. -/
theorem improperSpinorNormImage_eq_of_isometry (e : Isometry q r L M) :
    improperSpinorNormImage (q := q) (L := L) =
      improperSpinorNormImage (q := r) (L := M) := by
  apply Set.Subset.antisymm
  · rintro a ⟨f, hdet, rfl⟩
    refine ⟨e.conjugateAutomorphism f, ?_,
      integralSpinorNorm_conjugateAutomorphism e f⟩
    change LinearEquiv.det
        ((e.toLinearEquiv.symm.trans f.toLinearEquiv).trans
          e.toLinearEquiv) = (-1 : Kˣ)
    rw [LinearEquiv.det_conj, hdet]
  · rintro a ⟨f, hdet, rfl⟩
    refine ⟨e.symm.conjugateAutomorphism f, ?_,
      integralSpinorNorm_conjugateAutomorphism e.symm f⟩
    change LinearEquiv.det
        ((e.toLinearEquiv.trans f.toLinearEquiv).trans
          e.toLinearEquiv.symm) = (-1 : Kˣ)
    calc
      LinearEquiv.det
          ((e.toLinearEquiv.trans f.toLinearEquiv).trans
            e.toLinearEquiv.symm) = LinearEquiv.det f.toLinearEquiv := by
        simpa using LinearEquiv.det_conj f.toLinearEquiv e.toLinearEquiv.symm
      _ = (-1 : Kˣ) := hdet

/-- An integral automorphism preserves the integral dual lattice. -/
noncomputable def IntegralOrthogonalGroup.dual
    (f : IntegralOrthogonalGroup q L) :
    IntegralOrthogonalGroup q (dualLattice q L) where
  toLinearEquiv := f.toLinearEquiv
  map_bilin := f.map_bilin
  map_mem x := by
    have hmap : map f.toLinearEquiv (dualLattice q L) =
        dualLattice q L := by
      calc
        map f.toLinearEquiv (dualLattice q L) =
            dualLattice q (map f.toLinearEquiv L) :=
          (dualLattice_map_isometry f.toQuadraticSpaceIsometry L).symm
        _ = dualLattice q L := by rw [f.map_eq]
    constructor
    · intro hx
      rw [← hmap]
      exact (map_mem_map_iff f.toLinearEquiv (dualLattice q L) x).2 hx
    · intro hx
      have hx' : f.toLinearEquiv x ∈
          map f.toLinearEquiv (dualLattice q L) := by
        rwa [hmap]
      exact (map_mem_map_iff f.toLinearEquiv (dualLattice q L) x).1 hx'

@[simp]
theorem integralSpinorNorm_dual (f : IntegralOrthogonalGroup q L) :
    integralSpinorNorm f.dual = integralSpinorNorm f := by
  letI : Module.Finite K V := L.moduleFinite
  rfl

/-- A proper integral rotation acts properly on the dual lattice. -/
noncomputable def IntegralRotation.dual (f : IntegralRotation q L) :
    IntegralRotation q (dualLattice q L) where
  toIntegralOrthogonalGroup := f.toIntegralOrthogonalGroup.dual
  det_eq_one := f.det_eq_one

@[simp]
theorem IntegralRotation.spinorNorm_dual (f : IntegralRotation q L) :
    f.dual.spinorNorm = f.spinorNorm :=
  integralSpinorNorm_dual f.toIntegralOrthogonalGroup

theorem spinorNormImage_subset_dualLattice :
    spinorNormImage (q := q) (L := L) ⊆
      spinorNormImage (q := q) (L := dualLattice q L) := by
  rintro a ⟨f, rfl⟩
  exact ⟨f.dual, f.spinorNorm_dual⟩

/-- A lattice and its integral dual have the same integral spinor-norm image. -/
theorem spinorNormImage_dualLattice :
    spinorNormImage (q := q) (L := dualLattice q L) =
      spinorNormImage (q := q) (L := L) := by
  apply Set.Subset.antisymm
  · simpa using (spinorNormImage_subset_dualLattice
      (q := q) (L := dualLattice q L))
  · exact spinorNormImage_subset_dualLattice

theorem improperSpinorNormImage_subset_dualLattice :
    improperSpinorNormImage (q := q) (L := L) ⊆
      improperSpinorNormImage (q := q) (L := dualLattice q L) := by
  rintro a ⟨f, hdet, rfl⟩
  exact ⟨f.dual, hdet, integralSpinorNorm_dual f⟩

/-- A lattice and its integral dual have the same determinant-`-1` spinor
image. -/
theorem improperSpinorNormImage_dualLattice :
    improperSpinorNormImage (q := q) (L := dualLattice q L) =
      improperSpinorNormImage (q := q) (L := L) := by
  apply Set.Subset.antisymm
  · simpa using (improperSpinorNormImage_subset_dualLattice
      (q := q) (L := dualLattice q L))
  · exact improperSpinorNormImage_subset_dualLattice

end Lattice

end Bong
