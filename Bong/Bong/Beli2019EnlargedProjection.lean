/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019EnlargedLattice
import Bong.Bong.GoodMap
import Bong.Lattice.ProjectionScaling

/-!
# Beli (2019), the projected BONG in Lemma 5.7

The enlarged head `π⁻ˢy` spans the same line as `y`.  This file identifies
the projected enlarged lattice with the original projected lattice by a
lattice isometry and transports a chosen good BONG without changing its
orders or its underlying ambient vectors.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The projected enlarged lattice along `π⁻ˢy` is canonically isometric to
the projection of the original lattice along `y`. -/
noncomputable def lemma57ProjectedIsometry (q : QuadraticSpace K V)
    (N : Lattice K V) {y : V} (anisotropic : q.IsAnisotropic y)
    (s : Int) :
    Lattice.Isometry
      (q.orthogonalSpace (lemma57EnlargedHead (K := K) y s)
        (q.isAnisotropic_smul anisotropic
          (Units.ne_zero (uniformizerPowerUnit K (-s)))))
      (q.orthogonalSpace y anisotropic)
      (Lattice.projectedLattice q (lemma57EnlargedLattice N y s)
        (lemma57EnlargedHead (K := K) y s)
        (q.isAnisotropic_smul anisotropic
          (Units.ne_zero (uniformizerPowerUnit K (-s)))))
      (Lattice.projectedLattice q N y anisotropic) := by
  let a : K := (uniformizerPowerUnit K (-s) : K)
  have ha : a ≠ 0 := Units.ne_zero (uniformizerPowerUnit K (-s))
  let f := q.orthogonalSpaceSMulIsometry anisotropic ha
  apply Lattice.Isometry.ofMapEq _ f
  change Lattice.map (q.vectorOrthogonalSMulEquiv y ha)
      (Lattice.projectedLattice q (lemma57EnlargedLattice N y s)
        (a • y) (q.isAnisotropic_smul anisotropic ha)) =
    Lattice.projectedLattice q N y anisotropic
  rw [Lattice.map_projectedLattice_smul]
  exact projectedLattice_lemma57EnlargedLattice q N y anisotropic s

/-- Transport a chosen good BONG of `pr_(y⊥) N` to the projection of the
enlarged lattice along its scaled head. -/
noncomputable def lemma57ProjectedGoodBONG (q : QuadraticSpace K V)
    (N : Lattice K V) {y : V} (anisotropic : q.IsAnisotropic y)
    (s : Int) {n : Nat}
    (tail : GoodBONG (q.orthogonalSpace y anisotropic)
      (Lattice.projectedLattice q N y anisotropic) n) :
    GoodBONG
      (q.orthogonalSpace (lemma57EnlargedHead (K := K) y s)
        (q.isAnisotropic_smul anisotropic
          (Units.ne_zero (uniformizerPowerUnit K (-s)))))
      (Lattice.projectedLattice q (lemma57EnlargedLattice N y s)
        (lemma57EnlargedHead (K := K) y s)
        (q.isAnisotropic_smul anisotropic
          (Units.ne_zero (uniformizerPowerUnit K (-s))))) n :=
  tail.mapLatticeIsometry
    (lemma57ProjectedIsometry q N anisotropic s).symm

@[simp]
theorem lemma57ProjectedGoodBONG_order (q : QuadraticSpace K V)
    (N : Lattice K V) {y : V} (anisotropic : q.IsAnisotropic y)
    (s : Int) {n : Nat}
    (tail : GoodBONG (q.orthogonalSpace y anisotropic)
      (Lattice.projectedLattice q N y anisotropic) n) (i : Fin n) :
    (lemma57ProjectedGoodBONG q N anisotropic s tail).order i =
      tail.order i := by
  simp [lemma57ProjectedGoodBONG]

/-- The transported projected BONG consists of the same vectors in the
original ambient space. -/
@[simp]
theorem coe_ambientVector_lemma57ProjectedGoodBONG
    (q : QuadraticSpace K V) (N : Lattice K V) {y : V}
    (anisotropic : q.IsAnisotropic y) (s : Int) {n : Nat}
    (tail : GoodBONG (q.orthogonalSpace y anisotropic)
      (Lattice.projectedLattice q N y anisotropic) n) (i : Fin n) :
    (((lemma57ProjectedGoodBONG q N anisotropic s tail).toBONG.ambientVector i :
        q.vectorOrthogonal (lemma57EnlargedHead (K := K) y s)) : V) =
      (tail.toBONG.ambientVector i : V) := by
  change
    (((tail.toBONG.mapLatticeIsometry
      (lemma57ProjectedIsometry q N anisotropic s).symm).ambientVector i :
        q.vectorOrthogonal (lemma57EnlargedHead (K := K) y s)) : V) = _
  rw [BONG.ambientVector_mapLatticeIsometry]
  rfl

end BONG

end Bong
