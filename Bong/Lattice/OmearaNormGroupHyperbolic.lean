/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009WeightIdealProof
import Bong.Bong.Beli2009WeightIdealIsometry
import Bong.Lattice.ModularIsometry
import Bong.Lattice.OmearaHyperbolicModularStep
import Bong.Lattice.QuadraticValues

/-!
# O'Meara's norm group in the presence of a hyperbolic plane

The observation preceding O'Meara 93:3 says that an integral-scale lattice
containing a standard hyperbolic plane represents every element of its norm
group.  This is the representation input used in Examples 93:13 and in the
proof of Corollary 93:14a.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {W : Type v} [AddCommGroup W] [Module K W]

/-- If an integral-scale lattice contains a standard hyperbolic direct
summand, its norm group is exactly its set of represented values. -/
theorem normGroupSet_eq_quadraticValueSet_hyperbolicProduct
    (r : QuadraticSpace K W) (M : Lattice K W)
    (hscale : IsScaleIntegral
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) M)) :
    normGroupSet
        ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
        (product (hyperbolicPlaneLattice (K := K)) M) =
      quadraticValueSet
        ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
        (product (hyperbolicPlaneLattice (K := K)) M) := by
  let q := (QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r
  let L := product (hyperbolicPlaneLattice (K := K)) M
  apply Set.Subset.antisymm
  · rintro z ⟨x, hx, y, hy, rfl⟩
    have hxParts : x.1 ∈ hyperbolicPlaneLattice (K := K) ∧ x.2 ∈ M :=
      (mem_product_iff.mp hx)
    have hxCoordinates :=
      (mem_omearaPlaneLattice_iff (K := K) x.1).mp hxParts.1
    rcases hy with ⟨s, hs, hsy⟩
    have hsIntegral : s ∈ IntegerRing K := by
      apply mem_unitIdeal_iff.mp
      exact hscale hs
    let xZero : IntegerRing K := ⟨x.1 0, hxCoordinates.1⟩
    let xOne : IntegerRing K := ⟨x.1 1, hxCoordinates.2⟩
    let sIntegral : IntegerRing K := ⟨s, hsIntegral⟩
    let c : IntegerRing K := xZero * xOne + sIntegral
    let h : Fin 2 → K := fun i => if i = 0 then (c : K) else 1
    have hh : h ∈ hyperbolicPlaneLattice (K := K) := by
      rw [mem_omearaPlaneLattice_iff]
      constructor
      · simpa [h] using c.property
      · simp [h]
    rw [mem_quadraticValueSet_iff]
    refine ⟨(h, x.2), (mem_product_iff.mpr ⟨hh, hxParts.2⟩), ?_⟩
    change q.quadratic (h, x.2) = q.quadratic x + y
    rw [QuadraticSpace.orthogonalSum_quadratic_apply,
      QuadraticSpace.orthogonalSum_quadratic_apply,
      QuadraticSpace.hyperbolicPlane_quadratic_apply,
      QuadraticSpace.hyperbolicPlane_quadratic_apply]
    simp only [Units.val_one]
    have hzero : h 0 = (c : K) := by simp [h]
    have hone : h 1 = 1 := by simp [h]
    rw [hzero, hone, mul_one]
    dsimp only [c, xZero, xOne, sIntegral]
    push_cast
    simp only [mul_one]
    change (2 : K) * ((x.1 0 * x.1 1) + s) + r.quadratic x.2 =
      (2 : K) * (x.1 0 * x.1 1) + r.quadratic x.2 + y
    have hsy' : y =
        algebraMap (IntegerRing K) K (2 : IntegerRing K) * s := by
      simpa only [twoMulLinearMap_apply, Algebra.smul_def] using hsy.symm
    have htwo : algebraMap (IntegerRing K) K (2 : IntegerRing K) =
        (2 : K) := by
      change ((2 : IntegerRing K) : K) = (2 : K)
      rfl
    rw [hsy', htwo]
    ring
  · intro z hz
    rw [mem_quadraticValueSet_iff] at hz
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, hx, 0, (twoScaleIdeal q L).zero_mem, by simp⟩

/-- Scale-sensitive form of the observation preceding O'Meara 93:3.
If the scale ideal of a lattice containing the standard `H_a` summand is
contained in `a O`, every element of its norm group is represented by the
lattice. -/
theorem normGroupSet_eq_quadraticValueSet_scaledHyperbolicProduct
    (r : QuadraticSpace K W) (M : Lattice K W) (a : Kˣ)
    (hscale :
      scaleIdeal
          ((QuadraticSpace.hyperbolicPlane a).orthogonalSum r)
          (product (hyperbolicPlaneLattice (K := K)) M) ≤
        principalIdeal (K := K) (a : K)) :
    normGroupSet
        ((QuadraticSpace.hyperbolicPlane a).orthogonalSum r)
        (product (hyperbolicPlaneLattice (K := K)) M) =
      quadraticValueSet
        ((QuadraticSpace.hyperbolicPlane a).orthogonalSum r)
        (product (hyperbolicPlaneLattice (K := K)) M) := by
  let q := (QuadraticSpace.hyperbolicPlane a).orthogonalSum r
  let L := product (hyperbolicPlaneLattice (K := K)) M
  apply Set.Subset.antisymm
  · rintro z ⟨x, hx, y, hy, rfl⟩
    have hxParts : x.1 ∈ hyperbolicPlaneLattice (K := K) ∧ x.2 ∈ M :=
      mem_product_iff.mp hx
    have hxCoordinates :=
      (mem_omearaPlaneLattice_iff (K := K) x.1).mp hxParts.1
    rcases hy with ⟨s, hs, hsy⟩
    have hsPrincipal : s ∈ principalIdeal (K := K) (a : K) :=
      hscale hs
    have hsIntegral : ((a⁻¹ : Kˣ) : K) * s ∈ IntegerRing K := by
      apply mem_integerRing_of_mul_mem_principalIdeal (Units.ne_zero a)
      rw [show (a : K) * (((a⁻¹ : Kˣ) : K) * s) = s by
        simp [Units.ne_zero a]]
      exact hsPrincipal
    let xZero : IntegerRing K := ⟨x.1 0, hxCoordinates.1⟩
    let xOne : IntegerRing K := ⟨x.1 1, hxCoordinates.2⟩
    let sIntegral : IntegerRing K :=
      ⟨((a⁻¹ : Kˣ) : K) * s, hsIntegral⟩
    let c : IntegerRing K := xZero * xOne + sIntegral
    let h : Fin 2 → K := fun i => if i = 0 then (c : K) else 1
    have hh : h ∈ hyperbolicPlaneLattice (K := K) := by
      rw [mem_omearaPlaneLattice_iff]
      constructor
      · simpa [h] using c.property
      · simp [h]
    rw [mem_quadraticValueSet_iff]
    refine ⟨(h, x.2), mem_product_iff.mpr ⟨hh, hxParts.2⟩, ?_⟩
    change q.quadratic (h, x.2) = q.quadratic x + y
    rw [QuadraticSpace.orthogonalSum_quadratic_apply,
      QuadraticSpace.orthogonalSum_quadratic_apply,
      QuadraticSpace.hyperbolicPlane_quadratic_apply,
      QuadraticSpace.hyperbolicPlane_quadratic_apply]
    change (2 : K) * (a : K) * (h 0 * h 1) + r.quadratic x.2 =
      (2 : K) * (a : K) * (x.1 0 * x.1 1) + r.quadratic x.2 + y
    have hzero : h 0 = (c : K) := by simp [h]
    have hone : h 1 = 1 := by simp [h]
    rw [hzero, hone, mul_one]
    dsimp only [c, xZero, xOne, sIntegral]
    push_cast
    have htwo : algebraMap (IntegerRing K) K (2 : IntegerRing K) =
        (2 : K) := by
      rfl
    have hsy' : y = (2 : K) * s := by
      simpa only [twoMulLinearMap_apply, Algebra.smul_def, htwo] using hsy.symm
    rw [hsy']
    field_simp [Units.ne_zero a]
    <;> ring
  · intro z hz
    rw [mem_quadraticValueSet_iff] at hz
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, hx, 0, (twoScaleIdeal q L).zero_mem, by simp⟩

/-- In particular, modularity supplies the scale containment required by
the scale-sensitive hyperbolic norm-group theorem. -/
theorem normGroupSet_eq_quadraticValueSet_scaledHyperbolicProduct_of_modular
    (r : QuadraticSpace K W) (M : Lattice K W) (a : Kˣ)
    (hmodular : IsModular
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) M) a) :
    normGroupSet
        ((QuadraticSpace.hyperbolicPlane a).orthogonalSum r)
        (product (hyperbolicPlaneLattice (K := K)) M) =
      quadraticValueSet
        ((QuadraticSpace.hyperbolicPlane a).orthogonalSum r)
        (product (hyperbolicPlaneLattice (K := K)) M) :=
  normGroupSet_eq_quadraticValueSet_scaledHyperbolicProduct r M a
    hmodular.scaleIdeal_le_principal

/-- The equality `g(L) = Q(L)` transports from a displayed scaled
hyperbolic splitting back to the original modular lattice. -/
theorem normGroupSet_eq_quadraticValueSet_of_isometric_scaledHyperbolicProduct
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (r : QuadraticSpace K W) (M : Lattice K W) (a : Kˣ)
    (f : Isometry q
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum r) L
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hmodular : IsModular q L a) :
    normGroupSet q L = quadraticValueSet q L := by
  let target := (QuadraticSpace.hyperbolicPlane a).orthogonalSum r
  let N := product (hyperbolicPlaneLattice (K := K)) M
  have htargetModular : IsModular target N a :=
    hmodular.mapLatticeIsometry f
  have hnorm : normGroupSet target N = normGroupSet q L := by
    calc
      normGroupSet target N =
          normGroupSet target (map f.toLinearEquiv L) := by
            rw [f.map_eq]
      _ = normGroupSet q L :=
        normGroupSet_map_isometry f.toQuadraticSpaceIsometry L
  calc
    normGroupSet q L = normGroupSet target N := hnorm.symm
    _ = quadraticValueSet target N :=
      normGroupSet_eq_quadraticValueSet_scaledHyperbolicProduct_of_modular
        r M a htargetModular
    _ = quadraticValueSet q L :=
      quadraticValueSet_eq_of_latticeIsometry f

end Lattice

end Bong
