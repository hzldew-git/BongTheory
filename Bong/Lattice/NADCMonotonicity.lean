/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.NADC
import Bong.Lattice.PairedHyperbolicRepresentation

/-!
# Monotonicity of local ADC rank

An integral target of rank `n` whose ambient space embeds in the source can
be enlarged by one sufficiently deep integral line inside the orthogonal
complement. Consequently `(n+1)`-ADC implies `n`-ADC whenever the source
ambient rank is at least `n+1`.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Local ADC-ness is invariant under an integral lattice isometry. -/
theorem IsNADC.of_latticeIsometry
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (h : IsNADC.{u, u, u} q L n) (f : Isometry q r L M) :
    IsNADC.{u, u, u} r M n := by
  refine ⟨(isIntegral_iff_of_latticeIsometry f).mp h.isIntegral, ?_⟩
  intro U _ _ s N hRank hIntegral hAmbient
  have hQR : q.Represents r :=
    ⟨f.symm.toQuadraticSpaceIsometry.toRepresentation⟩
  have hSource := h.represents s N hRank hIntegral (hQR.trans hAmbient)
  have hRL : Represents r q M L := ⟨f.toRepresentation⟩
  exact hRL.trans hSource

/-- Symmetric form of ADC invariance under an integral lattice isometry. -/
theorem isNADC_iff_of_latticeIsometry
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (f : Isometry q r L M) :
    IsNADC.{u, u, u} q L n ↔ IsNADC.{u, u, u} r M n := by
  constructor
  · exact fun h ↦ h.of_latticeIsometry f
  · exact fun h ↦ h.of_latticeIsometry f.symm

/-- Local ADC-ness descends by one rank when an orthogonal line remains in
the source ambient space. -/
theorem IsNADC.of_succ (h : IsNADC.{u, u, u} q L (n + 1))
    (hrank : n + 1 ≤ finrank K V) : IsNADC.{u, u, u} q L n := by
  refine ⟨h.isIntegral, ?_⟩
  intro W _ _ r M hMRank hM hambient
  letI : Module.Finite K V := L.moduleFinite
  rcases hambient with ⟨f⟩
  let image : QuadraticSublattice q :=
    { carrier := LinearMap.range f.toLinearMap
      nondegenerate := f.range_nondegenerate
      lattice := map f.rangeEquiv M }
  let complement : QuadraticSublattice q :=
    { carrier := image.orthogonalCarrier
      nondegenerate := image.orthogonalCarrier_nondegenerate
      lattice := basisLattice
        (Module.Free.chooseBasis K image.orthogonalCarrier) }
  have hImageRank : finrank K image.carrier = n := by
    calc
      finrank K image.carrier = finrank K W := f.rangeEquiv.finrank_eq.symm
      _ = n := hMRank
  have hComplementPos : 0 < finrank K complement.carrier := by
    have hsum := Submodule.finrank_add_eq_of_isCompl
      image.carrier_isCompl_orthogonalCarrier
    change finrank K image.carrier + finrank K complement.carrier = finrank K V at hsum
    rw [hImageRank] at hsum
    omega
  obtain ⟨x, hx⟩ := complement.space.exists_isAnisotropic_of_finrank_pos hComplementPos
  let xValue : Kˣ := Units.mk0 (complement.space.quadratic x) hx
  let line := QuadraticSpace.scaledLine xValue
  let lineMap : K →ₗ[K] complement.carrier :=
    { toFun := fun c ↦ c • x
      map_add' := by
        intro c d
        exact add_smul c d x
      map_smul' := by
        intro c d
        exact mul_smul c d x }
  have lineMapInjective : Function.Injective lineMap := by
    intro c d hcd
    have hzero : (c - d) • x = 0 := by
      rw [sub_smul]
      have hcd' : c • x = d • x := hcd
      rw [hcd', sub_self]
    have hscalar : c - d = 0 :=
      (smul_eq_zero.mp hzero).resolve_right hx.ne_zero
    exact sub_eq_zero.mp hscalar
  let lineRepresentation : QuadraticSpace.Representation line complement.space :=
    { toLinearMap := lineMap
      injective := lineMapInjective
      map_bilin := by
        intro c d
        change complement.space.bilin (c • x) (d • x) =
          (xValue : K) * c * d
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        change d * (c * complement.space.quadratic x) =
          complement.space.quadratic x * c * d
        ring }
  obtain ⟨scale, hLineIntegral⟩ :=
    exists_integral_rescale line (BONG.unaryModelLattice (K := K))
  let lineLattice := rescale scale (BONG.unaryModelLattice (K := K))
  let targetForm := image.space.orthogonalSum line
  let targetLattice : Lattice K (image.carrier × K) :=
    product image.lattice lineLattice
  let rangeIsometry : Isometry r image.space M image.lattice := by
    exact Isometry.toMap r f.rangeIsometry M
  have hImageIntegral : IsIntegral image.space image.lattice :=
    (isIntegral_iff_of_latticeIsometry rangeIsometry).mp hM
  have hTargetIntegral : IsIntegral targetForm targetLattice :=
    orthogonalProduct_isIntegral hImageIntegral hLineIntegral
  let sumIsometry : QuadraticSpace.Isometry
      (image.space.orthogonalSum complement.space) q :=
    { toLinearEquiv := image.carrier.prodEquivOfIsCompl
        image.orthogonalCarrier image.carrier_isCompl_orthogonalCarrier
      map_bilin := by
        intro y z
        change q.bilin ((y.1 : V) + (y.2 : V))
            ((z.1 : V) + (z.2 : V)) =
          q.bilin (y.1 : V) (z.1 : V) +
            q.bilin (y.2 : V) (z.2 : V)
        simp only [map_add, LinearMap.add_apply]
        have hyz : q.bilin (y.1 : V) (z.2 : V) = 0 :=
          z.2.property (y.1 : V) y.1.property
        have hzy : q.bilin (y.2 : V) (z.1 : V) = 0 := by
          rw [q.isSymm.eq]
          exact y.2.property (z.1 : V) z.1.property
        rw [hyz, hzy]
        simp }
  let targetToSource : QuadraticSpace.Representation targetForm q :=
    sumIsometry.toRepresentation.trans
      ((QuadraticSpace.Representation.refl image.space).orthogonalSum
        lineRepresentation)
  have hTargetRank : finrank K (image.carrier × K) = n + 1 := by
    rw [Module.finrank_prod, hImageRank]
    simp
  have hBig := h.represents targetForm targetLattice hTargetRank
    hTargetIntegral ⟨targetToSource⟩
  let leftRepresentation : Representation image.space targetForm
      image.lattice targetLattice :=
    { toLinearMap := LinearMap.inl K image.carrier K
      injective := by
        intro y z hyz
        exact congrArg Prod.fst hyz
      map_bilin := by
        intro y z
        change image.space.bilin y z + line.bilin 0 0 = image.space.bilin y z
        simp
      map_mem := by
        intro y hy
        exact ⟨hy, lineLattice.zero_mem⟩ }
  exact hBig.trans ⟨leftRepresentation.trans rangeIsometry.toRepresentation⟩

end Lattice

end Bong
