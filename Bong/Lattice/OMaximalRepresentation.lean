/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.BeliUniversalLemma44
import Bong.Lattice.OMaximalUniqueness
import Bong.QuadraticSpace.RepresentationRange

/-!
# Representing maximal lattices from represented quadratic spaces

This file records the lattice-level consequence of O'Meara 82:18 and 91:2
used in He--Hu, Theorem 1.2.  If the ambient space of an `O`-maximal lattice
`N` embeds in the ambient space of an `O`-maximal lattice `M`, then `M`
integrally represents `N`.

The proof does not assume that the given space embedding is integral.  It
first transports `N` to the nondegenerate image, chooses a sufficiently
deep integral lattice on the orthogonal complement, and maps their
orthogonal product into the target space.  O'Meara 82:18 enlarges this
integral product to a maximal lattice, and 91:2 identifies that maximal
lattice with the originally specified target lattice.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {W : Type u} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {N : Lattice K W}

/-- A represented integral lattice can be placed inside some integral full
lattice of the target ambient space.  This is the orthogonal-complement
construction implicit in the use of O'Meara 82:18. -/
theorem exists_integral_full_lattice_representing
    (L₀ : Lattice K V) (hN : IsIntegral r N) (hspace : q.Represents r) :
    ∃ A : Lattice K V, IsIntegral q A ∧ Represents q r A N := by
  classical
  letI : Module.Finite K V := L₀.moduleFinite
  rcases hspace with ⟨f⟩
  let image : QuadraticSublattice q :=
    { carrier := LinearMap.range f.toLinearMap
      nondegenerate := f.range_nondegenerate
      lattice := map f.rangeEquiv N }
  let complement : QuadraticSublattice q :=
    { carrier := image.orthogonalCarrier
      nondegenerate := image.orthogonalCarrier_nondegenerate
      lattice := basisLattice
        (Module.Free.chooseBasis K image.orthogonalCarrier) }
  obtain ⟨c, hc⟩ := exists_integral_rescale complement.space complement.lattice
  let complementLattice : Lattice K complement.carrier :=
    rescale c complement.lattice
  let sumIsometry : QuadraticSpace.Isometry
      (image.space.orthogonalSum complement.space) q :=
    { toLinearEquiv := image.carrier.prodEquivOfIsCompl
        image.orthogonalCarrier image.carrier_isCompl_orthogonalCarrier
      map_bilin := by
        intro x y
        change q.bilin ((x.1 : V) + (x.2 : V))
            ((y.1 : V) + (y.2 : V)) =
          q.bilin (x.1 : V) (y.1 : V) +
            q.bilin (x.2 : V) (y.2 : V)
        simp only [map_add, LinearMap.add_apply]
        have hxy : q.bilin (x.1 : V) (y.2 : V) = 0 :=
          y.2.property (x.1 : V) x.1.property
        have hyx : q.bilin (x.2 : V) (y.1 : V) = 0 := by
          rw [q.isSymm.eq]
          exact x.2.property (y.1 : V) y.1.property
        rw [hxy, hyx]
        simp }
  let productLattice : Lattice K (image.carrier × complement.carrier) :=
    product image.lattice complementLattice
  let A : Lattice K V := map sumIsometry.toLinearEquiv productLattice
  let rangeIsometry : Isometry r image.space N image.lattice := by
    exact Isometry.toMap r f.rangeIsometry N
  let leftRepresentation : Representation image.space
      (image.space.orthogonalSum complement.space) image.lattice
      productLattice :=
    { toLinearMap := LinearMap.inl K image.carrier complement.carrier
      injective := by
        intro x y hxy
        exact congrArg Prod.fst hxy
      map_bilin := by
        intro x y
        simp [QuadraticSpace.orthogonalSum_bilin_apply]
      map_mem := by
        intro x hx
        exact ⟨hx, complementLattice.zero_mem⟩ }
  let mappedIsometry : Isometry
      (image.space.orthogonalSum complement.space) q productLattice A := by
    exact Isometry.toMap _ sumIsometry productLattice
  have hImageIntegral : IsIntegral image.space image.lattice :=
    (isIntegral_iff_of_latticeIsometry rangeIsometry).mp hN
  have hProductIntegral : IsIntegral
      (image.space.orthogonalSum complement.space) productLattice :=
    orthogonalProduct_isIntegral hImageIntegral hc
  have hAIntegral : IsIntegral q A :=
    (isIntegral_iff_of_latticeIsometry mappedIsometry).mp hProductIntegral
  have hrep : Represents q r A N := by
    exact ⟨mappedIsometry.toRepresentation.trans
      (leftRepresentation.trans rangeIsometry.toRepresentation)⟩
  exact ⟨A, hAIntegral, hrep⟩

/-- O'Meara 82:18 and 91:2 in the exact representation form used by
He--Hu: maximal lattices represent one another whenever their ambient
quadratic spaces are in the corresponding representation relation. -/
theorem IsOMaximal.represents_of_ambient
    (hL : IsOMaximal q L) (hN : IsOMaximal r N)
    (hspace : q.Represents r) : Represents q r L N := by
  obtain ⟨A, hAIntegral, hAN⟩ :=
    exists_integral_full_lattice_representing L hN.isIntegral hspace
  obtain ⟨P, hAP, hPmaximal⟩ :=
    exists_oMaximal_superlattice (q := q) (L := A) hAIntegral
  have hLP : IsIsometric q q L P :=
    oMaximal_isIsometric_of_isometric hL hPmaximal
      ⟨QuadraticSpace.Isometry.refl q⟩
  rcases hLP with ⟨g⟩
  have hPL : Represents q q L P := ⟨g.symm.toRepresentation⟩
  exact hPL.trans ((represents_of_le q hAP).trans hAN)

/-- For maximal source and target lattices, integral representability is
equivalent to representability of their ambient quadratic spaces. -/
theorem IsOMaximal.represents_iff_ambient
    (hL : IsOMaximal q L) (hN : IsOMaximal r N) :
    Represents q r L N ↔ q.Represents r := by
  constructor
  · exact Represents.ambient
  · exact hL.represents_of_ambient hN

end Lattice

end Bong
