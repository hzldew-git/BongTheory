/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalCodimensionOneCancellationProof
import Bong.Lattice.Determinant
import Bong.Lattice.Omeara9328Conditions
import Bong.QuadraticSpace.OrthogonalSumDiagonal

/-!
# Codimension-one cancellation from determinant classes

This file packages the quadratic-space argument used repeatedly in the
sufficiency proof of O'Meara 93:28.  If an equal-rank space embeds in a
one-line orthogonal extension of another and the two determinants have the
same ordinary square class, diagonal codimension-one cancellation produces
an actual isometry.  A second theorem obtains the square-class hypothesis
from the refined determinant classes of full lattices.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

universe u v w

/-- Reindexing the source coordinates of a diagonal representation along an
equivalence preserves representation. -/
theorem DiagonalRepresents.reindexSource
    {K : Type u} [Field K] {m n r : Nat}
    {source : Fin m → K} {target : Fin r → K}
    (e : Fin n ≃ Fin m) (h : DiagonalRepresents source target) :
    DiagonalRepresents (fun i ↦ source (e i)) target := by
  rcases h with ⟨f, hf, hquadratic⟩
  let E := LinearEquiv.piCongrLeft K (fun _ : Fin m ↦ K) e
  refine ⟨f.comp E.toLinearMap, hf.comp E.injective, ?_⟩
  intro x
  rw [LinearMap.comp_apply, hquadratic]
  have hE (i : Fin n) : E x (e i) = x i := by
    change (Equiv.piCongrLeft (fun _ : Fin m ↦ K) e) x (e i) = x i
    exact Equiv.piCongrLeft_apply_apply (fun _ : Fin m ↦ K) e x i
  unfold diagonalQuadratic
  calc
    (∑ i, source i * (E x i) ^ 2) =
        ∑ i, source (e i) * (E x (e i)) ^ 2 := by
      exact (Equiv.sum_comp e
        (fun j ↦ source j * (E x j) ^ 2)).symm
    _ = ∑ i, source (e i) * x i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hE]

/-- Equality of ordinary square classes makes the product of two
representatives a square. -/
theorem isSquare_mul_of_squareClass_eq
    {K : Type u} [Field K] (x y : Kˣ)
    (h : squareClass K x = squareClass K y) : IsSquare (x * y) := by
  change QuotientGroup.mk' (Subgroup.square Kˣ) x =
    QuotientGroup.mk' (Subgroup.square Kˣ) y at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  rcases h with ⟨z, hz, hxz⟩
  change IsSquare z at hz
  have hxSquare : IsSquare (x ^ 2) := ⟨x, pow_two x⟩
  have hproduct : IsSquare (x ^ 2 * z) := hxSquare.mul hz
  have heq : x * y = x ^ 2 * z := by
    rw [← hxz]
    simpa only [pow_two] using (mul_assoc x x z).symm
  rw [heq]
  exact hproduct

namespace QuadraticSpace

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  [FiniteDimensional K V] [FiniteDimensional K W]

/-- An equal-rank embedding into a one-line extension, together with equality
of determinant square classes, is an isometry of the original spaces. -/
theorem isIsometric_of_embedsInto_orthogonalSum_scaledLine_of_determinant
    (q : QuadraticSpace K V) (r : QuadraticSpace K W) (a : Kˣ)
    (hfinrank : finrank K V = finrank K W)
    (hembed : EmbedsInto q (r.orthogonalSum (scaledLine a)))
    (hdet : IsSquare
      (diagonalUnitDeterminant q.diagonalUnits *
        diagonalUnitDeterminant r.diagonalUnits)) :
    q.IsIsometric r := by
  let e : Fin (finrank K W) ≃ Fin (finrank K V) :=
    finCongr hfinrank.symm
  let candidate : Fin (finrank K W) → Kˣ :=
    fun i ↦ q.diagonalUnits (e i)
  have hdiagonalOriginal : DiagonalRepresents
      (diagonalUnitCoefficients q.diagonalUnits)
      (diagonalUnitCoefficients (Fin.snoc r.diagonalUnits a)) :=
    (orthogonalSum_scaledLine_represents_iff_diagonalRepresents r q a).1
      hembed
  have hdiagonal : DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients (Fin.snoc r.diagonalUnits a)) := by
    change DiagonalRepresents
      (fun i ↦ ((q.diagonalUnits (e i) : K)))
      (diagonalUnitCoefficients (Fin.snoc r.diagonalUnits a))
    exact hdiagonalOriginal.reindexSource e
  have hprefix :
      diagonalUnitPrefix (Fin.snoc r.diagonalUnits a) = r.diagonalUnits := by
    funext i
    simp [diagonalUnitPrefix]
  have hcandidateDeterminant :
      diagonalUnitDeterminant candidate =
        diagonalUnitDeterminant q.diagonalUnits := by
    unfold diagonalUnitDeterminant candidate
    exact e.prod_comp q.diagonalUnits
  have hdetCandidate : IsSquare
      (diagonalUnitDeterminant candidate *
        diagonalUnitDeterminant r.diagonalUnits) := by
    rw [hcandidateDeterminant]
    exact hdet
  let laws : DiagonalCodimensionOneCancellationLaws K := inferInstance
  have hcancelled : DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients r.diagonalUnits) :=
    laws.cancel r.diagonalUnits candidate (Fin.snoc r.diagonalUnits a)
      hprefix hdiagonal hdetCandidate
  have hcancelledOriginal : DiagonalRepresents
      (diagonalUnitCoefficients q.diagonalUnits)
      (diagonalUnitCoefficients r.diagonalUnits) := by
    change DiagonalRepresents (fun i ↦ ((q.diagonalUnits i : K)))
      (diagonalUnitCoefficients r.diagonalUnits)
    simpa only [candidate, diagonalUnitCoefficients,
      e, Equiv.apply_symm_apply] using
      hcancelled.reindexSource e.symm
  rcases (represents_iff_diagonalRepresents q r).2 hcancelledOriginal with ⟨f⟩
  exact ⟨f.toIsometryOfFinrankEq hfinrank⟩

end QuadraticSpace

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

/-- The ordinary square class of the chosen diagonal product is the image of
the refined determinant class of any full lattice in the same space. -/
theorem squareClass_diagonalUnitDeterminant_eq_determinantClass_toSquareClass
    [FiniteDimensional K V]
    (q : QuadraticSpace K V) (L : Lattice K V) :
    squareClass K (diagonalUnitDeterminant q.diagonalUnits) =
      unitSquareClassToSquareClass K (determinantClass q L) := by
  let latticeBONG := BONG.ofLattice q L
  calc
    squareClass K (diagonalUnitDeterminant q.diagonalUnits) =
        squareClass K q.diagonalizingBONG.valueProduct := by
      apply congrArg (squareClass K)
      apply Units.ext
      simp [diagonalUnitDeterminant, QuadraticSpace.diagonalUnits]
    _ = squareClass K latticeBONG.valueProduct :=
      (BONG.valueProduct_squareClass_eq
        latticeBONG q.diagonalizingBONG).symm
    _ = unitSquareClassToSquareClass K (determinantClass q L) :=
      (determinantClass_toSquareClass_eq_valueProduct latticeBONG).symm

namespace QuadraticSublattice

/-- The lattice-level form of codimension-one determinant cancellation.
This is the bridge used by conditions 93:28(ii) and 93:28(iii). -/
theorem space_isIsometric_of_embedsIntoOrthogonalSum_of_determinantClass_eq
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    (C : QuadraticSublattice q) (D : QuadraticSublattice r) (a : Kˣ)
    (hfinrank : finrank K C.carrier = finrank K D.carrier)
    (hembed : C.EmbedsIntoOrthogonalSum D
      (QuadraticSpace.scaledLine a))
    (hdet : determinantClass C.space C.lattice =
      determinantClass D.space D.lattice) :
    C.space.IsIsometric D.space := by
  letI : Module.Finite K C.carrier := C.lattice.moduleFinite
  letI : Module.Finite K D.carrier := D.lattice.moduleFinite
  have hclasses :
      squareClass K
          (diagonalUnitDeterminant C.space.diagonalUnits) =
        squareClass K
          (diagonalUnitDeterminant D.space.diagonalUnits) := by
    calc
      squareClass K
          (diagonalUnitDeterminant C.space.diagonalUnits) =
          unitSquareClassToSquareClass K
            (determinantClass C.space C.lattice) :=
        squareClass_diagonalUnitDeterminant_eq_determinantClass_toSquareClass
          C.space C.lattice
      _ = unitSquareClassToSquareClass K
          (determinantClass D.space D.lattice) :=
        congrArg (unitSquareClassToSquareClass K) hdet
      _ = squareClass K
          (diagonalUnitDeterminant D.space.diagonalUnits) :=
        (squareClass_diagonalUnitDeterminant_eq_determinantClass_toSquareClass
          D.space D.lattice).symm
  exact QuadraticSpace.isIsometric_of_embedsInto_orthogonalSum_scaledLine_of_determinant
    C.space D.space a hfinrank hembed
      (isSquare_mul_of_squareClass_eq _ _ hclasses)

end QuadraticSublattice

end Lattice

end Bong
