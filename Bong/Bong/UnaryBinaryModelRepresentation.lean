/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryAdmissibility
import Bong.Bong.Representation
import Bong.Bong.UnaryBinaryModel
import Bong.Lattice.OrthogonalProductIsometry

/-!
# Integral representations between unary--binary models

The normal form used in Beli (2019), Lemmas 9.5 and 9.8 is an orthogonal
product of a unary line and a binary lattice.  This file supplies the two
geometric operations needed to compare such normal forms without invoking
the main representation theorem: valuation-unit square scaling on the
unary line, and componentwise reassembly with a binary representation.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Multiplication by a valuation unit identifies unary model lattices when
their quadratic coefficients differ by the corresponding unit square. -/
noncomputable def unaryModelIsometryOfValuationUnitSquare
    (target source scale : Kˣ)
    (hscale : IsValuationUnit K (scale : K))
    (hsource : source = target * scale ^ 2) :
    Lattice.Isometry
      (QuadraticSpace.rescaleUnit source (QuadraticSpace.line K))
      (QuadraticSpace.rescaleUnit target (QuadraticSpace.line K))
      (unaryModelLattice : Lattice K K)
      (unaryModelLattice : Lattice K K) := by
  let f : K →ₗ[K] K := LinearMap.lsmul K K (scale : K)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      change (scale : K) * x = (scale : K) * y at hxy
      exact mul_left_cancel₀ (Units.ne_zero scale) hxy
    · intro y
      refine ⟨((scale⁻¹ : Kˣ) : K) * y, ?_⟩
      change (scale : K) * (((scale⁻¹ : Kˣ) : K) * y) = y
      simp
  let e : K ≃ₗ[K] K := LinearEquiv.ofBijective f hf
  have he (x : K) : e x = (scale : K) * x := rfl
  refine
    { toLinearEquiv := e
      map_bilin := ?_
      map_mem := ?_ }
  · intro x y
    rw [he, he]
    simp only [QuadraticSpace.rescaleUnit_bilin_apply,
      QuadraticSpace.line_bilin_apply]
    have hsourceCoe := congrArg (fun z : Kˣ ↦ (z : K)) hsource
    rw [hsourceCoe]
    push_cast
    ring
  · intro x
    rw [he, mem_unaryModelLattice_iff, mem_unaryModelLattice_iff]
    have hmem := valuationUnit_mem_integerRing_and_inv scale hscale
    constructor
    · intro hx
      exact (IntegerRing K).mul_mem (scale : K) x hmem.1 hx
    · intro hsx
      have hx := (IntegerRing K).mul_mem
        (((scale⁻¹ : Kˣ) : K)) ((scale : K) * x) hmem.2 hsx
      simpa [mul_assoc] using hx

/-- A valuation-unit square relation between unary coefficients gives an
integral representation in the direction dictated by that relation. -/
theorem unaryModel_represents_of_valuationUnitSquare
    (target source scale : Kˣ)
    (hscale : IsValuationUnit K (scale : K))
    (hsource : source = target * scale ^ 2) :
    Lattice.Represents
      (QuadraticSpace.rescaleUnit target (QuadraticSpace.line K))
      (QuadraticSpace.rescaleUnit source (QuadraticSpace.line K))
      (unaryModelLattice : Lattice K K)
      (unaryModelLattice : Lattice K K) :=
  ⟨(unaryModelIsometryOfValuationUnitSquare target source scale
    hscale hsource).toRepresentation⟩

/-- Reassemble a unary coefficient comparison and a binary representation
into a representation of the full unary--binary normal forms. -/
theorem unaryBinaryModel_represents_of_valuationUnitSquare
    (targetHead sourceHead scale : Kˣ)
    (hscale : IsValuationUnit K (scale : K))
    (hsourceHead : sourceHead = targetHead * scale ^ 2)
    (targetFirst targetSecond sourceFirst sourceSecond : Kˣ)
    (targetAdmissible :
      IsBinaryParameterAdmissible (targetSecond / targetFirst))
    (sourceAdmissible :
      IsBinaryParameterAdmissible (sourceSecond / sourceFirst))
    (hbinary : Lattice.Represents
      (binaryDiagonalModelSpace targetFirst targetSecond targetAdmissible)
      (binaryDiagonalModelSpace sourceFirst sourceSecond sourceAdmissible)
      (binaryDiagonalModelLattice : Lattice K (Fin 2 → K))
      (binaryDiagonalModelLattice : Lattice K (Fin 2 → K))) :
    Lattice.Represents
      (unaryBinaryModelSpace targetHead targetFirst targetSecond
        targetAdmissible)
      (unaryBinaryModelSpace sourceHead sourceFirst sourceSecond
        sourceAdmissible)
      (unaryBinaryModelLattice : Lattice K (K × (Fin 2 → K)))
      (unaryBinaryModelLattice : Lattice K (K × (Fin 2 → K))) := by
  have hunary := unaryModel_represents_of_valuationUnitSquare
    targetHead sourceHead scale hscale hsourceHead
  simpa only [unaryBinaryModelSpace, unaryBinaryModelLattice] using
    hunary.orthogonalProductBasic hbinary

end BONG

end Bong
