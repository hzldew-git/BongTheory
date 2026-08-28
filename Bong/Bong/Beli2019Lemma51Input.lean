/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019IndexPGenerator
import Bong.Bong.Beli2019Lemma51Block
import Bong.Lattice.AdjoinQuadraticSublattice
import Bong.Lattice.AdjoinRescale

/-!
# Beli (2019), Lemma 5.1: an adapted generator for the larger lattice

The Smith generator of an index-uniformizer inclusion is replaced by the
congruent representative selected by the recursive O'Meara block
construction.  Dividing either representative by the uniformizer gives the
same enlarged lattice.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- The adapted representative, viewed in the carrier of its selected block. -/
noncomputable def Beli2019Lemma51BlockData.carrierRepresentative
    {q : QuadraticSpace K V} {N : Lattice K V} {x : V}
    (D : Beli2019Lemma51BlockData q N x) : D.component.carrier := by
  refine ⟨D.representative, ?_⟩
  cases D with
  | unary z _ _ hz _ =>
      exact Submodule.mem_span_singleton_self z
  | binary z y _ _ _ hzy hleft hright _ _ =>
      change z ∈ BONG.binaryPairSpan (K := K) z y
      exact Submodule.subset_span ⟨0, by simp [BONG.binaryPairFamily]⟩

@[simp]
theorem Beli2019Lemma51BlockData.coe_carrierRepresentative
    {q : QuadraticSpace K V} {N : Lattice K V} {x : V}
    (D : Beli2019Lemma51BlockData q N x) :
    (D.carrierRepresentative : V) = D.representative :=
  rfl

/-- The adapted representative is an integral vector of the selected block,
not merely a vector in its underlying field subspace. -/
theorem Beli2019Lemma51BlockData.carrierRepresentative_mem
    {q : QuadraticSpace K V} {N : Lattice K V} {x : V}
    (D : Beli2019Lemma51BlockData q N x) :
    D.carrierRepresentative ∈ D.component.lattice := by
  cases D with
  | unary z hz hcongruent hanisotropic hpairing =>
      change (⟨z, Submodule.mem_span_singleton_self z⟩ : K ∙ z) ∈
        basisLattice (unarySpanBasis (K := K) z hanisotropic.ne_zero)
      change (⟨z, Submodule.mem_span_singleton_self z⟩ : K ∙ z) ∈
        Submodule.span (IntegerRing K)
          (Set.range (unarySpanBasis (K := K) z hanisotropic.ne_zero))
      apply Submodule.subset_span
      refine ⟨0, Subtype.ext ?_⟩
      exact coe_unarySpanBasis (K := K) z hanisotropic.ne_zero 0
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      let hli := binaryPair_linearIndependent_of_left_strict hzy hleft hright
      change (⟨z, Submodule.subset_span
          ⟨0, by simp [BONG.binaryPairFamily]⟩⟩ :
            BONG.binaryPairSpan (K := K) z y) ∈
        basisLattice (BONG.binaryPairBasis (K := K) z y hli)
      change (⟨z, Submodule.subset_span
          ⟨0, by simp [BONG.binaryPairFamily]⟩⟩ :
            BONG.binaryPairSpan (K := K) z y) ∈
        Submodule.span (IntegerRing K)
          (Set.range (BONG.binaryPairBasis (K := K) z y hli))
      apply Submodule.subset_span
      refine ⟨0, Subtype.ext ?_⟩
      rw [BONG.coe_binaryPairBasis, BONG.binaryPairFamily_zero]

private theorem uniformizerInv_smul_sub_mem_of_sub_mem_rescale
    {L : Lattice K V} {x z : V}
    (h : x - z ∈ rescale (uniformizerUnit K) L) :
    (((uniformizerUnit K)⁻¹ : Kˣ) : K) • x -
        (((uniformizerUnit K)⁻¹ : Kˣ) : K) • z ∈ L := by
  rw [mem_rescale_iff] at h
  obtain ⟨w, hw, hwEq⟩ := h
  have hscaled := congrArg
    (fun t : V ↦ (((uniformizerUnit K)⁻¹ : Kˣ) : K) • t) hwEq
  have hsub : (((uniformizerUnit K)⁻¹ : Kˣ) : K) • (x - z) = w := by
    rw [← hscaled]
    simp [smul_smul, uniformizer_ne_zero K]
  rw [← smul_sub, hsub]
  exact hw

/-- The algebraic and geometric inputs in the first paragraph of Lemma 5.1,
now obtained without a law instance. -/
structure Beli2019Lemma51InputData
    (q : QuadraticSpace K V) (M N : Lattice K V) : Type (max u v) where
  generator : Beli2019IndexPGeneratorData q M N
  block : Beli2019Lemma51BlockData q N generator.vector
  enlarged_eq :
    adjoinVector N
        ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • block.representative) = M

/-- Every literal index-`\mathfrak p` inclusion has the adapted input data of
Beli (2019), Lemma 5.1. -/
noncomputable def beli2019Lemma51InputData
    (q : QuadraticSpace K V) (M N : Lattice K V)
    (inclusion : Beli2019IndexPInclusion q M N) :
    Beli2019Lemma51InputData q M N := by
  let G := beli2019IndexPGeneratorData q M N inclusion
  let D := beli2019Lemma51BlockData q N G.vector G.mem G.primitive
  have hsub :
      (((uniformizerUnit K)⁻¹ : Kˣ) : K) • G.vector -
          (((uniformizerUnit K)⁻¹ : Kˣ) : K) • D.representative ∈ N :=
    uniformizerInv_smul_sub_mem_of_sub_mem_rescale
      D.sub_representative_mem_rescale
  have hadjoin := adjoinVector_eq_of_sub_mem hsub
  refine ⟨G, D, ?_⟩
  exact hadjoin.symm.trans G.enlarged_eq

namespace Beli2019Lemma51InputData

variable {q : QuadraticSpace K V} {M N : Lattice K V}

/-- The inverse-uniformizer representative inside the selected block. -/
noncomputable def enlargedVector (D : Beli2019Lemma51InputData q M N) :
    D.block.component.carrier :=
  (((uniformizerUnit K)⁻¹ : Kˣ) : K) • D.block.carrierRepresentative

/-- The enlarged unary or binary block `J'` in Lemma 5.1. -/
noncomputable def enlargedComponent (D : Beli2019Lemma51InputData q M N) :
    QuadraticSublattice q :=
  D.block.component.adjoinVector D.enlargedVector

/-- The original selected component is contained in the enlarged component. -/
theorem component_lattice_le_enlargedComponent
    (D : Beli2019Lemma51InputData q M N) :
    D.block.component.lattice ≤ D.enlargedComponent.lattice :=
  le_adjoinVector _ _

/-- Multiplication by the uniformizer carries the enlarged component back
into the original selected component. -/
theorem rescale_uniformizer_enlargedComponent_le
    (D : Beli2019Lemma51InputData q M N) :
    rescale (uniformizerUnit K) D.enlargedComponent.lattice ≤
      D.block.component.lattice := by
  exact rescale_uniformizer_adjoin_uniformizerInv_smul_le
    D.block.component.lattice D.block.carrierRepresentative_mem

/-- The smaller lattice splits as the selected block and its orthogonal
complement. -/
noncomputable def smallSplitting (D : Beli2019Lemma51InputData q M N) :
    OrthogonalDecomposition q N 2 :=
  D.block.splitting

/-- The larger lattice has the same orthogonal complement; only the selected
block is enlarged by the inverse-uniformizer representative. -/
noncomputable def largeSplitting (D : Beli2019Lemma51InputData q M N) :
    OrthogonalDecomposition q M 2 := by
  let E := D.block.splitting.adjoinFirst D.enlargedVector
  have hLattice : Lattice.adjoinVector N (D.enlargedVector : V) = M := by
    change Lattice.adjoinVector N
        ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • D.block.representative) = M
    exact D.enlarged_eq
  exact {
    component := E.component
    orthogonal := E.orthogonal
    sum_eq := E.sum_eq.trans (congrArg Lattice.toSubmodule hLattice) }

@[simp]
theorem smallSplitting_component_zero
    (D : Beli2019Lemma51InputData q M N) :
    D.smallSplitting.component 0 = D.block.component :=
  rfl

@[simp]
theorem largeSplitting_component_zero
    (D : Beli2019Lemma51InputData q M N) :
    D.largeSplitting.component 0 = D.enlargedComponent :=
  rfl

@[simp]
theorem largeSplitting_component_one
    (D : Beli2019Lemma51InputData q M N) :
    D.largeSplitting.component 1 = D.smallSplitting.component 1 := by
  simp [largeSplitting, smallSplitting, OrthogonalDecomposition.adjoinFirst]

end Beli2019Lemma51InputData

end Lattice

end Bong
