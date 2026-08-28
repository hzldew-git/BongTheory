/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma41AdaptedJordan
import Bong.Bong.GoodMap
import Bong.Bong.Beli2019Lemma710ProjectionProduct
import Bong.Lattice.OrthogonalDecompositionProduct
import Bong.Lattice.OrthogonalProductDecomposition
import Bong.Lattice.DeterminantProjection
import Bong.Lattice.ModularVolume
import Bong.Lattice.JordanPrepend
import Bong.Lattice.NormIdealOrthogonalProduct
import Bong.Bong.BeliLemma41PropertyAProof

/-!
# The binary branch of Beli (2003), Lemma 4.1(ii)

This file identifies the recursive projection after the first BONG vector
when the first adapted modular block has rank two.  Removing the prescribed
vector from that block leaves a rank-one projected lattice, orthogonally
summed with the unchanged complement of the block.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}

namespace Lattice.Beli2019Lemma51BlockData

/-- The representative, regarded as a vector of the selected component. -/
def representativeCarrier (D : Beli2019Lemma51BlockData q L x) :
    D.component.carrier := by
  cases D with
  | unary z hz hcongruent hanisotropic hpair =>
      refine ⟨z, ?_⟩
      change z ∈ K ∙ z
      exact Submodule.mem_span_singleton_self z
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      refine ⟨z, ?_⟩
      change z ∈ Submodule.span K (Set.range (BONG.binaryPairFamily z y))
      apply Submodule.subset_span
      exact ⟨0, BONG.binaryPairFamily_zero z y⟩

@[simp]
theorem coe_representativeCarrier
    (D : Beli2019Lemma51BlockData q L x) :
    (D.representativeCarrier : V) = D.representative := by
  cases D <;> rfl

/-- The representative is one of the integral basis vectors of the selected
component. -/
theorem representativeCarrier_mem
    (D : Beli2019Lemma51BlockData q L x) :
    D.representativeCarrier ∈ D.component.lattice := by
  cases D with
  | unary z hz hcongruent hanisotropic hpair =>
      let zC : K ∙ z := ⟨z, Submodule.mem_span_singleton_self z⟩
      change zC ∈ basisLattice
        (unarySpanBasis (K := K) z hanisotropic.ne_zero)
      change zC ∈ Submodule.span (IntegerRing K)
        (Set.range (unarySpanBasis (K := K) z hanisotropic.ne_zero))
      apply Submodule.subset_span
      refine ⟨0, ?_⟩
      apply Subtype.ext
      exact coe_unarySpanBasis z hanisotropic.ne_zero 0
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      let hli := binaryPair_linearIndependent_of_left_strict
        hzy hleft hright
      let zC : BONG.binaryPairSpan (K := K) z y := by
        refine ⟨z, ?_⟩
        apply Submodule.subset_span
        exact ⟨0, BONG.binaryPairFamily_zero z y⟩
      change zC ∈ basisLattice (BONG.binaryPairBasis (K := K) z y hli)
      change zC ∈ Submodule.span (IntegerRing K)
        (Set.range (BONG.binaryPairBasis (K := K) z y hli))
      apply Submodule.subset_span
      refine ⟨0, ?_⟩
      apply Subtype.ext
      rw [BONG.coe_binaryPairBasis, BONG.binaryPairFamily_zero]

/-- The binary branch has field rank two. -/
theorem component_rank_eq_two_of_isBinary
    (D : Beli2019Lemma51BlockData q L x) (hBinary : D.IsBinary) :
    finrank K D.component.carrier = 2 := by
  cases D with
  | unary z hz hcongruent hanisotropic hpair =>
      exact False.elim hBinary
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      change finrank K (BONG.binaryPairSpan (K := K) z y) = 2
      simpa using Module.finrank_eq_card_basis
        (BONG.binaryPairBasis (K := K) z y
          (binaryPair_linearIndependent_of_left_strict hzy hleft hright))

end Lattice.Beli2019Lemma51BlockData

namespace BONG

/-- The prescribed first BONG vector, regarded as a vector of the exact
adapted block that contains it. -/
noncomputable def firstJordanAdaptedHeadInBlock
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    (b.firstJordanAdaptedBlockData J hA ht).component.carrier := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  refine ⟨b.head, ?_⟩
  change b.head ∈ D.component.carrier
  have hrep : D.representative = b.head := by
    simpa only [D] using
      b.firstJordanAdaptedBlockData_representative J hA ht
  cases hD : D with
  | unary z hz hcongruent hanisotropic hpair =>
      have hzhead : z = b.head := by
        simpa [Lattice.Beli2019Lemma51BlockData.representative, hD] using hrep
      subst z
      change b.head ∈ K ∙ b.head
      exact Submodule.mem_span_singleton_self b.head
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      have hzhead : z = b.head := by
        simpa [Lattice.Beli2019Lemma51BlockData.representative, hD] using hrep
      subst z
      change b.head ∈
        Submodule.span K (Set.range (BONG.binaryPairFamily b.head y))
      apply Submodule.subset_span
      exact ⟨0, BONG.binaryPairFamily_zero b.head y⟩

@[simp]
theorem coe_firstJordanAdaptedHeadInBlock
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    (b.firstJordanAdaptedHeadInBlock J hA ht : V) = b.head :=
  rfl

/-- The prescribed vector belongs to the integral lattice of the adapted
component. -/
theorem firstJordanAdaptedHeadInBlock_mem
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    b.firstJordanAdaptedHeadInBlock J hA ht ∈
      (b.firstJordanAdaptedBlockData J hA ht).component.lattice := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  have hrep : D.representative = b.head := by
    simpa only [D] using
      b.firstJordanAdaptedBlockData_representative J hA ht
  have hcarrier :
      b.firstJordanAdaptedHeadInBlock J hA ht = D.representativeCarrier := by
    apply Subtype.ext
    simpa only [D, Lattice.Beli2019Lemma51BlockData.coe_representativeCarrier,
      b.coe_firstJordanAdaptedHeadInBlock J hA ht] using hrep.symm
  rw [hcarrier]
  exact D.representativeCarrier_mem

/-- The first vector stays anisotropic after restriction to the adapted
component. -/
theorem firstJordanAdaptedHeadInBlock_isAnisotropic
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    (b.firstJordanAdaptedBlockData J hA ht).component.space.IsAnisotropic
      (b.firstJordanAdaptedHeadInBlock J hA ht) := by
  change q.quadratic (b.firstJordanAdaptedHeadInBlock J hA ht : V) ≠ 0
  rw [b.coe_firstJordanAdaptedHeadInBlock J hA ht]
  exact b.head_isAnisotropic

/-- The prescribed first vector also generates the norm ideal of the exact
adapted component. -/
theorem firstJordanAdaptedHeadInBlock_isNormGenerator
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    Lattice.IsNormGenerator
      (b.firstJordanAdaptedBlockData J hA ht).component.space
      (b.firstJordanAdaptedBlockData J hA ht).component.lattice
      (b.firstJordanAdaptedHeadInBlock J hA ht) := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  let xD := b.firstJordanAdaptedHeadInBlock J hA ht
  constructor
  · exact b.firstJordanAdaptedHeadInBlock_mem J hA ht
  · apply le_antisymm
    · calc
        Lattice.normIdeal D.component.space D.component.lattice ≤
            Lattice.normIdeal q L :=
          D.component.normIdeal_le_of_ambientSubmodule_le D.component_contained
        _ = Lattice.principalIdeal (K := K) (q.quadratic b.head) :=
          b.head_isNormGenerator.normIdeal_eq
        _ = Lattice.principalIdeal (K := K)
            (D.component.space.quadratic xD) := by
          congr 1
    · rw [Lattice.principalIdeal, Submodule.span_le]
      rintro _ hvalue
      rw [Set.mem_singleton_iff] at hvalue
      subst hvalue
      exact Lattice.quadratic_mem_normIdeal_of_mem
        D.component.space D.component.lattice
        (b.firstJordanAdaptedHeadInBlock_mem J hA ht)

/-- A binary adapted block cannot collide in scale with the first component
of its complement: amalgamating a rank-two block with a positive-rank block
would contradict property A. -/
theorem not_firstJordanAdaptedScaleCollision_of_isBinary
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hBinary : (b.firstJordanAdaptedBlockData J hA ht).IsBinary) :
    ¬b.FirstJordanAdaptedScaleCollision J hA ht := by
  classical
  intro hcollision
  let D := b.firstJordanAdaptedBlockData J hA ht
  let W := b.firstJordanAdaptedWeakJordan J hA ht
  let i := Classical.choose hcollision
  have hscaleRaw := Classical.choose_spec hcollision
  have hi : i.val = 0 :=
    b.firstJordanAdaptedCollision_index_eq_zero J hA ht i hscaleRaw
  have hcountPos : 0 < b.firstJordanAdaptedComplementCount J hA ht := by
    omega
  let k : Fin (b.firstJordanAdaptedComplementCount J hA ht) :=
    ⟨0, hcountPos⟩
  have hk : k.val = 0 := rfl
  have hik : i = k := by
    apply Fin.ext
    exact hi
  have hkcast : k.castSucc =
      (0 : Fin (b.firstJordanAdaptedComplementCount J hA ht + 1)) := by
    apply Fin.ext
    exact hk
  have heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ) := by
    change ordUnit K D.scaleGenerator =
      ordUnit K
        ((b.firstJordanAdaptedComplementJordan J hA ht).scaleGenerator i)
      at hscaleRaw
    rw [hik] at hscaleRaw
    rw [hkcast]
    simpa only [W, D,
      firstJordanAdaptedWeakJordan_scaleGenerator_zero,
      firstJordanAdaptedWeakJordan_scaleGenerator_succ] using hscaleRaw
  let S := W.mergeAdjacentAt k heq
  have hstrict : StrictMono (fun a ↦ ordUnit K (S.scaleGenerator a)) :=
    Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
      W k heq
        (b.firstJordanAdaptedOnlyScaleCollisionAt J hA ht k hk heq)
  let G := S.toJordan hstrict
  have hG : G.HasPropertyA := J.hasPropertyA_of_hasPropertyA G hA
  have hmergedRank := hG.1 k
  change finrank K (S.component k).carrier = 1 ∨
      finrank K (S.component k).carrier = 2 at hmergedRank
  have hrankSum := W.mergeAdjacentAt_componentRank_self k heq
  change finrank K (S.component k).carrier =
      finrank K (W.component k.castSucc).carrier +
        finrank K (W.component k.succ).carrier at hrankSum
  have hleftRank : finrank K (W.component k.castSucc).carrier = 2 := by
    rw [hkcast]
    change finrank K D.component.carrier = 2
    exact D.component_rank_eq_two_of_isBinary hBinary
  have hrightPos : 0 < finrank K (W.component k.succ).carrier :=
    W.component_finrank_pos k.succ
  rcases hmergedRank with h | h <;> omega

/-- Removing the first vector from a binary adapted block leaves a
one-dimensional quadratic space. -/
theorem firstJordanAdaptedBinaryResidual_finrank_eq_one
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hBinary : (b.firstJordanAdaptedBlockData J hA ht).IsBinary) :
    finrank K
      ((b.firstJordanAdaptedBlockData J hA ht).component.space.vectorOrthogonal
        (b.firstJordanAdaptedHeadInBlock J hA ht)) = 1 := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  let xD := b.firstJordanAdaptedHeadInBlock J hA ht
  let hxD := b.firstJordanAdaptedHeadInBlock_isAnisotropic J hA ht
  have hdim :
      finrank K (D.component.space.vectorOrthogonal xD) + 1 =
        finrank K D.component.carrier :=
    D.component.space.finrank_vectorOrthogonal hxD
  have htwo : finrank K D.component.carrier = 2 :=
    D.component_rank_eq_two_of_isBinary hBinary
  change finrank K (D.component.space.vectorOrthogonal xD) = 1
  omega

/-- A chosen unary BONG of the residual line inside a binary adapted block. -/
noncomputable def firstJordanAdaptedBinaryResidualBONG
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hBinary : (b.firstJordanAdaptedBlockData J hA ht).IsBinary) :
    let D := b.firstJordanAdaptedBlockData J hA ht
    let xD := b.firstJordanAdaptedHeadInBlock J hA ht
    let hxD := b.firstJordanAdaptedHeadInBlock_isAnisotropic J hA ht
    BONG (D.component.space.vectorOrthogonal xD)
      (D.component.space.orthogonalSpace xD hxD)
      (D.component.lattice.projectedLattice D.component.space xD hxD) 1 := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  let xD := b.firstJordanAdaptedHeadInBlock J hA ht
  let hxD := b.firstJordanAdaptedHeadInBlock_isAnisotropic J hA ht
  let d := BONG.ofLattice
    (D.component.space.orthogonalSpace xD hxD)
    (D.component.lattice.projectedLattice D.component.space xD hxD)
  exact d.castLength
    (b.firstJordanAdaptedBinaryResidual_finrank_eq_one J hA ht hBinary)

/-- Exact order of the residual line: for a binary modular block of scale
`s` and first norm order `u`, projection leaves order `2s-u`. -/
theorem firstJordanAdaptedBinaryResidual_order
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hBinary : (b.firstJordanAdaptedBlockData J hA ht).IsBinary) :
    ordUnit K
        ((b.firstJordanAdaptedBinaryResidualBONG J hA ht hBinary).valueUnit 0) =
      2 * ordUnit K
          (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator -
        b.order 0 := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  let xD := b.firstJordanAdaptedHeadInBlock J hA ht
  let hxD := b.firstJordanAdaptedHeadInBlock_isAnisotropic J hA ht
  let d := b.firstJordanAdaptedBinaryResidualBONG J hA ht hBinary
  have htwo : finrank K D.component.carrier = 2 :=
    D.component_rank_eq_two_of_isBinary hBinary
  have hresidual : finrank K (D.component.space.vectorOrthogonal xD) = 1 :=
    b.firstJordanAdaptedBinaryResidual_finrank_eq_one J hA ht hBinary
  have hblockVolume := D.component_modular.volumeOrder_eq
  change Lattice.volumeOrder D.component.space D.component.lattice =
      (finrank K D.component.carrier : Int) *
        ordUnit K D.scaleGenerator at hblockVolume
  rw [htwo] at hblockVolume
  have hprojection := Lattice.volumeOrder_eq_ordUnit_add_projection
    D.component.space D.component.lattice xD
      (b.firstJordanAdaptedHeadInBlock_isNormGenerator J hA ht) hxD
  have hresidualVolume := d.isModular_valueUnit_zero_unary.volumeOrder_eq
  change Lattice.volumeOrder
      (D.component.space.orthogonalSpace xD hxD)
      (D.component.lattice.projectedLattice D.component.space xD hxD) =
        (finrank K (D.component.space.vectorOrthogonal xD) : Int) *
          ordUnit K (d.valueUnit 0) at hresidualVolume
  rw [hresidual] at hresidualVolume
  norm_num at hresidualVolume
  have hheadUnit :
      Units.mk0 (D.component.space.quadratic xD) hxD = b.valueUnit 0 := by
    apply Units.ext
    change q.quadratic b.head = b.value 0
    exact b.value_zero_eq_quadratic_head.symm
  have hheadOrder :
      ordUnit K (Units.mk0 (D.component.space.quadratic xD) hxD) =
        b.order 0 := by
    rw [hheadUnit]
    exact (b.order_eq_ordUnit 0).symm
  rw [hheadOrder] at hprojection
  change Lattice.volumeOrder D.component.space D.component.lattice =
      b.order 0 +
        Lattice.volumeOrder
          (D.component.space.orthogonalSpace xD hxD)
          (D.component.lattice.projectedLattice D.component.space xD hxD)
    at hprojection
  change ordUnit K (d.valueUnit 0) =
    2 * ordUnit K D.scaleGenerator - b.order 0
  omega

/-- The norm order selected on the first component of the adapted weak
decomposition is the order of the prescribed BONG head. -/
theorem firstJordanAdaptedWeakJordan_normOrder_zero_eq_head
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    ordUnit K
        ((b.firstJordanAdaptedWeakJordan J hA ht).normGeneratorUnit 0) =
      b.order 0 := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  let W := b.firstJordanAdaptedWeakJordan J hA ht
  let xD := b.firstJordanAdaptedHeadInBlock J hA ht
  let hxD := b.firstJordanAdaptedHeadInBlock_isAnisotropic J hA ht
  have hheadUnit :
      Units.mk0 (D.component.space.quadratic xD) hxD = b.valueUnit 0 := by
    apply Units.ext
    change q.quadratic b.head = b.value 0
    exact b.value_zero_eq_quadratic_head.symm
  have hideal :
      Lattice.principalIdeal (K := K) (W.normGeneratorUnit 0 : K) =
        Lattice.principalIdeal (K := K) (b.valueUnit 0 : K) := by
    calc
      Lattice.principalIdeal (K := K) (W.normGeneratorUnit 0 : K) =
          Lattice.normIdeal (W.component 0).space
            (W.component 0).lattice :=
        (W.normIdeal_eq_normGeneratorUnit 0).symm
      _ = Lattice.normIdeal D.component.space D.component.lattice := by
        rfl
      _ = Lattice.principalIdeal (K := K)
          (D.component.space.quadratic xD) :=
        (b.firstJordanAdaptedHeadInBlock_isNormGenerator J hA ht).normIdeal_eq
      _ = Lattice.principalIdeal (K := K) (b.valueUnit 0 : K) := by
        congr 1
        exact congrArg Units.val hheadUnit
  have horder :=
    (Lattice.principalIdeal_eq_iff_ordUnit_eq
      (W.normGeneratorUnit 0) (b.valueUnit 0)).mp hideal
  exact horder.trans (b.order_eq_ordUnit 0).symm

/-- In the binary branch the scale order is strictly below the norm order
of the prescribed first vector. -/
theorem firstJordanAdaptedBlock_scaleOrder_lt_headOrder_of_isBinary
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hBinary : (b.firstJordanAdaptedBlockData J hA ht).IsBinary) :
    ordUnit K (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator <
      b.order 0 := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  have hrep : D.representative = b.head := by
    simpa only [D] using
      b.firstJordanAdaptedBlockData_representative J hA ht
  change D.IsBinary at hBinary
  change ordUnit K D.scaleGenerator < b.order 0
  cases hD : D with
  | unary z hz hcongruent hanisotropic hpair =>
      simp [hD, Lattice.Beli2019Lemma51BlockData.IsBinary] at hBinary
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      have hzhead : z = b.head := by
        simpa [Lattice.Beli2019Lemma51BlockData.representative, hD] using hrep
      subst z
      have hlt :
          ordUnit K (Units.mk0 (q.bilin b.head y) hzy) <
            ordUnit K
              (Units.mk0 (q.quadratic b.head) b.head_isAnisotropic) := by
        apply WithTop.coe_lt_coe.mp
        simpa only [coe_ordUnit, Units.val_mk0] using hleft
      change ordUnit K (Units.mk0 (q.bilin b.head y) hzy) < b.order 0
      calc
        ordUnit K (Units.mk0 (q.bilin b.head y) hzy) <
            ordUnit K
              (Units.mk0 (q.quadratic b.head) b.head_isAnisotropic) := hlt
        _ = ordUnit K (b.valueUnit 0) := by
          congr 1
          apply Units.ext
          change q.quadratic b.head = b.value 0
          exact b.value_zero_eq_quadratic_head.symm
        _ = b.order 0 := (b.order_eq_ordUnit 0).symm

/-- In the unary branch the block scale is the norm of its representative,
and hence has exactly the order of the prescribed BONG head. -/
theorem firstJordanAdaptedBlock_scaleOrder_eq_headOrder_of_isUnary
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hUnary : (b.firstJordanAdaptedBlockData J hA ht).IsUnary) :
    ordUnit K (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator =
      b.order 0 := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  have hrep : D.representative = b.head := by
    simpa only [D] using
      b.firstJordanAdaptedBlockData_representative J hA ht
  change D.IsUnary at hUnary
  change ordUnit K D.scaleGenerator = b.order 0
  cases hD : D with
  | unary z hz hcongruent hanisotropic hpair =>
      have hzhead : z = b.head := by
        simpa [Lattice.Beli2019Lemma51BlockData.representative, hD] using hrep
      subst z
      change ordUnit K
          (Units.mk0 (q.quadratic b.head) b.head_isAnisotropic) = b.order 0
      calc
        ordUnit K (Units.mk0 (q.quadratic b.head) b.head_isAnisotropic) =
            ordUnit K (b.valueUnit 0) := by
          congr 1
          apply Units.ext
          change q.quadratic b.head = b.value 0
          exact b.value_zero_eq_quadratic_head.symm
        _ = b.order 0 := (b.order_eq_ordUnit 0).symm
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      simp [hD, Lattice.Beli2019Lemma51BlockData.IsUnary] at hUnary

/-- If the first Jordan component has rank one, its norm and scale orders
coincide, so the exact adapted block selected at the BONG head is unary. -/
theorem firstJordanAdaptedBlock_isUnary_of_firstJordan_rank_eq_one
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hrank : finrank K (J.component ⟨0, ht⟩).carrier = 1) :
    (b.firstJordanAdaptedBlockData J hA ht).IsUnary := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  have hnormScale : ordUnit K (J.normGenerator ⟨0, ht⟩) =
      ordUnit K (J.scaleGenerator ⟨0, ht⟩) :=
    Lattice.ordUnit_normGenerator_eq_scaleGenerator_of_finrank_eq_one
      (J.component ⟨0, ht⟩).space (J.component ⟨0, ht⟩).lattice
      (J.scaleGenerator ⟨0, ht⟩) (J.normGenerator ⟨0, ht⟩)
      hrank (J.modular ⟨0, ht⟩) (J.normIdeal_eq ⟨0, ht⟩)
  have hhead := b.headOrder_eq_firstJordanNormOrder J hA ht
  have hscale := b.firstJordanAdaptedBlockData_scaleOrder_eq_first J hA ht
  rcases D.isUnary_or_isBinary with hUnary | hBinary
  · simpa only [D] using hUnary
  · have hlt := b.firstJordanAdaptedBlock_scaleOrder_lt_headOrder_of_isBinary
      J hA ht (by simpa only [D] using hBinary)
    change ordUnit K D.scaleGenerator < b.order 0 at hlt
    change ordUnit K D.scaleGenerator =
      ordUnit K (J.scaleGenerator ⟨0, ht⟩) at hscale
    omega

/-- A rank-one first Jordan component cannot collide with the complement at
the same scale: after amalgamation the intrinsic rank at that scale would be
at least two. -/
theorem not_firstJordanAdaptedScaleCollision_of_firstJordan_rank_eq_one
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hrank : finrank K (J.component ⟨0, ht⟩).carrier = 1) :
    ¬b.FirstJordanAdaptedScaleCollision J hA ht := by
  classical
  intro hcollision
  let W := b.firstJordanAdaptedWeakJordan J hA ht
  let i := Classical.choose hcollision
  have hscaleRaw := Classical.choose_spec hcollision
  have hi : i.val = 0 :=
    b.firstJordanAdaptedCollision_index_eq_zero J hA ht i hscaleRaw
  have hcountPos : 0 < b.firstJordanAdaptedComplementCount J hA ht := by
    omega
  let k : Fin (b.firstJordanAdaptedComplementCount J hA ht) :=
    ⟨0, hcountPos⟩
  have hk : k.val = 0 := rfl
  have hik : i = k := by
    apply Fin.ext
    exact hi
  have hkcast : k.castSucc =
      (0 : Fin (b.firstJordanAdaptedComplementCount J hA ht + 1)) := by
    apply Fin.ext
    exact hk
  have heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ) := by
    change ordUnit K
        (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator =
      ordUnit K
        ((b.firstJordanAdaptedComplementJordan J hA ht).scaleGenerator i)
      at hscaleRaw
    rw [hik] at hscaleRaw
    rw [hkcast]
    simpa only [W,
      firstJordanAdaptedWeakJordan_scaleGenerator_zero,
      firstJordanAdaptedWeakJordan_scaleGenerator_succ] using hscaleRaw
  let S := W.mergeAdjacentAt k heq
  have hstrict : StrictMono (fun a ↦ ordUnit K (S.scaleGenerator a)) :=
    Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
      W k heq
        (b.firstJordanAdaptedOnlyScaleCollisionAt J hA ht k hk heq)
  let G := S.toJordan hstrict
  let i0 : Fin t := ⟨0, ht⟩
  have hmatchedIndex : J.scaleIndexEquiv G i0 = k := by
    apply Fin.ext
    simpa only [i0, hk] using J.scaleIndexEquiv_val G i0
  have hmatchedRank := J.componentRank_scaleIndexEquiv G i0
  rw [hmatchedIndex] at hmatchedRank
  change finrank K (S.component k).carrier =
    finrank K (J.component i0).carrier at hmatchedRank
  have hmergedRank : finrank K (S.component k).carrier = 1 := by
    rw [hmatchedRank]
    exact hrank
  have hrankSum := W.mergeAdjacentAt_componentRank_self k heq
  change finrank K (S.component k).carrier =
      finrank K (W.component k.castSucc).carrier +
        finrank K (W.component k.succ).carrier at hrankSum
  have hleftPos : 0 < finrank K (W.component k.castSucc).carrier :=
    W.component_finrank_pos k.castSucc
  have hrightPos : 0 < finrank K (W.component k.succ).carrier :=
    W.component_finrank_pos k.succ
  omega

/-- The old complement components lie strictly beyond both the norm and the
dual order of the binary first block. -/
theorem firstJordanAdaptedBinary_cross_gaps
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hBinary : (b.firstJordanAdaptedBlockData J hA ht).IsBinary)
    (i : Fin (b.firstJordanAdaptedComplementCount J hA ht)) :
    b.order 0 <
        ordUnit K
          ((b.firstJordanAdaptedComplementJordan J hA ht).normGenerator i) ∧
      2 * ordUnit K
          (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator -
          b.order 0 <
        2 * ordUnit K
            ((b.firstJordanAdaptedComplementJordan J hA ht).scaleGenerator i) -
          ordUnit K
            ((b.firstJordanAdaptedComplementJordan J hA ht).normGenerator i) := by
  let W := b.firstJordanAdaptedWeakJordan J hA ht
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  have hno := b.not_firstJordanAdaptedScaleCollision_of_isBinary
    J hA ht hBinary
  let hstrict :=
    b.firstJordanAdaptedWeakJordan_scaleOrder_strict_of_noCollision
      J hA ht hno
  let G := W.toJordan hstrict
  have hG : G.HasPropertyA := J.hasPropertyA_of_hasPropertyA G hA
  have hindex : (0 : Fin (b.firstJordanAdaptedComplementCount J hA ht + 1)) <
      i.succ := by
    simp
  have hgap := hG.2 hindex
  change
      0 < ordUnit K (W.normGeneratorUnit i.succ) -
          ordUnit K (W.normGeneratorUnit 0) ∧
        ordUnit K (W.normGeneratorUnit i.succ) -
            ordUnit K (W.normGeneratorUnit 0) <
          2 * (ordUnit K (W.scaleGenerator i.succ) -
            ordUnit K (W.scaleGenerator 0)) at hgap
  have hzero := b.firstJordanAdaptedWeakJordan_normOrder_zero_eq_head
    J hA ht
  have hsucc :=
    b.firstJordanAdaptedWeakJordan_normOrder_succ_eq_complement
      J hA ht i
  change ordUnit K (W.normGeneratorUnit 0) = b.order 0 at hzero
  change ordUnit K (W.normGeneratorUnit i.succ) =
    ordUnit K (H.normGenerator i) at hsucc
  rw [hzero, hsucc] at hgap
  change
      0 < ordUnit K (H.normGenerator i) - b.order 0 ∧
        ordUnit K (H.normGenerator i) - b.order 0 <
          2 * (ordUnit K (H.scaleGenerator i) -
            ordUnit K
              (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator)
    at hgap
  change
    b.order 0 < ordUnit K (H.normGenerator i) ∧
      2 * ordUnit K
          (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator -
          b.order 0 <
        2 * ordUnit K (H.scaleGenerator i) -
          ordUnit K (H.normGenerator i)
  constructor <;> omega

/-- When the unary first block does not collide in scale with the old
complement, every complement component lies strictly beyond the head in
both its norm and dual-norm order. -/
theorem firstJordanAdaptedUnary_cross_gaps_of_noCollision
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hUnary : (b.firstJordanAdaptedBlockData J hA ht).IsUnary)
    (hcollision : ¬b.FirstJordanAdaptedScaleCollision J hA ht)
    (i : Fin (b.firstJordanAdaptedComplementCount J hA ht)) :
    b.order 0 <
        ordUnit K
          ((b.firstJordanAdaptedComplementJordan J hA ht).normGenerator i) ∧
      b.order 0 <
        2 * ordUnit K
            ((b.firstJordanAdaptedComplementJordan J hA ht).scaleGenerator i) -
          ordUnit K
            ((b.firstJordanAdaptedComplementJordan J hA ht).normGenerator i) := by
  let W := b.firstJordanAdaptedWeakJordan J hA ht
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  let hstrict :=
    b.firstJordanAdaptedWeakJordan_scaleOrder_strict_of_noCollision
      J hA ht hcollision
  let G := W.toJordan hstrict
  have hG : G.HasPropertyA := J.hasPropertyA_of_hasPropertyA G hA
  have hindex : (0 : Fin (b.firstJordanAdaptedComplementCount J hA ht + 1)) <
      i.succ := by
    simp
  have hgap := hG.2 hindex
  change
      0 < ordUnit K (W.normGeneratorUnit i.succ) -
          ordUnit K (W.normGeneratorUnit 0) ∧
        ordUnit K (W.normGeneratorUnit i.succ) -
            ordUnit K (W.normGeneratorUnit 0) <
          2 * (ordUnit K (W.scaleGenerator i.succ) -
            ordUnit K (W.scaleGenerator 0)) at hgap
  have hzero := b.firstJordanAdaptedWeakJordan_normOrder_zero_eq_head
    J hA ht
  have hsucc :=
    b.firstJordanAdaptedWeakJordan_normOrder_succ_eq_complement
      J hA ht i
  have hscale :=
    b.firstJordanAdaptedBlock_scaleOrder_eq_headOrder_of_isUnary
      J hA ht hUnary
  change ordUnit K (W.normGeneratorUnit 0) = b.order 0 at hzero
  change ordUnit K (W.normGeneratorUnit i.succ) =
    ordUnit K (H.normGenerator i) at hsucc
  change ordUnit K (W.scaleGenerator 0) = b.order 0 at hscale
  rw [hzero, hsucc, hscale] at hgap
  change
      0 < ordUnit K (H.normGenerator i) - b.order 0 ∧
        ordUnit K (H.normGenerator i) - b.order 0 <
          2 * (ordUnit K (H.scaleGenerator i) - b.order 0) at hgap
  change
    b.order 0 < ordUnit K (H.normGenerator i) ∧
      b.order 0 <
        2 * ordUnit K (H.scaleGenerator i) -
          ordUnit K (H.normGenerator i)
  constructor <;> omega

/-- At the unique equal-scale collision, the first old complement component
is a unary component whose norm order is exactly the order of the prescribed
head. -/
theorem firstJordanAdaptedCollision_firstComplement_rank_one_and_normOrder
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hcollision : b.FirstJordanAdaptedScaleCollision J hA ht) :
    ∃ hcount : 0 < b.firstJordanAdaptedComplementCount J hA ht,
      finrank K
          ((b.firstJordanAdaptedComplementJordan J hA ht).component
            ⟨0, hcount⟩).carrier = 1 ∧
        ordUnit K
            ((b.firstJordanAdaptedComplementJordan J hA ht).normGenerator
              ⟨0, hcount⟩) = b.order 0 := by
  classical
  let D := b.firstJordanAdaptedBlockData J hA ht
  let C := b.firstJordanAdaptedComplement J hA ht
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  let W := b.firstJordanAdaptedWeakJordan J hA ht
  let i := Classical.choose hcollision
  have hscaleRaw := Classical.choose_spec hcollision
  have hi : i.val = 0 :=
    b.firstJordanAdaptedCollision_index_eq_zero J hA ht i hscaleRaw
  have hcountPos : 0 < b.firstJordanAdaptedComplementCount J hA ht := by
    omega
  let k : Fin (b.firstJordanAdaptedComplementCount J hA ht) :=
    ⟨0, hcountPos⟩
  have hk : k.val = 0 := rfl
  have hik : i = k := by
    apply Fin.ext
    exact hi
  have hscale : ordUnit K D.scaleGenerator =
      ordUnit K (H.scaleGenerator k) := by
    change ordUnit K
        (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator =
      ordUnit K
        ((b.firstJordanAdaptedComplementJordan J hA ht).scaleGenerator i)
      at hscaleRaw
    rw [hik] at hscaleRaw
    exact hscaleRaw
  have hkcast : k.castSucc =
      (0 : Fin (b.firstJordanAdaptedComplementCount J hA ht + 1)) := by
    apply Fin.ext
    exact hk
  have heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ) := by
    rw [hkcast]
    simpa only [W, D, H,
      firstJordanAdaptedWeakJordan_scaleGenerator_zero,
      firstJordanAdaptedWeakJordan_scaleGenerator_succ] using hscale
  let S := W.mergeAdjacentAt k heq
  have hstrict : StrictMono (fun a ↦ ordUnit K (S.scaleGenerator a)) :=
    Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
      W k heq
        (b.firstJordanAdaptedOnlyScaleCollisionAt J hA ht k hk heq)
  let G := S.toJordan hstrict
  have hG : G.HasPropertyA := J.hasPropertyA_of_hasPropertyA G hA
  have hmergedRank := hG.1 k
  change finrank K (S.component k).carrier = 1 ∨
      finrank K (S.component k).carrier = 2 at hmergedRank
  have hrankSum := W.mergeAdjacentAt_componentRank_self k heq
  change finrank K (S.component k).carrier =
      finrank K (W.component k.castSucc).carrier +
        finrank K (W.component k.succ).carrier at hrankSum
  have hleftPos : 0 < finrank K (W.component k.castSucc).carrier :=
    W.component_finrank_pos k.castSucc
  have hrightPos : 0 < finrank K (W.component k.succ).carrier :=
    W.component_finrank_pos k.succ
  have hrightRank : finrank K (W.component k.succ).carrier = 1 := by
    rcases hmergedRank with h | h <;> omega
  have hHrank : finrank K (H.component k).carrier = 1 := by
    change finrank K (C.liftNested (H.component k)).carrier = 1 at hrightRank
    simpa only [C.finrank_liftNested] using hrightRank
  have hHNorm : ordUnit K (H.normGenerator k) =
      ordUnit K (H.scaleGenerator k) :=
    Lattice.ordUnit_normGenerator_eq_scaleGenerator_of_finrank_eq_one
      (H.component k).space (H.component k).lattice
      (H.scaleGenerator k) (H.normGenerator k) hHrank
      (H.modular k) (H.normIdeal_eq k)
  have hUnary : D.IsUnary := by
    rcases D.isUnary_or_isBinary with hUnary | hBinary
    · exact hUnary
    · exact False.elim
        ((b.not_firstJordanAdaptedScaleCollision_of_isBinary
          J hA ht (by simpa only [D] using hBinary)) hcollision)
  have hDScale : ordUnit K D.scaleGenerator = b.order 0 := by
    simpa only [D] using
      b.firstJordanAdaptedBlock_scaleOrder_eq_headOrder_of_isUnary
        J hA ht (by simpa only [D] using hUnary)
  refine ⟨hcountPos, ?_, ?_⟩
  · simpa only [H, k] using hHrank
  · change ordUnit K (H.normGenerator k) = b.order 0
    exact hHNorm.trans (hscale.symm.trans hDScale)

/-- Projection after the prescribed first vector splits as the projection
inside the adapted block times the unchanged orthogonal complement. -/
noncomputable def firstJordanAdaptedProjectionProductIsometry
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    let D := b.firstJordanAdaptedBlockData J hA ht
    let C := D.splitting.component 1
    let xD := b.firstJordanAdaptedHeadInBlock J hA ht
    let hxD := b.firstJordanAdaptedHeadInBlock_isAnisotropic J hA ht
    Lattice.Isometry
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      ((D.component.space.orthogonalSpace xD hxD).orthogonalSum C.space)
      (L.projectedLattice q b.head b.head_isAnisotropic)
      (Lattice.product
        (D.component.lattice.projectedLattice D.component.space xD hxD)
        C.lattice) := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  let P := D.splitting
  let C := P.component 1
  let xD := b.firstJordanAdaptedHeadInBlock J hA ht
  let hxD := b.firstJordanAdaptedHeadInBlock_isAnisotropic J hA ht
  let F := P.pairProductLatticeIsometry
  let hxProduct := hxD.orthogonalSum_inl (r := C.space)
  have hFhead : F.toLinearEquiv (xD, 0) = b.head := by
    change P.pairProductLatticeIsometry.toLinearEquiv (xD, 0) = b.head
    rw [P.pairProductLatticeIsometry_apply_left]
    exact b.coe_firstJordanAdaptedHeadInBlock J hA ht
  let Fproj := F.projectedLatticeIsometryOfEq (xD, 0) hxProduct
    b.head b.head_isAnisotropic hFhead
  let G := Lattice.projectedOrthogonalProductIsometry
    (q := D.component.space) (r := C.space)
    (L := D.component.lattice) (M := C.lattice) hxD
  exact Fproj.symm.trans G

/-- In the binary branch, the next order of the prescribed BONG is exactly
the order of the residual line in the adapted binary block. -/
theorem order_one_eq_firstJordanAdaptedBinaryResidualOrder
    [FiniteDimensional K V]
    (b : BONG V q L (n + 2))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hBinary : (b.firstJordanAdaptedBlockData J hA ht).IsBinary) :
    b.order 1 =
      2 * ordUnit K
          (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator -
        b.order 0 := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  let C := D.splitting.component 1
  let xD := b.firstJordanAdaptedHeadInBlock J hA ht
  let hxD := b.firstJordanAdaptedHeadInBlock_isAnisotropic J hA ht
  let qR := D.component.space.orthogonalSpace xD hxD
  let LR := D.component.lattice.projectedLattice D.component.space xD hxD
  let d := b.firstJordanAdaptedBinaryResidualBONG J hA ht hBinary
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  let E := b.firstJordanAdaptedProjectionProductIsometry J hA ht
  have hresidualIdeal : Lattice.normIdeal qR LR =
      Lattice.principalIdeal (K := K) (d.valueUnit 0 : K) := by
    rw [d.coe_valueUnit, d.value_zero_eq_quadratic_head]
    exact d.head_isNormGenerator.normIdeal_eq
  have hresidualOrder : ordUnit K (d.valueUnit 0) =
      2 * ordUnit K D.scaleGenerator - b.order 0 :=
    b.firstJordanAdaptedBinaryResidual_order J hA ht hBinary
  have hscaleHead : ordUnit K D.scaleGenerator < b.order 0 :=
    b.firstJordanAdaptedBlock_scaleOrder_lt_headOrder_of_isBinary
      J hA ht hBinary
  have hcomplementLe : Lattice.normIdeal C.space C.lattice ≤
      Lattice.principalIdeal (K := K) (d.valueUnit 0 : K) := by
    change Lattice.normIdeal
        (b.firstJordanAdaptedComplement J hA ht).space
        (b.firstJordanAdaptedComplement J hA ht).lattice ≤ _
    rw [H.toOrthogonalDecomposition.normIdeal_eq_iSup_component]
    apply iSup_le
    intro i
    rw [H.normIdeal_eq i]
    apply (Lattice.principalIdeal_le_iff_ord_ge
      (Units.ne_zero (H.normGenerator i))
      (Units.ne_zero (d.valueUnit 0))).2
    have hle : ordUnit K (d.valueUnit 0) ≤
        ordUnit K (H.normGenerator i) := by
      have hgap := b.firstJordanAdaptedBinary_cross_gaps
        J hA ht hBinary i
      change b.order 0 < ordUnit K (H.normGenerator i) ∧ _ at hgap
      rw [hresidualOrder]
      omega
    simpa only [coe_ordUnit] using WithTop.coe_le_coe.mpr hle
  have hproductIdeal :
      Lattice.normIdeal (qR.orthogonalSum C.space)
          (Lattice.product LR C.lattice) =
        Lattice.principalIdeal (K := K) (d.valueUnit 0 : K) := by
    rw [Lattice.normIdeal_orthogonalProduct, hresidualIdeal]
    exact sup_eq_left.mpr hcomplementLe
  have hisometryIdeal :
      Lattice.normIdeal (qR.orthogonalSum C.space)
          (Lattice.product LR C.lattice) =
        Lattice.normIdeal
          (q.orthogonalSpace b.head b.head_isAnisotropic)
          (L.projectedLattice q b.head b.head_isAnisotropic) := by
    rw [← E.map_eq]
    exact Lattice.normIdeal_map_isometry E.toQuadraticSpaceIsometry
      (L.projectedLattice q b.head b.head_isAnisotropic)
  have hideal :
      Lattice.principalIdeal (K := K) (b.tail.valueUnit 0 : K) =
        Lattice.principalIdeal (K := K) (d.valueUnit 0 : K) := by
    calc
      Lattice.principalIdeal (K := K) (b.tail.valueUnit 0 : K) =
          Lattice.normIdeal
            (q.orthogonalSpace b.head b.head_isAnisotropic)
            (L.projectedLattice q b.head b.head_isAnisotropic) := by
        rw [b.tail.coe_valueUnit, b.tail.value_zero_eq_quadratic_head]
        exact b.tail.head_isNormGenerator.normIdeal_eq.symm
      _ = Lattice.normIdeal (qR.orthogonalSum C.space)
          (Lattice.product LR C.lattice) := hisometryIdeal.symm
      _ = Lattice.principalIdeal (K := K) (d.valueUnit 0 : K) :=
        hproductIdeal
  have horder := (Lattice.principalIdeal_eq_iff_ordUnit_eq
    (b.tail.valueUnit 0) (d.valueUnit 0)).mp hideal
  rw [← b.tail.order_eq_ordUnit, b.order_tail,
    hresidualOrder] at horder
  exact horder

/-- If both the norm and dual norm of the first Jordan component lie above a
fixed threshold, then the next order of every BONG lies above that threshold.
The unary branch uses integral projection; the binary branch uses the exact
residual-line formula. -/
theorem threshold_lt_order_one_of_firstJordan_norm_dual_gt
    [FiniteDimensional K V]
    (b : BONG V q L (n + 2))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) (c : Int)
    (hnorm : c < ordUnit K (J.normGenerator ⟨0, ht⟩))
    (hdual : c <
      2 * ordUnit K (J.scaleGenerator ⟨0, ht⟩) -
        ordUnit K (J.normGenerator ⟨0, ht⟩)) :
    c < b.order 1 := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  have hhead : b.order 0 = ordUnit K (J.normGenerator ⟨0, ht⟩) :=
    b.headOrder_eq_firstJordanNormOrder J hA ht
  rcases D.isUnary_or_isBinary with hUnary | hBinary
  · have hmono : b.order 0 ≤ b.order 1 :=
      b.order_zero_le_order_one_of_firstJordanAdaptedBlockData_isUnary
        J hA ht (by simpa only [D] using hUnary)
    omega
  · have hresidual :=
      b.order_one_eq_firstJordanAdaptedBinaryResidualOrder
        J hA ht (by simpa only [D] using hBinary)
    have hscale := b.firstJordanAdaptedBlockData_scaleOrder_eq_first
      J hA ht
    change ordUnit K D.scaleGenerator =
      ordUnit K (J.scaleGenerator ⟨0, ht⟩) at hscale
    change b.order 1 = 2 * ordUnit K D.scaleGenerator - b.order 0
      at hresidual
    omega

/-- A Jordan decomposition of a space carrying a nonempty BONG has at least
one component. -/
theorem jordanCount_pos_of_bong_positive_length
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) :
    0 < t := by
  by_contra ht
  have htZero : t = 0 := by omega
  subst t
  have hsum := J.sum_componentRank_eq_finrank
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  have hlength := b.length_eq_finrank
  change n + 1 = finrank K V at hlength
  omega

/-- A Jordan decomposition of a space carrying a BONG of length at least two
cannot consist of a single rank-one component. -/
theorem one_lt_jordanCount_of_bong_length_at_least_two_and_first_rank_one
    [FiniteDimensional K V]
    (b : BONG V q L (n + 2))
    (J : Lattice.JordanDecomposition q L t)
    (ht : 0 < t)
    (hrank : finrank K (J.component ⟨0, ht⟩).carrier = 1) :
    1 < t := by
  by_contra htwo
  have htOne : t = 1 := by omega
  subst t
  have hsum := J.sum_componentRank_eq_finrank
  simp only [Fin.sum_univ_one] at hsum
  change finrank K (J.component 0).carrier = finrank K V at hsum
  have hrank' : finrank K (J.component 0).carrier = 1 := by
    have hidx : (⟨0, ht⟩ : Fin 1) = 0 := Subsingleton.elim _ _
    rw [hidx] at hrank
    exact hrank
  have hlength := b.length_eq_finrank
  change n + 2 = finrank K V at hlength
  omega

/-- If the first Jordan component has rank one, removing an arbitrary norm
generator shifts the intrinsic Jordan profile by exactly one component. -/
theorem order_one_eq_secondJordanNorm_of_firstJordan_rank_eq_one
    [FiniteDimensional K V]
    (b : BONG V q L (n + 2))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) (htwo : 1 < t)
    (hrank : finrank K (J.component ⟨0, ht⟩).carrier = 1) :
    b.order 1 = ordUnit K (J.normGenerator ⟨1, htwo⟩) := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  let W := b.firstJordanAdaptedWeakJordan J hA ht
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  have hUnary : D.IsUnary := by
    simpa only [D] using
      b.firstJordanAdaptedBlock_isUnary_of_firstJordan_rank_eq_one
        J hA ht hrank
  have hno : ¬b.FirstJordanAdaptedScaleCollision J hA ht :=
    b.not_firstJordanAdaptedScaleCollision_of_firstJordan_rank_eq_one
      J hA ht hrank
  let hstrict :=
    b.firstJordanAdaptedWeakJordan_scaleOrder_strict_of_noCollision
      J hA ht hno
  let G := W.toJordan hstrict
  let i1 : Fin t := ⟨1, htwo⟩
  have hmatchedVal : (J.scaleIndexEquiv G i1).val = 1 := by
    simpa only [i1] using J.scaleIndexEquiv_val G i1
  have hcount : 0 < b.firstJordanAdaptedComplementCount J hA ht := by
    have hbound := (J.scaleIndexEquiv G i1).isLt
    change (J.scaleIndexEquiv G i1).val <
      b.firstJordanAdaptedComplementCount J hA ht + 1 at hbound
    omega
  let k0 : Fin (b.firstJordanAdaptedComplementCount J hA ht) :=
    ⟨0, hcount⟩
  let one : Fin (b.firstJordanAdaptedComplementCount J hA ht + 1) :=
    ⟨1, by omega⟩
  have hmatched : J.scaleIndexEquiv G i1 = one := by
    apply Fin.ext
    exact hmatchedVal
  have hinvariant :=
    J.normOrder_scaleIndexEquiv_eq_of_hasPropertyA G hA i1
  rw [hmatched] at hinvariant
  have hone : one = k0.succ := by
    apply Fin.ext
    rfl
  rw [hone] at hinvariant
  change ordUnit K (W.normGeneratorUnit k0.succ) =
    ordUnit K (J.normGenerator i1) at hinvariant
  have hsucc :=
    b.firstJordanAdaptedWeakJordan_normOrder_succ_eq_complement
      J hA ht k0
  change ordUnit K (W.normGeneratorUnit k0.succ) =
    ordUnit K (H.normGenerator k0) at hsucc
  rw [hsucc] at hinvariant
  have horder :=
    b.order_one_eq_firstJordanAdaptedComplementNorm_of_isUnary
      J hA ht (by simpa only [D] using hUnary) hcount
  change b.order 1 = ordUnit K (H.normGenerator k0) at horder
  exact horder.trans hinvariant

/-- The explicit property-A Jordan decomposition of the product obtained in
the binary branch: the residual rank-one line is prepended to the unchanged
old complement. -/
noncomputable def firstJordanAdaptedBinaryProductJordanWitness
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hBinary : (b.firstJordanAdaptedBlockData J hA ht).IsBinary) :
    let D := b.firstJordanAdaptedBlockData J hA ht
    let C := D.splitting.component 1
    let xD := b.firstJordanAdaptedHeadInBlock J hA ht
    let hxD := b.firstJordanAdaptedHeadInBlock_isAnisotropic J hA ht
    let qR := D.component.space.orthogonalSpace xD hxD
    let LR := D.component.lattice.projectedLattice D.component.space xD hxD
    {T : Lattice.JordanDecomposition
        (qR.orthogonalSum C.space) (Lattice.product LR C.lattice)
        (b.firstJordanAdaptedComplementCount J hA ht + 1) //
      T.HasPropertyA} := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  let C := D.splitting.component 1
  let xD := b.firstJordanAdaptedHeadInBlock J hA ht
  let hxD := b.firstJordanAdaptedHeadInBlock_isAnisotropic J hA ht
  let qR := D.component.space.orthogonalSpace xD hxD
  let LR := D.component.lattice.projectedLattice D.component.space xD hxD
  let d := b.firstJordanAdaptedBinaryResidualBONG J hA ht hBinary
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  have hH : H.HasPropertyA :=
    b.firstJordanAdaptedComplementJordan_hasPropertyA J hA ht
  let P := Lattice.orthogonalProductDecomposition qR C.space LR C.lattice
  let leftIso :=
    Lattice.orthogonalProductLeftComponentIsometry qR C.space LR
  let rightIso :=
    Lattice.orthogonalProductRightComponentIsometry qR C.space C.lattice
  let H' := H.mapIsometry rightIso
  have hH' : H'.HasPropertyA := hH.mapIsometry rightIso
  have hresidualRank : finrank K (D.component.space.vectorOrthogonal xD) = 1 :=
    b.firstJordanAdaptedBinaryResidual_finrank_eq_one J hA ht hBinary
  have hleftRank : finrank K (P.component 0).carrier = 1 := by
    change finrank K
      (Lattice.orthogonalProductLeftComponent qR C.space LR).carrier = 1
    exact leftIso.toLinearEquiv.finrank_eq.symm.trans hresidualRank
  have hmodularLeft : Lattice.IsModular
      (P.component 0).space (P.component 0).lattice (d.valueUnit 0) := by
    change Lattice.IsModular
      (Lattice.orthogonalProductLeftComponent qR C.space LR).space
      (Lattice.orthogonalProductLeftComponent qR C.space LR).lattice
      (d.valueUnit 0)
    exact d.isModular_valueUnit_zero_unary.mapLatticeIsometry leftIso
  have hnormLeft :
      Lattice.normIdeal (P.component 0).space (P.component 0).lattice =
        Lattice.principalIdeal (K := K) (d.valueUnit 0 : K) := by
    calc
      Lattice.normIdeal (P.component 0).space (P.component 0).lattice =
          Lattice.scaleIdeal (P.component 0).space
            (P.component 0).lattice :=
        Lattice.normIdeal_eq_scaleIdeal_of_finrank_eq_one
          (P.component 0).space (P.component 0).lattice hleftRank
      _ = Lattice.principalIdeal (K := K) (d.valueUnit 0 : K) :=
        hmodularLeft.scaleIdeal_eq_principal (by omega)
  have hresidualOrder : ordUnit K (d.valueUnit 0) =
      2 * ordUnit K D.scaleGenerator - b.order 0 :=
    b.firstJordanAdaptedBinaryResidual_order J hA ht hBinary
  have hscaleHead : ordUnit K D.scaleGenerator < b.order 0 :=
    b.firstJordanAdaptedBlock_scaleOrder_lt_headOrder_of_isBinary
      J hA ht hBinary
  have hcrossNorm : ∀ i : Fin (b.firstJordanAdaptedComplementCount J hA ht),
      ordUnit K (d.valueUnit 0) < ordUnit K (H'.normGenerator i) := by
    intro i
    have hgap := b.firstJordanAdaptedBinary_cross_gaps J hA ht hBinary i
    change
      b.order 0 < ordUnit K (H.normGenerator i) ∧
        2 * ordUnit K D.scaleGenerator - b.order 0 <
          2 * ordUnit K (H.scaleGenerator i) -
            ordUnit K (H.normGenerator i) at hgap
    change ordUnit K (d.valueUnit 0) < ordUnit K (H.normGenerator i)
    rw [hresidualOrder]
    omega
  have hcrossDual : ∀ i : Fin (b.firstJordanAdaptedComplementCount J hA ht),
      2 * ordUnit K (d.valueUnit 0) - ordUnit K (d.valueUnit 0) <
        2 * ordUnit K (H'.scaleGenerator i) -
          ordUnit K (H'.normGenerator i) := by
    intro i
    have hgap := b.firstJordanAdaptedBinary_cross_gaps J hA ht hBinary i
    change
      b.order 0 < ordUnit K (H.normGenerator i) ∧
        2 * ordUnit K D.scaleGenerator - b.order 0 <
          2 * ordUnit K (H.scaleGenerator i) -
            ordUnit K (H.normGenerator i) at hgap
    change 2 * ordUnit K (d.valueUnit 0) - ordUnit K (d.valueUnit 0) <
      2 * ordUnit K (H.scaleGenerator i) -
        ordUnit K (H.normGenerator i)
    rw [hresidualOrder]
    omega
  exact Lattice.JordanDecomposition.prependPropertyAWitness
    P H' hH' (d.valueUnit 0) (d.valueUnit 0)
      hmodularLeft hnormLeft (Or.inl hleftRank) hcrossNorm hcrossDual

/-- The first component of the binary product witness is the residual line. -/
theorem firstJordanAdaptedBinaryProductJordanWitness_firstRank
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hBinary : (b.firstJordanAdaptedBlockData J hA ht).IsBinary) :
    finrank K
        ((b.firstJordanAdaptedBinaryProductJordanWitness
          J hA ht hBinary).1.component 0).carrier = 1 := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  let C := D.splitting.component 1
  let xD := b.firstJordanAdaptedHeadInBlock J hA ht
  let hxD := b.firstJordanAdaptedHeadInBlock_isAnisotropic J hA ht
  let qR := D.component.space.orthogonalSpace xD hxD
  let LR := D.component.lattice.projectedLattice D.component.space xD hxD
  let leftIso :=
    Lattice.orthogonalProductLeftComponentIsometry qR C.space LR
  have hresidualRank : finrank K (D.component.space.vectorOrthogonal xD) = 1 :=
    b.firstJordanAdaptedBinaryResidual_finrank_eq_one J hA ht hBinary
  change finrank K
    (Lattice.orthogonalProductLeftComponent qR C.space LR).carrier = 1
  exact leftIso.toLinearEquiv.finrank_eq.symm.trans hresidualRank

/-- Positive components of the binary product witness retain the norm
generators of the old complement. -/
@[simp]
theorem firstJordanAdaptedBinaryProductJordanWitness_normGenerator_succ
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hBinary : (b.firstJordanAdaptedBlockData J hA ht).IsBinary)
    (i : Fin (b.firstJordanAdaptedComplementCount J hA ht)) :
    (b.firstJordanAdaptedBinaryProductJordanWitness
        J hA ht hBinary).1.normGenerator i.succ =
      (b.firstJordanAdaptedComplementJordan J hA ht).normGenerator i := by
  rfl

/-- In the binary branch, the residual line and the old complement form a
property-A orthogonal product.  Transporting it through the projection
isometry proves property A for the recursive tail lattice. -/
theorem tailLattice_hasJordanPropertyA_of_firstJordanAdaptedBlock_isBinary
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hBinary : (b.firstJordanAdaptedBlockData J hA ht).IsBinary) :
    Lattice.HasJordanPropertyA
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic) := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  let C := D.splitting.component 1
  let xD := b.firstJordanAdaptedHeadInBlock J hA ht
  let hxD := b.firstJordanAdaptedHeadInBlock_isAnisotropic J hA ht
  let qR := D.component.space.orthogonalSpace xD hxD
  let LR := D.component.lattice.projectedLattice D.component.space xD hxD
  let d := b.firstJordanAdaptedBinaryResidualBONG J hA ht hBinary
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  have hH : H.HasPropertyA :=
    b.firstJordanAdaptedComplementJordan_hasPropertyA J hA ht
  let P := Lattice.orthogonalProductDecomposition qR C.space LR C.lattice
  let leftIso :=
    Lattice.orthogonalProductLeftComponentIsometry qR C.space LR
  let rightIso :=
    Lattice.orthogonalProductRightComponentIsometry qR C.space C.lattice
  let H' := H.mapIsometry rightIso
  have hH' : H'.HasPropertyA := hH.mapIsometry rightIso
  have hresidualRank : finrank K (D.component.space.vectorOrthogonal xD) = 1 :=
    b.firstJordanAdaptedBinaryResidual_finrank_eq_one J hA ht hBinary
  have hleftRank : finrank K (P.component 0).carrier = 1 := by
    change finrank K
      (Lattice.orthogonalProductLeftComponent qR C.space LR).carrier = 1
    exact leftIso.toLinearEquiv.finrank_eq.symm.trans hresidualRank
  have hmodularLeft : Lattice.IsModular
      (P.component 0).space (P.component 0).lattice (d.valueUnit 0) := by
    change Lattice.IsModular
      (Lattice.orthogonalProductLeftComponent qR C.space LR).space
      (Lattice.orthogonalProductLeftComponent qR C.space LR).lattice
      (d.valueUnit 0)
    exact d.isModular_valueUnit_zero_unary.mapLatticeIsometry leftIso
  have hnormLeft :
      Lattice.normIdeal (P.component 0).space (P.component 0).lattice =
        Lattice.principalIdeal (K := K) (d.valueUnit 0 : K) := by
    calc
      Lattice.normIdeal (P.component 0).space (P.component 0).lattice =
          Lattice.scaleIdeal (P.component 0).space
            (P.component 0).lattice :=
        Lattice.normIdeal_eq_scaleIdeal_of_finrank_eq_one
          (P.component 0).space (P.component 0).lattice hleftRank
      _ = Lattice.principalIdeal (K := K) (d.valueUnit 0 : K) :=
        hmodularLeft.scaleIdeal_eq_principal (by omega)
  have hresidualOrder : ordUnit K (d.valueUnit 0) =
      2 * ordUnit K D.scaleGenerator - b.order 0 := by
    exact b.firstJordanAdaptedBinaryResidual_order J hA ht hBinary
  have hscaleHead : ordUnit K D.scaleGenerator < b.order 0 :=
    b.firstJordanAdaptedBlock_scaleOrder_lt_headOrder_of_isBinary
      J hA ht hBinary
  have hcrossNorm : ∀ i : Fin (b.firstJordanAdaptedComplementCount J hA ht),
      ordUnit K (d.valueUnit 0) < ordUnit K (H'.normGenerator i) := by
    intro i
    have hgap := b.firstJordanAdaptedBinary_cross_gaps J hA ht hBinary i
    change
      b.order 0 < ordUnit K (H.normGenerator i) ∧
        2 * ordUnit K D.scaleGenerator - b.order 0 <
          2 * ordUnit K (H.scaleGenerator i) -
            ordUnit K (H.normGenerator i) at hgap
    change ordUnit K (d.valueUnit 0) < ordUnit K (H.normGenerator i)
    rw [hresidualOrder]
    omega
  have hcrossDual : ∀ i : Fin (b.firstJordanAdaptedComplementCount J hA ht),
      2 * ordUnit K (d.valueUnit 0) - ordUnit K (d.valueUnit 0) <
        2 * ordUnit K (H'.scaleGenerator i) -
          ordUnit K (H'.normGenerator i) := by
    intro i
    have hgap := b.firstJordanAdaptedBinary_cross_gaps J hA ht hBinary i
    change
      b.order 0 < ordUnit K (H.normGenerator i) ∧
        2 * ordUnit K D.scaleGenerator - b.order 0 <
          2 * ordUnit K (H.scaleGenerator i) -
            ordUnit K (H.normGenerator i) at hgap
    change 2 * ordUnit K (d.valueUnit 0) - ordUnit K (d.valueUnit 0) <
      2 * ordUnit K (H.scaleGenerator i) -
        ordUnit K (H.normGenerator i)
    rw [hresidualOrder]
    omega
  let T := Lattice.JordanDecomposition.prependPropertyAWitness
    P H' hH' (d.valueUnit 0) (d.valueUnit 0)
      hmodularLeft hnormLeft (Or.inl hleftRank) hcrossNorm hcrossDual
  have hProduct : Lattice.HasJordanPropertyA
      (qR.orthogonalSum C.space) (Lattice.product LR C.lattice) :=
    ⟨b.firstJordanAdaptedComplementCount J hA ht + 1, T.1, T.2⟩
  let E := b.firstJordanAdaptedProjectionProductIsometry J hA ht
  exact hProduct.mapIsometry E.symm

/-- Removing the first vector of an arbitrary BONG from a property-A lattice
again leaves a property-A lattice.  The adapted block supplied by Lemma 5.1
is necessarily unary or binary, so the preceding two geometric arguments are
exhaustive. -/
theorem tailLattice_hasJordanPropertyA
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    Lattice.HasJordanPropertyA
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic) := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  rcases D.isUnary_or_isBinary with hUnary | hBinary
  · exact b.tailLattice_hasJordanPropertyA_of_firstJordanAdaptedBlock_isUnary
      J hA ht (by simpa only [D] using hUnary)
  · exact b.tailLattice_hasJordanPropertyA_of_firstJordanAdaptedBlock_isBinary
      J hA ht (by simpa only [D] using hBinary)

/-- In the unary adapted-block branch, the first two-step BONG inequality
follows by transporting the complement Jordan decomposition to the recursive
tail.  The strict-scale case uses the two threshold gaps; the collision case
uses the rank-one profile shift to the next Jordan component. -/
theorem order_zero_lt_order_two_of_firstJordanAdaptedBlock_isUnary
    [FiniteDimensional K V]
    (b : BONG V q L (n + 3))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hUnary : (b.firstJordanAdaptedBlockData J hA ht).IsUnary) :
    b.order 0 < b.order 2 := by
  classical
  let D := b.firstJordanAdaptedBlockData J hA ht
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  have hrep : D.representative = b.head := by
    simpa only [D] using
      b.firstJordanAdaptedBlockData_representative J hA ht
  have hH : H.HasPropertyA :=
    b.firstJordanAdaptedComplementJordan_hasPropertyA J hA ht
  cases hD : D with
  | unary z hz hcongruent hanisotropic hpair =>
      have hzhead : z = b.head := by
        simpa [Lattice.Beli2019Lemma51BlockData.representative, hD] using hrep
      subst z
      have hpairC : ∀
          (y : (Lattice.unaryScaleComponent
            (q := q) b.head b.head_isAnisotropic).carrier),
          y ∈ (Lattice.unaryScaleComponent
            (q := q) b.head b.head_isAnisotropic).lattice →
          ∀ w : V, w ∈ L →
            q.bilin (y : V) w ∈
              Lattice.principalIdeal (K := K) (q.quadratic b.head) := by
        intro y hy w hw
        exact
          (Lattice.Beli2019Lemma51BlockData.unary b.head hz hcongruent
            hanisotropic hpair).component_pairing y hy w hw
      have hprojectedIntegral : ∀ y : q.vectorOrthogonal b.head,
          y ∈ L.projectedLattice q b.head b.head_isAnisotropic →
            (y : V) ∈ L := by
        intro y hy
        exact Lattice.coe_mem_of_mem_projectedLattice_of_pairing_divisible
          b.head_isNormGenerator.mem b.head_isAnisotropic hpair hy
      let N :=
        (Lattice.unaryScaleComponent
          (q := q) b.head b.head_isAnisotropic).orthogonalLattice
            (Lattice.unaryScaleComponent_ambientSubmodule_le
              b.head_isAnisotropic b.head_isNormGenerator.mem)
            (Lattice.unaryScaleComponent_isModular b.head_isAnisotropic)
            hpairC
      have heq : L.projectedLattice q b.head b.head_isAnisotropic = N := by
        exact Lattice.projectedLattice_eq_unaryOrthogonalLattice
          b.head_isNormGenerator.mem b.head_isAnisotropic hpairC
          hprojectedIntegral
      let c : BONG (q.vectorOrthogonal b.head)
          (q.orthogonalSpace b.head b.head_isAnisotropic) N (n + 2) :=
        b.tail.castLattice heq
      have horder : c.order 1 = b.order 2 := by
        calc
          c.order 1 = b.tail.order 1 := by simp only [c, order_castLattice]
          _ = b.order 2 := b.order_tail 1
      by_cases hcollision : b.FirstJordanAdaptedScaleCollision J hA ht
      · rcases
          b.firstJordanAdaptedCollision_firstComplement_rank_one_and_normOrder
            J hA ht hcollision with ⟨hcount, hrank, hnorm⟩
        change finrank K (H.component ⟨0, hcount⟩).carrier = 1 at hrank
        change ordUnit K (H.normGenerator ⟨0, hcount⟩) = b.order 0 at hnorm
        have HWCraw :
            {G : Lattice.JordanDecomposition
                (D.splitting.component 1).space
                (D.splitting.component 1).lattice
                (b.firstJordanAdaptedComplementCount J hA ht) //
              G.HasPropertyA ∧
                finrank K (G.component ⟨0, hcount⟩).carrier = 1 ∧
                ordUnit K (G.normGenerator ⟨0, hcount⟩) = b.order 0} :=
          ⟨H, hH, hrank, hnorm⟩
        rw [hD] at HWCraw
        change
          {G : Lattice.JordanDecomposition
              (q.orthogonalSpace b.head b.head_isAnisotropic) N
              (b.firstJordanAdaptedComplementCount J hA ht) //
            G.HasPropertyA ∧
              finrank K (G.component ⟨0, hcount⟩).carrier = 1 ∧
              ordUnit K (G.normGenerator ⟨0, hcount⟩) = b.order 0} at HWCraw
        let H' := HWCraw.1
        have hH' : H'.HasPropertyA := HWCraw.2.1
        have hrank' : finrank K (H'.component ⟨0, hcount⟩).carrier = 1 :=
          HWCraw.2.2.1
        have hnorm' : ordUnit K (H'.normGenerator ⟨0, hcount⟩) =
            b.order 0 := HWCraw.2.2.2
        have htwo : 1 < b.firstJordanAdaptedComplementCount J hA ht :=
          c.one_lt_jordanCount_of_bong_length_at_least_two_and_first_rank_one
            H' hcount hrank'
        have hshift :=
          c.order_one_eq_secondJordanNorm_of_firstJordan_rank_eq_one
            H' hH' hcount htwo hrank'
        have hgap := hH'.2
          (show (⟨0, hcount⟩ :
              Fin (b.firstJordanAdaptedComplementCount J hA ht)) <
            ⟨1, htwo⟩ by simp)
        change
            0 < ordUnit K (H'.normGenerator ⟨1, htwo⟩) -
              ordUnit K (H'.normGenerator ⟨0, hcount⟩) ∧ _ at hgap
        rw [hnorm'] at hgap
        rw [← hshift] at hgap
        rw [horder] at hgap
        omega
      · have HWraw :
            {G : Lattice.JordanDecomposition
                (D.splitting.component 1).space
                (D.splitting.component 1).lattice
                (b.firstJordanAdaptedComplementCount J hA ht) //
              G.HasPropertyA} := ⟨H, hH⟩
        rw [hD] at HWraw
        change
          {G : Lattice.JordanDecomposition
              (q.orthogonalSpace b.head b.head_isAnisotropic) N
              (b.firstJordanAdaptedComplementCount J hA ht) //
            G.HasPropertyA} at HWraw
        have hcount : 0 < b.firstJordanAdaptedComplementCount J hA ht :=
          c.jordanCount_pos_of_bong_positive_length HWraw.1
        let i0 : Fin (b.firstJordanAdaptedComplementCount J hA ht) :=
          ⟨0, hcount⟩
        have hgapRaw :=
          b.firstJordanAdaptedUnary_cross_gaps_of_noCollision
            J hA ht hUnary hcollision i0
        change
          b.order 0 < ordUnit K (H.normGenerator i0) ∧
            b.order 0 <
              2 * ordUnit K (H.scaleGenerator i0) -
                ordUnit K (H.normGenerator i0) at hgapRaw
        have HWGapRaw :
            {G : Lattice.JordanDecomposition
                (D.splitting.component 1).space
                (D.splitting.component 1).lattice
                (b.firstJordanAdaptedComplementCount J hA ht) //
              G.HasPropertyA ∧
                (b.order 0 < ordUnit K (G.normGenerator i0) ∧
                  b.order 0 <
                    2 * ordUnit K (G.scaleGenerator i0) -
                      ordUnit K (G.normGenerator i0))} :=
          ⟨H, hH, hgapRaw⟩
        rw [hD] at HWGapRaw
        change
          {G : Lattice.JordanDecomposition
              (q.orthogonalSpace b.head b.head_isAnisotropic) N
              (b.firstJordanAdaptedComplementCount J hA ht) //
            G.HasPropertyA ∧
              (b.order 0 < ordUnit K (G.normGenerator i0) ∧
                b.order 0 <
                  2 * ordUnit K (G.scaleGenerator i0) -
                    ordUnit K (G.normGenerator i0))} at HWGapRaw
        let H' := HWGapRaw.1
        have hH' : H'.HasPropertyA := HWGapRaw.2.1
        have hgap := HWGapRaw.2.2
        have hthreshold :=
          c.threshold_lt_order_one_of_firstJordan_norm_dual_gt
            H' hH' hcount (b.order 0) hgap.1 hgap.2
        rw [horder] at hthreshold
        exact hthreshold
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      exact False.elim (by
        have : ¬D.IsUnary := by
          rw [hD]
          exact Lattice.Beli2019Lemma51BlockData.not_isUnary_binary
            z y hz hy hcongruent hzy hleft hright hpairZ hpairY
        exact this hUnary)

/-- In the binary adapted-block branch, transport the recursive tail to the
residual-line product.  Its first Jordan component has rank one, so the next
tail order is the norm order of the first old complement component, which is
strictly larger than the original head order. -/
theorem order_zero_lt_order_two_of_firstJordanAdaptedBlock_isBinary
    [FiniteDimensional K V]
    (b : BONG V q L (n + 3))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hBinary : (b.firstJordanAdaptedBlockData J hA ht).IsBinary) :
    b.order 0 < b.order 2 := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  let C := D.splitting.component 1
  let xD := b.firstJordanAdaptedHeadInBlock J hA ht
  let hxD := b.firstJordanAdaptedHeadInBlock_isAnisotropic J hA ht
  let qR := D.component.space.orthogonalSpace xD hxD
  let LR := D.component.lattice.projectedLattice D.component.space xD hxD
  let E := b.firstJordanAdaptedProjectionProductIsometry J hA ht
  let c := b.tail.mapLatticeIsometry E
  let TW := b.firstJordanAdaptedBinaryProductJordanWitness J hA ht hBinary
  let T := TW.1
  have hT : T.HasPropertyA := TW.2
  have hfirst : finrank K (T.component 0).carrier = 1 := by
    simpa only [T, TW] using
      b.firstJordanAdaptedBinaryProductJordanWitness_firstRank
        J hA ht hBinary
  have hTpos : 0 < b.firstJordanAdaptedComplementCount J hA ht + 1 := by
    omega
  have htwo : 1 < b.firstJordanAdaptedComplementCount J hA ht + 1 :=
    c.one_lt_jordanCount_of_bong_length_at_least_two_and_first_rank_one
      T hTpos hfirst
  have hcount : 0 < b.firstJordanAdaptedComplementCount J hA ht := by
    omega
  let i0 : Fin (b.firstJordanAdaptedComplementCount J hA ht) :=
    ⟨0, hcount⟩
  let i1 : Fin (b.firstJordanAdaptedComplementCount J hA ht + 1) :=
    ⟨1, htwo⟩
  have hi1 : i1 = i0.succ := by
    apply Fin.ext
    rfl
  have hshift :=
    c.order_one_eq_secondJordanNorm_of_firstJordan_rank_eq_one
      T hT hTpos htwo hfirst
  change c.order 1 = ordUnit K (T.normGenerator i1) at hshift
  have hnorm : ordUnit K (T.normGenerator i1) =
      ordUnit K
        ((b.firstJordanAdaptedComplementJordan J hA ht).normGenerator i0) := by
    rw [hi1]
    have hgen :=
      b.firstJordanAdaptedBinaryProductJordanWitness_normGenerator_succ
        J hA ht hBinary i0
    change T.normGenerator i0.succ =
      (b.firstJordanAdaptedComplementJordan J hA ht).normGenerator i0 at hgen
    exact congrArg (ordUnit K) hgen
  have hgap := (b.firstJordanAdaptedBinary_cross_gaps
    J hA ht hBinary i0).1
  have horder : c.order 1 = b.order 2 := by
    calc
      c.order 1 = b.tail.order 1 := by
        simp only [c, order_mapLatticeIsometry]
      _ = b.order 2 := b.order_tail 1
  rw [hshift, hnorm] at horder
  change b.order 0 <
    ordUnit K
      ((b.firstJordanAdaptedComplementJordan J hA ht).normGenerator i0)
    at hgap
  rw [horder] at hgap
  exact hgap

/-- The first two-step strict inequality is independent of which exact block
is selected by the adapted form of Lemma 5.1. -/
theorem order_zero_lt_order_two_of_hasJordanPropertyA
    [FiniteDimensional K V]
    (b : BONG V q L (n + 3))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    b.order 0 < b.order 2 := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  rcases D.isUnary_or_isBinary with hUnary | hBinary
  · exact b.order_zero_lt_order_two_of_firstJordanAdaptedBlock_isUnary
      J hA ht (by simpa only [D] using hUnary)
  · exact b.order_zero_lt_order_two_of_firstJordanAdaptedBlock_isBinary
      J hA ht (by simpa only [D] using hBinary)

/-- Every BONG on a property-A Jordan lattice has the strict two-step order
property.  The first comparison is the adapted-block theorem above; all
remaining comparisons follow recursively from the projected tail lattice. -/
theorem hasPropertyA_of_jordanPropertyA_succ
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    b.HasPropertyA := by
  induction n using Nat.strong_induction_on generalizing V t with
  | h n ih =>
      by_cases hsmall : n + 1 ≤ 2
      · exact b.hasPropertyA_of_length_le_two hsmall
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 :=
          ⟨n - 2, by omega⟩
        intro i hi
        by_cases hiZero : i.val = 0
        · have hfirst := b.order_zero_lt_order_two_of_hasJordanPropertyA
            J hA ht
          have hizero : i = 0 := by
            apply Fin.ext
            exact hiZero
          subst i
          have hidx :
              (⟨(0 : Fin (k + 3)).val + 2, hi⟩ : Fin (k + 3)) = 2 := by
            apply Fin.ext
            rfl
          rw [hidx]
          exact hfirst
        · have hiPos : 0 < i.val := by omega
          let j : Fin (k + 2) := ⟨i.val - 1, by omega⟩
          have hjbound : j.val + 2 < k + 2 := by
            change i.val - 1 + 2 < k + 2
            omega
          rcases b.tailLattice_hasJordanPropertyA J hA ht with
            ⟨s, H, hH⟩
          have hs : 0 < s :=
            b.tail.jordanCount_pos_of_bong_positive_length H
          have htail : b.tail.HasPropertyA :=
            ih (k + 1) (by omega) b.tail H hH hs
          have hj := htail j hjbound
          let j2 : Fin (k + 2) := ⟨j.val + 2, hjbound⟩
          have hji : j.succ = i := by
            apply Fin.ext
            change i.val - 1 + 1 = i.val
            omega
          have hj2i : j2.succ =
              (⟨i.val + 2, hi⟩ : Fin (k + 3)) := by
            apply Fin.ext
            change (i.val - 1 + 2) + 1 = i.val + 2
            omega
          change b.tail.order j < b.tail.order j2 at hj
          rw [b.order_tail j, b.order_tail j2, hji, hj2i] at hj
          exact hj

/-- The unique empty Jordan decomposition of a zero-dimensional lattice. -/
noncomputable def emptyJordanDecomposition_of_finrank_eq_zero
    [FiniteDimensional K V]
    (hfin : finrank K V = 0) :
    Lattice.JordanDecomposition q L 0 where
  component := Fin.elim0
  orthogonal := by
    intro i
    exact Fin.elim0 i
  sum_eq := by
    simp only [iSup_of_empty]
    apply le_antisymm
    · exact bot_le
    · intro x hx
      have hx0 : x = 0 := (finrank_zero_iff_forall_zero.mp hfin) x
      simpa [hx0]
  scaleGenerator := Fin.elim0
  normGenerator := Fin.elim0
  modular := fun i ↦ Fin.elim0 i
  scaleIdeal_eq := fun i ↦ Fin.elim0 i
  normIdeal_eq := fun i ↦ Fin.elim0 i
  scaleOrder_strict := by
    intro i
    exact Fin.elim0 i

/-- The empty decomposition satisfies property A vacuously. -/
theorem emptyJordanDecomposition_of_finrank_eq_zero_hasPropertyA
    [FiniteDimensional K V]
    (hfin : finrank K V = 0) :
    (emptyJordanDecomposition_of_finrank_eq_zero
      (q := q) (L := L) hfin).HasPropertyA := by
  constructor
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

/-- Unconditional Jordan-to-coordinate direction of Beli (2003), Lemma
4.1(ii) and Corollary 4.2(i). -/
theorem hasPropertyA_of_hasJordanPropertyA
    [FiniteDimensional K V]
    (b : BONG V q L n)
    (hL : Lattice.HasJordanPropertyA q L) :
    b.HasPropertyA := by
  by_cases hn : n = 0
  · subst n
    exact b.hasPropertyA_of_length_le_two (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, by omega⟩
    rcases hL with ⟨t, J, hJ⟩
    have ht : 0 < t := b.jordanCount_pos_of_bong_positive_length J
    exact b.hasPropertyA_of_jordanPropertyA_succ J hJ ht

/-- Coordinate property A implies the lattice Jordan condition also in the
zero-rank boundary case. -/
theorem hasJordanPropertyA_of_hasPropertyA
    [FiniteDimensional K V]
    (b : BONG V q L n) (hA : b.HasPropertyA) :
    Lattice.HasJordanPropertyA q L := by
  by_cases hn : n = 0
  · subst n
    have hfin : finrank K V = 0 := b.length_eq_finrank.symm
    exact ⟨0, emptyJordanDecomposition_of_finrank_eq_zero
      (q := q) (L := L) hfin,
      emptyJordanDecomposition_of_finrank_eq_zero_hasPropertyA
        (q := q) (L := L) hfin⟩
  · exact b.hasJordanPropertyA_of_hasPropertyA_of_length_pos hA
      (Nat.pos_of_ne_zero hn)

/-- Beli's Jordan property A is exactly the strict two-step condition for
every BONG, with no local-law parameter. -/
theorem hasJordanPropertyA_iff_hasPropertyA
    [FiniteDimensional K V]
    (b : BONG V q L n) :
    Lattice.HasJordanPropertyA q L ↔ b.HasPropertyA :=
  ⟨b.hasPropertyA_of_hasJordanPropertyA,
    b.hasJordanPropertyA_of_hasPropertyA⟩

/-- Beli (2003), Lemma 4.1(ii), now obtained unconditionally from the
Jordan-coordinate equivalence and the explicit consecutive-block
construction. -/
theorem propertyA_putTogether_proof
    (b : BONG V q L n) (hL : Lattice.HasJordanPropertyA q L) :
    ∃ (t : Nat) (J : Lattice.JordanDecomposition q L t),
      J.HasPropertyA ∧
        ∃ c : J.toOrthogonalDecomposition.ComponentBONGFamily,
          b.IsPutTogether J.toOrthogonalDecomposition c := by
  letI : Module.Finite K V := L.moduleFinite
  by_cases hn : n = 0
  · subst n
    have hfin : finrank K V = 0 := b.length_eq_finrank.symm
    let J := emptyJordanDecomposition_of_finrank_eq_zero
      (q := q) (L := L) hfin
    have hJ : J.HasPropertyA :=
      emptyJordanDecomposition_of_finrank_eq_zero_hasPropertyA
        (q := q) (L := L) hfin
    let c : J.toOrthogonalDecomposition.ComponentBONGFamily :=
      fun i ↦ Fin.elim0 i
    let e : Fin 0 ≃
        Σ i : Fin 0,
          Fin (J.toOrthogonalDecomposition.componentRank i) :=
      { toFun := fun i ↦ Fin.elim0 i
        invFun := fun a ↦ Fin.elim0 a.1
        left_inv := fun i ↦ Fin.elim0 i
        right_inv := fun a ↦ Fin.elim0 a.1 }
    refine ⟨0, J, hJ, c, ⟨{
      indexEquiv := e
      order_iff := ?_
      ambientVector_eq := ?_
    }⟩⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  · have hbA : b.HasPropertyA := b.hasPropertyA_of_hasJordanPropertyA hL
    rcases b.exists_propertyAJordanWitness_of_hasPropertyA hbA
        (Nat.pos_of_ne_zero hn) with ⟨T⟩
    exact ⟨T.blockCount + 1, T.jordan, T.propertyA,
      T.componentBONG, T.putTogether⟩

/-- The former Jordan-coordinate law interface is now discharged by the
unconditional proof. -/
noncomputable instance beli2003JordanCoordinateLaws :
    BONGJordanCoordinateLaws.{u, v} K where
  propertyA_coordinates := by
    intro V instAdd instModule q L n b
    letI : Module.Finite K V := L.moduleFinite
    exact b.hasJordanPropertyA_iff_hasPropertyA

/-- All three fields of Beli's Section 4 interface are now theorems. -/
noncomputable instance beliSectionFourLawsProved :
    BeliSectionFourLaws.{u, v} K where
  maximalNorm_putTogether := BONG.maximalNorm_putTogether_proof
  propertyA_putTogether := BONG.propertyA_putTogether_proof
  maximalNorm_putTogether_isGood :=
    BONG.maximalNorm_putTogether_isGood_proof

end BONG

end Bong
