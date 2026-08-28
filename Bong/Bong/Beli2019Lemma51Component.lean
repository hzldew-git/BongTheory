/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma51Input
import Bong.Lattice.ModularCriterion
import Bong.Lattice.ModularVolume

/-!
# Beli (2019), Lemma 5.1: the enlarged modular component

The adapted unary or binary block selected in `Beli2019Lemma51Block` is
enlarged by dividing its distinguished integral vector by the uniformizer.
This file proves the remaining local assertions of Lemma 5.1: the volume
drops by two, the enlarged block is modular, and its scale drops by two in
rank one and by one in rank two.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

variable {q : QuadraticSpace K V} {L : Lattice K V} {x : V}

namespace Beli2019Lemma51BlockData

/-- The integral lattice obtained by dividing the distinguished block vector
by the uniformizer. -/
noncomputable def enlargedLattice (D : Beli2019Lemma51BlockData q L x) :
    Lattice K D.component.carrier :=
  adjoinVector D.component.lattice
    ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • D.carrierRepresentative)

/-- The scale generator predicted by Lemma 5.1 for the enlarged block. -/
noncomputable def enlargedScaleGenerator
    (D : Beli2019Lemma51BlockData q L x) : Kˣ :=
  match D with
  | .unary z _ _ hz _ =>
      Units.mk0 (q.quadratic z) hz * (uniformizerUnit K)⁻¹ ^ 2
  | .binary z y _ _ _ hzy _ _ _ _ =>
      Units.mk0 (q.bilin z y) hzy * (uniformizerUnit K)⁻¹

/-- The two scale alternatives in Lemma 5.1.  Enlarging a unary selected
block lowers its scale order by two, while enlarging a binary selected block
lowers its scale order by one. -/
theorem componentRank_and_enlargedScaleOrder
    (D : Beli2019Lemma51BlockData q L x) :
    (finrank K D.component.carrier = 1 ∧
        ordUnit K D.enlargedScaleGenerator =
          ordUnit K D.scaleGenerator - 2) ∨
      (finrank K D.component.carrier = 2 ∧
        ordUnit K D.enlargedScaleGenerator =
          ordUnit K D.scaleGenerator - 1) := by
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    simpa [uniformizerPowerUnit] using
      (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
  cases D with
  | unary z hz hcongruent hanisotropic hpairing =>
      left
      constructor
      · change finrank K (K ∙ z) = 1
        simpa using Module.finrank_eq_card_basis
          (unarySpanBasis (K := K) z hanisotropic.ne_zero)
      · simp only [enlargedScaleGenerator, scaleGenerator, ordUnit_mul,
          ordUnit_pow, ordUnit_inv, hpi]
        omega
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      right
      constructor
      · change finrank K (BONG.binaryPairSpan (K := K) z y) = 2
        simpa using Module.finrank_eq_card_basis
          (BONG.binaryPairBasis (K := K) z y
            (binaryPair_linearIndependent_of_left_strict hzy hleft hright))
      · simp only [enlargedScaleGenerator, scaleGenerator, ordUnit_mul,
          ordUnit_inv, hpi]
        omega

/-- Enlarging the selected block by one inverse-uniformizer vector lowers its
volume order by exactly two. -/
theorem volumeOrder_enlargedLattice
    (D : Beli2019Lemma51BlockData q L x) :
    volumeOrder D.component.space D.enlargedLattice =
      volumeOrder D.component.space D.component.lattice - 2 := by
  cases D with
  | unary z hz hcongruent hanisotropic hpairing =>
      let b := unarySpanBasis (K := K) z hanisotropic.ne_zero
      have hhead :
          (Beli2019Lemma51BlockData.carrierRepresentative
              (.unary z hz hcongruent hanisotropic hpairing) : K ∙ z) = b 0 := by
        apply Subtype.ext
        exact (coe_unarySpanBasis (K := K) z hanisotropic.ne_zero 0).symm
      unfold enlargedLattice component
      rw [hhead]
      change volumeOrder
          (q.restrict (K ∙ z) (unarySpan_restrict_nondegenerate hanisotropic))
          (adjoinVector (basisLattice b)
            ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • b 0)) =
        volumeOrder
          (q.restrict (K ∙ z) (unarySpan_restrict_nondegenerate hanisotropic))
          (basisLattice b) - 2
      rw [adjoin_basisLattice_uniformizerInv_eq]
      exact volumeOrder_basisLattice_uniformizerInvScaleBasisAt _ b 0
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      let hli := binaryPair_linearIndependent_of_left_strict hzy hleft hright
      let hnondeg := binaryPair_restrict_nondegenerate_of_left_strict
        hzy hleft hright
      let b := BONG.binaryPairBasis (K := K) z y hli
      have hhead :
          (Beli2019Lemma51BlockData.carrierRepresentative
              (.binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY) :
                BONG.binaryPairSpan (K := K) z y) = b 0 := by
        apply Subtype.ext
        change z = (b 0 : V)
        rw [BONG.coe_binaryPairBasis, BONG.binaryPairFamily_zero]
      unfold enlargedLattice component
      rw [hhead]
      change volumeOrder
          (q.restrict (BONG.binaryPairSpan (K := K) z y) hnondeg)
          (adjoinVector (basisLattice b)
            ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • b 0)) =
        volumeOrder
          (q.restrict (BONG.binaryPairSpan (K := K) z y) hnondeg)
          (basisLattice b) - 2
      rw [adjoin_basisLattice_uniformizerInv_eq]
      exact volumeOrder_basisLattice_uniformizerInvScaleBasisAt _ b 0

private theorem scaleIdeal_uniformizerInv_binaryPairBasis_le
    (z y : V) (hzy : q.bilin z y ≠ 0)
    (hleft : ord K (q.bilin z y) < ord K (q.quadratic z))
    (hright : ord K (q.bilin z y) ≤ ord K (q.quadratic y)) :
    let hli := binaryPair_linearIndependent_of_left_strict hzy hleft hright
    let hnondeg := binaryPair_restrict_nondegenerate_of_left_strict
      hzy hleft hright
    let b := BONG.binaryPairBasis (K := K) z y hli
    scaleIdeal
        (q.restrict (BONG.binaryPairSpan (K := K) z y) hnondeg)
        (basisLattice (uniformizerInvScaleBasisAt b 0)) ≤
      principalIdeal (K := K)
        (((Units.mk0 (q.bilin z y) hzy *
          (uniformizerUnit K)⁻¹ : Kˣ) : K)) := by
  dsimp only
  let d : Kˣ := Units.mk0 (q.bilin z y) hzy
  let pi : Kˣ := uniformizerUnit K
  let hli := binaryPair_linearIndependent_of_left_strict hzy hleft hright
  let b := BONG.binaryPairBasis (K := K) z y hli
  have hpi : ordUnit K pi = 1 := by
    simpa [pi, uniformizerPowerUnit] using
      (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
  have hbzero : (b 0 : V) = z := by
    rw [BONG.coe_binaryPairBasis, BONG.binaryPairFamily_zero]
  have hbone : (b 1 : V) = y := by
    rw [BONG.coe_binaryPairBasis, BONG.binaryPairFamily_one]
  have hcZero :
      ((uniformizerInvScaleBasisAt b 0 0 :
        BONG.binaryPairSpan (K := K) z y) : V) =
        ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • z) := by
    rw [uniformizerInvScaleBasisAt_apply_same]
    change (((uniformizerUnit K)⁻¹ : Kˣ) : K) • (b 0 : V) = _
    rw [hbzero]
  have hcOne :
      ((uniformizerInvScaleBasisAt b 0 1 :
        BONG.binaryPairSpan (K := K) z y) : V) = y := by
    rw [uniformizerInvScaleBasisAt_apply_of_ne b (by decide)]
    exact hbone
  apply scaleIdeal_basisLattice_le_of_basis _
    (uniformizerInvScaleBasisAt b 0) _
  intro i j
  change q.bilin
      ((uniformizerInvScaleBasisAt b 0 i :
        BONG.binaryPairSpan (K := K) z y) : V)
      ((uniformizerInvScaleBasisAt b 0 j :
        BONG.binaryPairSpan (K := K) z y) : V) ∈ _
  have hi : i = 0 ∨ i = 1 := by
    have hval : i.val = 0 ∨ i.val = 1 := by omega
    rcases hval with hval | hval
    · exact Or.inl (Fin.ext hval)
    · exact Or.inr (Fin.ext hval)
  have hj : j = 0 ∨ j = 1 := by
    have hval : j.val = 0 ∨ j.val = 1 := by omega
    rcases hval with hval | hval
    · exact Or.inl (Fin.ext hval)
    · exact Or.inr (Fin.ext hval)
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · rw [hcZero]
    change q.quadratic ((((pi⁻¹ : Kˣ) : K)) • z) ∈
      principalIdeal (K := K) (((d * pi⁻¹ : Kˣ) : K))
    by_cases hz : q.quadratic z = 0
    · rw [q.quadratic_smul, hz, mul_zero]
      exact Submodule.zero_mem _
    · let az : Kˣ := Units.mk0 (q.quadratic z) hz
      have hleftInt : ordUnit K d < ordUnit K az := by
        apply WithTop.coe_lt_coe.mp
        simpa [d, az] using hleft
      have horderInt :
          ordUnit K (d * pi⁻¹) ≤ ordUnit K ((pi⁻¹) ^ 2 * az) := by
        simp only [ordUnit_mul, ordUnit_inv, ordUnit_pow, hpi]
        omega
      apply mem_principalIdeal_of_ord_le (Units.ne_zero (d * pi⁻¹))
      calc
        ord K (((d * pi⁻¹ : Kˣ) : K)) =
            ((ordUnit K (d * pi⁻¹) : Int) : WithTop Int) :=
          (coe_ordUnit K (d * pi⁻¹)).symm
        _ ≤ ((ordUnit K ((pi⁻¹) ^ 2 * az) : Int) : WithTop Int) :=
          WithTop.coe_le_coe.mpr horderInt
        _ = ord K ((((pi⁻¹) ^ 2 * az : Kˣ) : K)) :=
          coe_ordUnit K ((pi⁻¹) ^ 2 * az)
        _ = ord K (q.quadratic ((((pi⁻¹ : Kˣ) : K)) • z)) := by
          congr 1
          simp [az, pi, q.quadratic_smul]
  · rw [hcZero, hcOne]
    change q.bilin ((((pi⁻¹ : Kˣ) : K)) • z) y ∈
      principalIdeal (K := K) (((d * pi⁻¹ : Kˣ) : K))
    have heq : q.bilin ((((pi⁻¹ : Kˣ) : K)) • z) y =
        ((d * pi⁻¹ : Kˣ) : K) := by
      rw [LinearMap.BilinForm.smul_left]
      change ((pi⁻¹ : Kˣ) : K) * q.bilin z y =
        q.bilin z y * ((pi⁻¹ : Kˣ) : K)
      exact mul_comm _ _
    rw [heq]
    exact generator_mem_principalIdeal _
  · rw [hcZero, hcOne]
    change q.bilin y ((((pi⁻¹ : Kˣ) : K)) • z) ∈
      principalIdeal (K := K) (((d * pi⁻¹ : Kˣ) : K))
    rw [q.isSymm.eq y]
    have heq : q.bilin ((((pi⁻¹ : Kˣ) : K)) • z) y =
        ((d * pi⁻¹ : Kˣ) : K) := by
      rw [LinearMap.BilinForm.smul_left]
      change ((pi⁻¹ : Kˣ) : K) * q.bilin z y =
        q.bilin z y * ((pi⁻¹ : Kˣ) : K)
      exact mul_comm _ _
    rw [heq]
    exact generator_mem_principalIdeal _
  · rw [hcOne]
    change q.quadratic y ∈
      principalIdeal (K := K) (((d * pi⁻¹ : Kˣ) : K))
    by_cases hy : q.quadratic y = 0
    · rw [hy]
      exact Submodule.zero_mem _
    · let ay : Kˣ := Units.mk0 (q.quadratic y) hy
      have hrightInt : ordUnit K d ≤ ordUnit K ay := by
        apply WithTop.coe_le_coe.mp
        simpa [d, ay] using hright
      have horderInt : ordUnit K (d * pi⁻¹) ≤ ordUnit K ay := by
        simp only [ordUnit_mul, ordUnit_inv, hpi]
        omega
      apply mem_principalIdeal_of_ord_le (Units.ne_zero (d * pi⁻¹))
      calc
        ord K (((d * pi⁻¹ : Kˣ) : K)) =
            ((ordUnit K (d * pi⁻¹) : Int) : WithTop Int) :=
          (coe_ordUnit K (d * pi⁻¹)).symm
        _ ≤ ((ordUnit K ay : Int) : WithTop Int) :=
          WithTop.coe_le_coe.mpr horderInt
        _ = ord K (q.quadratic y) := by
          simpa [ay] using coe_ordUnit K ay

private theorem uniformizerInv_binaryPairBasis_isModular
    (z y : V) (hzy : q.bilin z y ≠ 0)
    (hleft : ord K (q.bilin z y) < ord K (q.quadratic z))
    (hright : ord K (q.bilin z y) ≤ ord K (q.quadratic y)) :
    let hli := binaryPair_linearIndependent_of_left_strict hzy hleft hright
    let hnondeg := binaryPair_restrict_nondegenerate_of_left_strict
      hzy hleft hright
    let b := BONG.binaryPairBasis (K := K) z y hli
    IsModular
      (q.restrict (BONG.binaryPairSpan (K := K) z y) hnondeg)
      (basisLattice (uniformizerInvScaleBasisAt b 0))
      (Units.mk0 (q.bilin z y) hzy * (uniformizerUnit K)⁻¹) := by
  dsimp only
  let d : Kˣ := Units.mk0 (q.bilin z y) hzy
  let pi : Kˣ := uniformizerUnit K
  let hli := binaryPair_linearIndependent_of_left_strict hzy hleft hright
  let b := BONG.binaryPairBasis (K := K) z y hli
  apply isModular_of_scaleIdeal_le_of_volumeOrder_eq
  · exact scaleIdeal_uniformizerInv_binaryPairBasis_le z y
      hzy hleft hright
  · rw [volumeOrder_basisLattice_uniformizerInvScaleBasisAt,
      volumeOrder_binaryPairBasis_eq_two_mul_ordUnit_of_left_strict
        hzy hleft hright]
    have hfin : finrank K (BONG.binaryPairSpan (K := K) z y) = 2 := by
      simpa using Module.finrank_eq_card_basis b
    have hpi : ordUnit K pi = 1 := by
      simpa [pi, uniformizerPowerUnit] using
        (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
    rw [hfin]
    change 2 * ordUnit K d - 2 = 2 * ordUnit K (d * pi⁻¹)
    rw [ordUnit_mul, ordUnit_inv, hpi]
    omega
/-- In the unary case, the enlargement is global inverse-uniformizer
rescaling of the original block. -/
theorem enlargedLattice_eq_rescale_of_unary
    (z : V) (hz : z ∈ L)
    (hcongruent : x - z ∈ rescale (uniformizerUnit K) L)
    (hanisotropic : q.IsAnisotropic z)
    (hpairing : ∀ w : V, w ∈ L →
      q.bilin z w ∈ principalIdeal (K := K) (q.quadratic z)) :
    let D : Beli2019Lemma51BlockData q L x :=
      .unary z hz hcongruent hanisotropic hpairing
    D.enlargedLattice =
      rescale (uniformizerUnit K)⁻¹ D.component.lattice := by
  intro D
  let b := unarySpanBasis (K := K) z hanisotropic.ne_zero
  have hhead :
      (D.carrierRepresentative : K ∙ z) = b 0 := by
    apply Subtype.ext
    exact (coe_unarySpanBasis (K := K) z hanisotropic.ne_zero 0).symm
  unfold enlargedLattice component
  rw [hhead]
  change adjoinVector (basisLattice b)
      ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • b 0) =
    rescale (uniformizerUnit K)⁻¹ (basisLattice b)
  exact adjoin_basisLattice_uniformizerInv_fin_one_eq_rescale b

/-- In rank one, the enlarged block is modular at scale `a π⁻²`. -/
theorem enlargedLattice_isModular_of_unary
    (z : V) (hz : z ∈ L)
    (hcongruent : x - z ∈ rescale (uniformizerUnit K) L)
    (hanisotropic : q.IsAnisotropic z)
    (hpairing : ∀ w : V, w ∈ L →
      q.bilin z w ∈ principalIdeal (K := K) (q.quadratic z)) :
    let D : Beli2019Lemma51BlockData q L x :=
      .unary z hz hcongruent hanisotropic hpairing
    IsModular D.component.space D.enlargedLattice
      D.enlargedScaleGenerator := by
  intro D
  rw [enlargedLattice_eq_rescale_of_unary z hz hcongruent
    hanisotropic hpairing]
  exact D.component_modular.rescale (uniformizerUnit K)⁻¹

/-- In rank two, the enlarged block is modular at scale `a π⁻¹`.
The diagonal entries are divisible by this new scale, while the mixed entry
is a generator; the volume calculation then gives equality with the dual. -/
theorem enlargedLattice_isModular_of_binary
    (z y : V) (hz : z ∈ L) (hy : y ∈ L)
    (hcongruent : x - z ∈ rescale (uniformizerUnit K) L)
    (hzy : q.bilin z y ≠ 0)
    (hleft : ord K (q.bilin z y) < ord K (q.quadratic z))
    (hright : ord K (q.bilin z y) ≤ ord K (q.quadratic y))
    (hpairZ : ∀ w : V, w ∈ L →
      q.bilin z w ∈ principalIdeal (K := K) (q.bilin z y))
    (hpairY : ∀ w : V, w ∈ L →
      q.bilin y w ∈ principalIdeal (K := K) (q.bilin z y)) :
    let D : Beli2019Lemma51BlockData q L x :=
      .binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY
    IsModular D.component.space D.enlargedLattice
      D.enlargedScaleGenerator := by
  intro D
  subst D
  let hli := binaryPair_linearIndependent_of_left_strict hzy hleft hright
  let b := BONG.binaryPairBasis (K := K) z y hli
  have hhead :
      ((Beli2019Lemma51BlockData.carrierRepresentative
          (.binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY) :
            BONG.binaryPairSpan (K := K) z y)) = b 0 := by
    apply Subtype.ext
    change z = (b 0 : V)
    rw [BONG.coe_binaryPairBasis, BONG.binaryPairFamily_zero]
  change IsModular (asymmetricBinaryScaleComponent hzy hleft hright).space
    (adjoinVector (asymmetricBinaryScaleComponent hzy hleft hright).lattice
      ((((uniformizerUnit K)⁻¹ : Kˣ) : K) •
        (Beli2019Lemma51BlockData.carrierRepresentative
          (.binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY))))
    (Units.mk0 (q.bilin z y) hzy * (uniformizerUnit K)⁻¹)
  rw [hhead]
  change IsModular
    (q.restrict (BONG.binaryPairSpan (K := K) z y)
      (binaryPair_restrict_nondegenerate_of_left_strict hzy hleft hright))
    (adjoinVector (basisLattice b)
      ((((uniformizerUnit K)⁻¹ : Kˣ) : K) •
        (BONG.binaryPairBasis (K := K) z y hli) 0))
    (Units.mk0 (q.bilin z y) hzy * (uniformizerUnit K)⁻¹)
  rw [adjoin_basisLattice_uniformizerInv_eq]
  exact uniformizerInv_binaryPairBasis_isModular z y hzy hleft hright

/-- Both alternatives in Beli's Lemma 5.1 produce the asserted enlarged
modular component, with the rank-dependent scale generator. -/
theorem enlargedLattice_isModular
    (D : Beli2019Lemma51BlockData q L x) :
    IsModular D.component.space D.enlargedLattice
      D.enlargedScaleGenerator := by
  cases D with
  | unary z hz hcongruent hanisotropic hpairing =>
      exact enlargedLattice_isModular_of_unary z hz hcongruent
        hanisotropic hpairing
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      exact enlargedLattice_isModular_of_binary z y hz hy hcongruent
        hzy hleft hright hpairZ hpairY

end Beli2019Lemma51BlockData

namespace Beli2019Lemma51InputData

variable {q : QuadraticSpace K V} {M N : Lattice K V}

/-- The component called `J'` in Lemma 5.1 is the enlarged block just
constructed above. -/
theorem enlargedComponent_lattice_eq_block
    (D : Beli2019Lemma51InputData q M N) :
    D.enlargedComponent.lattice = D.block.enlargedLattice :=
  rfl

/-- The enlarged component in the large-lattice splitting is modular at the
rank-dependent scale predicted in Lemma 5.1. -/
theorem enlargedComponent_isModular
    (D : Beli2019Lemma51InputData q M N) :
    IsModular D.enlargedComponent.space D.enlargedComponent.lattice
      D.block.enlargedScaleGenerator := by
  exact D.block.enlargedLattice_isModular

end Beli2019Lemma51InputData

end Lattice

end Bong
