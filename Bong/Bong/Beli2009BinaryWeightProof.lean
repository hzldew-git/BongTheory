/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2009WeightIdealProof
import Bong.Bong.Beli2009OrthogonalIdealProof
import Bong.Bong.BinaryAdaptedValues
import Bong.Bong.BinaryDualModular
import Bong.Bong.Beli2009BinaryRemarks
import Bong.Bong.ResidueDefectProductProof

/-!
# The binary weight calculation in Beli (2009), Lemma 2.14

This module proves the scaled form of O'Meara 93:10 needed for the
strictly decreasing binary base case.  A shear of the adapted binary basis
puts its second diagonal value in the weight ideal.  The normalized Gram
determinant represents the adjacent square class; parity then identifies its
quadratic defect exactly below the `2e` endpoint.
-/

namespace Bong

open Dyadic


universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice

variable [Beli2009WeightIdealData.{u, v} K]

theorem exists_quadratic_order_eq_weightIdealOrder_of_lt_twoScale
    (a : Kˣ) (ha : IsNormGeneratorValue q L a)
    (hlt : weightIdealOrder q L < canonicalTwoScaleOrder q L) :
    ∃ x : V, x ∈ L ∧ q.quadratic x ≠ 0 ∧
      ord K (q.quadratic x) =
        ((weightIdealOrder q L : Int) : WithTop Int) ∧
      Odd (ordUnit K a + weightIdealOrder q L) := by
  have hweight := weightIdealOrder_eq_canonicalWeightOrder a ha
  rcases canonicalWeightOffset_spec q L with hoff | hopp
  · have hsearch := canonicalWeightSearchBound_cast ha
    have hcanonical : canonicalWeightOrder q L =
        canonicalTwoScaleOrder q L := by
      rw [canonicalWeightOrder_eq ha, hoff]
      omega
    rw [hweight, hcanonical] at hlt
    exact (lt_irrefl _ hlt).elim
  · rcases hopp.2 with ⟨z, hzGroup, hzOrder⟩
    rcases hzGroup with ⟨x, hx, y, hy, hzy⟩
    have hyOrder : ((canonicalTwoScaleOrder q L : Int) : WithTop Int) ≤
        ord K y := by
      rw [twoScaleIdeal_eq_powerIdeal_canonicalTwoScaleOrder ha] at hy
      exact (mem_powerIdeal_iff _ _).1 hy
    have hzOrderField : ord K (z : K) =
        ((weightIdealOrder q L : Int) : WithTop Int) := by
      rw [← coe_ordUnit, hzOrder, ← canonicalWeightOrder_eq ha,
        ← hweight]
    have hzLtY : ord K (z : K) < ord K y := by
      rw [hzOrderField]
      exact lt_of_lt_of_le (by exact_mod_cast hlt) hyOrder
    have hq : q.quadratic x = (z : K) - y := by
      rw [hzy]
      ring
    have hqOrder : ord K (q.quadratic x) =
        ((weightIdealOrder q L : Int) : WithTop Int) := by
      rw [hq, (ord K).map_sub_eq_of_lt_left hzLtY, hzOrderField]
    have hqNe : q.quadratic x ≠ 0 := by
      intro hzero
      rw [hzero, ord_zero] at hqOrder
      exact WithTop.top_ne_coe hqOrder
    refine ⟨x, hx, hqNe, hqOrder, ?_⟩
    have hodd := odd_normOrder_add_canonicalWeightOrder_of_offset ha hopp
    rwa [← hweight] at hodd

end Lattice

namespace BONG

/-- In the strictly decreasing binary branch, the scalar which clears the
denominator of the second orthogonal BONG vector. -/
noncomputable def terminalMultiplierUnit (b : BONG V q L 2)
    (hstrict : b.order 1 < b.order 0) : Kˣ :=
  b.valueUnit 0 / b.binaryMixedPairingUnit hstrict

/-- Twice the order of the terminal multiplier is the binary order drop. -/
theorem two_mul_ordUnit_terminalMultiplierUnit
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    2 * ordUnit K (b.terminalMultiplierUnit hstrict) =
      b.order 0 - b.order 1 := by
  rw [terminalMultiplierUnit, div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
    ← b.order_eq_ordUnit 0]
  have hmixed :=
    b.two_mul_ordUnit_binaryMixedPairing_eq_order_add hstrict
  omega

/-- The terminal multiplier is integral. -/
theorem terminalMultiplierUnit_mem_integerRing
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    (b.terminalMultiplierUnit hstrict : K) ∈ IntegerRing K := by
  apply (mem_integerRing_iff K).2
  rw [Dyadic.IsIntegral, ← coe_ordUnit]
  exact_mod_cast (show 0 ≤ ordUnit K (b.terminalMultiplierUnit hstrict) by
    have hdrop := b.two_mul_ordUnit_terminalMultiplierUnit hstrict
    omega)

/-- The integral terminal vector obtained by clearing the denominator of the
second orthogonal BONG vector. -/
noncomputable def terminalNormVector (b : BONG V q L 2)
    (hstrict : b.order 1 < b.order 0) : V :=
  (b.terminalMultiplierUnit hstrict : K) • b.ambientVector 1

/-- The cleared terminal BONG vector belongs to the original binary lattice. -/
theorem terminalNormVector_mem
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    b.terminalNormVector hstrict ∈ L := by
  let s : K := b.terminalMultiplierUnit hstrict
  let sO : IntegerRing K :=
    ⟨s, b.terminalMultiplierUnit_mem_integerRing hstrict⟩
  have hprojection :
      q.orthogonalProjection b.head b.binarySecondVector =
        b.ambientVector 1 := by
    calc
      q.orthogonalProjection b.head b.binarySecondVector =
          (b.tail.head : V) := by
        simpa only [QuadraticSpace.projectionToOrthogonal_coe] using
          congrArg Subtype.val b.projectionToOrthogonal_binarySecondVector
      _ = (b.tail.ambientVector 0 : V) := by
        rw [b.tail.ambientVector_zero_eq_head]
      _ = b.ambientVector 1 := b.coe_ambientVector_tail 0
  have hcancel :
      s * (b.binaryMixedPairing / q.quadratic b.head) = 1 := by
    have hunit : b.terminalMultiplierUnit hstrict *
        b.binaryMixedPairingUnit hstrict = b.valueUnit 0 := by
      simp [terminalMultiplierUnit]
    have hprod : s * b.binaryMixedPairing = b.value 0 := by
      have hcoe := congrArg (fun u : Kˣ => (u : K)) hunit
      simpa only [s, Units.val_mul, b.coe_binaryMixedPairingUnit,
        b.coe_valueUnit] using hcoe
    rw [div_eq_mul_inv]
    calc
      s * (b.binaryMixedPairing * (q.quadratic b.head)⁻¹) =
          (s * b.binaryMixedPairing) * (q.quadratic b.head)⁻¹ := by ring
      _ = q.quadratic b.head * (q.quadratic b.head)⁻¹ := by
        rw [hprod, b.value_zero_eq_quadratic_head]
      _ = 1 := mul_inv_cancel₀ b.head_isAnisotropic
  have heq : b.terminalNormVector hstrict =
      s • b.binarySecondVector - b.head := by
    rw [terminalNormVector, ← hprojection,
      q.orthogonalProjection_apply, smul_sub, smul_smul]
    change s • b.binarySecondVector -
      (s * (b.binaryMixedPairing / q.quadratic b.head)) • b.head =
        s • b.binarySecondVector - b.head
    rw [hcancel, one_smul]
  rw [heq]
  exact L.sub_mem (L.smul_mem sO b.binarySecondVector_mem)
    b.head_isNormGenerator.mem

/-- The value of the cleared terminal vector is the terminal BONG value
multiplied by the square of the clearing scalar. -/
theorem quadratic_terminalNormVector
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    q.quadratic (b.terminalNormVector hstrict) =
      ((b.terminalMultiplierUnit hstrict ^ 2 * b.valueUnit 1 : Kˣ) : K) := by
  rw [terminalNormVector, q.quadratic_smul, b.quadratic_ambientVector]
  rfl

/-- The cleared terminal value has the norm order of the binary lattice. -/
theorem ordUnit_terminalValue_eq_order_zero
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    ordUnit K (b.terminalMultiplierUnit hstrict ^ 2 * b.valueUnit 1) =
      b.order 0 := by
  rw [ordUnit_mul, ordUnit_pow, ← b.order_eq_ordUnit 1]
  have hmult := b.two_mul_ordUnit_terminalMultiplierUnit hstrict
  omega

/-- Beli (2009), Lemma 2.13(iii), in the binary improper-modular case:
after multiplication by the canonical clearing square, the terminal BONG
value is represented by a norm generator of the binary lattice. -/
theorem terminalNormVector_isNormGenerator
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    Lattice.IsNormGenerator q L (b.terminalNormVector hstrict) := by
  refine ⟨b.terminalNormVector_mem hstrict, ?_⟩
  calc
    Lattice.normIdeal q L =
        Lattice.principalIdeal (K := K) (b.valueUnit 0 : K) := by
      simpa only [b.coe_valueUnit, b.value_zero_eq_quadratic_head] using
        b.head_isNormGenerator.normIdeal_eq
    _ = Lattice.principalIdeal (K := K)
        ((b.terminalMultiplierUnit hstrict ^ 2 * b.valueUnit 1 : Kˣ) : K) := by
      apply (Lattice.principalIdeal_eq_iff_ordUnit_eq
        (b.valueUnit 0)
        (b.terminalMultiplierUnit hstrict ^ 2 * b.valueUnit 1)).2
      rw [← b.order_eq_ordUnit 0]
      exact (b.ordUnit_terminalValue_eq_order_zero hstrict).symm
    _ = Lattice.principalIdeal (K := K)
        (q.quadratic (b.terminalNormVector hstrict)) := by
      rw [b.quadratic_terminalNormVector hstrict]

theorem valueUnit_zero_isNormGeneratorValue
    (b : BONG V q L (Nat.succ 1)) :
    Lattice.IsNormGeneratorValue q L (b.valueUnit 0) := by
  have h := b.head_isNormGenerator.isNormGeneratorValue
    b.head_isAnisotropic
  let a : Kˣ := Units.mk0 (q.quadratic b.head) b.head_isAnisotropic
  have ha : a = b.valueUnit 0 := by
    apply Units.ext
    change q.quadratic b.head = (b.valueUnit 0 : K)
    rw [← b.value_zero_eq_quadratic_head, b.coe_valueUnit]
  rw [← ha]
  exact h

variable [Beli2009WeightIdealData.{u, v} K]

theorem exists_weight_shear
    (b : BONG V q L 2) :
    ∃ c : IntegerRing K,
      let y := b.binarySecondVector + (c : K) • b.head
      y ∈ L ∧ q.quadratic y ∈ Lattice.weightIdeal q L ∧
        ∀ z : V, z ∈ L → ∃ r s : IntegerRing K,
          z = (r : K) • b.head + (s : K) • y := by
  let a : Kˣ := b.valueUnit 0
  have ha : Lattice.IsNormGeneratorValue q L a := by
    simpa [a] using b.valueUnit_zero_isNormGeneratorValue
  have hqGroup : q.quadratic b.binarySecondVector ∈
      Lattice.normGroupSet q L := by
    refine ⟨b.binarySecondVector, b.binarySecondVector_mem,
      0, Submodule.zero_mem _, ?_⟩
    simp
  rw [Lattice.normGroupSet_eq_integralSquareCoset_weightIdeal a ha]
      at hqGroup
  rcases hqGroup with ⟨c, eta, heta, hq⟩
  refine ⟨c, ?_, ?_, ?_⟩
  · exact L.add_mem b.binarySecondVector_mem
      (L.smul_mem c b.head_isNormGenerator.mem)
  · have hheadScale : q.quadratic b.head ∈ Lattice.scaleIdeal q L :=
      Lattice.bilin_mem_scaleIdeal_of_mem q L
        b.head_isNormGenerator.mem b.head_isNormGenerator.mem
    have hmixedScale : b.binaryMixedPairing ∈ Lattice.scaleIdeal q L :=
      Lattice.bilin_mem_scaleIdeal_of_mem q L
        b.head_isNormGenerator.mem b.binarySecondVector_mem
    have hheadTwo : (2 : K) * (c : K) ^ 2 * q.quadratic b.head ∈
        Lattice.twoScaleIdeal q L := by
      refine ⟨(c ^ 2) • q.quadratic b.head,
        (Lattice.scaleIdeal q L).smul_mem (c ^ 2) hheadScale, ?_⟩
      change (2 : K) * ((c : K) ^ 2 * q.quadratic b.head) = _
      ring
    have hmixedTwo : (2 : K) * (c : K) * b.binaryMixedPairing ∈
        Lattice.twoScaleIdeal q L := by
      refine ⟨c • b.binaryMixedPairing,
        (Lattice.scaleIdeal q L).smul_mem c hmixedScale, ?_⟩
      change (2 : K) * ((c : K) * b.binaryMixedPairing) = _
      ring
    have hheadWeight := Lattice.twoScaleIdeal_le_weightIdeal q L hheadTwo
    have hmixedWeight := Lattice.twoScaleIdeal_le_weightIdeal q L hmixedTwo
    have hsum := (Lattice.weightIdeal q L).add_mem
      ((Lattice.weightIdeal q L).add_mem hheadWeight heta) hmixedWeight
    rw [q.quadratic_add, q.quadratic_smul,
      LinearMap.BilinForm.smul_right, q.isSymm.eq b.binarySecondVector b.head,
      hq]
    simp only [a, b.coe_valueUnit, b.value_zero_eq_quadratic_head,
      binaryMixedPairing]
    unfold binaryMixedPairing at hsum
    convert hsum using 1 <;> ring
  · intro z hz
    rcases b.exists_binaryIntegralBasis_coefficients hz with ⟨r, s, hrs⟩
    refine ⟨r - s * c, s, ?_⟩
    rw [hrs]
    simp only [map_sub, map_mul, IsScalarTower.algebraMap_smul K,
      smul_add]
    module

theorem weightShear_mixedPairing
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0)
    (c : IntegerRing K) :
    let y := b.binarySecondVector + (c : K) • b.head
    ∃ s : Kˣ, (s : K) = q.bilin b.head y ∧
      2 * ordUnit K s = b.order 0 + b.order 1 := by
  let m := b.binaryMixedPairingUnit hstrict
  have hmOrder : ord K (m : K) =
      ((ordUnit K m : Int) : WithTop Int) := by
    rw [coe_ordUnit]
  have hcOrder : (0 : WithTop Int) ≤ ord K (c : K) :=
    (mem_integerRing_iff K).1 c.property
  have hheadOrder : ord K (q.quadratic b.head) =
      ((b.order 0 : Int) : WithTop Int) := by
    rw [← b.value_zero_eq_quadratic_head, ← b.coe_order]
  have hmLtHead : ordUnit K m < b.order 0 :=
    b.ordUnit_binaryMixedPairing_lt_order_zero hstrict
  have hmLtCorrection : ord K (m : K) <
      ord K ((c : K) * q.quadratic b.head) := by
    rw [hmOrder, ord_mul, hheadOrder]
    have hle : ((b.order 0 : Int) : WithTop Int) ≤
        ord K (c : K) + (b.order 0 : WithTop Int) := by
      simpa [add_comm] using
        add_le_add_right hcOrder (b.order 0 : WithTop Int)
    have hmLtHead' : ((ordUnit K m : Int) : WithTop Int) <
        ((b.order 0 : Int) : WithTop Int) := by
      exact_mod_cast hmLtHead
    exact hmLtHead'.trans_le hle
  have hbilin : q.bilin b.head
      (b.binarySecondVector + (c : K) • b.head) =
        (m : K) + (c : K) * q.quadratic b.head := by
    rw [LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_right]
    rfl
  have hpairOrder : ord K (q.bilin b.head
      (b.binarySecondVector + (c : K) • b.head)) =
        ((ordUnit K m : Int) : WithTop Int) := by
    rw [hbilin, (ord K).map_add_eq_of_lt_left hmLtCorrection, hmOrder]
  have hpairNe : q.bilin b.head
      (b.binarySecondVector + (c : K) • b.head) ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hpairOrder
    exact WithTop.top_ne_coe hpairOrder
  let s : Kˣ := Units.mk0
    (q.bilin b.head (b.binarySecondVector + (c : K) • b.head)) hpairNe
  refine ⟨s, rfl, ?_⟩
  have hsOrder : ordUnit K s = ordUnit K m := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, coe_ordUnit]
    simpa [s] using hpairOrder
  rw [hsOrder]
  exact b.two_mul_ordUnit_binaryMixedPairing_eq_order_add hstrict

theorem weightShear_gramDet
    (b : BONG V q L 2) (c : IntegerRing K) :
    q.quadratic b.head *
          q.quadratic (b.binarySecondVector + (c : K) • b.head) -
        q.bilin b.head
            (b.binarySecondVector + (c : K) • b.head) ^ 2 =
      b.value 0 * b.value 1 := by
  rw [q.quadratic_add, q.quadratic_smul,
    LinearMap.BilinForm.smul_right,
    q.isSymm.eq b.binarySecondVector b.head,
    LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_right,
    b.value_zero_eq_quadratic_head,
    b.quadratic_binarySecondVector_eq]
  rw [b.value_zero_eq_quadratic_head]
  have hself : q.bilin b.head b.head = q.quadratic b.head := rfl
  rw [hself]
  unfold binaryMixedPairing
  have hheadNe : q.quadratic b.head ≠ 0 := b.head_isAnisotropic
  field_simp [hheadNe]
  ring

theorem canonicalTwoScaleOrder_eq_binaryMixed
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0) :
    Lattice.canonicalTwoScaleOrder q L =
      ordUnit K (b.binaryMixedPairingUnit hstrict) +
        ramificationIndex K := by
  let a : Kˣ := b.valueUnit 0
  have ha : Lattice.IsNormGeneratorValue q L a := by
    simpa [a] using b.valueUnit_zero_isNormGeneratorValue
  have hcanonical := Lattice.scaleIdeal_eq_powerIdeal_canonicalScaleOrder ha
  have hm := b.scaleIdeal_eq_principal_binaryMixedPairing hstrict
  have hprincipal := Lattice.principalIdeal_eq_powerIdeal
    (b.binaryMixedPairingUnit hstrict)
  have hscaleOrder : Lattice.canonicalScaleOrder q L =
      ordUnit K (b.binaryMixedPairingUnit hstrict) := by
    apply Lattice.powerIdeal_order_eq_of_eq (K := K)
    calc
      Lattice.powerIdeal (K := K) (Lattice.canonicalScaleOrder q L) =
          Lattice.scaleIdeal q L := hcanonical.symm
      _ = Lattice.principalIdeal (K := K) b.binaryMixedPairing := hm
      _ = Lattice.principalIdeal (K := K)
          (b.binaryMixedPairingUnit hstrict : K) := rfl
      _ = Lattice.powerIdeal (K := K)
          (ordUnit K (b.binaryMixedPairingUnit hstrict)) := hprincipal
  rw [Lattice.canonicalTwoScaleOrder, hscaleOrder]

theorem weightShear_quadratic_order_eq_of_lt_twoScale
    (b : BONG V q L 2) (hstrict : b.order 1 < b.order 0)
    (c : IntegerRing K)
    (hbeta : q.quadratic
        (b.binarySecondVector + (c : K) • b.head) ∈
      Lattice.weightIdeal q L)
    (hcoords : ∀ z : V, z ∈ L → ∃ r s : IntegerRing K,
      z = (r : K) • b.head + (s : K) •
        (b.binarySecondVector + (c : K) • b.head))
    (hlt : Lattice.weightIdealOrder q L <
      Lattice.canonicalTwoScaleOrder q L) :
    ord K (q.quadratic
      (b.binarySecondVector + (c : K) • b.head)) =
        ((Lattice.weightIdealOrder q L : Int) : WithTop Int) := by
  let y : V := b.binarySecondVector + (c : K) • b.head
  let W : Int := Lattice.weightIdealOrder q L
  let T : Int := Lattice.canonicalTwoScaleOrder q L
  let a : Kˣ := b.valueUnit 0
  have ha : Lattice.IsNormGeneratorValue q L a := by
    simpa [a] using b.valueUnit_zero_isNormGeneratorValue
  have hbetaLower : ((W : Int) : WithTop Int) ≤
      ord K (q.quadratic y) := by
    rw [Lattice.weightIdeal_eq_powerIdeal] at hbeta
    exact (Lattice.mem_powerIdeal_iff _ _).1 hbeta
  by_contra hne
  have hbetaStrict : ((W : Int) : WithTop Int) <
      ord K (q.quadratic y) :=
    lt_of_le_of_ne hbetaLower (Ne.symm hne)
  have hltWT : W < T := hlt
  rcases Lattice.exists_quadratic_order_eq_weightIdealOrder_of_lt_twoScale
      a ha hlt with ⟨x, hx, hxNe, hxOrder, hxOdd⟩
  rcases hcoords x hx with ⟨r, s, hxRep⟩
  rcases b.weightShear_mixedPairing hstrict c with
    ⟨m, hmField, hmDouble⟩
  have hmOriginalDouble :=
    b.two_mul_ordUnit_binaryMixedPairing_eq_order_add hstrict
  have hmOrderEq : ordUnit K m =
      ordUnit K (b.binaryMixedPairingUnit hstrict) := by
    omega
  have hrNonneg : (0 : WithTop Int) ≤ ord K (r : K) :=
    (mem_integerRing_iff K).1 r.property
  have hsNonneg : (0 : WithTop Int) ≤ ord K (s : K) :=
    (mem_integerRing_iff K).1 s.property
  let headTerm : K := (r : K) ^ 2 * q.quadratic b.head
  let betaTerm : K := (s : K) ^ 2 * q.quadratic y
  let crossTerm : K :=
    (2 : K) * (r : K) * (s : K) * q.bilin b.head y
  have hbetaTermGt : ((W : Int) : WithTop Int) < ord K betaTerm := by
    have hle : ord K (q.quadratic y) ≤ ord K betaTerm := by
      dsimp [betaTerm]
      rw [ord_mul, ord_pow]
      have htwoS : (0 : WithTop Int) ≤ 2 • ord K (s : K) := by
        exact nsmul_nonneg hsNonneg 2
      simpa [add_comm] using
        add_le_add_right htwoS (ord K (q.quadratic y))
    exact hbetaStrict.trans_le hle
  have hcrossTermGt : ((W : Int) : WithTop Int) < ord K crossTerm := by
    have hTLe : ((T : Int) : WithTop Int) ≤ ord K crossTerm := by
      dsimp [crossTerm]
      rw [← hmField, ord_mul, ord_mul, ord_mul,
        ← ramificationIndex_spec, ← coe_ordUnit]
      have hcoeff : (0 : WithTop Int) ≤
          ord K (r : K) + ord K (s : K) := add_nonneg hrNonneg hsNonneg
      rw [hmOrderEq]
      have hT := b.canonicalTwoScaleOrder_eq_binaryMixed hstrict
      dsimp [T]
      rw [hT]
      have hbound := add_le_add_right
        (add_le_add_left hcoeff
          ((ramificationIndex K : Int) : WithTop Int))
        ((ordUnit K (b.binaryMixedPairingUnit hstrict) : Int) :
          WithTop Int)
      convert hbound using 1
      · push_cast
        simp
      · push_cast
        ac_rfl
    have hltCast : ((W : Int) : WithTop Int) <
        ((T : Int) : WithTop Int) := by
      exact_mod_cast hltWT
    exact hltCast.trans_le hTLe
  have hremainderGt : ((W : Int) : WithTop Int) <
      ord K (betaTerm + crossTerm) := by
    exact (lt_min hbetaTermGt hcrossTermGt).trans_le
      (min_ord_le_ord_add K betaTerm crossTerm)
  have hxFormula : q.quadratic x =
      headTerm + betaTerm + crossTerm := by
    rw [hxRep, q.quadratic_add, q.quadratic_smul,
      q.quadratic_smul, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right]
    dsimp [headTerm, betaTerm, crossTerm]
    ring
  have hheadEq : headTerm = q.quadratic x -
      (betaTerm + crossTerm) := by
    rw [hxFormula]
    ring
  have hxOrderW : ord K (q.quadratic x) =
      ((W : Int) : WithTop Int) := hxOrder
  have hxLtRemainder : ord K (q.quadratic x) <
      ord K (betaTerm + crossTerm) := by
    rw [hxOrderW]
    exact hremainderGt
  have hheadOrder : ord K headTerm =
      ((W : Int) : WithTop Int) := by
    rw [hheadEq, (ord K).map_sub_eq_of_lt_left hxLtRemainder, hxOrderW]
  have hrNe : (r : K) ≠ 0 := by
    intro hrZero
    dsimp [headTerm] at hheadOrder
    rw [hrZero, zero_pow (by norm_num), zero_mul, ord_zero] at hheadOrder
    exact WithTop.top_ne_coe hheadOrder
  let ru : Kˣ := Units.mk0 (r : K) hrNe
  have hheadOrderInt : W = 2 * ordUnit K ru + b.order 0 := by
    have hrOrder : ord K (r : K) =
        ((ordUnit K ru : Int) : WithTop Int) := by
      change ord K (ru : K) = _
      exact (coe_ordUnit K ru).symm
    have hqHeadOrder : ord K (q.quadratic b.head) =
        ((b.order 0 : Int) : WithTop Int) := by
      rw [← b.value_zero_eq_quadratic_head, ← b.coe_order]
    apply WithTop.coe_injective
    rw [← hheadOrder]
    dsimp [headTerm]
    rw [ord_mul, ord_pow, hrOrder, hqHeadOrder]
    norm_cast
  have hxOdd' : Odd (b.order 0 + W) := by
    simpa [a, W, b.order_eq_ordUnit] using hxOdd
  have hxEven : Even (b.order 0 + W) := by
    refine ⟨b.order 0 + ordUnit K ru, ?_⟩
    omega
  exact (Int.not_odd_iff_even.mpr hxEven hxOdd').elim

/-- The Gram determinant of a weight shear, divided by the square of its
mixed coefficient, is the adjacent square class. -/
theorem weightShear_normalizedAdjacent
    (b : GoodBONG q L 2) (c : IntegerRing K) (m : Kˣ)
    (hm : (m : K) = q.bilin b.toBONG.head
      (b.toBONG.binarySecondVector + (c : K) • b.toBONG.head)) :
    let y := b.toBONG.binarySecondVector + (c : K) • b.toBONG.head
    let v : Kˣ := b.adjacentProduct 0 / m ^ 2
    (v : K) = 1 - q.quadratic b.toBONG.head * q.quadratic y / (m : K) ^ 2 := by
  intro y v
  have hdet := b.toBONG.weightShear_gramDet c
  have hmNe : (m : K) ≠ 0 := Units.ne_zero m
  dsimp only [v]
  simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
  unfold GoodBONG.adjacentProduct
  simp only [Units.val_neg, Units.val_mul, b.coe_valueUnit]
  change -(b.toBONG.value 0 * b.toBONG.value 1) / (m : K) ^ 2 = _
  rw [b.toBONG.value_zero_eq_quadratic_head] at hdet
  dsimp only [y]
  rw [← hm] at hdet
  rw [b.toBONG.value_zero_eq_quadratic_head]
  rw [← hdet]
  field_simp [hmNe]
  ring

/-- The normalized Gram determinant has valuation zero. -/
theorem weightShear_normalizedAdjacent_order
    (b : GoodBONG q L 2) (hstrict : b.order 1 < b.order 0)
    (m : Kˣ) (hmDouble : 2 * ordUnit K m = b.order 0 + b.order 1) :
    ordUnit K (b.adjacentProduct 0 / m ^ 2) = 0 := by
  have hzero : ordUnit K (b.valueUnit 0) = b.order 0 :=
    (b.toBONG.order_eq_ordUnit 0).symm
  have hone : ordUnit K (b.valueUnit 1) = b.order 1 :=
    (b.toBONG.order_eq_ordUnit 1).symm
  unfold GoodBONG.adjacentProduct
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
  rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow,
    ordUnit_neg, ordUnit_mul, hzero, hone]
  omega

/-- Dividing the adjacent product by the square of the mixed coefficient
does not change its quadratic defect. -/
theorem weightShear_normalizedAdjacent_defect
    (b : GoodBONG q L 2) (m : Kˣ) :
    GoodBONG.defectOrder (K := K) (b.adjacentProduct 0 / m ^ 2) =
      b.adjacentDefect 0 := by
  unfold GoodBONG.adjacentDefect
  have hfactor : (b.adjacentProduct 0 / m ^ 2) * m ^ 2 =
      b.adjacentProduct 0 := by simp
  calc
    GoodBONG.defectOrder (K := K) (b.adjacentProduct 0 / m ^ 2) =
        GoodBONG.defectOrder (K := K)
          ((b.adjacentProduct 0 / m ^ 2) * m ^ 2) :=
      (GoodBONG.defectOrder_mul_square
        (b.adjacentProduct 0 / m ^ 2) m).symm
    _ = GoodBONG.defectOrder (K := K) (b.adjacentProduct 0) := by rw [hfactor]

/-- The ideal membership of the sheared diagonal coefficient gives the
corresponding lower bound for the adjacent quadratic defect. -/
theorem weightShear_adjacentDefect_lowerBound
    (b : GoodBONG q L 2) (hstrict : b.order 1 < b.order 0)
    (c : IntegerRing K) (m : Kˣ)
    (hm : (m : K) = q.bilin b.toBONG.head
      (b.toBONG.binarySecondVector + (c : K) • b.toBONG.head))
    (hmDouble : 2 * ordUnit K m = b.order 0 + b.order 1)
    (hbeta : q.quadratic
        (b.toBONG.binarySecondVector + (c : K) • b.toBONG.head) ∈
      Lattice.weightIdeal q L)
    (d : Nat)
    (hd : (d : Int) = b.order 0 + Lattice.weightIdealOrder q L -
      2 * ordUnit K m) :
    ((((d : Nat) : ℚ) : WithTop ℚ) ≤ b.adjacentDefect 0) := by
  let y : V := b.toBONG.binarySecondVector + (c : K) • b.toBONG.head
  let v : Kˣ := b.adjacentProduct 0 / m ^ 2
  let error : K :=
    -(q.quadratic b.toBONG.head * q.quadratic y / (m : K) ^ 2)
  have hvField : (v : K) = 1 + error := by
    have h := weightShear_normalizedAdjacent b c m hm
    dsimp only [y, v] at h
    dsimp only [error]
    rw [h]
    ring
  have hvOrder : ordUnit K v = 0 := by
    exact weightShear_normalizedAdjacent_order b hstrict m hmDouble
  have hvUnit : IsValuationUnit K (v : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K v).2 hvOrder
  have hbetaOrder :
      ((Lattice.weightIdealOrder q L : Int) : WithTop Int) ≤
        ord K (q.quadratic y) := by
    rw [Lattice.weightIdeal_eq_powerIdeal] at hbeta
    exact (Lattice.mem_powerIdeal_iff _ _).1 hbeta
  have hheadOrder : ord K (q.quadratic b.toBONG.head) =
      ((b.order 0 : Int) : WithTop Int) := by
    change ord K (q.quadratic b.toBONG.head) =
      ((b.toBONG.order 0 : Int) : WithTop Int)
    rw [← b.toBONG.value_zero_eq_quadratic_head,
      ← b.toBONG.coe_order]
  have hmOrder : ord K (m : K) =
      ((ordUnit K m : Int) : WithTop Int) := by rw [← coe_ordUnit]
  have htwoOrderTop :
      ((2 : Int) : WithTop Int) *
          ((ordUnit K m : Int) : WithTop Int) =
        ((ordUnit K m : Int) : WithTop Int) +
          ((ordUnit K m : Int) : WithTop Int) := by
    norm_cast
    omega
  have herrorOrderExact : ord K error =
      ((b.order 0 : Int) : WithTop Int) + ord K (q.quadratic y) +
        (-((ordUnit K m : Int) : WithTop Int) +
          -((ordUnit K m : Int) : WithTop Int)) := by
    dsimp only [error]
    rw [ord_neg, div_eq_mul_inv, ord_mul, AddValuation.map_inv,
      ord_mul, ord_pow, hheadOrder, hmOrder]
    simp only [two_nsmul, neg_add_rev, add_assoc]
  have herrorOrder : ((d : Int) : WithTop Int) ≤ ord K error := by
    calc
      ((d : Int) : WithTop Int) =
          ((b.order 0 : Int) : WithTop Int) +
            ((Lattice.weightIdealOrder q L : Int) : WithTop Int) +
              (-((ordUnit K m : Int) : WithTop Int) +
                -((ordUnit K m : Int) : WithTop Int)) := by
        rw [hd]
        push_cast
        rw [htwoOrderTop]
        simp only [sub_eq_add_neg, neg_add_rev, add_assoc]
      _ ≤ ((b.order 0 : Int) : WithTop Int) +
          ord K (q.quadratic y) +
            (-((ordUnit K m : Int) : WithTop Int) +
              -((ordUnit K m : Int) : WithTop Int)) := by
        exact add_le_add
          (add_le_add (le_refl (b.order 0 : WithTop Int)) hbetaOrder)
          (le_refl _)
      _ = ord K error := herrorOrderExact.symm
  have happ : IsQuadraticApproximation K v d := by
    refine ⟨1, ?_⟩
    have hnormalized : 1 - (1 : K) ^ 2 / (v : K) =
        error / (v : K) := by
      calc
        1 - (1 : K) ^ 2 / (v : K) =
            ((v : K) - 1) / (v : K) := by
          field_simp [Units.ne_zero v]
        _ = error / (v : K) := by rw [hvField]; ring
    rw [hnormalized, div_eq_mul_inv, ord_mul,
      AddValuation.map_inv, hvUnit]
    simpa using herrorOrder
  have hlower := GoodBONG.natCast_le_defectOrder_of_isQuadraticApproximation
    (K := K) v d happ
  rw [weightShear_normalizedAdjacent_defect b m] at hlower
  exact hlower

/-- When the sheared diagonal coefficient has exact weight order and the
normalized error is positive, odd, and below `2e`, its defect is exact. -/
theorem weightShear_adjacentDefect_eq
    (b : GoodBONG q L 2) (hstrict : b.order 1 < b.order 0)
    (c : IntegerRing K) (m : Kˣ)
    (hm : (m : K) = q.bilin b.toBONG.head
      (b.toBONG.binarySecondVector + (c : K) • b.toBONG.head))
    (hmDouble : 2 * ordUnit K m = b.order 0 + b.order 1)
    (hbetaOrder : ord K (q.quadratic
        (b.toBONG.binarySecondVector + (c : K) • b.toBONG.head)) =
      ((Lattice.weightIdealOrder q L : Int) : WithTop Int))
    (d : Nat)
    (hd : (d : Int) = b.order 0 + Lattice.weightIdealOrder q L -
      2 * ordUnit K m)
    (hdPos : 0 < d) (hdOdd : Odd d)
    (hdLt : d < 2 * ramificationIndex K) :
    b.adjacentDefect 0 = (((d : Nat) : ℚ) : WithTop ℚ) := by
  let y : V := b.toBONG.binarySecondVector + (c : K) • b.toBONG.head
  let v : Kˣ := b.adjacentProduct 0 / m ^ 2
  let error : K :=
    -(q.quadratic b.toBONG.head * q.quadratic y / (m : K) ^ 2)
  have hvField : (v : K) = 1 + error := by
    have h := weightShear_normalizedAdjacent b c m hm
    dsimp only [y, v] at h
    dsimp only [error]
    rw [h]
    ring
  have hheadOrder : ord K (q.quadratic b.toBONG.head) =
      ((b.order 0 : Int) : WithTop Int) := by
    change ord K (q.quadratic b.toBONG.head) =
      ((b.toBONG.order 0 : Int) : WithTop Int)
    rw [← b.toBONG.value_zero_eq_quadratic_head,
      ← b.toBONG.coe_order]
  have hmOrder : ord K (m : K) =
      ((ordUnit K m : Int) : WithTop Int) := by rw [← coe_ordUnit]
  have herrorOrder : ord K error = ((d : Int) : WithTop Int) := by
    dsimp only [error, y] at hbetaOrder ⊢
    rw [ord_neg, div_eq_mul_inv, ord_mul, AddValuation.map_inv,
      ord_mul, ord_pow, hheadOrder, hmOrder, hbetaOrder]
    apply WithTop.coe_injective
    norm_cast
    simp only [two_nsmul]
    omega
  have hvDefect : quadraticDefect K v = (d : ℕ∞) :=
    quadraticDefect_eq_of_principal_exact_odd v error d hvField
      herrorOrder hdPos hdOdd hdLt
  calc
    b.adjacentDefect 0 = GoodBONG.defectOrder (K := K) v :=
      (weightShear_normalizedAdjacent_defect b m).symm
    _ = (((d : Nat) : ℚ) : WithTop ℚ) := by
      unfold GoodBONG.defectOrder
      rw [hvDefect]
      rfl

/-- O'Meara 93:10, in the strict binary modular orientation, gives the
binary base case of Beli (2009), Lemma 2.14. -/
theorem weightIdealOrder_binary_strict
    (b : GoodBONG q L 2) (hstrict : b.order 1 < b.order 0) :
    (Lattice.weightIdealOrder q L : ℚ) =
      (b.order 0 : ℚ) + b.alphaValue 0 := by
  let a : Kˣ := b.toBONG.valueUnit 0
  have ha : Lattice.IsNormGeneratorValue q L a := by
    simpa [a] using b.toBONG.valueUnit_zero_isNormGeneratorValue
  have hweightLe : Lattice.weightIdealOrder q L ≤
      Lattice.canonicalTwoScaleOrder q L := by
    have hle := Lattice.twoScaleIdeal_le_weightIdeal q L
    rw [Lattice.twoScaleIdeal_eq_powerIdeal_canonicalTwoScaleOrder ha,
      Lattice.weightIdeal_eq_powerIdeal,
      Lattice.powerIdeal_le_iff] at hle
    exact hle
  rcases b.toBONG.exists_weight_shear with
    ⟨c, _hyMem, hbeta, hcoords⟩
  rcases b.toBONG.weightShear_mixedPairing hstrict c with
    ⟨m, hm, hmDouble⟩
  have hmDoubleGood : 2 * ordUnit K m = b.order 0 + b.order 1 := by
    simpa only [GoodBONG.order] using hmDouble
  have hmOriginal : 2 * ordUnit K
      (b.toBONG.binaryMixedPairingUnit hstrict) =
        b.order 0 + b.order 1 := by
    simpa only [GoodBONG.order] using
      b.toBONG.two_mul_ordUnit_binaryMixedPairing_eq_order_add hstrict
  have hmEq : ordUnit K m =
      ordUnit K (b.toBONG.binaryMixedPairingUnit hstrict) := by
    omega
  have htwoScale : Lattice.canonicalTwoScaleOrder q L =
      ordUnit K m + ramificationIndex K := by
    rw [b.toBONG.canonicalTwoScaleOrder_eq_binaryMixed hstrict, hmEq]
  have hhalf : b.halfGapCandidate 0 =
      ((((Lattice.canonicalTwoScaleOrder q L - b.order 0 : Int) : ℚ) :
        WithTop ℚ)) := by
    unfold GoodBONG.halfGapCandidate
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
    norm_cast
    rw [Rat.divInt_eq_div]
    push_cast
    have hscaleQ : (Lattice.canonicalTwoScaleOrder q L : ℚ) =
        (ordUnit K m : ℚ) + (ramificationIndex K : ℚ) := by
      exact_mod_cast htwoScale
    have hmQ : 2 * (ordUnit K m : ℚ) =
        (b.order 0 : ℚ) + (b.order 1 : ℚ) := by
      exact_mod_cast hmDoubleGood
    linarith
  rcases hweightLe.eq_or_lt with hterminal | hbelow
  · let p : Int := b.order 0 + Lattice.weightIdealOrder q L -
        2 * ordUnit K m
    have hpEq : p = Lattice.weightIdealOrder q L - b.order 1 := by
      dsimp only [p]
      omega
    have hpTerminal : p =
        Lattice.canonicalTwoScaleOrder q L - b.order 1 := by
      omega
    have hpPos : 0 < p := by
      rw [hpTerminal, htwoScale]
      have hePos : 0 < (ramificationIndex K : Int) := by
        exact_mod_cast ramificationIndex_pos (K := K)
      have hmGt : b.order 1 < ordUnit K m := by omega
      omega
    let d : Nat := Int.toNat p
    have hdCast : (d : Int) = p := by
      dsimp only [d]
      rw [Int.toNat_of_nonneg hpPos.le]
    have hdefectLower := weightShear_adjacentDefect_lowerBound
      b hstrict c m hm hmDoubleGood hbeta d (by simpa [p] using hdCast)
    have hdefectLower' :
        ((((p : Int) : ℚ) : WithTop ℚ) ≤ b.adjacentDefect 0) := by
      have hcastQ : (d : ℚ) = (p : ℚ) := by exact_mod_cast hdCast
      simpa only [hcastQ] using hdefectLower
    have hleftGe : b.halfGapCandidate 0 ≤
        b.leftDefectCandidate 0 0 := by
      rw [hhalf]
      unfold GoodBONG.leftDefectCandidate
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
      calc
        ((((Lattice.canonicalTwoScaleOrder q L - b.order 0 : Int) : ℚ) :
            WithTop ℚ)) =
            (((b.order 1 - b.order 0 : Int) : ℚ) : WithTop ℚ) +
              (((p : Int) : ℚ) : WithTop ℚ) := by
          congr 1
          push_cast
          exact_mod_cast (show
            Lattice.canonicalTwoScaleOrder q L - b.order 0 =
              (b.order 1 - b.order 0) + p by
                rw [hpTerminal]
                omega)
        _ ≤ (((b.order 1 - b.order 0 : Int) : ℚ) : WithTop ℚ) +
            b.adjacentDefect 0 :=
          add_le_add
            (le_refl (((b.order 1 - b.order 0 : Int) : ℚ) : WithTop ℚ))
            hdefectLower'
    have halphaTop : (b.alphaValue 0 : WithTop ℚ) =
        b.halfGapCandidate 0 := by
      rw [b.binary_alpha_eq_min_candidates]
      exact min_eq_left hleftGe
    have halpha : b.alphaValue 0 =
        ((Lattice.weightIdealOrder q L - b.order 0 : Int) : ℚ) := by
      apply WithTop.coe_injective
      rw [halphaTop, hhalf]
      congr 1
      exact_mod_cast (show
        Lattice.canonicalTwoScaleOrder q L - b.order 0 =
          Lattice.weightIdealOrder q L - b.order 0 by omega)
    rw [halpha]
    push_cast
    ring
  · have hbetaOrder :=
      b.toBONG.weightShear_quadratic_order_eq_of_lt_twoScale
        hstrict c hbeta hcoords hbelow
    have hnormLower : b.order 0 ≤ Lattice.weightIdealOrder q L := by
      have h := Lattice.normGeneratorOrder_le_weightIdealOrder a ha
      have horder : ordUnit K a = b.order 0 := by
        dsimp only [a]
        exact (b.toBONG.order_eq_ordUnit 0).symm
      rwa [horder] at h
    let p : Int := b.order 0 + Lattice.weightIdealOrder q L -
        2 * ordUnit K m
    have hpEq : p = Lattice.weightIdealOrder q L - b.order 1 := by
      dsimp only [p]
      omega
    have hpPos : 0 < p := by
      rw [hpEq]
      omega
    have hoddWeight : Odd
        (b.order 0 + Lattice.weightIdealOrder q L) := by
      rcases Lattice.exists_quadratic_order_eq_weightIdealOrder_of_lt_twoScale
          a ha hbelow with ⟨_x, _hx, _hxNe, _hxOrder, hodd⟩
      have horder : ordUnit K a = b.order 0 := by
        dsimp only [a]
        exact (b.toBONG.order_eq_ordUnit 0).symm
      rwa [horder] at hodd
    have hpOdd : Odd p := by
      rcases hoddWeight with ⟨z, hz⟩
      refine ⟨z - ordUnit K m, ?_⟩
      dsimp only [p]
      omega
    have hgapLower := b.orderGap_ge_neg_two_mul_e_for_properties 0
    have hpLt : p < 2 * (ramificationIndex K : Int) := by
      rw [hpEq]
      change -(2 * (ramificationIndex K : Int)) ≤
        b.order 1 - b.order 0 at hgapLower
      omega
    let d : Nat := Int.toNat p
    have hdCast : (d : Int) = p := by
      dsimp only [d]
      rw [Int.toNat_of_nonneg hpPos.le]
    have hdPos : 0 < d := by exact_mod_cast (hdCast.symm ▸ hpPos)
    have hdOdd : Odd d := by
      have : Odd (d : Int) := by simpa only [hdCast] using hpOdd
      exact_mod_cast this
    have hdLt : d < 2 * ramificationIndex K := by
      exact_mod_cast (show (d : Int) <
        2 * (ramificationIndex K : Int) by rw [hdCast]; exact hpLt)
    have hdefect := weightShear_adjacentDefect_eq b hstrict c m hm
      hmDoubleGood hbetaOrder d (by simpa [p] using hdCast)
      hdPos hdOdd hdLt
    have hleft : b.leftDefectCandidate 0 0 =
        ((((Lattice.weightIdealOrder q L - b.order 0 : Int) : ℚ) :
          WithTop ℚ)) := by
      unfold GoodBONG.leftDefectCandidate
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, hdefect]
      congr 1
      push_cast
      exact_mod_cast (show
        (b.order 1 - b.order 0) + (d : Int) =
          Lattice.weightIdealOrder q L - b.order 0 by
            rw [hdCast]
            rw [hpEq]
            omega)
    have hleftLe : b.leftDefectCandidate 0 0 ≤
        b.halfGapCandidate 0 := by
      rw [hleft, hhalf]
      exact_mod_cast (show
        Lattice.weightIdealOrder q L - b.order 0 ≤
          Lattice.canonicalTwoScaleOrder q L - b.order 0 by omega)
    have halphaTop : (b.alphaValue 0 : WithTop ℚ) =
        b.leftDefectCandidate 0 0 := by
      rw [b.binary_alpha_eq_min_candidates]
      exact min_eq_right hleftLe
    have halpha : b.alphaValue 0 =
        ((Lattice.weightIdealOrder q L - b.order 0 : Int) : ℚ) := by
      apply WithTop.coe_injective
      rw [halphaTop, hleft]
    rw [halpha]
    push_cast
    ring

end BONG

end Bong
