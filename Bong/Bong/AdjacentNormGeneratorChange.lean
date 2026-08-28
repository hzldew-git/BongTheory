/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryNormGeneratorGroup
import Bong.Bong.BeliLemmas48To410
import Bong.Bong.OrthogonalBasis
import Bong.Bong.AlternatingEndpointProduct
import Bong.Lattice.BasisUnits

/-!
# Changing two adjacent BONG values by a norm-generator multiplier

Beli (2003), paragraph 3.12, first changes the norm generator in a binary
segment and then invokes the good-segment replacement theorem.  This file
records that argument in the exact form used later in Beli (2019), Lemma
7.17: a valuation-unit class in the binary norm-generator group multiplies
both adjacent values, while all other values are unchanged.

No new local-field interface is introduced here.  The only inputs are the
binary value theorem already isolated in `BinaryNormGeneratorLocalLaws` and
the segment replacement theorem already isolated in `BeliLemma49Laws`.
-/

namespace Bong

open Dyadic
open Module

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The exact binary output of paragraph 3.12. -/
structure BinaryAdjacentMultiplierData
    (b : BONG V q L 2) (u : valuationUnitSubgroup K) where
  bong : GoodBONG q L 2
  valueUnit_zero : bong.valueUnit 0 = (u : Kˣ) * b.valueUnit 0
  valueUnit_one : bong.valueUnit 1 = (u : Kˣ) * b.valueUnit 1

private noncomputable def secondScaleFactors (z : Kˣ) : Fin 1 → Kˣ :=
  fun _ ↦ z

private noncomputable def secondScaledTailBasis
    (b : BONG V q L 2) (z : Kˣ) :
    Basis (Fin 1) K (q.vectorOrthogonal b.head) :=
  b.tail.basis.unitsSMul (secondScaleFactors z)

private theorem secondScaledTailBasis_iIsOrtho
    (b : BONG V q L 2) (z : Kˣ) :
    (q.orthogonalSpace b.head b.head_isAnisotropic).bilin.iIsOrtho
      (secondScaledTailBasis b z) := by
  rw [LinearMap.BilinForm.iIsOrtho_def]
  intro i j hij
  exact False.elim (hij (Subsingleton.elim i j))

private theorem secondScaledTailBasis_quadratic_ne
    (b : BONG V q L 2) (z : Kˣ) :
    (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
      (secondScaledTailBasis b z 0) ≠ 0 := by
  rw [secondScaledTailBasis, Basis.unitsSMul_apply]
  change q.quadratic ((z : K) • (b.tail.basis 0 : V)) ≠ 0
  rw [q.quadratic_smul]
  apply mul_ne_zero (pow_ne_zero 2 (Units.ne_zero z))
  change (q.orthogonalSpace b.head b.head_isAnisotropic).quadratic
    (b.tail.ambientVector 0) ≠ 0
  rw [b.tail.quadratic_ambientVector]
  exact b.tail.value_ne_zero 0

private theorem secondScaledTailBasis_lattice_eq
    (b : BONG V q L 2) (z : Kˣ)
    (hz : IsValuationUnit K (z : K)) :
    Lattice.basisLattice (secondScaledTailBasis b z) =
      L.projectedLattice q b.head b.head_isAnisotropic := by
  rw [secondScaledTailBasis,
    Lattice.basisLattice_unitsSMul_eq b.tail.basis
      (secondScaleFactors z) (fun _ ↦ hz)]
  exact b.tail.lattice_eq_basisLattice.symm

/-- Binary form of Beli (2003), paragraph 3.12, with exact representatives.
The first value comes from the chosen norm generator.  The second BONG vector
is then rescaled by a valuation unit so that the second value has the same
exact multiplier, not merely the same square class. -/
theorem exists_binaryAdjacentMultiplierData
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    (b : BONG V q L 2) (u : valuationUnitSubgroup K)
    (hu : valuationUnitClassHom K u ∈
      beliNormGeneratorGroup K b.binaryParameter) :
    Nonempty (BinaryAdjacentMultiplierData b u) := by
  classical
  rcases b.exists_normGeneratorValueRatioUnit_eq_of_mem_beliNormGeneratorGroup
      u hu with ⟨y, hy, hratio⟩
  let hyAn : q.IsAnisotropic y :=
    b.isAnisotropic_of_isNormGenerator_binary hy
  have hfin : Module.finrank K V = 2 := b.length_eq_finrank.symm
  let c : BONG V q L 2 :=
    BONG.ofNormGeneratorBinary q L y hy hyAn hfin
  have hcZero : c.valueUnit 0 = (u : Kˣ) * b.valueUnit 0 := by
    let yUnit : Kˣ := Units.mk0 (q.quadratic y) hyAn
    have hyUnit : c.valueUnit 0 = yUnit := by
      apply Units.ext
      change c.value 0 = q.quadratic y
      rw [c.value_zero_eq_quadratic_head,
        BONG.head_ofNormGeneratorBinary q L y hy hyAn hfin]
    rw [hyUnit]
    calc
      yUnit = (yUnit / b.valueUnit 0) * b.valueUnit 0 := by simp
      _ = (u : Kˣ) * b.valueUnit 0 := by
        simpa only [yUnit, normGeneratorValueRatioUnit] using
          congrArg (fun z : Kˣ ↦ z * b.valueUnit 0) hratio
  rcases BONG.exists_valueProduct_eq_mul_square b c with ⟨p, hp⟩
  have hpUnit : IsValuationUnit K (p : K) := by
    have hvolume : ordUnit K c.valueProduct = ordUnit K b.valueProduct := by
      rw [← c.volumeOrder_eq_ordUnit_valueProduct,
        ← b.volumeOrder_eq_ordUnit_valueProduct]
    have horder := congrArg (ordUnit K) hp
    rw [ordUnit_mul, ordUnit_pow] at horder
    have hpOrder : ordUnit K p = 0 := by omega
    exact (isValuationUnit_iff_ordUnit_eq_zero K p).2 hpOrder
  let z : Kˣ := (u : Kˣ) * p⁻¹
  have hzUnit : IsValuationUnit K (z : K) := by
    have hpInv : ord K (((p⁻¹ : Kˣ) : K)) = 0 := by
      rw [Units.val_inv_eq_inv_val, AddValuation.map_inv, hpUnit]
      simp
    change ord K (((u : Kˣ) : K) * ((p⁻¹ : Kˣ) : K)) = 0
    rw [ord_mul, u.property, hpInv]
    simp
  have hcOne : c.valueUnit 1 =
      ((u : Kˣ)⁻¹ * b.valueUnit 1 * p ^ 2) := by
    calc
      c.valueUnit 1 =
          ((u : Kˣ) * b.valueUnit 0)⁻¹ *
            (((u : Kˣ) * b.valueUnit 0) * c.valueUnit 1) := by
              group
      _ = ((u : Kˣ) * b.valueUnit 0)⁻¹ * c.valueProduct := by
        rw [← hcZero]
        simp only [valueProduct_fin_two]
      _ = ((u : Kˣ)⁻¹ * b.valueUnit 1 * p ^ 2) := by
        rw [hp, b.valueProduct_fin_two]
        simp [mul_comm, mul_left_comm, mul_assoc]
  let scaledBasis := secondScaledTailBasis c z
  let rawTail : BONG
      (q.vectorOrthogonal c.head)
      (q.orthogonalSpace c.head c.head_isAnisotropic)
      (Lattice.basisLattice scaledBasis) 1 :=
    BONG.ofOrthogonalBasisFinOne
      (q.orthogonalSpace c.head c.head_isAnisotropic)
      scaledBasis
      (secondScaledTailBasis_iIsOrtho c z)
      (secondScaledTailBasis_quadratic_ne c z)
  have htailLattice : Lattice.basisLattice scaledBasis =
      L.projectedLattice q c.head c.head_isAnisotropic := by
    exact secondScaledTailBasis_lattice_eq c z hzUnit
  let scaledTail := rawTail.castLattice htailLattice
  let changed : BONG V q L 2 :=
    BONG.cons c.head c.head_isNormGenerator c.head_isAnisotropic scaledTail
  have hchangedZero : changed.valueUnit 0 =
      (u : Kˣ) * b.valueUnit 0 := by
    apply Units.ext
    change q.quadratic c.head =
      (((u : Kˣ) * b.valueUnit 0 : Kˣ) : K)
    rw [← c.value_zero_eq_quadratic_head]
    exact congrArg Units.val hcZero
  have hscaledTail : scaledTail.valueUnit 0 =
      (u : Kˣ) * b.valueUnit 1 := by
    apply Units.ext
    change scaledTail.value 0 =
      (((u : Kˣ) * b.valueUnit 1 : Kˣ) : K)
    rw [BONG.value_castLattice]
    rw [← rawTail.quadratic_ambientVector,
      BONG.ambientVector_ofOrthogonalBasisFinOne]
    rw [show scaledBasis 0 = (z : K) • c.tail.basis 0 by
      simp [scaledBasis, secondScaledTailBasis, secondScaleFactors,
        Basis.unitsSMul_apply, Units.smul_def]]
    rw [(q.orthogonalSpace c.head c.head_isAnisotropic).quadratic_smul]
    have htailValue : c.tail.valueUnit 0 = c.valueUnit 1 := by
      apply Units.ext
      exact c.value_tail 0
    have hzEq : z ^ 2 * c.tail.valueUnit 0 =
        (u : Kˣ) * b.valueUnit 1 := by
      rw [htailValue, hcOne]
      apply Units.ext
      simp only [z, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_inv_eq_inv_val]
      field_simp [Units.ne_zero p, Units.ne_zero (u : Kˣ)]
    have htailQuadratic :
        (q.orthogonalSpace c.head c.head_isAnisotropic).quadratic
            (c.tail.basis 0) = c.tail.value 0 := by
      exact c.tail.quadratic_ambientVector 0
    rw [htailQuadratic]
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val,
      BONG.coe_valueUnit] using congrArg Units.val hzEq
  have hchangedOne : changed.valueUnit 1 =
      (u : Kˣ) * b.valueUnit 1 := by
    apply Units.ext
    change scaledTail.value 0 =
      (((u : Kˣ) * b.valueUnit 1 : Kˣ) : K)
    exact congrArg Units.val hscaledTail
  exact ⟨{
    bong := ⟨changed, changed.isGood_binary⟩
    valueUnit_zero := hchangedZero
    valueUnit_one := hchangedOne }⟩

/-- Rescaling the second vector of a binary BONG by a valuation unit preserves
the integral lattice and multiplies only the second BONG value by its square.
This is the elementary exact-representative adjustment used after changing a
binary norm generator. -/
theorem exists_secondValueSquareScaled
    (b : GoodBONG q L 2) (z : Kˣ)
    (hz : IsValuationUnit K (z : K)) :
    ∃ c : GoodBONG q L 2,
      c.valueUnit 0 = b.valueUnit 0 ∧
      c.valueUnit 1 = z ^ 2 * b.valueUnit 1 := by
  let scaledBasis := secondScaledTailBasis b.toBONG z
  let rawTail : BONG
      (q.vectorOrthogonal b.toBONG.head)
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (Lattice.basisLattice scaledBasis) 1 :=
    BONG.ofOrthogonalBasisFinOne
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      scaledBasis
      (secondScaledTailBasis_iIsOrtho b.toBONG z)
      (secondScaledTailBasis_quadratic_ne b.toBONG z)
  have htailLattice : Lattice.basisLattice scaledBasis =
      L.projectedLattice q b.toBONG.head b.toBONG.head_isAnisotropic := by
    exact secondScaledTailBasis_lattice_eq b.toBONG z hz
  let scaledTail := rawTail.castLattice htailLattice
  let changed : BONG V q L 2 :=
    BONG.cons b.toBONG.head b.toBONG.head_isNormGenerator
      b.toBONG.head_isAnisotropic scaledTail
  have hchangedZero : changed.valueUnit 0 = b.valueUnit 0 := by
    apply Units.ext
    change q.quadratic b.toBONG.head = b.value 0
    exact b.toBONG.value_zero_eq_quadratic_head.symm
  have hscaledTail : scaledTail.valueUnit 0 =
      z ^ 2 * b.valueUnit 1 := by
    apply Units.ext
    change scaledTail.value 0 = (((z ^ 2 * b.valueUnit 1 : Kˣ) : K))
    rw [BONG.value_castLattice]
    rw [← rawTail.quadratic_ambientVector,
      BONG.ambientVector_ofOrthogonalBasisFinOne]
    rw [show scaledBasis 0 = (z : K) • b.toBONG.tail.basis 0 by
      simp [scaledBasis, secondScaledTailBasis, secondScaleFactors,
        Basis.unitsSMul_apply, Units.smul_def]]
    rw [(q.orthogonalSpace b.toBONG.head
      b.toBONG.head_isAnisotropic).quadratic_smul]
    have htailValue : b.toBONG.tail.valueUnit 0 = b.valueUnit 1 := by
      apply Units.ext
      exact b.toBONG.value_tail 0
    have htailQuadratic :
        (q.orthogonalSpace b.toBONG.head
          b.toBONG.head_isAnisotropic).quadratic
            (b.toBONG.tail.basis 0) = b.toBONG.tail.value 0 := by
      exact b.toBONG.tail.quadratic_ambientVector 0
    rw [htailQuadratic]
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val,
      BONG.coe_valueUnit] using congrArg Units.val
        (show z ^ 2 * b.toBONG.tail.valueUnit 0 =
            z ^ 2 * b.valueUnit 1 by rw [htailValue])
  have hchangedOne : changed.valueUnit 1 =
      z ^ 2 * b.valueUnit 1 := by
    apply Units.ext
    change scaledTail.value 0 = (((z ^ 2 * b.valueUnit 1 : Kˣ) : K))
    exact congrArg Units.val hscaledTail
  exact ⟨⟨changed, changed.isGood_binary⟩, hchangedZero, hchangedOne⟩

/-- Exact binary coefficient replacement after a permitted norm-generator
change.  Equal orders make the first-value ratio a valuation unit; the
determinant square-class equality then supplies the valuation-unit square used
to adjust the second vector. -/
theorem exists_binaryExactValues
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    (b : GoodBONG q L 2) (targetZero targetOne : Kˣ)
    (hzeroOrder : ordUnit K targetZero = ordUnit K (b.valueUnit 0))
    (honeOrder : ordUnit K targetOne = ordUnit K (b.valueUnit 1))
    (hdet : IsSquare
      ((b.valueUnit 0 * b.valueUnit 1) * (targetZero * targetOne)))
    (u : valuationUnitSubgroup K)
    (huValue : (u : Kˣ) = targetZero / b.valueUnit 0)
    (hu : valuationUnitClassHom K u ∈
      beliNormGeneratorGroup K b.toBONG.binaryParameter) :
    ∃ c : GoodBONG q L 2,
      c.valueUnit 0 = targetZero ∧ c.valueUnit 1 = targetOne := by
  rcases exists_binaryAdjacentMultiplierData b.toBONG u hu with ⟨D⟩
  have hDZero : D.bong.valueUnit 0 = targetZero := by
    rw [D.valueUnit_zero]
    change (u : Kˣ) * b.valueUnit 0 = targetZero
    rw [huValue]
    simp
  have hDOne : D.bong.valueUnit 1 =
      (u : Kˣ) * b.valueUnit 1 := D.valueUnit_one
  have hratioSquare : IsSquare
      (targetOne / ((u : Kˣ) * b.valueUnit 1)) := by
    have hdenSquare : IsSquare
        ((b.valueUnit 0 * ((u : Kˣ) * b.valueUnit 1)) ^ 2) :=
      ⟨b.valueUnit 0 * ((u : Kˣ) * b.valueUnit 1), by
        simp only [pow_two]⟩
    have hquotient := hdet.div hdenSquare
    have heq : targetOne / ((u : Kˣ) * b.valueUnit 1) =
        ((b.valueUnit 0 * b.valueUnit 1) * (targetZero * targetOne)) /
          (b.valueUnit 0 * ((u : Kˣ) * b.valueUnit 1)) ^ 2 := by
      rw [huValue]
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul,
        Units.val_pow_eq_pow_val]
      field_simp [Units.ne_zero targetZero, Units.ne_zero targetOne,
        Units.ne_zero (b.valueUnit 0), Units.ne_zero (b.valueUnit 1)]
    rw [heq]
    exact hquotient
  rcases hratioSquare with ⟨z, hzSquare⟩
  have huOrder : ordUnit K (u : Kˣ) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K (u : Kˣ)).1 u.property
  have hzOrder : ordUnit K z = 0 := by
    have h := congrArg (ordUnit K) hzSquare
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_mul,
      huOrder, honeOrder, ordUnit_mul] at h
    omega
  have hzUnit : IsValuationUnit K (z : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K z).2 hzOrder
  rcases exists_secondValueSquareScaled D.bong z hzUnit with
    ⟨c, hcZero, hcOne⟩
  refine ⟨c, hcZero.trans hDZero, ?_⟩
  rw [hcOne, hDOne]
  calc
    z ^ 2 * ((u : Kˣ) * b.valueUnit 1) =
        (targetOne / ((u : Kˣ) * b.valueUnit 1)) *
          ((u : Kˣ) * b.valueUnit 1) := by
            rw [hzSquare]
            simp only [pow_two]
    _ = targetOne := by simp

/-- Global output of an adjacent multiplier change. -/
structure AdjacentMultiplierData {n : Nat}
    (b : GoodBONG q L n) (i : Fin n) (hi : i.val + 1 < n)
    (u : valuationUnitSubgroup K) where
  bong : GoodBONG q L n
  valueUnit_left : bong.valueUnit i = (u : Kˣ) * b.valueUnit i
  valueUnit_right : bong.valueUnit ⟨i.val + 1, hi⟩ =
    (u : Kˣ) * b.valueUnit ⟨i.val + 1, hi⟩
  valueUnit_before (j : Fin n) (hj : j.val < i.val) :
    bong.valueUnit j = b.valueUnit j
  valueUnit_after (j : Fin n) (hj : i.val + 2 ≤ j.val) :
    bong.valueUnit j = b.valueUnit j

/-- A good BONG obtained by replacing one adjacent binary block with two
prescribed exact values, while all entries outside the block stay fixed. -/
structure ExactPairReplacementData {n : Nat}
    (b : GoodBONG q L n) (i : Fin n) (hi : i.val + 1 < n)
    (targetZero targetOne : Kˣ) where
  bong : GoodBONG q L n
  valueUnit_left : bong.valueUnit i = targetZero
  valueUnit_right : bong.valueUnit ⟨i.val + 1, hi⟩ = targetOne
  valueUnit_before (j : Fin n) (hj : j.val < i.val) :
    bong.valueUnit j = b.valueUnit j
  valueUnit_after (j : Fin n) (hj : i.val + 2 ≤ j.val) :
    bong.valueUnit j = b.valueUnit j

/-- Beli (2003), paragraph 3.12, inserted at an arbitrary adjacent pair of a
good BONG. -/
theorem exists_adjacentMultiplierData
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    {n : Nat} (b : GoodBONG q L n) (i : Fin n)
    (hi : i.val + 1 < n) (u : valuationUnitSubgroup K)
    (hu : valuationUnitClassHom K u ∈
      beliNormGeneratorGroup K (b.toBONG.adjacentParameter i hi)) :
    Nonempty (AdjacentMultiplierData b i hi u) := by
  classical
  have hbound : i.val + 2 ≤ n := by omega
  rcases b.toBONG.exists_segmentWitness i.val 2 hbound with ⟨w⟩
  have hwZero : w.bong.valueUnit 0 = b.valueUnit i := by
    apply Units.ext
    change w.bong.value 0 = b.toBONG.value i
    simpa [BONG.SegmentWitness.sourceIndex] using
      (w.value_eq (0 : Fin 2))
  have hwOne : w.bong.valueUnit 1 =
      b.valueUnit ⟨i.val + 1, hi⟩ := by
    apply Units.ext
    change w.bong.value 1 = b.toBONG.value ⟨i.val + 1, hi⟩
    simpa [BONG.SegmentWitness.sourceIndex] using
      (w.value_eq (1 : Fin 2))
  have hparameter : w.bong.binaryParameter =
      b.toBONG.adjacentParameter i hi := by
    change w.bong.valueUnit 1 / w.bong.valueUnit 0 =
      b.valueUnit ⟨i.val + 1, hi⟩ / b.valueUnit i
    rw [hwZero, hwOne]
  have huLocal : valuationUnitClassHom K u ∈
      beliNormGeneratorGroup K w.bong.binaryParameter := by
    rwa [hparameter]
  rcases w.bong.exists_binaryAdjacentMultiplierData u huLocal with ⟨C⟩
  rcases b.toBONG.beliLemma49_ii b.good w C.bong.toBONG C.bong.good with
    ⟨R⟩
  let result : GoodBONG q L n := ⟨R.bong, R.good⟩
  have hinsideValue (j : Fin 2) :
      result.valueUnit ⟨i.val + j.val, by omega⟩ =
        C.bong.valueUnit j := by
    apply Units.ext
    change R.bong.value ⟨i.val + j.val, by omega⟩ =
      C.bong.toBONG.value j
    rw [← R.bong.quadratic_ambientVector,
      ← C.bong.toBONG.quadratic_ambientVector]
    exact congrArg q.quadratic (R.inside_eq j)
  refine ⟨{
    bong := result
    valueUnit_left := ?_
    valueUnit_right := ?_
    valueUnit_before := ?_
    valueUnit_after := ?_ }⟩
  · have hindex : (⟨i.val + (0 : Fin 2).val, by omega⟩ : Fin n) = i := by
      apply Fin.ext
      simp
    calc
      result.valueUnit i = C.bong.valueUnit 0 := by
        simpa only [hindex] using hinsideValue (0 : Fin 2)
      _ = (u : Kˣ) * w.bong.valueUnit 0 := C.valueUnit_zero
      _ = (u : Kˣ) * b.valueUnit i := by rw [hwZero]
  · have hindex :
        (⟨i.val + (1 : Fin 2).val, by omega⟩ : Fin n) =
          ⟨i.val + 1, hi⟩ := by
      apply Fin.ext
      rfl
    calc
      result.valueUnit ⟨i.val + 1, hi⟩ = C.bong.valueUnit 1 := by
        simpa only [hindex] using hinsideValue (1 : Fin 2)
      _ = (u : Kˣ) * w.bong.valueUnit 1 := C.valueUnit_one
      _ = (u : Kˣ) * b.valueUnit ⟨i.val + 1, hi⟩ := by
        rw [hwOne]
  · intro j hj
    apply Units.ext
    change R.bong.value j = b.toBONG.value j
    rw [← R.bong.quadratic_ambientVector,
      ← b.toBONG.quadratic_ambientVector, R.before_eq j hj]
  · intro j hj
    apply Units.ext
    change R.bong.value j = b.toBONG.value j
    rw [← R.bong.quadratic_ambientVector,
      ← b.toBONG.quadratic_ambientVector, R.after_eq j hj]

/-- Insert the exact binary replacement into an arbitrary consecutive pair of
a good BONG.  This is Beli (2003), Lemma 4.9(ii), applied to the explicit
binary construction above. -/
theorem exists_exactPairReplacementData
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    {n : Nat} (b : GoodBONG q L n) (i : Fin n)
    (hi : i.val + 1 < n) (targetZero targetOne : Kˣ)
    (hzeroOrder : ordUnit K targetZero = ordUnit K (b.valueUnit i))
    (honeOrder : ordUnit K targetOne =
      ordUnit K (b.valueUnit ⟨i.val + 1, hi⟩))
    (hdet : IsSquare
      ((b.valueUnit i * b.valueUnit ⟨i.val + 1, hi⟩) *
        (targetZero * targetOne)))
    (u : valuationUnitSubgroup K)
    (huValue : (u : Kˣ) = targetZero / b.valueUnit i)
    (hu : valuationUnitClassHom K u ∈
      beliNormGeneratorGroup K (b.toBONG.adjacentParameter i hi)) :
    Nonempty (ExactPairReplacementData b i hi targetZero targetOne) := by
  classical
  have hbound : i.val + 2 ≤ n := by omega
  rcases b.toBONG.exists_segmentWitness i.val 2 hbound with ⟨w⟩
  have hwZero : w.bong.valueUnit 0 = b.valueUnit i := by
    apply Units.ext
    change w.bong.value 0 = b.toBONG.value i
    simpa [BONG.SegmentWitness.sourceIndex] using
      (w.value_eq (0 : Fin 2))
  have hwOne : w.bong.valueUnit 1 =
      b.valueUnit ⟨i.val + 1, hi⟩ := by
    apply Units.ext
    change w.bong.value 1 = b.toBONG.value ⟨i.val + 1, hi⟩
    simpa [BONG.SegmentWitness.sourceIndex] using
      (w.value_eq (1 : Fin 2))
  let localBong : GoodBONG
      (q.restrict w.carrier w.nondegenerate) w.lattice 2 :=
    ⟨w.bong, w.isGood b.good⟩
  have hparameter : localBong.toBONG.binaryParameter =
      b.toBONG.adjacentParameter i hi := by
    change w.bong.valueUnit 1 / w.bong.valueUnit 0 =
      b.valueUnit ⟨i.val + 1, hi⟩ / b.valueUnit i
    rw [hwZero, hwOne]
  have hzeroOrderLocal : ordUnit K targetZero =
      ordUnit K (localBong.valueUnit 0) := by
    change ordUnit K targetZero = ordUnit K (w.bong.valueUnit 0)
    rw [hwZero]
    exact hzeroOrder
  have honeOrderLocal : ordUnit K targetOne =
      ordUnit K (localBong.valueUnit 1) := by
    change ordUnit K targetOne = ordUnit K (w.bong.valueUnit 1)
    rw [hwOne]
    exact honeOrder
  have hdetLocal : IsSquare
      ((localBong.valueUnit 0 * localBong.valueUnit 1) *
        (targetZero * targetOne)) := by
    change IsSquare
      ((w.bong.valueUnit 0 * w.bong.valueUnit 1) *
        (targetZero * targetOne))
    rw [hwZero, hwOne]
    exact hdet
  have huValueLocal : (u : Kˣ) =
      targetZero / localBong.valueUnit 0 := by
    change (u : Kˣ) = targetZero / w.bong.valueUnit 0
    rw [hwZero]
    exact huValue
  have huLocal : valuationUnitClassHom K u ∈
      beliNormGeneratorGroup K localBong.toBONG.binaryParameter := by
    rwa [hparameter]
  rcases exists_binaryExactValues localBong targetZero targetOne
      hzeroOrderLocal honeOrderLocal hdetLocal u huValueLocal huLocal with
    ⟨C, hCZero, hCOne⟩
  rcases b.toBONG.beliLemma49_ii b.good w C.toBONG C.good with ⟨R⟩
  let result : GoodBONG q L n := ⟨R.bong, R.good⟩
  have hinsideValue (j : Fin 2) :
      result.valueUnit ⟨i.val + j.val, by omega⟩ = C.valueUnit j := by
    apply Units.ext
    change R.bong.value ⟨i.val + j.val, by omega⟩ = C.toBONG.value j
    rw [← R.bong.quadratic_ambientVector,
      ← C.toBONG.quadratic_ambientVector]
    exact congrArg q.quadratic (R.inside_eq j)
  refine ⟨{
    bong := result
    valueUnit_left := ?_
    valueUnit_right := ?_
    valueUnit_before := ?_
    valueUnit_after := ?_ }⟩
  · have hindex : (⟨i.val + (0 : Fin 2).val, by omega⟩ : Fin n) = i := by
      apply Fin.ext
      simp
    calc
      result.valueUnit i = C.valueUnit 0 := by
        simpa only [hindex] using hinsideValue (0 : Fin 2)
      _ = targetZero := hCZero
  · have hindex :
        (⟨i.val + (1 : Fin 2).val, by omega⟩ : Fin n) =
          ⟨i.val + 1, hi⟩ := by
      apply Fin.ext
      rfl
    calc
      result.valueUnit ⟨i.val + 1, hi⟩ = C.valueUnit 1 := by
        simpa only [hindex] using hinsideValue (1 : Fin 2)
      _ = targetOne := hCOne
  · intro j hj
    apply Units.ext
    change R.bong.value j = b.toBONG.value j
    rw [← R.bong.quadratic_ambientVector,
      ← b.toBONG.quadratic_ambientVector, R.before_eq j hj]
  · intro j hj
    apply Units.ext
    change R.bong.value j = b.toBONG.value j
    rw [← R.bong.quadratic_ambientVector,
      ← b.toBONG.quadratic_ambientVector, R.after_eq j hj]

/-- Multiplication by a valuation unit leaves every BONG order unchanged. -/
theorem AdjacentMultiplierData.order_eq
    {n : Nat} {b : GoodBONG q L n} {i : Fin n}
    {hi : i.val + 1 < n} {u : valuationUnitSubgroup K}
    (D : AdjacentMultiplierData b i hi u) (j : Fin n) :
    D.bong.order j = b.order j := by
  change D.bong.toBONG.order j = b.toBONG.order j
  rw [D.bong.toBONG.order_eq_ordUnit, b.toBONG.order_eq_ordUnit]
  change ordUnit K (D.bong.valueUnit j) = ordUnit K (b.valueUnit j)
  by_cases hjLeft : j.val < i.val
  · rw [D.valueUnit_before j hjLeft]
  by_cases hjEq : j.val = i.val
  · have hji : j = i := Fin.ext hjEq
    rw [hji, D.valueUnit_left, ordUnit_mul]
    have hu : ordUnit K (u : Kˣ) = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K (u : Kˣ)).1 u.property
    rw [hu, zero_add]
  by_cases hjRight : j.val = i.val + 1
  · have hji : j = ⟨i.val + 1, hi⟩ := Fin.ext hjRight
    rw [hji, D.valueUnit_right, ordUnit_mul]
    have hu : ordUnit K (u : Kˣ) = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K (u : Kˣ)).1 u.property
    rw [hu, zero_add]
  · have hjAfter : i.val + 2 ≤ j.val := by omega
    rw [D.valueUnit_after j hjAfter]

/-- At the cut immediately after the changed left entry, the prefix product
is multiplied by exactly the chosen valuation unit. -/
theorem AdjacentMultiplierData.prefixProduct_leftBoundary
    {n : Nat} {b : GoodBONG q L n} {i : Fin n}
    {hi : i.val + 1 < n} {u : valuationUnitSubgroup K}
    (D : AdjacentMultiplierData b i hi u) :
    D.bong.prefixProduct (i.val + 1) =
      (u : Kˣ) * b.prefixProduct (i.val + 1) := by
  classical
  have hprefix : D.bong.prefixProduct i.val = b.prefixProduct i.val := by
    unfold GoodBONG.prefixProduct BONG.prefixProduct
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact D.valueUnit_before j hj
  change D.bong.toBONG.prefixProduct (i.val + 1) =
    (u : Kˣ) * b.toBONG.prefixProduct (i.val + 1)
  change D.bong.toBONG.prefixProduct i.val =
    b.toBONG.prefixProduct i.val at hprefix
  rw [D.bong.toBONG.prefixProduct_succ i.val i.isLt,
    b.toBONG.prefixProduct_succ i.val i.isLt, hprefix]
  change b.toBONG.prefixProduct i.val *
      D.bong.valueUnit ⟨i.val, i.isLt⟩ =
    (u : Kˣ) *
      (b.toBONG.prefixProduct i.val * b.valueUnit ⟨i.val, i.isLt⟩)
  have hiFin : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.ext rfl
  rw [hiFin, D.valueUnit_left]
  ac_rfl

/-- Signed even-prefix form of `prefixProduct_leftBoundary`. -/
theorem AdjacentMultiplierData.signedEvenPrefixProduct_leftBoundary
    {n : Nat} {b : GoodBONG q L n} {i : Fin n}
    {hi : i.val + 1 < n} {u : valuationUnitSubgroup K}
    (D : AdjacentMultiplierData b i hi u)
    (pairs : Nat) (hcut : 2 * pairs = i.val + 1) :
    D.bong.toBONG.signedEvenPrefixProduct pairs =
      (u : Kˣ) * b.toBONG.signedEvenPrefixProduct pairs := by
  unfold signedEvenPrefixProduct
  rw [hcut]
  change (-1 : Kˣ) ^ pairs * D.bong.prefixProduct (i.val + 1) = _
  rw [D.prefixProduct_leftBoundary]
  unfold GoodBONG.prefixProduct
  ac_rfl

/-- Every prefix containing both changed entries has its product multiplied by
the square of the chosen unit. -/
theorem AdjacentMultiplierData.prefixProduct_afterChangedPair
    {n : Nat} {b : GoodBONG q L n} {i : Fin n}
    {hi : i.val + 1 < n} {u : valuationUnitSubgroup K}
    (D : AdjacentMultiplierData b i hi u)
    (m : Nat) (hlower : i.val + 2 ≤ m) (hupper : m ≤ n) :
    D.bong.prefixProduct m = (u : Kˣ) ^ 2 * b.prefixProduct m := by
  have hbase : D.bong.prefixProduct (i.val + 2) =
      (u : Kˣ) ^ 2 * b.prefixProduct (i.val + 2) := by
    have hboundary := D.prefixProduct_leftBoundary
    have hright := D.valueUnit_right
    change D.bong.toBONG.prefixProduct (i.val + 1) =
      (u : Kˣ) * b.toBONG.prefixProduct (i.val + 1) at hboundary
    change D.bong.toBONG.valueUnit ⟨i.val + 1, hi⟩ =
      (u : Kˣ) * b.toBONG.valueUnit ⟨i.val + 1, hi⟩ at hright
    change D.bong.toBONG.prefixProduct (i.val + 2) =
      (u : Kˣ) ^ 2 * b.toBONG.prefixProduct (i.val + 2)
    rw [D.bong.toBONG.prefixProduct_succ (i.val + 1) hi,
      b.toBONG.prefixProduct_succ (i.val + 1) hi,
      hboundary, hright]
    simp only [pow_two]
    ac_rfl
  induction m, hlower using Nat.le_induction with
  | base => exact hbase
  | succ m hm ih =>
      have hmBound : m < n := by omega
      have ih' := ih (by omega)
      change D.bong.toBONG.prefixProduct m =
        (u : Kˣ) ^ 2 * b.toBONG.prefixProduct m at ih'
      change D.bong.toBONG.prefixProduct (m + 1) =
        (u : Kˣ) ^ 2 * b.toBONG.prefixProduct (m + 1)
      rw [D.bong.toBONG.prefixProduct_succ m hmBound,
        b.toBONG.prefixProduct_succ m hmBound, ih']
      have hafter : D.bong.valueUnit ⟨m, hmBound⟩ =
          b.valueUnit ⟨m, hmBound⟩ :=
        D.valueUnit_after ⟨m, hmBound⟩ hm
      change D.bong.toBONG.valueUnit ⟨m, hmBound⟩ =
        b.toBONG.valueUnit ⟨m, hmBound⟩ at hafter
      rw [hafter]
      ac_rfl

/-- Changing a norm generator on either neighboring pair produces a good
BONG whose middle adjacent parameter is multiplied by the prescribed unit. -/
theorem exists_goodBONG_adjacentParameter_eq_mul_of_adjacentMultiplier
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    {n : Nat} (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hpair : i.val + 1 < n)
    (ζ : valuationUnitSubgroup K)
    (hζ : (∃ hleft : 1 ≤ i.val,
        valuationUnitClassHom K ζ ∈ beliNormGeneratorGroup K
          (b.valueUnit i / b.valueUnit ⟨i.val - 1, by omega⟩)) ∨
      (∃ hright : i.val + 2 < n,
        valuationUnitClassHom K ζ ∈ beliNormGeneratorGroup K
          (b.valueUnit ⟨i.val + 2, hright⟩ /
            b.valueUnit ⟨i.val + 1, hpair⟩))) :
    ∃ c : GoodBONG q L n,
      c.toBONG.adjacentParameter i hpair =
        (ζ : Kˣ) * b.adjacentParameter i hpair := by
  let gb : GoodBONG q L n := ⟨b, hgood⟩
  rcases hζ with ⟨hleft, hζLeft⟩ | ⟨hright, hζRight⟩
  · let j : Fin n := ⟨i.val - 1, by omega⟩
    have hj : j.val + 1 < n := by
      dsimp only [j]
      omega
    have hparameter : gb.toBONG.adjacentParameter j hj =
        b.valueUnit i / b.valueUnit ⟨i.val - 1, by omega⟩ := by
      unfold adjacentParameter
      congr 2
      apply Fin.ext
      dsimp only [j]
      omega
    have hζInv : valuationUnitClassHom K ζ⁻¹ ∈
        beliNormGeneratorGroup K (gb.toBONG.adjacentParameter j hj) := by
      rw [hparameter, map_inv]
      exact (beliNormGeneratorGroup K
        (b.valueUnit i / b.valueUnit ⟨i.val - 1, by omega⟩)).inv_mem hζLeft
    rcases exists_adjacentMultiplierData gb j hj ζ⁻¹ hζInv with ⟨D⟩
    have hcurrent : D.bong.valueUnit i =
        ((ζ : Kˣ)⁻¹ * b.valueUnit i) := by
      have hindex : (⟨j.val + 1, hj⟩ : Fin n) = i := by
        apply Fin.ext
        dsimp only [j]
        omega
      have h := D.valueUnit_right
      rw [hindex] at h
      change D.bong.valueUnit i =
        ((ζ : Kˣ)⁻¹ * b.valueUnit i) at h
      exact h
    have hnext : D.bong.valueUnit ⟨i.val + 1, hpair⟩ =
        b.valueUnit ⟨i.val + 1, hpair⟩ :=
      D.valueUnit_after ⟨i.val + 1, hpair⟩ (by
        dsimp only [j]
        omega)
    have hmiddle : D.bong.toBONG.adjacentParameter i hpair =
        (ζ : Kˣ) * b.adjacentParameter i hpair := by
      unfold adjacentParameter
      change D.bong.valueUnit ⟨i.val + 1, hpair⟩ /
          D.bong.valueUnit i =
        (ζ : Kˣ) *
          (b.valueUnit ⟨i.val + 1, hpair⟩ / b.valueUnit i)
      rw [hcurrent, hnext]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ac_rfl
    exact ⟨D.bong, hmiddle⟩
  · let j : Fin n := ⟨i.val + 1, by omega⟩
    have hj : j.val + 1 < n := by
      dsimp only [j]
      omega
    have hparameter : gb.toBONG.adjacentParameter j hj =
        b.valueUnit ⟨i.val + 2, hright⟩ /
          b.valueUnit ⟨i.val + 1, by omega⟩ := by
      unfold adjacentParameter
      congr 2
    have hζRight' : valuationUnitClassHom K ζ ∈
        beliNormGeneratorGroup K (gb.toBONG.adjacentParameter j hj) := by
      rwa [hparameter]
    rcases exists_adjacentMultiplierData gb j hj ζ hζRight' with ⟨D⟩
    have hcurrent : D.bong.valueUnit i = b.valueUnit i :=
      D.valueUnit_before i (by
        dsimp only [j]
        omega)
    have hnext : D.bong.valueUnit ⟨i.val + 1, hpair⟩ =
        (ζ : Kˣ) * b.valueUnit ⟨i.val + 1, hpair⟩ := by
      have h := D.valueUnit_left
      change D.bong.valueUnit j = (ζ : Kˣ) * b.valueUnit j at h
      simpa only [j] using h
    have hmiddle : D.bong.toBONG.adjacentParameter i hpair =
        (ζ : Kˣ) * b.adjacentParameter i hpair := by
      unfold adjacentParameter
      change D.bong.valueUnit ⟨i.val + 1, hpair⟩ /
          D.bong.valueUnit i =
        (ζ : Kˣ) *
          (b.valueUnit ⟨i.val + 1, hpair⟩ / b.valueUnit i)
      rw [hcurrent, hnext]
      simp only [div_eq_mul_inv, mul_assoc]
    exact ⟨D.bong, hmiddle⟩

/-- A neighboring norm-generator change preserves admissibility of the
twisted middle binary parameter. -/
theorem isBinaryParameterAdmissible_mul_adjacentParameter_of_adjacentMultiplier
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    {n : Nat} (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hpair : i.val + 1 < n)
    (ζ : valuationUnitSubgroup K)
    (hζ : (∃ hleft : 1 ≤ i.val,
        valuationUnitClassHom K ζ ∈ beliNormGeneratorGroup K
          (b.valueUnit i / b.valueUnit ⟨i.val - 1, by omega⟩)) ∨
      (∃ hright : i.val + 2 < n,
        valuationUnitClassHom K ζ ∈ beliNormGeneratorGroup K
          (b.valueUnit ⟨i.val + 2, hright⟩ /
            b.valueUnit ⟨i.val + 1, hpair⟩))) :
    IsBinaryParameterAdmissible
      ((ζ : Kˣ) * b.adjacentParameter i hpair) := by
  rcases exists_goodBONG_adjacentParameter_eq_mul_of_adjacentMultiplier
      b hgood i hpair ζ hζ with ⟨c, hparameter⟩
  rw [← hparameter]
  exact c.toBONG.adjacentParameter_isBinaryParameterAdmissible i hpair

/-- Beli (2003), Corollary 4.10(iii), obtained by changing the adjacent
norm generator on the left or on the right and then applying the binary
spinor formula to the new middle pair. -/
theorem twistedAdjacentSpinorGroup_subset_of_adjacentMultiplier
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinarySpinorLocalLaws.{u, v} K]
    {n : Nat} (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hpair : i.val + 1 < n)
    (ζ : valuationUnitSubgroup K)
    (hζ : (∃ hleft : 1 ≤ i.val,
        valuationUnitClassHom K ζ ∈ beliNormGeneratorGroup K
          (b.valueUnit i / b.valueUnit ⟨i.val - 1, by omega⟩)) ∨
      (∃ hright : i.val + 2 < n,
        valuationUnitClassHom K ζ ∈ beliNormGeneratorGroup K
          (b.valueUnit ⟨i.val + 2, hright⟩ /
            b.valueUnit ⟨i.val + 1, hpair⟩))) :
    (beliSpinorGroup K
        (unitSquareClass K ((ζ : Kˣ) * b.adjacentParameter i hpair)) :
      Set (SquareClass K)) ⊆
      Lattice.spinorNormImage (q := q) (L := L) := by
  rcases exists_goodBONG_adjacentParameter_eq_mul_of_adjacentMultiplier
      b hgood i hpair ζ hζ with ⟨c, hparameter⟩
  have hbinary := c.toBONG.beliCorollary410_ii c.good i hpair
  rw [adjacentUnitSquareClass, hparameter] at hbinary
  exact hbinary

/-- Corollary 4.10(iii) introduces no independent local law: it follows from
the binary value theorem and the already proved segment-replacement law. -/
instance beliCorollary410IIILawsOfAdjacentMultiplier
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinarySpinorLocalLaws.{u, v} K] :
    BeliCorollary410IIILaws.{u, v} K where
  twistedAdjacentSpinorGroup_subset :=
    twistedAdjacentSpinorGroup_subset_of_adjacentMultiplier

end BONG

end Bong
