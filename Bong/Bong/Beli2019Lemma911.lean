/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma71Index
import Bong.Bong.Beli2009BinaryRemarks
import Bong.Bong.Beli2019Lemma79NormOrder
import Bong.Bong.Beli2019VolumeOrders
import Bong.Bong.BinaryValueIsometry
import Bong.Lattice.BasisIsometry
import Bong.Lattice.FormRescale

/-!
# Beli (2019), Lemma 9.11: the binary non-generator sublattice

Let `b` be a good BONG of a binary lattice `L`, and suppose
`S₂ - S₁ + d(-a₁a₂) = 1`.  Beli's Lemma 7.1 identifies the vectors which are
not norm generators of `L` with an index-`p` sublattice.  This file proves
that the latter has both BONG orders shifted by one and is isometric to the
form rescaling `L^{π ε}` for a valuation unit `ε`.

The proof is intrinsic: equality of the two adjacent quadratic defects and
the determinant square class determine the binary rescaling.  No local-law
interface specific to Lemma 9.11 is introduced.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice.Isometry

/-- A lattice isometry remains an isometry after rescaling both quadratic
forms by the same nonzero scalar. -/
noncomputable def rescaleUnit
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (f : Lattice.Isometry q r L M) (a : Kˣ) :
    Lattice.Isometry (q.rescaleUnit a) (r.rescaleUnit a) L M where
  toLinearEquiv := f.toLinearEquiv
  map_bilin x y := by
    simp only [QuadraticSpace.rescaleUnit_bilin_apply, f.map_bilin]
  map_mem := f.map_mem

/-- Iterated form rescaling is identified with multiplication of the two
rescaling factors, by the identity map on the underlying lattice. -/
noncomputable def rescaleUnit_mul
    (r : QuadraticSpace K V) (M : Lattice K V) (a b : Kˣ) :
    Lattice.Isometry (r.rescaleUnit (a * b))
      ((r.rescaleUnit b).rescaleUnit a) M M where
  toLinearEquiv := LinearEquiv.refl K V
  map_bilin x y := by
    simp only [LinearEquiv.refl_apply,
      QuadraticSpace.rescaleUnit_bilin_apply, Units.val_mul]
    ring
  map_mem := fun _ => Iff.rfl

end Lattice.Isometry

namespace BONG.GoodBONG

/-- The numerical hypothesis in Beli (2019), Lemma 9.11 excludes the
exceptional binary gap `-2e`. -/
theorem firstGap_ne_negTwoE_of_gap_add_adjacentDefect_eq_one
    [QuadraticDefectLaws K]
    (b : GoodBONG q L 2)
    (hboundary :
      (((b.orderGap 0 : Int) : ℚ) : WithTop ℚ) +
          b.adjacentDefect 0 = 1) :
    b.orderGap 0 ≠ -(2 * (ramificationIndex K : Int)) := by
  intro hgap
  let a : Kˣ := -b.toBONG.binaryParameter
  have hadmissible :=
    b.toBONG.binaryParameter_isBinaryParameterAdmissible
  have habsolute : HasNonnegativeAbsoluteQuadraticDefect a := by
    have hcriterion :=
      (BONG.isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
        b.toBONG.binaryParameter).1 hadmissible
    simpa only [a] using hcriterion.2
  have horderNeg (z : Kˣ) : ordUnit K (-z) = ordUnit K z := by
    apply WithTop.coe_injective
    simp only [coe_ordUnit, Units.val_neg, ord_neg]
  have haOrder : ordUnit K a = b.orderGap 0 := by
    dsimp only [a]
    rw [horderNeg]
    exact b.binaryParameter_orderGap
  have haNegative : ordUnit K a < 0 := by
    rw [haOrder, hgap]
    have he : 0 < (ramificationIndex K : Int) := by
      exact_mod_cast ramificationIndex_pos K
    omega
  have hthresholdInt :
      (absoluteDefectThreshold a : Int) =
        2 * (ramificationIndex K : Int) := by
    rw [coe_absoluteDefectThreshold_eq_neg_of_neg haNegative,
      haOrder, hgap]
    ring
  have hthresholdNat :
      absoluteDefectThreshold a = 2 * ramificationIndex K := by
    exact_mod_cast hthresholdInt
  have hlower :
      ((2 * ramificationIndex K : Nat) : ℕ∞) ≤ quadraticDefect K a := by
    have h :=
      (hasNonnegativeAbsoluteQuadraticDefect_iff_threshold_le a).1
        habsolute
    rwa [hthresholdNat] at h
  by_cases hsquare : IsSquare a
  · have hdefect : b.adjacentDefect 0 = ⊤ := by
      rw [b.binary_adjacentDefect_eq_parameterDefect]
      exact defectOrder_eq_top_of_isSquare hsquare
    rw [hdefect] at hboundary
    simp at hboundary
  · have hupper :
        quadraticDefect K a ≤
          ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      quadraticDefect_le_two_mul_e_of_not_isSquare (K := K) hsquare
    have hraw : quadraticDefect K a =
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      le_antisymm hupper hlower
    have hdefect : b.adjacentDefect 0 =
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      rw [b.binary_adjacentDefect_eq_parameterDefect]
      unfold defectOrder
      rw [hraw]
      rfl
    rw [hgap, hdefect] at hboundary
    norm_cast at hboundary
    push_cast at hboundary
    linarith

/-- Binary admissibility gives `S₂-S₁+d(-b₁b₂) ≥ 0` whenever the
quadratic defect is finite. -/
theorem orderGap_add_adjacentDefect_nonneg_of_ne_top
    (b : GoodBONG q L 2)
    (hfinite : b.adjacentDefect 0 ≠ ⊤) :
    (0 : WithTop ℚ) ≤
      (((b.orderGap 0 : Int) : ℚ) : WithTop ℚ) +
        b.adjacentDefect 0 := by
  let a := b.toBONG.binaryParameter
  have hadmissible :=
    b.toBONG.binaryParameter_isBinaryParameterAdmissible
  have hparameterFinite : beliParameterDefect K a ≠ ⊤ := by
    intro htop
    apply hfinite
    rw [b.binary_adjacentDefect_eq_parameterDefect]
    unfold defectOrder
    have hraw : quadraticDefect K (-b.toBONG.binaryParameter) = ⊤ := by
      simpa only [a, beliParameterDefect] using htop
    rw [hraw]
    rfl
  have hnonneg := beli2009_order_add_parameterDefect_nonneg
    (K := K) hadmissible hparameterFinite
  have hdefect : b.adjacentDefect 0 =
      ((((beliParameterDefect K a).toNat : Nat) : ℚ) : WithTop ℚ) := by
    rw [b.binary_adjacentDefect_eq_parameterDefect]
    unfold defectOrder
    have hraw : quadraticDefect K (-b.toBONG.binaryParameter) =
        ((beliParameterDefect K a).toNat : ℕ∞) := by
      have hcoe := (ENat.coe_toNat hparameterFinite).symm
      simpa only [a, beliParameterDefect] using hcoe
    rw [hraw]
    rfl
  rw [hdefect]
  norm_cast
  change (0 : Int) ≤ b.orderGap 0 +
    ((beliParameterDefect K a).toNat : Int)
  simpa only [a, b.binaryParameter_orderGap] using hnonneg

/-- The raw binary adjacent defect depends only on the ambient quadratic
space: changing the lattice changes the two-value product by a square. -/
theorem adjacentDefect_eq_of_binaryBONGs
    {M : Lattice K V}
    (b : GoodBONG q L 2) (c : GoodBONG q M 2) :
    c.adjacentDefect 0 = b.adjacentDefect 0 := by
  rcases BONG.exists_valueProduct_eq_mul_square
      b.toBONG c.toBONG with ⟨p, hp⟩
  unfold adjacentDefect adjacentProduct
  change defectOrder (K := K)
      (-(c.toBONG.valueUnit 0 * c.toBONG.valueUnit 1)) =
    defectOrder (K := K)
      (-(b.toBONG.valueUnit 0 * b.toBONG.valueUnit 1))
  rw [← c.toBONG.valueProduct_fin_two,
    ← b.toBONG.valueProduct_fin_two, hp]
  have hneg : -(b.toBONG.valueProduct * p ^ 2) =
      (-b.toBONG.valueProduct) * p ^ 2 := by
    simp
  rw [hneg, defectOrder_mul_square]

/-- For the index-`p` non-norm-generator lattice of Lemma 7.1, the two
binary BONG orders both increase by exactly one under the numerical
hypothesis of Lemma 9.11. -/
theorem Beli2019Lemma71Data.binaryOrders_eq_add_one
    [QuadraticDefectLaws K]
    [BeliCorollary44Laws.{u, v} K]
    (b : GoodBONG q L 2)
    (hboundary :
      (((b.orderGap 0 : Int) : ℚ) : WithTop ℚ) +
          b.adjacentDefect 0 = 1)
    (D : Beli2019Lemma71Data b)
    (c : BONG V q D.lattice 2) :
    c.order 0 = b.order 0 + 1 ∧
      c.order 1 = b.order 1 + 1 := by
  let cGood : GoodBONG q D.lattice 2 :=
    ⟨c, c.isGood_binary⟩
  have hnormLe : Lattice.normIdeal q D.lattice ≤
      Lattice.normIdeal q L :=
    Lattice.normIdeal_mono q D.indexP.lattice_le
  have hnormNe : Lattice.normIdeal q D.lattice ≠
      Lattice.normIdeal q L := by
    intro hnormEq
    let x : V := c.head
    have hxGeneratorL : Lattice.IsNormGenerator q L x := by
      refine ⟨D.indexP.lattice_le c.head_isNormGenerator.mem, ?_⟩
      exact hnormEq.symm.trans c.head_isNormGenerator.normIdeal_eq
    have hxMem : x ∈ D.lattice := c.head_isNormGenerator.mem
    rw [D.lattice_eq,
      Lattice.mem_nonNormGeneratorLattice_iff] at hxMem
    exact hxMem.2 hxGeneratorL
  have hnormLt : Lattice.normIdeal q D.lattice <
      Lattice.normIdeal q L :=
    lt_of_le_of_ne hnormLe hnormNe
  have hfirstLower : b.order 0 + 1 ≤ c.order 0 :=
    b.toBONG.order_zero_add_one_le_of_normIdeal_lt c hnormLt
  have hvolume := D.indexPInclusion.volumeOrder_eq
  have hsum : c.order 0 + c.order 1 =
      b.order 0 + b.order 1 + 2 := by
    rw [c.volumeOrder_eq_sum_order,
      b.toBONG.volumeOrder_eq_sum_order] at hvolume
    simpa only [GoodBONG.order, Fin.sum_univ_two] using hvolume
  have hdefectEq : cGood.adjacentDefect 0 =
      b.adjacentDefect 0 :=
    adjacentDefect_eq_of_binaryBONGs b cGood
  have hbFinite : b.adjacentDefect 0 ≠ ⊤ := by
    intro htop
    rw [htop] at hboundary
    simp at hboundary
  have hcFinite : cGood.adjacentDefect 0 ≠ ⊤ := by
    rw [hdefectEq]
    exact hbFinite
  have hcAdmissible :=
    cGood.orderGap_add_adjacentDefect_nonneg_of_ne_top hcFinite
  rcases WithTop.ne_top_iff_exists.mp hbFinite with ⟨d, hd⟩
  have hboundaryQ : (b.orderGap 0 : ℚ) + d = 1 := by
    rw [← hd] at hboundary
    norm_cast at hboundary
  have hcAdmissibleQ : 0 ≤ (cGood.orderGap 0 : ℚ) + d := by
    rw [hdefectEq, ← hd] at hcAdmissible
    norm_cast at hcAdmissible
  have hgapLowerQ : (b.orderGap 0 : ℚ) - 1 ≤
      (cGood.orderGap 0 : ℚ) := by
    linarith
  have hgapLower : b.orderGap 0 - 1 ≤ cGood.orderGap 0 := by
    exact_mod_cast hgapLowerQ
  have hfirst : c.order 0 = b.order 0 + 1 := by
    change b.order 1 - b.order 0 - 1 ≤
      c.order 1 - c.order 0 at hgapLower
    omega
  have hsecond : c.order 1 = b.order 1 + 1 := by
    omega
  exact ⟨hfirst, hsecond⟩

/-- Complete formal output of Beli (2019), Lemma 9.11.  The lattice from
Lemma 7.1 is the sublattice of non-norm-generators, its binary orders are
`R₁+1,R₂+1`, and it is isometric to `L^{π ε}` for a valuation unit `ε`. -/
structure Beli2019Lemma911Data
    [BeliCorollary44Laws.{u, v} K]
    (b : GoodBONG q L 2) where
  lemma71 : Beli2019Lemma71Data b
  bong : BONG V q lemma71.lattice 2
  firstOrder : bong.order 0 = b.order 0 + 1
  secondOrder : bong.order 1 = b.order 1 + 1
  epsilon : Kˣ
  epsilon_isValuationUnit : IsValuationUnit K (epsilon : K)
  isometricFormRescale :
    Lattice.IsIsometric q
      (q.rescaleUnit (uniformizerUnit K * epsilon))
      lemma71.lattice L

end BONG.GoodBONG

namespace BONG

/-- If the two values of a binary BONG are obtained by a common form
rescaling and a valuation-unit square in the second coordinate, then the
corresponding lattices are isometric after rescaling the form. -/
theorem binary_isIsometric_formRescale_of_valueUnit_relations
    {M : Lattice K V}
    (b : BONG V q L 2) (c : BONG V q M 2)
    (lambda s : Kˣ)
    (hs : IsValuationUnit K (s : K))
    (hzero : c.valueUnit 0 = lambda * b.valueUnit 0)
    (hone : c.valueUnit 1 =
      lambda * b.valueUnit 1 * s ^ 2) :
    Lattice.IsIsometric q (q.rescaleUnit lambda) M L := by
  have hparameter : b.binaryParameter * s ^ 2 = c.binaryParameter := by
    unfold binaryParameter
    rw [hzero, hone]
    simp only [pow_two, div_eq_mul_inv]
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero lambda, Units.ne_zero (b.valueUnit 0),
      Units.ne_zero s]
  have hparameterCoe :
      (b.binaryParameter : K) * (s : K) ^ 2 =
        (c.binaryParameter : K) :=
    congrArg Units.val hparameter
  let cScaled : K := c.binaryModelCoefficient / (s : K)
  have hsInvMem : (s : K)⁻¹ ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    unfold Dyadic.IsIntegral
    rw [AddValuation.map_inv, hs]
    simp
  have hcAdmissible := c.binaryModelCoefficient_isAdmissibleWitness
  have hbAdmissible := b.binaryModelCoefficient_isAdmissibleWitness
  have hcScaledTwo : (2 : K) * cScaled ∈ IntegerRing K := by
    have h := (IntegerRing K).mul_mem
      ((2 : K) * c.binaryModelCoefficient) ((s : K)⁻¹)
      hcAdmissible.1 hsInvMem
    simpa only [cScaled, div_eq_mul_inv,
      mul_assoc] using h
  have hcScaledDiag :
      cScaled ^ 2 + (b.binaryParameter : K) ∈ IntegerRing K := by
    have hsInvSqMem : ((s : K)⁻¹) ^ 2 ∈ IntegerRing K := by
      simpa only [pow_two] using
        (IntegerRing K).mul_mem _ _ hsInvMem hsInvMem
    have h := (IntegerRing K).mul_mem
      (c.binaryModelCoefficient ^ 2 + (c.binaryParameter : K))
      (((s : K)⁻¹) ^ 2) hcAdmissible.2 hsInvSqMem
    have heq : cScaled ^ 2 + (b.binaryParameter : K) =
        (c.binaryModelCoefficient ^ 2 + (c.binaryParameter : K)) *
          ((s : K)⁻¹) ^ 2 := by
      dsimp only [cScaled]
      rw [← hparameterCoe]
      field_simp [Units.ne_zero s]
    rw [heq]
    exact h
  have hshear :
      cScaled - b.binaryModelCoefficient ∈ IntegerRing K :=
    binaryShear_sub_mem_integerRing b.binaryParameter
      cScaled b.binaryModelCoefficient
      hcScaledTwo hcScaledDiag hbAdmissible.1 hbAdmissible.2
  have hsquareModel :=
    rescaledBinaryModel_isIsometric_mul_valuationUnit_square
      (c.valueUnit 0) c.binaryParameter b.binaryParameter s
      c.binaryModelCoefficient hs hparameter
  have hshearModel :=
    rescaledBinaryModel_isIsometric_of_shear_sub_integral
      (c.valueUnit 0) b.binaryParameter
      cScaled b.binaryModelCoefficient hshear
  let assoc : Lattice.Isometry
      (QuadraticSpace.rescaleUnit (c.valueUnit 0)
        (QuadraticSpace.binaryModel b.binaryParameter
          b.binaryModelCoefficient))
      (QuadraticSpace.rescaleUnit lambda b.normalizedBinaryModelSpace)
      (binaryModelLattice (K := K)) (binaryModelLattice (K := K)) := by
    refine {
      toLinearEquiv := LinearEquiv.refl K (Fin 2 → K)
      map_bilin := ?_
      map_mem := fun _ => Iff.rfl }
    intro x y
    simp only [LinearEquiv.refl_apply, normalizedBinaryModelSpace,
      QuadraticSpace.rescaleUnit_bilin_apply, hzero, Units.val_mul]
    ring
  rcases c.normalizedBinaryModel_isIsometric with ⟨fc⟩
  rcases b.normalizedBinaryModel_isIsometric with ⟨fb⟩
  let fbScaled := Lattice.Isometry.rescaleUnit fb lambda
  rcases hsquareModel with ⟨fsquare⟩
  rcases hshearModel with ⟨fshear⟩
  exact ⟨fc.symm.trans
    (fsquare.trans (fshear.trans (assoc.trans fbScaled)))⟩

end BONG

namespace BONG.GoodBONG

/-- Beli (2019), Lemma 9.11. -/
theorem beli2019Lemma911
    [QuadraticDefectLaws K]
    [PerfectResidueFieldLaws K]
    [BeliCorollary44Laws.{u, v} K]
    (b : GoodBONG q L 2)
    (hboundary :
      (((b.orderGap 0 : Int) : ℚ) : WithTop ℚ) +
          b.adjacentDefect 0 = 1) :
    Nonempty (Beli2019Lemma911Data b) := by
  have hgap : b.order 1 - b.order 0 ≠
      -(2 * (ramificationIndex K : Int)) := by
    exact b.firstGap_ne_negTwoE_of_gap_add_adjacentDefect_eq_one
      hboundary
  let D := b.beli2019Lemma71 hgap
  have hfin : Module.finrank K V = 2 :=
    b.toBONG.length_eq_finrank.symm
  let c : BONG V q D.lattice 2 :=
    (BONG.ofLattice q D.lattice).castLength hfin
  have horders := D.binaryOrders_eq_add_one b hboundary c
  rcases BONG.exists_valueProduct_eq_mul_square
      b.toBONG c with ⟨p, hp⟩
  let lambda : Kˣ := c.valueUnit 0 / b.valueUnit 0
  have hzero : c.valueUnit 0 = lambda * b.valueUnit 0 := by
    dsimp only [lambda]
    simp
  have hlambdaOrder : ordUnit K lambda = 1 := by
    dsimp only [lambda]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
      ← c.order_eq_ordUnit]
    change c.order 0 + -b.order 0 = 1
    rw [horders.1]
    omega
  have hpiOrder : ordUnit K (uniformizerUnit K) = 1 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, coe_uniformizerUnit, ord_uniformizer]
    rfl
  let epsilon : Kˣ := lambda / uniformizerUnit K
  have hepsilonOrder : ordUnit K epsilon = 0 := by
    dsimp only [epsilon]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
      hlambdaOrder, hpiOrder]
    omega
  have hepsilonUnit : IsValuationUnit K (epsilon : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K epsilon).2 hepsilonOrder
  have hlambdaFactor : uniformizerUnit K * epsilon = lambda := by
    dsimp only [epsilon]
    simp only [div_eq_mul_inv]
    rw [mul_comm]
    simp
  let s : Kˣ := p / lambda
  have hpValues : c.valueUnit 0 * c.valueUnit 1 =
      b.valueUnit 0 * b.valueUnit 1 * p ^ 2 := by
    simpa only [BONG.valueProduct_fin_two, GoodBONG.valueUnit] using hp
  have hone : c.valueUnit 1 =
      lambda * b.valueUnit 1 * s ^ 2 := by
    apply mul_left_cancel (a := c.valueUnit 0)
    rw [hpValues]
    dsimp only [s]
    rw [hzero]
    simp only [div_eq_mul_inv, pow_two]
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero lambda]
  have hsOrder : ordUnit K s = 0 := by
    have h := congrArg (ordUnit K) hone
    rw [ordUnit_mul, ordUnit_mul, ordUnit_pow,
      ← c.order_eq_ordUnit] at h
    change c.order 1 = ordUnit K lambda + b.order 1 +
      2 * ordUnit K s at h
    rw [horders.2, hlambdaOrder] at h
    omega
  have hsUnit : IsValuationUnit K (s : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K s).2 hsOrder
  have hisometricLambda :=
    BONG.binary_isIsometric_formRescale_of_valueUnit_relations
      b.toBONG c lambda s hsUnit hzero hone
  have hisometric :
      Lattice.IsIsometric q
        (q.rescaleUnit (uniformizerUnit K * epsilon))
        D.lattice L := by
    rw [hlambdaFactor]
    exact hisometricLambda
  exact ⟨{
    lemma71 := D
    bong := c
    firstOrder := horders.1
    secondOrder := horders.2
    epsilon := epsilon
    epsilon_isValuationUnit := hepsilonUnit
    isometricFormRescale := hisometric }⟩

end BONG.GoodBONG

end Bong
