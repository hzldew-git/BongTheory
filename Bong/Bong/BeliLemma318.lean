/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma317
import Bong.Bong.BinaryAutomorphism
import Bong.Bong.BinaryNormGeneratorSpinorInclusion
import Bong.Bong.OrthogonalBasis

/-!
# Beli 2003, Lemma 3.18

This file studies two equal-value norm generators of a binary lattice.  The
first part proves directly that reflection in their anisotropic difference is
integral and identifies the resulting product of reflection classes.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace QuadraticSpace

omit [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
/-- Reflection in `x - x'` carries `x` to `x'` when the two vectors have the
 same quadratic value. -/
theorem reflectionLinearEquiv_sub_apply_left_of_quadratic_eq
    (q : QuadraticSpace K V) (x x' : V)
    (hsub : q.IsAnisotropic (x - x'))
    (heq : q.quadratic x = q.quadratic x') :
    q.reflectionLinearEquiv (x - x') hsub x = x' := by
  have hnumerator :
      2 * q.bilin (x - x') x = q.quadratic (x - x') := by
    simp only [quadratic, LinearMap.BilinForm.sub_left,
      LinearMap.BilinForm.sub_right]
    have heq' : q.bilin x x = q.bilin x' x' := heq
    rw [q.isSymm.eq x' x]
    linear_combination heq'
  have hcoefficient :
      2 * q.bilin (x - x') x / q.quadratic (x - x') = 1 := by
    rw [hnumerator, div_self hsub]
  rw [q.reflectionLinearEquiv_apply, hcoefficient, one_smul]
  abel

end QuadraticSpace

namespace Dyadic

/-- If `1 - α²` has order strictly above `2e`, exactly one of `1 - α` and
`1 + α` has order `e = ord(2)` and the other has larger order. -/
theorem one_sub_one_add_order_dichotomy_of_two_ord_two_lt
    (α : K)
    (hlarge : ord K (2 : K) + ord K (2 : K) <
      ord K (1 - α ^ 2)) :
    (ord K (1 - α) = ord K (2 : K) ∧
        ord K (2 : K) < ord K (1 + α)) ∨
      (ord K (1 + α) = ord K (2 : K) ∧
        ord K (2 : K) < ord K (1 - α)) := by
  have hfactor :
      ord K (1 - α) + ord K (1 + α) = ord K (1 - α ^ 2) := by
    calc
      ord K (1 - α) + ord K (1 + α) =
          ord K ((1 - α) * (1 + α)) := (ord_mul K _ _).symm
      _ = ord K (1 - α ^ 2) := by
        congr 1
        ring
  have hsum : ord K (2 : K) + ord K (2 : K) <
      ord K (1 - α) + ord K (1 + α) := by
    rwa [hfactor]
  by_cases hminus : ord K (2 : K) < ord K (1 - α)
  · right
    refine ⟨?_, hminus⟩
    have hid : (1 + α : K) = 2 - (1 - α) := by ring
    rw [hid]
    exact (ord K).map_sub_eq_of_lt_left hminus
  · left
    have hminusLe : ord K (1 - α) ≤ ord K (2 : K) :=
      le_of_not_gt hminus
    have hplus : ord K (2 : K) < ord K (1 + α) := by
      by_contra hnot
      have hplusLe : ord K (1 + α) ≤ ord K (2 : K) :=
        le_of_not_gt hnot
      exact (not_lt_of_ge (add_le_add hminusLe hplusLe)) hsum
    refine ⟨?_, hplus⟩
    have hid : (1 - α : K) = 2 - (1 + α) := by ring
    rw [hid]
    exact (ord K).map_sub_eq_of_lt_left hplus

/-- An integral square times a parameter of order above `2e` still has order
above `2e`.  This is the valuation step in Lemma 3.18(ii). -/
theorem two_ord_two_lt_order_one_sub_sq_of_integral_parameter
    (a : Kˣ) (α β : K) (hβ : β ∈ IntegerRing K)
    (horder : 2 * (ramificationIndex K : Int) < ordUnit K a)
    (heq : 1 - α ^ 2 = β ^ 2 * (a : K)) :
    ord K (2 : K) + ord K (2 : K) < ord K (1 - α ^ 2) := by
  have hβSq : β ^ 2 ∈ IntegerRing K :=
    (IntegerRing K).pow_mem hβ 2
  have hβSqNonneg : 0 ≤ ord K (β ^ 2) :=
    (mem_integerRing_iff K).1 hβSq
  have hparameter : ord K (2 : K) + ord K (2 : K) <
      ord K (a : K) := by
    have horder' : (ramificationIndex K : Int) +
        ramificationIndex K < ordUnit K a := by omega
    rw [← ramificationIndex_spec K, ← coe_ordUnit]
    exact_mod_cast horder'
  rw [heq, ord_mul]
  exact hparameter.trans_le (by
    simpa [add_comm] using
      add_le_add_left hβSqNonneg (ord K (a : K)))

/-- Representative-free form of Beli (2003), Lemma 3.13(i): lowering a
parameter by the square of `π^e` turns `G'` into the norm-generator group. -/
theorem beliAuxiliarySpinorGroup_eq_div_ramificationSquare
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    beliAuxiliarySpinorGroup K a hR =
      beliNormGeneratorSquareClassGroup K
        (a / uniformizerPowerUnit K (ramificationIndex K : Int) ^ 2) := by
  let R : Int := ordUnit K a
  let ε : Kˣ := normalizedUnitPart K a
  let s : Kˣ := uniformizerPowerUnit K (ramificationIndex K : Int)
  have hε : IsValuationUnit K (ε : K) :=
    normalizedUnitPart_isValuationUnit K a
  have ha : uniformizerPowerUnit K R * ε = a :=
    uniformizerPower_mul_normalizedUnitPart K a
  have hshift :
      uniformizerPowerUnit K
          (R - 2 * (ramificationIndex K : Int)) * ε = a / s ^ 2 := by
    have hsquare := uniformizerParameter_shift_two_e_square
      (K := K) R ε
    have hmul : a =
        (uniformizerPowerUnit K
          (R - 2 * (ramificationIndex K : Int)) * ε) * s ^ 2 := by
      rw [ha] at hsquare
      calc
        a = -(-a) := by simp
        _ = -(-((uniformizerPowerUnit K
              (R - 2 * (ramificationIndex K : Int)) * ε)) * s ^ 2) :=
          congrArg Neg.neg hsquare
        _ = (uniformizerPowerUnit K
              (R - 2 * (ramificationIndex K : Int)) * ε) * s ^ 2 := by
          simp
    rw [hmul]
    simp
  simpa only [ha, hshift] using
    (beliAuxiliarySpinorGroup_eq_shiftedNormGeneratorGroup
      (K := K) R ε hε (by simpa [R] using hR))

end Dyadic

namespace BONG

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
private theorem squareClass_mul (a c : Kˣ) :
    squareClass K a * squareClass K c = squareClass K (a * c) :=
  rfl

/-- Coordinate scalars for multiplying only the head of a binary BONG by
`s`. -/
noncomputable def binaryScaledHeadFactors (s : Kˣ) : Fin 2 → Kˣ :=
  fun i => if i = 0 then s else 1

/-- The orthogonal basis obtained by multiplying only the BONG head by `s`. -/
noncomputable def binaryScaledHeadBasis (b : BONG V q L 2) (s : Kˣ) :
    Basis (Fin 2) K V :=
  b.basis.unitsSMul (binaryScaledHeadFactors s)

@[simp]
theorem binaryScaledHeadBasis_zero (b : BONG V q L 2) (s : Kˣ) :
    b.binaryScaledHeadBasis s 0 = (s : K) • b.basis 0 := by
  simp [binaryScaledHeadBasis, binaryScaledHeadFactors,
    Basis.unitsSMul_apply, Units.smul_def]

@[simp]
theorem binaryScaledHeadBasis_one (b : BONG V q L 2) (s : Kˣ) :
    b.binaryScaledHeadBasis s 1 = b.basis 1 := by
  simp [binaryScaledHeadBasis, binaryScaledHeadFactors,
    Basis.unitsSMul_apply]

private theorem binaryScaledHeadBasis_iIsOrtho
    (b : BONG V q L 2) (s : Kˣ) :
    q.bilin.iIsOrtho (b.binaryScaledHeadBasis s) := by
  rw [LinearMap.BilinForm.iIsOrtho_def]
  intro i j hij
  simp only [binaryScaledHeadBasis, Basis.unitsSMul_apply,
    Units.smul_def,
    LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  have hzero : q.bilin (b.basis i) (b.basis j) = 0 := by
    change q.bilin (b.ambientVector i) (b.ambientVector j) = 0
    exact (LinearMap.BilinForm.iIsOrtho_def.mp b.ambientVector_iIsOrtho)
      i j hij
  rw [hzero]
  simp

private theorem binaryScaledHeadBasis_quadratic_zero_ne
    (b : BONG V q L 2) (s : Kˣ) :
    q.quadratic (b.binaryScaledHeadBasis s 0) ≠ 0 := by
  rw [binaryScaledHeadBasis_zero, q.quadratic_smul]
  have hvalue : q.quadratic (b.basis 0) = b.value 0 :=
    b.quadratic_ambientVector 0
  rw [hvalue]
  exact mul_ne_zero (pow_ne_zero 2 (Units.ne_zero s)) (b.value_ne_zero 0)

private theorem binaryScaledHeadBasis_quadratic_one_ne
    (b : BONG V q L 2) (s : Kˣ) :
    q.quadratic (b.binaryScaledHeadBasis s 1) ≠ 0 := by
  have hvalue : q.quadratic (b.basis 1) = b.value 1 :=
    b.quadratic_ambientVector 1
  simpa only [binaryScaledHeadBasis_one, hvalue] using b.value_ne_zero 1

/-- Scaling the head by `s` preserves the order needed for a BONG exactly
when twice the order of `s` does not exceed the original binary gap. -/
theorem binaryScaledHeadBasis_order_le
    (b : BONG V q L 2) (s : Kˣ)
    (hscale : 2 * ordUnit K s ≤ b.binaryOrderGap) :
    ord K (q.quadratic (b.binaryScaledHeadBasis s 0)) ≤
      ord K (q.quadratic (b.binaryScaledHeadBasis s 1)) := by
  have hInt : 2 * ordUnit K s + b.order 0 ≤ b.order 1 := by
    rw [binaryOrderGap] at hscale
    omega
  have hvalueZero : q.quadratic (b.basis 0) = b.value 0 :=
    b.quadratic_ambientVector 0
  have hvalueOne : q.quadratic (b.basis 1) = b.value 1 :=
    b.quadratic_ambientVector 1
  calc
    ord K (q.quadratic (b.binaryScaledHeadBasis s 0)) =
        (((2 * ordUnit K s + b.order 0 : Int)) : WithTop Int) := by
      rw [binaryScaledHeadBasis_zero, q.quadratic_smul,
        ord_mul, ord_pow, hvalueZero, ← b.coe_order, ← coe_ordUnit]
      norm_cast
    _ ≤ (b.order 1 : WithTop Int) := WithTop.coe_le_coe.mpr hInt
    _ = ord K (q.quadratic (b.binaryScaledHeadBasis s 1)) := by
      simpa only [binaryScaledHeadBasis_one, hvalueOne] using b.coe_order 1

/-- The BONG carried by the head-scaled orthogonal basis. -/
noncomputable def binaryScaledHeadBONG
    (b : BONG V q L 2) (s : Kˣ)
    (hscale : 2 * ordUnit K s ≤ b.binaryOrderGap) :
    BONG V q (Lattice.basisLattice (b.binaryScaledHeadBasis s)) 2 :=
  BONG.ofOrthogonalBasisFinTwoOfOrdLe q (b.binaryScaledHeadBasis s)
    (binaryScaledHeadBasis_iIsOrtho b s)
    (binaryScaledHeadBasis_quadratic_zero_ne b s)
    (binaryScaledHeadBasis_quadratic_one_ne b s)
    (b.binaryScaledHeadBasis_order_le s hscale)

@[simp]
theorem binaryScaledHeadBONG_ambientVector
    (b : BONG V q L 2) (s : Kˣ)
    (hscale : 2 * ordUnit K s ≤ b.binaryOrderGap) (i : Fin 2) :
    (b.binaryScaledHeadBONG s hscale).ambientVector i =
      b.binaryScaledHeadBasis s i := by
  exact ambientVector_ofOrthogonalBasisFinTwoOfOrdLe
    q (b.binaryScaledHeadBasis s)
      (binaryScaledHeadBasis_iIsOrtho b s)
      (binaryScaledHeadBasis_quadratic_zero_ne b s)
      (binaryScaledHeadBasis_quadratic_one_ne b s)
      (b.binaryScaledHeadBasis_order_le s hscale) i

@[simp]
theorem binaryScaledHeadBONG_binaryParameter
    (b : BONG V q L 2) (s : Kˣ)
    (hscale : 2 * ordUnit K s ≤ b.binaryOrderGap) :
    (b.binaryScaledHeadBONG s hscale).binaryParameter =
      b.binaryParameter / s ^ 2 := by
  rw [binaryScaledHeadBONG,
    binaryParameter_ofOrthogonalBasisFinTwoOfOrdLe]
  apply Units.ext
  simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
    Units.val_mk0]
  have hvalueZero : q.quadratic (b.basis 0) = b.value 0 :=
    b.quadratic_ambientVector 0
  have hvalueOne : q.quadratic (b.basis 1) = b.value 1 :=
    b.quadratic_ambientVector 1
  rw [binaryScaledHeadBasis_zero, binaryScaledHeadBasis_one,
    q.quadratic_smul, hvalueZero, hvalueOne, b.coe_binaryParameter]
  field_simp [b.value_ne_zero 0, Units.ne_zero s]

/-- Beli (2003), Lemma 3.18(i), integrality assertion: reflection in the
anisotropic difference of two equal-value binary norm generators preserves
the lattice. -/
theorem isIntegralReflection_sub_of_equal_normGenerators_binary
    (b : BONG V q L 2) (x x' : V)
    (hx : Lattice.IsNormGenerator q L x)
    (hx' : Lattice.IsNormGenerator q L x')
    (heq : q.quadratic x = q.quadratic x')
    (hsub : q.IsAnisotropic (x - x')) :
    Lattice.IsIntegralReflection (L := L) hsub := by
  have hfin : Module.finrank K V = 2 := b.length_eq_finrank.symm
  let hxAn := b.isAnisotropic_of_isNormGenerator_binary hx
  let hx'An := b.isAnisotropic_of_isNormGenerator_binary hx'
  let bx : BONG V q L 2 :=
    BONG.ofNormGeneratorBinary q L x hx hxAn hfin
  let bx' : BONG V q L 2 :=
    BONG.ofNormGeneratorBinary q L x' hx' hx'An hfin
  let f : QuadraticSpace.Isometry q q :=
    q.reflectionIsometry (x - x') hsub
  let mapped : BONG V q (Lattice.map f.toLinearEquiv L) 2 := bx.map f
  have hmappedHead : mapped.head = x' := by
    calc
      mapped.head = mapped.ambientVector 0 :=
        mapped.ambientVector_zero_eq_head.symm
      _ = f.toLinearEquiv (bx.ambientVector 0) :=
        ambientVector_map f bx 0
      _ = f.toLinearEquiv bx.head :=
        congrArg f.toLinearEquiv bx.ambientVector_zero_eq_head
      _ = f.toLinearEquiv x := by
        rw [head_ofNormGeneratorBinary q L x hx hxAn hfin]
      _ = x' :=
        q.reflectionLinearEquiv_sub_apply_left_of_quadratic_eq x x' hsub heq
  have hbx'Head : bx'.head = x' :=
    head_ofNormGeneratorBinary q L x' hx' hx'An hfin
  have hgap : mapped.binaryOrderGap = bx'.binaryOrderGap := by
    calc
      mapped.binaryOrderGap = bx.binaryOrderGap := binaryOrderGap_map f bx
      _ = bx'.binaryOrderGap := bx.binaryOrderGap_eq bx'
  have hmap : Lattice.map f.toLinearEquiv L = L :=
    mapped.lattice_eq_of_head_eq_of_binaryOrderGap_eq bx'
      (hmappedHead.trans hbx'Head.symm) hgap
  intro y hy
  have hyMap := (Lattice.map_mem_map_iff f.toLinearEquiv L y).2 hy
  rw [hmap] at hyMap
  exact hyMap

variable [BinarySpinorLocalLaws.{u, v} K]

/-- Beli (2003), Lemma 3.18(i), spinor assertion.  The product
`Q(x) Q(x - x')`, viewed modulo squares, belongs to `G(a(L))`. -/
theorem equalNormGenerator_reflectionProduct_mem_beliSpinorGroup
    (b : BONG V q L 2) (x x' : V)
    (hx : Lattice.IsNormGenerator q L x)
    (hx' : Lattice.IsNormGenerator q L x')
    (heq : q.quadratic x = q.quadratic x')
    (hsub : q.IsAnisotropic (x - x')) :
    squareClass K
        (Units.mk0 (q.quadratic x)
            (b.isAnisotropic_of_isNormGenerator_binary hx) *
          Units.mk0 (q.quadratic (x - x')) hsub) ∈
      beliSpinorGroup K b.binaryUnitSquareClass := by
  let hxAn := b.isAnisotropic_of_isNormGenerator_binary hx
  let integralX := hx.isIntegralReflection hxAn
  let integralSub :=
    b.isIntegralReflection_sub_of_equal_normGenerators_binary
      x x' hx hx' heq hsub
  let reflectionX : Lattice.IntegralOrthogonalGroup q L :=
    Lattice.integralReflection hxAn integralX
  let reflectionSub : Lattice.IntegralOrthogonalGroup q L :=
    Lattice.integralReflection hsub integralSub
  have hmem :
      Lattice.reflectionSpinorClass hxAn *
          Lattice.reflectionSpinorClass hsub ∈
        Lattice.spinorNormImage (q := q) (L := L) := by
    refine ⟨Lattice.integralReflectionProduct
      hxAn integralX hsub integralSub, ?_⟩
    change Lattice.integralSpinorNorm (reflectionX * reflectionSub) = _
    rw [Lattice.integralSpinorNorm_mul]
    rw [Lattice.integralSpinorNorm_integralReflection,
      Lattice.integralSpinorNorm_integralReflection]
  rw [b.spinorNormImage_eq_beliSpinorGroup] at hmem
  simp only [Lattice.reflectionSpinorClass] at hmem
  rw [squareClass_mul] at hmem
  exact hmem

/-- Field-product form of Lemma 3.18(i), matching the notation in the paper. -/
theorem squareClass_quadratic_mul_sub_mem_beliSpinorGroup
    (b : BONG V q L 2) (x x' : V)
    (hx : Lattice.IsNormGenerator q L x)
    (hx' : Lattice.IsNormGenerator q L x')
    (heq : q.quadratic x = q.quadratic x')
    (hsub : q.IsAnisotropic (x - x')) :
    squareClass K
        (Units.mk0
          (q.quadratic x * q.quadratic (x - x'))
          (mul_ne_zero
            (b.isAnisotropic_of_isNormGenerator_binary hx) hsub)) ∈
      beliSpinorGroup K b.binaryUnitSquareClass := by
  have hmem :=
    b.equalNormGenerator_reflectionProduct_mem_beliSpinorGroup
      x x' hx hx' heq hsub
  convert hmem using 1
  congr 1
  apply Units.ext
  rfl

omit [BinarySpinorLocalLaws K] in
/-- A direct standard-model form of Lemma 3.18(i).  If `p = 1 - a²`, then
the first and second standard vectors of the binary model with shear `a`
have equal value.  Consequently the reflection product represented by
`2(1-a)` belongs to `G(p)`.  This is the algebraic bridge used in Lemma 6.6
for the binary lattice generated by a norm generator and an equal-value
vector. -/
theorem squareClass_two_mul_one_sub_mem_beliSpinorGroup
    [BinarySpinorLocalLaws.{u, u} K]
    (a : K) (p : Kˣ)
    (hp : (p : K) = 1 - a ^ 2)
    (htwo : (2 : K) * a ∈ IntegerRing K)
    (hne : (2 : K) * (1 - a) ≠ 0) :
    squareClass K (Units.mk0 (2 * (1 - a)) hne) ∈
      beliSpinorGroup K (unitSquareClass K p) := by
  have hdiag : a ^ 2 + (p : K) ∈ IntegerRing K := by
    rw [hp]
    convert (IntegerRing K).one_mem using 1 <;> ring
  let model := binaryModelBONG p a htwo hdiag
  let first : Fin 2 → K := QuadraticSpace.binaryModelFirst
  let second : Fin 2 → K := QuadraticSpace.binaryModelSecond
  have hfirst : Lattice.IsNormGenerator
      (QuadraticSpace.binaryModel p a) (binaryModelLattice (K := K)) first := by
    simpa only [first] using binaryModelFirst_isNormGenerator p a htwo hdiag
  have hsecondMem : second ∈ binaryModelLattice (K := K) := by
    simpa only [second] using binaryModelSecond_mem p a
  have hsecondValue :
      (QuadraticSpace.binaryModel p a).quadratic second = 1 := by
    simp only [second, QuadraticSpace.binaryModel_quadratic_second, hp]
    ring
  have hsecond : Lattice.IsNormGenerator
      (QuadraticSpace.binaryModel p a) (binaryModelLattice (K := K)) second := by
    refine ⟨hsecondMem, ?_⟩
    calc
      Lattice.normIdeal (QuadraticSpace.binaryModel p a)
          (binaryModelLattice (K := K)) =
          Lattice.principalIdeal (K := K)
            ((QuadraticSpace.binaryModel p a).quadratic first) :=
        hfirst.normIdeal_eq
      _ = Lattice.principalIdeal (K := K)
          ((QuadraticSpace.binaryModel p a).quadratic second) := by
        rw [show (QuadraticSpace.binaryModel p a).quadratic first = 1 by
          simp only [first, QuadraticSpace.binaryModel_quadratic_first],
          hsecondValue]
  have hfirstValue :
      (QuadraticSpace.binaryModel p a).quadratic first = 1 := by
    simp only [first, QuadraticSpace.binaryModel_quadratic_first]
  have heq : (QuadraticSpace.binaryModel p a).quadratic first =
      (QuadraticSpace.binaryModel p a).quadratic second := by
    rw [hfirstValue, hsecondValue]
  have hsubValue :
      (QuadraticSpace.binaryModel p a).quadratic (first - second) =
        2 * (1 - a) := by
    rw [QuadraticSpace.binaryModel_quadratic_apply]
    simp only [first, second, QuadraticSpace.binaryModelFirst,
      QuadraticSpace.binaryModelSecond, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
      Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero,
      zero_sub, one_pow]
    rw [hp]
    ring
  have hsub : (QuadraticSpace.binaryModel p a).IsAnisotropic
      (first - second) := by
    rw [QuadraticSpace.IsAnisotropic, hsubValue]
    exact hne
  have hmem := model.equalNormGenerator_reflectionProduct_mem_beliSpinorGroup
    first second hfirst hsecond heq hsub
  rw [binaryModelBONG_binaryUnitSquareClass] at hmem
  change squareClass K
      (Units.mk0
          ((QuadraticSpace.binaryModel p a).quadratic first)
          (model.isAnisotropic_of_isNormGenerator_binary hfirst) *
        Units.mk0
          ((QuadraticSpace.binaryModel p a).quadratic (first - second))
          hsub) ∈
    beliSpinorGroup K (unitSquareClass K p) at hmem
  have hunit :
      Units.mk0
          ((QuadraticSpace.binaryModel p a).quadratic first)
          (model.isAnisotropic_of_isNormGenerator_binary hfirst) *
        Units.mk0
          ((QuadraticSpace.binaryModel p a).quadratic (first - second))
          hsub =
        Units.mk0 (2 * (1 - a)) hne := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0, hfirstValue, hsubValue, one_mul]
  rw [hunit] at hmem
  exact hmem

/-- The order conclusion in Beli (2003), Lemma 3.18(ii).  Both signs have
order at least `ord Q(x) + 2e`, and exactly one sign attains the bound. -/
def BeliLemma318OrderConclusion (q : QuadraticSpace K V) (x x' : V) : Prop :=
  let bound := ord K (q.quadratic x) + ord K (2 : K) + ord K (2 : K)
  bound ≤ ord K (q.quadratic (x + x')) ∧
    bound ≤ ord K (q.quadratic (x - x')) ∧
      ((ord K (q.quadratic (x + x')) = bound ∧
          bound < ord K (q.quadratic (x - x'))) ∨
        (ord K (q.quadratic (x - x')) = bound ∧
          bound < ord K (q.quadratic (x + x'))))

omit [BinarySpinorLocalLaws K] in
/-- Beli (2003), Lemma 3.18(ii). -/
theorem equalNormGenerators_orderConclusion_of_two_e_lt_binaryOrderGap
    (b : BONG V q L 2) (x x' : V)
    (hx : Lattice.IsNormGenerator q L x)
    (hx' : Lattice.IsNormGenerator q L x')
    (heq : q.quadratic x = q.quadratic x')
    (hgap : 2 * (ramificationIndex K : Int) < b.binaryOrderGap) :
    BeliLemma318OrderConclusion q x x' := by
  have hfin : Module.finrank K V = 2 := b.length_eq_finrank.symm
  let hxAn := b.isAnisotropic_of_isNormGenerator_binary hx
  let bx : BONG V q L 2 :=
    BONG.ofNormGeneratorBinary q L x hx hxAn hfin
  have hbxGap : bx.binaryOrderGap = b.binaryOrderGap :=
    bx.binaryOrderGap_eq b
  have hbxGapLarge :
      2 * (ramificationIndex K : Int) < bx.binaryOrderGap := by
    rwa [hbxGap]
  have hbxGapNonneg : 0 ≤ bx.binaryOrderGap := by
    have hePos := ramificationIndex_pos K
    omega
  have hLattice :=
    bx.lattice_eq_basisLattice_of_binaryOrderGap_nonneg hbxGapNonneg
  have hx'MemBasis : x' ∈ Lattice.basisLattice bx.basis := by
    rw [← hLattice]
    exact hx'.mem
  have hcoordinates :=
    (Lattice.mem_basisLattice_iff_repr_mem_integerRing bx.basis x').1
      hx'MemBasis
  let α : K := bx.basis.repr x' 0
  let β : K := bx.basis.repr x' 1
  have hα : α ∈ IntegerRing K := hcoordinates 0
  have hβ : β ∈ IntegerRing K := hcoordinates 1
  have hbasisZero : bx.basis 0 = x := by
    change bx.ambientVector 0 = x
    rw [bx.ambientVector_zero_eq_head,
      head_ofNormGeneratorBinary q L x hx hxAn hfin]
  have hx'Decomp : x' = α • bx.basis 0 + β • bx.basis 1 := by
    have hrepr := bx.basis.sum_repr x'
    rw [Fin.sum_univ_two] at hrepr
    exact hrepr.symm
  have hvalueZero : bx.value 0 = q.quadratic x := by
    rw [bx.value_zero_eq_quadratic_head,
      head_ofNormGeneratorBinary q L x hx hxAn hfin]
  have hnormEquation :
      bx.value 0 = α ^ 2 * bx.value 0 + β ^ 2 * bx.value 1 := by
    calc
      bx.value 0 = q.quadratic x := hvalueZero
      _ = q.quadratic x' := heq
      _ = α ^ 2 * bx.value 0 + β ^ 2 * bx.value 1 := by
        simpa [α, β] using bx.quadratic_eq_binaryBasis_repr x'
  have hnormDifference :
      bx.value 0 - α ^ 2 * bx.value 0 = β ^ 2 * bx.value 1 := by
    linear_combination hnormEquation
  have hparameterEquation :
      1 - α ^ 2 = β ^ 2 * (bx.binaryParameter : K) := by
    rw [bx.coe_binaryParameter]
    calc
      1 - α ^ 2 =
          (bx.value 0 - α ^ 2 * bx.value 0) / bx.value 0 := by
        field_simp [bx.value_ne_zero 0]
      _ = β ^ 2 * bx.value 1 / bx.value 0 := by
        rw [hnormDifference]
      _ = β ^ 2 * (bx.value 1 / bx.value 0) := by ring
  have hparameterOrder :
      ordUnit K bx.binaryParameter = bx.binaryOrderGap := by
    simpa [binaryParameterOrder, ordUnit] using
      bx.binaryParameterOrder_eq_orderGap
  have hlarge : ord K (2 : K) + ord K (2 : K) <
      ord K (1 - α ^ 2) := by
    apply two_ord_two_lt_order_one_sub_sq_of_integral_parameter
      bx.binaryParameter α β hβ
    · rwa [hparameterOrder]
    · exact hparameterEquation
  have hdichotomy :=
    one_sub_one_add_order_dichotomy_of_two_ord_two_lt α hlarge
  have horth : q.bilin (bx.basis 0) (bx.basis 1) = 0 := by
    apply (LinearMap.BilinForm.iIsOrtho_def.mp bx.ambientVector_iIsOrtho)
    decide
  have hpair : q.bilin x x' = α * q.quadratic x := by
    rw [hx'Decomp, ← hbasisZero]
    simp only [LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_right, horth, mul_zero, add_zero]
    change α * q.quadratic (bx.basis 0) =
      α * q.quadratic (bx.basis 0)
    rfl
  have hplusValue :
      q.quadratic (x + x') = 2 * (1 + α) * q.quadratic x := by
    rw [q.quadratic_add, ← heq, hpair]
    ring
  have hminusValue :
      q.quadratic (x - x') = 2 * (1 - α) * q.quadratic x := by
    rw [sub_eq_add_neg, q.quadratic_add, q.quadratic_neg,
      LinearMap.BilinForm.neg_right, ← heq, hpair]
    ring
  let orderPrefix : WithTop Int :=
    ord K (q.quadratic x) + ord K (2 : K)
  let bound : WithTop Int := orderPrefix + ord K (2 : K)
  have hprefixNe : orderPrefix ≠ ⊤ := by
    dsimp [orderPrefix]
    exact (WithTop.add_ne_top).2
      ⟨(ord_eq_top_iff K).not.mpr hxAn, ord_two_ne_top K⟩
  have hplusOrder :
      ord K (q.quadratic (x + x')) =
        orderPrefix + ord K (1 + α) := by
    rw [hplusValue, ord_mul, ord_mul]
    dsimp [orderPrefix]
    ac_rfl
  have hminusOrder :
      ord K (q.quadratic (x - x')) =
        orderPrefix + ord K (1 - α) := by
    rw [hminusValue, ord_mul, ord_mul]
    dsimp [orderPrefix]
    ac_rfl
  change bound ≤ ord K (q.quadratic (x + x')) ∧
    bound ≤ ord K (q.quadratic (x - x')) ∧
      ((ord K (q.quadratic (x + x')) = bound ∧
          bound < ord K (q.quadratic (x - x'))) ∨
        (ord K (q.quadratic (x - x')) = bound ∧
          bound < ord K (q.quadratic (x + x'))))
  rcases hdichotomy with hminus | hplus
  · have hplusHigh : bound < ord K (q.quadratic (x + x')) := by
      rw [hplusOrder]
      exact WithTop.add_lt_add_left hprefixNe hminus.2
    have hminusEq : ord K (q.quadratic (x - x')) = bound := by
      rw [hminusOrder, hminus.1]
    exact ⟨hplusHigh.le, hminusEq.ge,
      Or.inr ⟨hminusEq, hplusHigh⟩⟩
  · have hminusHigh : bound < ord K (q.quadratic (x - x')) := by
      rw [hminusOrder]
      exact WithTop.add_lt_add_left hprefixNe hplus.2
    have hplusEq : ord K (q.quadratic (x + x')) = bound := by
      rw [hplusOrder, hplus.1]
    exact ⟨hplusEq.ge, hminusHigh.le,
      Or.inl ⟨hplusEq, hminusHigh⟩⟩

variable [BinaryNormGeneratorLocalLaws.{u, v} K]

omit [BinarySpinorLocalLaws K] in
/-- Beli (2003), Lemma 3.18(iii), with the first norm generator chosen as
 the BONG head. -/
theorem headEqualNormGenerator_reflectionProduct_mem_auxiliarySpinorGroup
    (b : BONG V q L 2) (x' : V)
    (hx' : Lattice.IsNormGenerator q L x')
    (heq : q.quadratic b.head = q.quadratic x')
    (hsub : q.IsAnisotropic (b.head - x'))
    (hgap : 2 * (ramificationIndex K : Int) < b.binaryOrderGap)
    (hminusOrder :
      ord K (q.quadratic (b.head - x')) =
        ord K (q.quadratic b.head) + ord K (2 : K) + ord K (2 : K)) :
    squareClass K
        (Units.mk0 (q.quadratic b.head) b.head_isAnisotropic *
          Units.mk0 (q.quadratic (b.head - x')) hsub) ∈
      beliAuxiliarySpinorGroup K b.binaryParameter (by
        have hparameterOrder :
            ordUnit K b.binaryParameter = b.binaryOrderGap := by
          simpa [binaryParameterOrder, ordUnit] using
            b.binaryParameterOrder_eq_orderGap
        rwa [hparameterOrder]) := by
  have hgapNonneg : 0 ≤ b.binaryOrderGap := by
    have hePos := ramificationIndex_pos K
    omega
  have hLattice :=
    b.lattice_eq_basisLattice_of_binaryOrderGap_nonneg hgapNonneg
  have hx'MemBasis : x' ∈ Lattice.basisLattice b.basis := by
    rw [← hLattice]
    exact hx'.mem
  have hcoordinates :=
    (Lattice.mem_basisLattice_iff_repr_mem_integerRing b.basis x').1
      hx'MemBasis
  let α : K := b.basis.repr x' 0
  let β : K := b.basis.repr x' 1
  have hβ : β ∈ IntegerRing K := hcoordinates 1
  have hbasisZero : b.basis 0 = b.head := by
    exact b.ambientVector_zero_eq_head
  have hx'Decomp : x' = α • b.basis 0 + β • b.basis 1 := by
    have hrepr := b.basis.sum_repr x'
    rw [Fin.sum_univ_two] at hrepr
    exact hrepr.symm
  have horth : q.bilin (b.basis 0) (b.basis 1) = 0 := by
    apply (LinearMap.BilinForm.iIsOrtho_def.mp b.ambientVector_iIsOrtho)
    decide
  have hpair : q.bilin b.head x' = α * q.quadratic b.head := by
    rw [hx'Decomp, ← hbasisZero]
    simp only [LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_right, horth, mul_zero, add_zero]
    change α * q.quadratic (b.basis 0) =
      α * q.quadratic (b.basis 0)
    rfl
  have hminusValue :
      q.quadratic (b.head - x') =
        2 * (1 - α) * q.quadratic b.head := by
    rw [sub_eq_add_neg, q.quadratic_add, q.quadratic_neg,
      LinearMap.BilinForm.neg_right, ← heq, hpair]
    ring
  let orderPrefix : WithTop Int :=
    ord K (q.quadratic b.head) + ord K (2 : K)
  have hprefixNe : orderPrefix ≠ ⊤ := by
    dsimp [orderPrefix]
    exact (WithTop.add_ne_top).2
      ⟨(ord_eq_top_iff K).not.mpr b.head_isAnisotropic,
        ord_two_ne_top K⟩
  have hminusOrderFormula :
      ord K (q.quadratic (b.head - x')) =
        orderPrefix + ord K (1 - α) := by
    rw [hminusValue, ord_mul, ord_mul]
    dsimp [orderPrefix]
    ac_rfl
  have hminusFactorOrder : ord K (1 - α) = ord K (2 : K) := by
    apply (add_right_inj_of_ne_top hprefixNe).mp
    calc
      orderPrefix + ord K (1 - α) =
          ord K (q.quadratic (b.head - x')) :=
        hminusOrderFormula.symm
      _ = ord K (q.quadratic b.head) +
          ord K (2 : K) + ord K (2 : K) := hminusOrder
      _ = orderPrefix + ord K (2 : K) := by
        dsimp [orderPrefix]
  let s : Kˣ := uniformizerPowerUnit K (ramificationIndex K : Int)
  have hsOrder : ordUnit K s = ramificationIndex K := by
    exact ordUnit_uniformizerPowerUnit (K := K) _
  have hscale : 2 * ordUnit K s ≤ b.binaryOrderGap := by
    rw [hsOrder]
    omega
  let c := b.binaryScaledHeadBONG s hscale
  let M : Lattice K V :=
    Lattice.basisLattice (b.binaryScaledHeadBasis s)
  have hreprZero :
      b.basis.repr (b.head - x') 0 = 1 - α := by
    rw [← hbasisZero]
    simp [α]
  have hreprOne :
      b.basis.repr (b.head - x') 1 = -β := by
    rw [← hbasisZero]
    simp [β]
  have hsubMem : b.head - x' ∈ M := by
    apply (Lattice.mem_basisLattice_iff_repr_mem_integerRing
      (b.binaryScaledHeadBasis s) (b.head - x')).2
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [binaryScaledHeadBasis, Basis.repr_unitsSMul, hreprZero]
      change ((s⁻¹ : Kˣ) : K) * (1 - α) ∈ IntegerRing K
      apply (mem_integerRing_iff K).2
      change 0 ≤ ord K (((s⁻¹ : Kˣ) : K) * (1 - α))
      rw [Units.val_inv_eq_inv_val, ord_mul, AddValuation.map_inv,
        ← coe_ordUnit,
        hsOrder, hminusFactorOrder, ← ramificationIndex_spec K]
      simp
    · have hj : j = 0 := Subsingleton.elim j 0
      subst j
      have hreprOne' :
          b.basis.repr (b.head - x') (Fin.succ 0) = -β := by
        simpa using hreprOne
      rw [binaryScaledHeadBasis, Basis.repr_unitsSMul, hreprOne']
      have hfactor : binaryScaledHeadFactors s (Fin.succ 0) = 1 := by
        simp [binaryScaledHeadFactors]
      rw [hfactor]
      simpa only [inv_one, one_smul] using
        (IntegerRing K).neg_mem β hβ
  have hcHead : c.head = (s : K) • b.head := by
    calc
      c.head = c.ambientVector 0 := c.ambientVector_zero_eq_head.symm
      _ = b.binaryScaledHeadBasis s 0 := by
        exact b.binaryScaledHeadBONG_ambientVector s hscale 0
      _ = (s : K) • b.basis 0 := b.binaryScaledHeadBasis_zero s
      _ = (s : K) • b.head := by rw [hbasisZero]
  have hscaledHeadOrder :
      ord K (q.quadratic c.head) =
        ord K (q.quadratic b.head) + ord K (2 : K) + ord K (2 : K) := by
    rw [hcHead, q.quadratic_smul, ord_mul, ord_pow,
      ← coe_ordUnit, hsOrder, ramificationIndex_spec]
    rw [two_nsmul]
    ac_rfl
  have hvalueOrders :
      ordUnit K (Units.mk0 (q.quadratic (b.head - x')) hsub) =
        ordUnit K (Units.mk0 (q.quadratic c.head)
          c.head_isAnisotropic) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, coe_ordUnit]
    exact hminusOrder.trans hscaledHeadOrder.symm
  have hsubGenerator : Lattice.IsNormGenerator q M (b.head - x') := by
    apply (c.head_isNormGenerator.iff_isValuationUnit_valueRatio
      c.head_isAnisotropic hsubMem hsub).2
    rw [isValuationUnit_iff_ordUnit_eq_zero]
    simp only [div_eq_mul_inv, ordUnit_mul, ordUnit_inv]
    rw [hvalueOrders]
    omega
  have hclassMem :
      c.normGeneratorValueRatioClass (b.head - x') hsubGenerator ∈
        beliNormGeneratorGroup K c.binaryParameter := by
    have hmem :
        c.normGeneratorValueRatioClass (b.head - x') hsubGenerator ∈
          c.normGeneratorValueRatioClassSet :=
      ⟨b.head - x', hsubGenerator, rfl⟩
    rw [c.normGeneratorValueRatioClassSet_eq_beliNormGeneratorGroup]
      at hmem
    exact hmem
  have hsquareMem :
      valuationUnitClassToSquareClass K
          (c.normGeneratorValueRatioClass (b.head - x') hsubGenerator) ∈
        beliNormGeneratorSquareClassGroup K c.binaryParameter :=
    ⟨c.normGeneratorValueRatioClass (b.head - x') hsubGenerator,
      hclassMem, rfl⟩
  have hcParameter : c.binaryParameter = b.binaryParameter / s ^ 2 := by
    exact b.binaryScaledHeadBONG_binaryParameter s hscale
  rw [hcParameter] at hsquareMem
  have hparameterOrder :
      ordUnit K b.binaryParameter = b.binaryOrderGap := by
    simpa [binaryParameterOrder, ordUnit] using
      b.binaryParameterOrder_eq_orderGap
  have hRParameter :
      2 * (ramificationIndex K : Int) < ordUnit K b.binaryParameter := by
    rwa [hparameterOrder]
  rw [beliAuxiliarySpinorGroup_eq_div_ramificationSquare
    (K := K) b.binaryParameter hRParameter]
  change squareClass K
      (Units.mk0 (q.quadratic b.head) b.head_isAnisotropic *
        Units.mk0 (q.quadratic (b.head - x')) hsub) ∈
    beliNormGeneratorSquareClassGroup K (b.binaryParameter / s ^ 2)
  have hsquareMem' :
      squareClass K
          (c.normGeneratorValueRatioUnit (b.head - x') hsubGenerator) ∈
        beliNormGeneratorSquareClassGroup K (b.binaryParameter / s ^ 2) := by
    change squareClass K
        (c.normGeneratorValueRatioUnit (b.head - x') hsubGenerator) ∈
      beliNormGeneratorSquareClassGroup K (b.binaryParameter / s ^ 2)
      at hsquareMem
    exact hsquareMem
  let qx : Kˣ := Units.mk0 (q.quadratic b.head) b.head_isAnisotropic
  let qd : Kˣ := Units.mk0 (q.quadratic (b.head - x')) hsub
  have hcValueZero : c.valueUnit 0 = s ^ 2 * qx := by
    apply Units.ext
    rw [coe_valueUnit]
    rw [c.value_zero_eq_quadratic_head, hcHead, q.quadratic_smul]
    rfl
  have hratio :
      c.normGeneratorValueRatioUnit (b.head - x') hsubGenerator =
        qd / (s ^ 2 * qx) := by
    unfold normGeneratorValueRatioUnit
    rw [hcValueZero]
  have hunitIdentity :
      c.normGeneratorValueRatioUnit (b.head - x') hsubGenerator *
          (s * qx) ^ 2 = qx * qd := by
    rw [hratio]
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero s, Units.ne_zero qx, Units.ne_zero qd]
  have hclassIdentity :
      squareClass K (qx * qd) =
        squareClass K
          (c.normGeneratorValueRatioUnit (b.head - x') hsubGenerator) := by
    calc
      squareClass K (qx * qd) =
          squareClass K
            (c.normGeneratorValueRatioUnit (b.head - x') hsubGenerator *
              (s * qx) ^ 2) := congrArg (squareClass K) hunitIdentity.symm
      _ = squareClass K
          (c.normGeneratorValueRatioUnit (b.head - x') hsubGenerator) :=
        squareClass_mul_square K _ _
  change squareClass K (qx * qd) ∈
    beliNormGeneratorSquareClassGroup K (b.binaryParameter / s ^ 2)
  rw [hclassIdentity]
  exact hsquareMem'

omit [BinarySpinorLocalLaws K] in
/-- Intrinsic form of Beli (2003), Lemma 3.18(iii), for arbitrary equal-value
 norm generators. -/
theorem equalNormGenerator_reflectionProduct_mem_auxiliarySpinorGroup
    (b : BONG V q L 2) (x x' : V)
    (hx : Lattice.IsNormGenerator q L x)
    (hx' : Lattice.IsNormGenerator q L x')
    (heq : q.quadratic x = q.quadratic x')
    (hsub : q.IsAnisotropic (x - x'))
    (hgap : 2 * (ramificationIndex K : Int) < b.binaryOrderGap)
    (hminusOrder :
      ord K (q.quadratic (x - x')) =
        ord K (q.quadratic x) + ord K (2 : K) + ord K (2 : K)) :
    squareClass K
        (Units.mk0 (q.quadratic x)
            (b.isAnisotropic_of_isNormGenerator_binary hx) *
          Units.mk0 (q.quadratic (x - x')) hsub) ∈
      beliAuxiliarySpinorGroup K b.binaryParameter (by
        have hparameterOrder :
            ordUnit K b.binaryParameter = b.binaryOrderGap := by
          simpa [binaryParameterOrder, ordUnit] using
            b.binaryParameterOrder_eq_orderGap
        rwa [hparameterOrder]) := by
  have hfin : Module.finrank K V = 2 := b.length_eq_finrank.symm
  let hxAn := b.isAnisotropic_of_isNormGenerator_binary hx
  let bx : BONG V q L 2 :=
    BONG.ofNormGeneratorBinary q L x hx hxAn hfin
  have hhead : bx.head = x :=
    head_ofNormGeneratorBinary q L x hx hxAn hfin
  have hbxGap : bx.binaryOrderGap = b.binaryOrderGap :=
    bx.binaryOrderGap_eq b
  have hgapBx :
      2 * (ramificationIndex K : Int) < bx.binaryOrderGap := by
    rwa [hbxGap]
  have hsubBx : q.IsAnisotropic (bx.head - x') := by
    rwa [hhead]
  have hminusOrderBx :
      ord K (q.quadratic (bx.head - x')) =
        ord K (q.quadratic bx.head) + ord K (2 : K) + ord K (2 : K) := by
    simpa only [hhead] using hminusOrder
  have hmem :=
    bx.headEqualNormGenerator_reflectionProduct_mem_auxiliarySpinorGroup
      x' hx' (by simpa only [hhead] using heq) hsubBx hgapBx
      hminusOrderBx
  change squareClass K
      (Units.mk0 (q.quadratic x) hxAn *
        Units.mk0 (q.quadratic (x - x')) hsub) ∈
    beliAuxiliarySpinorGroupRepresentative K b.binaryParameter
  change squareClass K
      (Units.mk0 (q.quadratic bx.head) bx.head_isAnisotropic *
        Units.mk0 (q.quadratic (bx.head - x')) hsubBx) ∈
    beliAuxiliarySpinorGroupRepresentative K bx.binaryParameter at hmem
  have hgroup :
      beliAuxiliarySpinorGroupRepresentative K bx.binaryParameter =
        beliAuxiliarySpinorGroupRepresentative K b.binaryParameter :=
    beliAuxiliarySpinorGroupRepresentative_eq_of_unitSquareClass_eq K
      (bx.binaryUnitSquareClass_eq b)
  rw [hgroup] at hmem
  simpa only [hhead] using hmem

omit [BinarySpinorLocalLaws K] in
/-- Field-product form of Lemma 3.18(iii). -/
theorem squareClass_quadratic_mul_sub_mem_auxiliarySpinorGroup
    (b : BONG V q L 2) (x x' : V)
    (hx : Lattice.IsNormGenerator q L x)
    (hx' : Lattice.IsNormGenerator q L x')
    (heq : q.quadratic x = q.quadratic x')
    (hsub : q.IsAnisotropic (x - x'))
    (hgap : 2 * (ramificationIndex K : Int) < b.binaryOrderGap)
    (hminusOrder :
      ord K (q.quadratic (x - x')) =
        ord K (q.quadratic x) + ord K (2 : K) + ord K (2 : K)) :
    squareClass K
        (Units.mk0
          (q.quadratic x * q.quadratic (x - x'))
          (mul_ne_zero
            (b.isAnisotropic_of_isNormGenerator_binary hx) hsub)) ∈
      beliAuxiliarySpinorGroup K b.binaryParameter (by
        have hparameterOrder :
            ordUnit K b.binaryParameter = b.binaryOrderGap := by
          simpa [binaryParameterOrder, ordUnit] using
            b.binaryParameterOrder_eq_orderGap
        rwa [hparameterOrder]) := by
  have hmem :=
    b.equalNormGenerator_reflectionProduct_mem_auxiliarySpinorGroup
      x x' hx hx' heq hsub hgap hminusOrder
  convert hmem using 1
  congr 1
  apply Units.ext
  rfl

/-- Beli (2003), Lemma 3.18, collecting assertions (i)--(iii). -/
theorem beliLemma318
    (b : BONG V q L 2) (x x' : V)
    (hx : Lattice.IsNormGenerator q L x)
    (hx' : Lattice.IsNormGenerator q L x')
    (heq : q.quadratic x = q.quadratic x')
    (hsub : q.IsAnisotropic (x - x'))
    (hgap : 2 * (ramificationIndex K : Int) < b.binaryOrderGap) :
    (Lattice.IsIntegralReflection (L := L) hsub ∧
      squareClass K
          (Units.mk0
            (q.quadratic x * q.quadratic (x - x'))
            (mul_ne_zero
              (b.isAnisotropic_of_isNormGenerator_binary hx) hsub)) ∈
        beliSpinorGroup K b.binaryUnitSquareClass) ∧
      BeliLemma318OrderConclusion q x x' ∧
        (ord K (q.quadratic (x - x')) =
            ord K (q.quadratic x) + ord K (2 : K) + ord K (2 : K) →
          squareClass K
              (Units.mk0
                (q.quadratic x * q.quadratic (x - x'))
                (mul_ne_zero
                  (b.isAnisotropic_of_isNormGenerator_binary hx) hsub)) ∈
            beliAuxiliarySpinorGroup K b.binaryParameter (by
              have hparameterOrder :
                  ordUnit K b.binaryParameter = b.binaryOrderGap := by
                simpa [binaryParameterOrder, ordUnit] using
                  b.binaryParameterOrder_eq_orderGap
              rwa [hparameterOrder])) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact b.isIntegralReflection_sub_of_equal_normGenerators_binary
      x x' hx hx' heq hsub
  · exact b.squareClass_quadratic_mul_sub_mem_beliSpinorGroup
      x x' hx hx' heq hsub
  · exact b.equalNormGenerators_orderConclusion_of_two_e_lt_binaryOrderGap
      x x' hx hx' heq hgap
  · intro hminusOrder
    exact b.squareClass_quadratic_mul_sub_mem_auxiliarySpinorGroup
      x x' hx hx' heq hsub hgap hminusOrder

end BONG

end Bong
