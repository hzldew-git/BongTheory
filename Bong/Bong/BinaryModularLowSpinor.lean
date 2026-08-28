/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.BinaryModularNonlowComplete
import Bong.Bong.BeliEndpointNormGenerator
import Bong.Bong.DiscriminantClassProof
import Bong.Dyadic.UnramifiedNormDirectProof

/-!
# The low-defect binary spinor formula in the negative modular branch

This file proves the remaining part of Beli (2003), Lemma 3.7.  Away from
the lower endpoint, Hsia's Proposition B is implemented as an elementary
coordinate calculation: in a defect-adapted modular model every primitive
vector defines an integral reflection.  At the non-hyperbolic endpoint the
argument instead uses the norm group of the unramified quadratic extension.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Dividing by a nonzero element preserves integrality whenever the
denominator has no larger order than the numerator. -/
private theorem div_mem_integerRing_of_ord_le
    {x y : K} (hy : y ≠ 0) (hord : ord K y ≤ ord K x) :
    x / y ∈ IntegerRing K := by
  apply (mem_integerRing_iff K).2
  change (0 : WithTop Int) ≤ ord K (x / y)
  rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv]
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_eq_top_iff K).not.mpr hy)
  rw [← hd] at hord ⊢
  have h := add_le_add_right hord (-(d : WithTop Int))
  simpa [add_assoc, add_comm] using h

/-- Hsia's low modular coordinate lemma.  The cross coefficient has order
`s`, the second diagonal coefficient has positive odd order `m`, and
`m ≤ s < e`.  Under these hypotheses every primitive vector of the
standard lattice defines an integral reflection. -/
theorem primitive_isIntegralReflection_binaryModel_of_modular_low
    (a : Kˣ) (c : K) (m : Nat) (s : Int)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiagIntegral : c ^ 2 + (a : K) ∈ IntegerRing K)
    (hcross : ord K ((2 : K) * c) = (s : WithTop Int))
    (hdiag : ord K (c ^ 2 + (a : K)) =
      (((m : Nat) : Int) : WithTop Int))
    (hmPos : 0 < m) (hmOdd : Odd m)
    (hsNonneg : 0 ≤ s)
    (hmLeS : (m : Int) ≤ s)
    (hsLtE : s < (ramificationIndex K : Int))
    {z : Fin 2 → K}
    (hz : (QuadraticSpace.binaryModel a c).IsAnisotropic z)
    (hzMem : z ∈ binaryModelLattice (K := K))
    (hzPrimitive : z ∉ Lattice.rescale (uniformizerUnit K)
      (binaryModelLattice (K := K))) :
    Lattice.IsIntegralReflection
      (q := QuadraticSpace.binaryModel a c)
      (L := binaryModelLattice (K := K)) hz := by
  classical
  let x : K := z 0
  let y : K := z 1
  let D : K := c ^ 2 + (a : K)
  let qv : K := (QuadraticSpace.binaryModel a c).quadratic z
  have hqvNe : qv ≠ 0 := by
    change (QuadraticSpace.binaryModel a c).quadratic z ≠ 0
    exact hz
  have hqExpanded :
      qv = x ^ 2 + ((2 : K) * c) * x * y + D * y ^ 2 := by
    simp only [qv, x, y, D,
      QuadraticSpace.binaryModel_quadratic_apply]
    ring
  have hzCoords := (mem_binaryModelLattice_iff z).1 hzMem
  have hxMem : x ∈ IntegerRing K := by simpa [x] using hzCoords 0
  have hyMem : y ∈ IntegerRing K := by simpa [y] using hzCoords 1
  have hxNonneg : (0 : WithTop Int) ≤ ord K x :=
    (mem_integerRing_iff K).1 hxMem
  have hyNonneg : (0 : WithTop Int) ≤ ord K y :=
    (mem_integerRing_iff K).1 hyMem
  have hprimitive :=
    (primitive_binaryModelLattice_iff_coordinate_unit z hzMem).1
      hzPrimitive
  have hmPosTop : (0 : WithTop Int) < ((m : Int) : WithTop Int) := by
    exact_mod_cast hmPos
  have hsNonnegTop : (0 : WithTop Int) ≤ (s : WithTop Int) := by
    exact_mod_cast hsNonneg
  have htwoOrder : ord K (2 : K) =
      ((ramificationIndex K : Int) : WithTop Int) :=
    (ramificationIndex_spec K).symm
  apply (isIntegralReflection_binaryModel_iff_of_primitive
    a c hz hzMem hzPrimitive).2
  by_cases hxUnit : IsValuationUnit K x
  · have hxOrder : ord K x = 0 := hxUnit
    let B : K := ((2 : K) * c) * x * y
    let C : K := D * y ^ 2
    have hBLower : (s : WithTop Int) ≤ ord K B := by
      dsimp only [B]
      rw [ord_mul, ord_mul, hcross, hxOrder]
      simpa [add_assoc, add_comm] using
        add_le_add_left hyNonneg (s : WithTop Int)
    have hCLower : ((m : Int) : WithTop Int) ≤ ord K C := by
      dsimp only [C]
      rw [ord_mul, show ord K D = (((m : Nat) : Int) : WithTop Int) by
        simpa only [D] using hdiag, ord_pow]
      have hpow : (0 : WithTop Int) ≤ (2 : Nat) • ord K y :=
        nsmul_nonneg hyNonneg 2
      simpa [add_comm] using
        add_le_add_left hpow (((m : Int) : WithTop Int))
    have hmLeSTop : (((m : Int) : WithTop Int)) ≤ (s : WithTop Int) := by
      exact_mod_cast hmLeS
    have hBPos : (0 : WithTop Int) < ord K B :=
      hmPosTop.trans_le (hmLeSTop.trans hBLower)
    have hCPos : (0 : WithTop Int) < ord K C := hmPosTop.trans_le hCLower
    have herrorPos : (0 : WithTop Int) < ord K (B + C) :=
      (lt_min hBPos hCPos).trans_le (min_ord_le_ord_add K B C)
    have hxSqOrder : ord K (x ^ 2) = 0 := by
      rw [ord_pow, hxOrder]
      norm_num
    have hqOrder : ord K qv = 0 := by
      have hdecomp : qv = x ^ 2 + (B + C) := by
        rw [hqExpanded]
        simp only [B, C]
        ring
      rw [hdecomp, (ord K).map_add_eq_of_lt_left]
      · exact hxSqOrder
      · simpa only [hxSqOrder] using herrorPos
    have hqInv : qv⁻¹ ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      change (0 : WithTop Int) ≤ ord K qv⁻¹
      rw [AddValuation.map_inv, hqOrder]
      simp
    constructor
    · have hnumerator : 2 * (x + c * y) ∈ IntegerRing K := by
        have hfirst := (IntegerRing K).mul_mem _ _
          (show (2 : K) ∈ IntegerRing K by norm_num) hxMem
        have hsecond := (IntegerRing K).mul_mem _ _ htwo hyMem
        convert (IntegerRing K).add_mem _ _ hfirst hsecond using 1 <;> ring
      simpa [x, y, qv, div_eq_mul_inv] using
        (IntegerRing K).mul_mem _ _ hnumerator hqInv
    · have hnumerator : 2 * (c * x + D * y) ∈ IntegerRing K := by
        have hfirst := (IntegerRing K).mul_mem _ _ htwo hxMem
        have hsecond := (IntegerRing K).mul_mem _ _
          ((IntegerRing K).mul_mem _ _
            (show (2 : K) ∈ IntegerRing K by norm_num)
            hdiagIntegral) hyMem
        convert (IntegerRing K).add_mem _ _ hfirst hsecond using 1 <;>
          simp only [D] <;> ring
      simpa [x, y, D, qv, div_eq_mul_inv] using
        (IntegerRing K).mul_mem _ _ hnumerator hqInv
  · have hyUnit : IsValuationUnit K y := hprimitive.resolve_left hxUnit
    have hyOrder : ord K y = 0 := hyUnit
    by_cases hxZero : x = 0
    · have hqOrder : ord K qv = (((m : Nat) : Int) : WithTop Int) := by
        have hdecomp : qv = D * y ^ 2 := by
          rw [hqExpanded, hxZero]
          ring
        rw [hdecomp, ord_mul,
          show ord K D = (((m : Nat) : Int) : WithTop Int) by
            simpa only [D] using hdiag,
          ord_pow, hyOrder]
        norm_num
      constructor
      · apply div_mem_integerRing_of_ord_le hqvNe
        have hnumerator : 2 * (x + c * y) = ((2 : K) * c) * y := by
          rw [hxZero]
          ring
        rw [hnumerator, ord_mul, hcross, hyOrder, hqOrder]
        simpa using (show
          (((m : Nat) : Int) : WithTop Int) ≤ (s : WithTop Int) by
            exact_mod_cast hmLeS)
      · apply div_mem_integerRing_of_ord_le hqvNe
        have hnumerator : 2 * (c * x + D * y) = (2 : K) * D * y := by
          rw [hxZero]
          ring
        rw [hnumerator, ord_mul, ord_mul, htwoOrder,
          show ord K D = (((m : Nat) : Int) : WithTop Int) by
            simpa only [D] using hdiag,
          hyOrder, hqOrder]
        norm_cast
        have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
        omega
    · let xu : Kˣ := Units.mk0 x hxZero
      let X : Int := ordUnit K xu
      have hxOrder : ord K x = (X : WithTop Int) := by
        simpa only [X, xu, Units.val_mk0] using (coe_ordUnit K xu).symm
      have hXNonneg : 0 ≤ X := by
        exact Lattice.ordUnit_nonneg_of_mem_integerRing xu
          (by simpa [xu] using hxMem)
      have hXNe : X ≠ 0 := by
        intro hzero
        apply hxUnit
        simpa [xu] using
          (isValuationUnit_iff_ordUnit_eq_zero K xu).2 hzero
      have hXPos : 0 < X := lt_of_le_of_ne hXNonneg (Ne.symm hXNe)
      let A : K := x ^ 2
      let B : K := ((2 : K) * c) * x * y
      let C : K := D * y ^ 2
      have hAOrder : ord K A = ((2 * X : Int) : WithTop Int) := by
        dsimp only [A]
        rw [ord_pow, hxOrder]
        norm_cast
      have hBOrder : ord K B = ((s + X : Int) : WithTop Int) := by
        dsimp only [B]
        rw [ord_mul, ord_mul, hcross, hxOrder, hyOrder]
        norm_cast
        ring
      have hCOrder : ord K C = (((m : Nat) : Int) : WithTop Int) := by
        dsimp only [C]
        rw [ord_mul, show ord K D = (((m : Nat) : Int) : WithTop Int) by
          simpa only [D] using hdiag, ord_pow, hyOrder]
        norm_num
      have hACNe : ord K A ≠ ord K C := by
        rw [hAOrder, hCOrder]
        intro heq
        have heqInt : 2 * X = (m : Int) := by exact_mod_cast heq
        rcases hmOdd with ⟨k, hk⟩
        omega
      have hBMin : min (ord K A) (ord K C) < ord K B := by
        rw [hAOrder, hBOrder, hCOrder]
        have hminInt : min (2 * X) (m : Int) < s + X := by
          by_cases hle : 2 * X ≤ (m : Int)
          · rw [min_eq_left hle]
            omega
          · rw [min_eq_right (le_of_not_ge hle)]
            omega
        exact_mod_cast hminInt
      have hqOrder : ord K qv =
          ((min (2 * X) (m : Int) : Int) : WithTop Int) := by
        have hsum := scratch_ord_add_add_eq_min_of_middle_gt
          A B C hACNe hBMin
        have hdecomp : qv = A + B + C := by
          rw [hqExpanded]
        rw [hdecomp, hsum, hAOrder, hCOrder]
        norm_cast
      have hqLeM : min (2 * X) (m : Int) ≤ (m : Int) := min_le_right _ _
      constructor
      · apply div_mem_integerRing_of_ord_le hqvNe
        have hnumerator : 2 * (x + c * y) =
            (2 : K) * x + ((2 : K) * c) * y := by ring
        rw [hnumerator]
        rw [hqOrder]
        apply (show
          ((min (2 * X) (m : Int) : Int) : WithTop Int) ≤
            ord K ((2 : K) * x + ((2 : K) * c) * y) from ?_)
        apply (le_min ?_ ?_).trans
          (min_ord_le_ord_add K ((2 : K) * x) (((2 : K) * c) * y))
        · rw [ord_mul, htwoOrder, hxOrder]
          exact_mod_cast (show min (2 * X) (m : Int) ≤
            (ramificationIndex K : Int) + X by omega)
        · rw [ord_mul, hcross, hyOrder]
          have hbound :
              ((min (2 * X) (m : Int) : Int) : WithTop Int) ≤
                (s : WithTop Int) := by
            exact_mod_cast hqLeM.trans hmLeS
          simpa using hbound
      · apply div_mem_integerRing_of_ord_le hqvNe
        have hnumerator : 2 * (c * x + D * y) =
            ((2 : K) * c) * x + (2 : K) * D * y := by ring
        rw [hnumerator]
        rw [hqOrder]
        apply (show
          ((min (2 * X) (m : Int) : Int) : WithTop Int) ≤
            ord K (((2 : K) * c) * x + (2 : K) * D * y) from ?_)
        apply (le_min ?_ ?_).trans
          (min_ord_le_ord_add K (((2 : K) * c) * x) ((2 : K) * D * y))
        · rw [ord_mul, hcross, hxOrder]
          exact_mod_cast (show min (2 * X) (m : Int) ≤ s + X by omega)
        · rw [ord_mul, ord_mul, htwoOrder,
            show ord K D = (((m : Nat) : Int) : WithTop Int) by
              simpa only [D] using hdiag,
            hyOrder]
          norm_cast
          have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
          omega

/-- If every primitive vector in an admissible sheared model defines an
integral reflection, then its proper spinor image is the full quadratic
norm square-class subgroup. -/
theorem spinorNormImage_binaryModel_eq_norm_of_all_primitive_reflections
    (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K)
    (hreflection : ∀ {z : Fin 2 → K},
      (hz : (QuadraticSpace.binaryModel a c).IsAnisotropic z) →
      (hzMem : z ∈ binaryModelLattice (K := K)) →
      (hzPrimitive : z ∉ Lattice.rescale (uniformizerUnit K)
        (binaryModelLattice (K := K))) →
      Lattice.IsIntegralReflection
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) hz) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) =
      quadraticNormSquareClassSubgroup K (-a) := by
  rw [spinorNormImage_binaryModel_eq_primitiveReflectionClassSet
    a c htwo hdiag]
  ext A
  constructor
  · rintro ⟨z, hz, _hzMem, _hzPrimitive, _hfirst, _hsecond, hclass⟩
    have hnorm := squareClass_binaryModelValue_mem_quadraticNorm
      (K := K) a c hz
    rwa [hclass] at hnorm
  · intro hA
    rcases hA with ⟨u, huNorm, huClass⟩
    rcases huNorm with ⟨x, y, hxy⟩
    let z : Fin 2 → K := ![x - c * y, y]
    have hvalue : (QuadraticSpace.binaryModel a c).quadratic z = (u : K) := by
      rw [QuadraticSpace.binaryModel_quadratic_apply]
      dsimp only [z]
      calc
        (x - c * y) ^ 2 + (2 * c) * ((x - c * y) * y) +
            (c ^ 2 + (a : K)) * y ^ 2 = x ^ 2 + (a : K) * y ^ 2 := by
          ring
        _ = (u : K) := by
          convert hxy using 1 <;> simp only [Units.val_neg] <;> ring
    have hz : (QuadraticSpace.binaryModel a c).IsAnisotropic z := by
      rw [QuadraticSpace.IsAnisotropic, hvalue]
      exact Units.ne_zero u
    have hz0 : z ≠ 0 := by
      intro hzero
      apply hz
      rw [hzero]
      simp [QuadraticSpace.quadratic]
    rcases Lattice.exists_unit_smul_mem_not_mem_uniformizer_rescale
        (binaryModelLattice (K := K)) hz0 with
      ⟨t, htzMem, htzPrimitive⟩
    let w : Fin 2 → K := (t : K) • z
    let hw : (QuadraticSpace.binaryModel a c).IsAnisotropic w := hz.unit_smul t
    have hwIntegral : Lattice.IsIntegralReflection
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) hw :=
      hreflection hw (by simpa [w] using htzMem)
        (by simpa [w] using htzPrimitive)
    have hcoefficients :=
      (isIntegralReflection_binaryModel_iff_of_primitive
        a c hw (by simpa [w] using htzMem)
          (by simpa [w] using htzPrimitive)).1 hwIntegral
    refine ⟨w, hw, by simpa [w] using htzMem,
      by simpa [w] using htzPrimitive,
      hcoefficients.1, hcoefficients.2, ?_⟩
    let valueUnit : Kˣ := Units.mk0
      ((QuadraticSpace.binaryModel a c).quadratic w) hw
    have hvalueScaled : valueUnit = t ^ 2 * u := by
      apply Units.ext
      simp only [valueUnit, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_mk0]
      rw [(QuadraticSpace.binaryModel a c).quadratic_smul, hvalue]
    change squareClass K valueUnit = A
    rw [hvalueScaled]
    calc
      squareClass K (t ^ 2 * u) = squareClass K (u * t ^ 2) := by
        congr 1
        ac_rfl
      _ = squareClass K u := squareClass_mul_square K u t
      _ = A := huClass

/-- Hsia, Proposition B away from the lower endpoint: a negative even
low-defect admissible model has the full quadratic norm group as its proper
spinor image. -/
theorem spinorNormImage_binaryModel_eq_quadraticNorm_negative_even_low_nonendpoint
    (a : Kˣ) (c : K)
    (ha : IsBinaryParameterAdmissible a)
    (hRneg : ordUnit K a < 0)
    (hEven : Even (ordUnit K a))
    (hdLow : 2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞))
    (hnotEndpoint : ordUnit K a ≠
      -(2 * (ramificationIndex K : Int)))
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) =
      quadraticNormSquareClassSubgroup K (-a) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  letI : UnitQuadraticDefectParityLaws K :=
    unitQuadraticDefectParityLawsProved
  have hfinite : beliParameterDefect K a ≠ ⊤ := by
    intro htop
    rw [htop] at hdLow
    simp at hdLow
  have hRupper : ¬2 * (ramificationIndex K : Int) < ordUnit K a := by
    have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  have hdLow' : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞) := by
    simpa only [beliDefectCutoff, beliSpinorCaseIIILowerCutoff] using hdLow
  have harithmetic := scratch_beliLowBranch_arithmetic
    (K := K) a ha hRupper hdLow' hEven hnotEndpoint
  rcases harithmetic with
    ⟨hmPos, hmOdd, _hmLtTwoE, _hmLtTwoS, hmLeS⟩
  rcases exists_defectAdaptedShear a ha hEven with
    ⟨c₀, htwo₀, hdiag₀, hcross₀, hsecond₀⟩
  have hdiagOrder₀ : ord K (c₀ ^ 2 + (a : K)) =
      (((beliLowDefectExponent K a : Nat) : Int) : WithTop Int) := by
    rcases hsecond₀ with htop | hfiniteCase
    · exact (hfinite htop.1).elim
    · rw [hfiniteCase.2]
      norm_cast
      exact (scratch_beliLowDefectExponent_cast a ha hfinite).symm
  have hsNonneg : 0 ≤
      (ramificationIndex K : Int) + ordUnit K a / 2 := by
    have hmPosInt : 0 < (beliLowDefectExponent K a : Int) := by
      exact_mod_cast hmPos
    omega
  have hsLtE :
      (ramificationIndex K : Int) + ordUnit K a / 2 <
        (ramificationIndex K : Int) := by
    rcases hEven with ⟨r, hr⟩
    omega
  have hadapted :
      Lattice.spinorNormImage
          (q := QuadraticSpace.binaryModel a c₀)
          (L := binaryModelLattice (K := K)) =
        quadraticNormSquareClassSubgroup K (-a) := by
    apply spinorNormImage_binaryModel_eq_norm_of_all_primitive_reflections
      a c₀ htwo₀ hdiag₀
    intro z hz hzMem hzPrimitive
    exact primitive_isIntegralReflection_binaryModel_of_modular_low
      a c₀ (beliLowDefectExponent K a)
        ((ramificationIndex K : Int) + ordUnit K a / 2)
          htwo₀ hdiag₀ hcross₀ hdiagOrder₀ hmPos hmOdd
            hsNonneg hmLeS hsLtE hz hzMem hzPrimitive
  have hsub : c₀ - c ∈ IntegerRing K :=
    binaryShear_sub_mem_integerRing a c₀ c
      htwo₀ hdiag₀ htwo hdiag
  rcases binaryModel_isIsometric_of_shear_sub_integral
      a c₀ c hsub with ⟨f⟩
  have hspinor :
      Lattice.spinorNormImage
          (q := QuadraticSpace.binaryModel a c₀)
          (L := binaryModelLattice (K := K)) =
        Lattice.spinorNormImage
          (q := QuadraticSpace.binaryModel a c)
          (L := binaryModelLattice (K := K)) :=
    Lattice.spinorNormImage_eq_of_isometry f
  rw [← hspinor]
  exact hadapted

/-- Every norm-generator unit square class of a binary model occurs as an
integral spinor norm.  This is the scaled-first construction with trivial
scale factor. -/
theorem beliNormGeneratorSquareClassGroup_le_spinorNormImage_binaryModel
    (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    beliNormGeneratorSquareClassGroup K a ≤
      Lattice.spinorNormImageSubgroup
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) := by
  apply
    beliNormGeneratorSquareClassGroup_le_spinorNormImage_binaryModel_of_scaledFirst
      a a (1 : Kˣ) c
  · simpa using htwo
  · simpa using hdiag
  · exact htwo
  · exact hdiag
  · simp
  · norm_num
  · norm_num
  · simpa using htwo
  · simpa using htwo
  · have htwoDiag : (2 : K) * (c ^ 2 + (a : K)) ∈ IntegerRing K :=
      (IntegerRing K).mul_mem _ _
        (show (2 : K) ∈ IntegerRing K by norm_num) hdiag
    simpa using htwoDiag

/-- The square-class norm group of the distinguished unramified quadratic
extension is exactly the subgroup represented by valuation units. -/
theorem quadraticNormSquareClassSubgroup_discriminant_eq_valuationUnit
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K] :
    quadraticNormSquareClassSubgroup K laws.discriminantUnit =
      valuationUnitSquareClassSubgroup K := by
  ext A
  constructor
  · rintro ⟨b, hbNorm, hclass⟩
    have hEven : Even (ordUnit K b) :=
      (isQuadraticNorm_discriminant_iff_even_order b).1 hbNorm
    have hunit : squareClass K b ∈
        valuationUnitSquareClassSubgroup K :=
      (squareClass_mem_valuationUnitSquareClassSubgroup_iff_even b).2 hEven
    have hclass' : squareClass K b = A := by
      simpa only [squareClassHom_apply] using hclass
    rwa [hclass'] at hunit
  · rintro ⟨b, hbUnit, hclass⟩
    have hbOrder : ordUnit K b = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K b).1 hbUnit
    have hEven : Even (ordUnit K b) := by
      rw [hbOrder]
      exact ⟨0, by simp⟩
    exact ⟨b, (isQuadraticNorm_discriminant_iff_even_order b).2 hEven,
      hclass⟩

/-- Every valuation-unit square class belongs to the norm-generator group
at either admissible lower endpoint. -/
theorem valuationUnitSquareClassSubgroup_le_beliNormGeneratorSquareClassGroup_endpoint
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    (a : Kˣ)
    (horder : ordUnit K a =
      -(2 * (ramificationIndex K : Int)))
    (hclass : unitSquareClass K a =
        unitSquareClass K (negativeQuarterUnit K) ∨
      unitSquareClass K a = unitSquareClass K
        (negativeQuarterUnit K * laws.discriminantUnit)) :
    valuationUnitSquareClassSubgroup K ≤
      beliNormGeneratorSquareClassGroup K a := by
  rintro A ⟨b, hbUnit, hclassA⟩
  let u : valuationUnitSubgroup K := ⟨b, hbUnit⟩
  have hu := valuationUnitClassHom_mem_beliNormGeneratorGroup_of_endpoint
    a horder hclass u
  have hmem := valuationUnitClassToSquareClass_mem_beliNormGeneratorGroup
    (K := K) hu
  have hmap : valuationUnitClassToSquareClass K
      (valuationUnitClassHom K u) = squareClass K b := rfl
  have hclassA' : squareClass K b = A := by
    simpa only [squareClassHom_apply] using hclassA
  rw [hmap, hclassA'] at hmem
  exact hmem

/-- The finite-defect lower endpoint is the `-Δ/4` class.  Its quadratic
norm group is the even-valuation subgroup, while all unit classes occur as
norm-generator spinor classes. -/
theorem spinorNormImage_binaryModel_eq_quadraticNorm_endpoint_finite
    (a : Kˣ) (c : K)
    (ha : IsBinaryParameterAdmissible a)
    (horder : ordUnit K a =
      -(2 * (ramificationIndex K : Int)))
    (hfinite : beliParameterDefect K a ≠ ⊤)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) =
      quadraticNormSquareClassSubgroup K (-a) := by
  letI disc : DyadicDiscriminantClassLaws K :=
    dyadicDiscriminantClassLawsProved
  letI unramified : DyadicUnramifiedNormLaws K :=
    dyadicUnramifiedNormLawsProvedDirect
  have hclasses := disc.endpoint_parameter_class a ha horder
  have hdiscriminant : unitSquareClass K a = unitSquareClass K
      (negativeQuarterUnit K * disc.discriminantUnit) := by
    rcases hclasses with hquarter | hdiscriminant
    · have hdefect := beliParameterDefect_eq_of_unitSquareClass_eq
        (K := K) hquarter
      rw [beliParameterDefect_negativeQuarterUnit] at hdefect
      exact (hfinite hdefect).elim
    · exact hdiscriminant
  have hsquare : IsSquare (-a * disc.discriminantUnit) :=
    isSquare_neg_mul_discriminant_of_endpointClass hdiscriminant
  rcases hsquare with ⟨s, hs⟩
  have hfactor : -a = disc.discriminantUnit *
      (s * disc.discriminantUnit⁻¹) ^ 2 := by
    calc
      -a = (-a * disc.discriminantUnit) *
          disc.discriminantUnit⁻¹ := by simp
      _ = (s * s) * disc.discriminantUnit⁻¹ := by rw [hs]
      _ = disc.discriminantUnit *
          (s * disc.discriminantUnit⁻¹) ^ 2 := by
        simp only [pow_two]
        calc
          s * s * disc.discriminantUnit⁻¹ =
              (disc.discriminantUnit * disc.discriminantUnit⁻¹) *
                (s * s) * disc.discriminantUnit⁻¹ := by simp
          _ = disc.discriminantUnit * s * disc.discriminantUnit⁻¹ * s *
                disc.discriminantUnit⁻¹ := by ac_rfl
          _ = disc.discriminantUnit *
              (s * disc.discriminantUnit⁻¹ *
                (s * disc.discriminantUnit⁻¹)) := by group
  have hnorm : quadraticNormSquareClassSubgroup K (-a) =
      valuationUnitSquareClassSubgroup K := by
    rw [hfactor, quadraticNormSquareClassSubgroup_mul_square]
    exact quadraticNormSquareClassSubgroup_discriminant_eq_valuationUnit
      (K := K)
  have hunitLeG : valuationUnitSquareClassSubgroup K ≤
      beliNormGeneratorSquareClassGroup K a :=
    valuationUnitSquareClassSubgroup_le_beliNormGeneratorSquareClassGroup_endpoint
      a horder (Or.inr hdiscriminant)
  have hGLeSpin :=
    beliNormGeneratorSquareClassGroup_le_spinorNormImage_binaryModel
      a c htwo hdiag
  apply Set.Subset.antisymm
  · exact spinorNormImage_binaryModel_le_quadraticNorm a c htwo hdiag
  · intro A hA
    have hunit : A ∈ valuationUnitSquareClassSubgroup K := by
      rw [← hnorm]
      exact hA
    have hspin := hGLeSpin (hunitLeG hunit)
    change A ∈ Lattice.spinorNormImage
      (q := QuadraticSpace.binaryModel a c)
      (L := binaryModelLattice (K := K)) at hspin
    exact hspin

/-- Complete low-defect formula for every negative even admissible binary
model, including the finite non-hyperbolic lower endpoint. -/
theorem spinorNormImage_binaryModel_eq_beliSpinorGroupRepresentative_negative_even_low
    (a : Kˣ) (c : K)
    (ha : IsBinaryParameterAdmissible a)
    (hRneg : ordUnit K a < 0)
    (hEven : Even (ordUnit K a))
    (hdLow : 2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞))
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) =
      (beliSpinorGroupRepresentative K a : Set (SquareClass K)) := by
  have hfinite : beliParameterDefect K a ≠ ⊤ := by
    intro htop
    rw [htop] at hdLow
    simp at hdLow
  have hnorm :
      Lattice.spinorNormImage
          (q := QuadraticSpace.binaryModel a c)
          (L := binaryModelLattice (K := K)) =
        quadraticNormSquareClassSubgroup K (-a) := by
    by_cases hendpoint : ordUnit K a =
        -(2 * (ramificationIndex K : Int))
    · exact spinorNormImage_binaryModel_eq_quadraticNorm_endpoint_finite
        a c ha hendpoint hfinite htwo hdiag
    · exact
        spinorNormImage_binaryModel_eq_quadraticNorm_negative_even_low_nonendpoint
          a c ha hRneg hEven hdLow hendpoint htwo hdiag
  have hquarter : unitSquareClass K a ≠
      unitSquareClass K (negativeQuarterUnit K) := by
    intro hclass
    have hdefect := beliParameterDefect_eq_of_unitSquareClass_eq
      (K := K) hclass
    rw [beliParameterDefect_negativeQuarterUnit] at hdefect
    exact hfinite hdefect
  have hRupper : ordUnit K a ≤
      2 * (ramificationIndex K : Int) := by
    have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  have hformula := beliSpinorGroupRepresentative_caseIII_low
    K a ha hquarter hRupper hdLow
  calc
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) =
      (quadraticNormSquareClassSubgroup K (-a) : Set (SquareClass K)) := hnorm
    _ = (beliSpinorGroupRepresentative K a : Set (SquareClass K)) := by
      exact congrArg
        (fun H : Subgroup (SquareClass K) => (H : Set (SquareClass K)))
        hformula.symm

/-- Intrinsic low-defect formula for a binary BONG with negative even gap. -/
theorem spinorNormImage_eq_beliSpinorGroupRepresentative_negative_even_low
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2)
    (hRneg : b.binaryOrderGap < 0)
    (hEven : Even b.binaryOrderGap)
    (hdLow : 2 * beliParameterDefect K b.binaryParameter ≤
      (beliSpinorCaseIIILowerCutoff K b.binaryParameter : ℕ∞)) :
    Lattice.spinorNormImage (q := q) (L := L) =
      (beliSpinorGroupRepresentative K b.binaryParameter :
        Set (SquareClass K)) := by
  rw [b.spinorNormImage_eq_binaryModel]
  apply
    spinorNormImage_binaryModel_eq_beliSpinorGroupRepresentative_negative_even_low
  · exact b.binaryParameter_isBinaryParameterAdmissible
  · change b.binaryParameterOrder < 0
    rwa [b.binaryParameterOrder_eq_orderGap]
  · change Even b.binaryParameterOrder
    rwa [b.binaryParameterOrder_eq_orderGap]
  · exact hdLow
  · exact b.binaryModelCoefficient_isAdmissibleWitness.1
  · exact b.binaryModelCoefficient_isAdmissibleWitness.2

/-- A strictly negative binary BONG gap is even.  This is the parity part of
Beli (2003), Lemma 3.3(iii), obtained from the mixed modular scale. -/
theorem binaryOrderGap_even_of_negative
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2) (hnegative : b.binaryOrderGap < 0) :
    Even b.binaryOrderGap := by
  have hstrict : b.order 1 < b.order 0 := by
    rw [binaryOrderGap] at hnegative
    omega
  have hsum := b.two_mul_ordUnit_binaryMixedPairing_eq_order_add hstrict
  refine ⟨ordUnit K (b.binaryMixedPairingUnit hstrict) - b.order 0, ?_⟩
  rw [binaryOrderGap]
  omega

/-- Beli (2003), Lemma 3.7 for every negative binary BONG gap. -/
theorem spinorNormImage_eq_beliSpinorGroupRepresentative_of_negative
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2) (hnegative : b.binaryOrderGap < 0) :
    Lattice.spinorNormImage (q := q) (L := L) =
      (beliSpinorGroupRepresentative K b.binaryParameter :
        Set (SquareClass K)) := by
  have hEven := b.binaryOrderGap_even_of_negative hnegative
  by_cases hdLow : 2 * beliParameterDefect K b.binaryParameter ≤
      (beliSpinorCaseIIILowerCutoff K b.binaryParameter : ℕ∞)
  · exact
      b.spinorNormImage_eq_beliSpinorGroupRepresentative_negative_even_low
        hnegative hEven hdLow
  · exact
      b.spinorNormImage_eq_beliSpinorGroupRepresentative_negative_even_nonlow
        hnegative hEven hdLow

end BONG

end Bong
