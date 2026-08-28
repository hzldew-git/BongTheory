/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.BinaryDefectAdaptedValues
import Bong.Bong.BinaryEndpointProduct
import Bong.Bong.Beli2009BinaryRemarks
import Bong.Dyadic.UnramifiedNorm

/-!
# Beli (2019), Corollary 5.15

This file proves the numerical binary representation dichotomy used in the
collision case of Section 5.  The proof transports an arbitrary represented
value to a defect-adapted binary model.  At the lower endpoint it combines
the endpoint square-class alternative with the norm group of the unramified
quadratic extension; thus the conclusion is derived from the established
dyadic local-field interfaces rather than assumed as a Section 5 law.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- A normalized defect-adapted binary model cannot represent an element of
order one when its cross coefficient has positive order and its second
diagonal coefficient has order at least two. -/
private theorem no_model_order_one_of_cross_diag_ge_two
    (a : Kˣ) (c : K) (x : Fin 2 → K)
    (hx : ∀ i, x i ∈ IntegerRing K)
    (hcross : ((1 : Int) : WithTop Int) ≤ ord K ((2 : K) * c))
    (hdiag : ((2 : Int) : WithTop Int) ≤
      ord K (c ^ 2 + (a : K)))
    (hvalue : ord K
      ((QuadraticSpace.binaryModel a c).quadratic x) =
        ((1 : Int) : WithTop Int)) :
    False := by
  have hxzero : (0 : WithTop Int) ≤ ord K (x 0) :=
    (mem_integerRing_iff K).1 (hx 0)
  have hxone : (0 : WithTop Int) ≤ ord K (x 1) :=
    (mem_integerRing_iff K).1 (hx 1)
  have hlast : ((2 : Int) : WithTop Int) ≤
      ord K ((c ^ 2 + (a : K)) * (x 1) ^ 2) := by
    calc
      ((2 : Int) : WithTop Int) ≤
          ord K (c ^ 2 + (a : K)) + (0 : WithTop Int) := by
        simpa using hdiag
      _ ≤ ord K (c ^ 2 + (a : K)) +
          (ord K (x 1) + ord K (x 1)) := by
        exact add_le_add le_rfl (add_nonneg hxone hxone)
      _ = ord K (c ^ 2 + (a : K)) + ord K ((x 1) ^ 2) := by
        rw [ord_pow]
        simp only [two_nsmul]
      _ = ord K ((c ^ 2 + (a : K)) * (x 1) ^ 2) :=
        (ord_mul K _ _).symm
  let value : K := (QuadraticSpace.binaryModel a c).quadratic x
  by_cases hmax : ((1 : Int) : WithTop Int) ≤ ord K (x 0)
  · have hfirst : ((2 : Int) : WithTop Int) ≤ ord K ((x 0) ^ 2) := by
      rw [ord_pow]
      have htwo : ((2 : Int) : WithTop Int) =
          ((1 : Int) : WithTop Int) + ((1 : Int) : WithTop Int) := by
        norm_num
      rw [htwo]
      simpa only [two_nsmul] using add_le_add hmax hmax
    have hmiddle : ((2 : Int) : WithTop Int) ≤
        ord K (((2 : K) * c) * (x 0 * x 1)) := by
      calc
        ((2 : Int) : WithTop Int) ≤
            ord K ((2 : K) * c) + ord K (x 0) + 0 := by
          have := add_le_add hcross hmax
          have htwo : ((2 : Int) : WithTop Int) =
              ((1 : Int) : WithTop Int) + ((1 : Int) : WithTop Int) := by
            norm_num
          rw [htwo]
          simpa only [add_zero] using this
        _ ≤ ord K ((2 : K) * c) + ord K (x 0) + ord K (x 1) :=
          add_le_add le_rfl hxone
        _ = ord K ((2 : K) * c) + ord K (x 0 * x 1) := by
          rw [ord_mul K (x 0) (x 1)]
          exact add_assoc _ _ _
        _ = ord K (((2 : K) * c) * (x 0 * x 1)) :=
          (ord_mul K _ _).symm
    have hfirstMiddle : ((2 : Int) : WithTop Int) ≤
        ord K ((x 0) ^ 2 + ((2 : K) * c) * (x 0 * x 1)) :=
      (le_min hfirst hmiddle).trans (min_ord_le_ord_add K _ _)
    have htotal : ((2 : Int) : WithTop Int) ≤ ord K value := by
      have := (le_min hfirstMiddle hlast).trans
        (min_ord_le_ord_add K
          ((x 0) ^ 2 + ((2 : K) * c) * (x 0 * x 1))
          ((c ^ 2 + (a : K)) * (x 1) ^ 2))
      simpa only [value, QuadraticSpace.binaryModel_quadratic_apply] using this
    rw [show ord K value = ((1 : Int) : WithTop Int) by
      simpa only [value] using hvalue] at htotal
    exact (not_le_of_gt (WithTop.coe_lt_coe.mpr (by omega))) htotal
  · have hxzeroField : x 0 ≠ 0 := by
      intro hz
      apply hmax
      rw [hz, ord_zero]
      exact le_top
    let xu : Kˣ := Units.mk0 (x 0) hxzeroField
    have hxOrder : ord K (x 0) =
        ((ordUnit K xu : Int) : WithTop Int) :=
      (coe_ordUnit K xu).symm
    have hxUnitOrder : ordUnit K xu = 0 := by
      have hxNonneg : 0 ≤ ordUnit K xu := by
        have := hxzero
        rw [hxOrder] at this
        exact WithTop.coe_nonneg.mp this
      have hxLt : ordUnit K xu < 1 := by
        rw [hxOrder] at hmax
        exact WithTop.coe_lt_coe.mp (lt_of_not_ge hmax)
      omega
    have hfirst : ord K ((x 0) ^ 2) = 0 := by
      rw [ord_pow, hxOrder, hxUnitOrder]
      simp
    have hmiddle : ((1 : Int) : WithTop Int) ≤
        ord K (((2 : K) * c) * (x 0 * x 1)) := by
      calc
        ((1 : Int) : WithTop Int) ≤
            ord K ((2 : K) * c) + (0 : WithTop Int) + 0 := by
          simpa using hcross
        _ ≤ ord K ((2 : K) * c) + ord K (x 0) + ord K (x 1) :=
          add_le_add (add_le_add le_rfl hxzero) hxone
        _ = ord K ((2 : K) * c) + ord K (x 0 * x 1) := by
          rw [ord_mul K (x 0) (x 1)]
          exact add_assoc _ _ _
        _ = ord K (((2 : K) * c) * (x 0 * x 1)) :=
          (ord_mul K _ _).symm
    let error : K := ((2 : K) * c) * (x 0 * x 1) +
      (c ^ 2 + (a : K)) * (x 1) ^ 2
    have herror : ((1 : Int) : WithTop Int) ≤ ord K error := by
      exact (le_min hmiddle
        ((WithTop.coe_le_coe.mpr (by omega)).trans hlast)).trans
          (min_ord_le_ord_add K _ _)
    have hstrict : ord K ((x 0) ^ 2) < ord K error := by
      rw [hfirst]
      exact (WithTop.coe_lt_coe.mpr (by omega)).trans_le herror
    have hsum := (ord K).map_add_eq_of_lt_left hstrict
    have hidentity : (x 0) ^ 2 + error = value := by
      dsimp only [error, value]
      rw [QuadraticSpace.binaryModel_quadratic_apply]
      ring
    rw [hidentity, hfirst] at hsum
    have hvalueZero : ord K value = 0 := hsum
    rw [show ord K value = ((1 : Int) : WithTop Int) by
      simpa only [value] using hvalue] at hvalueZero
    norm_num at hvalueZero

/-- When the cross coefficient of the defect-adapted binary model has
positive order, representation one order above the norm generator forces
the finite second-diagonal exponent to be at most one. -/
private theorem represented_order_succ_finite_low_le_one_of_cross_pos
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    (b : BONG V q L 2)
    (heven : Even b.binaryOrderGap)
    {z : V} (hzL : z ∈ L)
    (hzOrder : ord K (q.quadratic z) =
      (((b.order 0 + 1 : Int)) : WithTop Int))
    (hcrossPos : 0 < (ramificationIndex K : Int) +
      b.binaryOrderGap / 2) :
    beliParameterDefect K b.binaryParameter ≠ ⊤ ∧
      b.binaryOrderGap +
        (beliParameterDefectNat K b.binaryParameter : Int) ≤ 1 := by
  have hparameterOrder : ordUnit K b.binaryParameter =
      b.binaryOrderGap := by
    change b.binaryParameterOrder = b.binaryOrderGap
    exact b.binaryParameterOrder_eq_orderGap
  have hparameterEven : Even (ordUnit K b.binaryParameter) := by
    rw [hparameterOrder]
    exact heven
  rcases exists_defectAdaptedShear b.binaryParameter
      b.binaryParameter_isBinaryParameterAdmissible hparameterEven with
    ⟨c, htwo, hdiagIntegral, hcrossEq, hdiagCases⟩
  rw [hparameterOrder] at hcrossEq hdiagCases
  let c₀ : K := b.binaryModelCoefficient
  have hc₀ := b.binaryModelCoefficient_isAdmissibleWitness
  have hsub : c - c₀ ∈ IntegerRing K :=
    binaryShear_sub_mem_integerRing b.binaryParameter c c₀
      htwo hdiagIntegral hc₀.1 hc₀.2
  rcases rescaledBinaryModel_isIsometric_of_shear_sub_integral
      (b.valueUnit 0) b.binaryParameter c c₀ hsub with ⟨g⟩
  rcases b.normalizedBinaryModel_isIsometric with ⟨f⟩
  let F : Lattice.Isometry
      (QuadraticSpace.rescaleUnit (b.valueUnit 0)
        (QuadraticSpace.binaryModel b.binaryParameter c)) q
      (binaryModelLattice (K := K)) L :=
    g.trans f
  let x : Fin 2 → K := F.toLinearEquiv.symm z
  have hxmem : x ∈ binaryModelLattice (K := K) := by
    apply (F.map_mem x).mpr
    simpa [x] using hzL
  have hx : ∀ i, x i ∈ IntegerRing K :=
    (mem_binaryModelLattice_iff_coordinates x).1 hxmem
  have hFx : F.toLinearEquiv x = z := by simp [x]
  have hmap := F.map_quadratic x
  change q.quadratic (F.toLinearEquiv x) =
    (b.valueUnit 0 : K) *
      (QuadraticSpace.binaryModel b.binaryParameter c).quadratic x at hmap
  have hmodelOrder : ord K
      ((QuadraticSpace.binaryModel b.binaryParameter c).quadratic x) =
        ((1 : Int) : WithTop Int) := by
    have hqOrder : ord K (q.quadratic (F.toLinearEquiv x)) =
        (((b.order 0 + 1 : Int)) : WithTop Int) := by
      rw [hFx]
      exact hzOrder
    rw [hmap, ord_mul, ← coe_ordUnit,
      ← b.order_eq_ordUnit] at hqOrder
    have hcancel :
        ((b.order 0 : Int) : WithTop Int) +
            ord K ((QuadraticSpace.binaryModel
              b.binaryParameter c).quadratic x) =
          ((b.order 0 : Int) : WithTop Int) +
            ((1 : Int) : WithTop Int) := by
      simpa only [WithTop.coe_add] using hqOrder
    exact (WithTop.add_left_inj (x :=
      ((b.order 0 : Int) : WithTop Int)) WithTop.coe_ne_top).mp hcancel
  have hcrossLower : ((1 : Int) : WithTop Int) ≤
      ord K ((2 : K) * c) := by
    rw [hcrossEq]
    exact WithTop.coe_le_coe.mpr (by omega)
  by_cases hfinite : beliParameterDefect K b.binaryParameter ≠ ⊤
  · refine ⟨hfinite, ?_⟩
    by_contra hnot
    have hlowGt : 1 < b.binaryOrderGap +
        (beliParameterDefectNat K b.binaryParameter : Int) := by omega
    have hdiagLower : ((2 : Int) : WithTop Int) ≤
        ord K (c ^ 2 + (b.binaryParameter : K)) := by
      rcases hdiagCases with htop | hfin
      · exact False.elim (hfinite htop.1)
      · rw [hfin.2]
        exact WithTop.coe_le_coe.mpr (by omega)
    exact no_model_order_one_of_cross_diag_ge_two
      b.binaryParameter c x hx hcrossLower hdiagLower hmodelOrder
  · exfalso
    have htop : beliParameterDefect K b.binaryParameter = ⊤ := by
      simpa using hfinite
    have hdiagzero : c ^ 2 + (b.binaryParameter : K) = 0 := by
      rcases hdiagCases with htopCase | hfin
      · exact htopCase.2
      · exact False.elim (hfin.1 htop)
    have hdiagLower : ((2 : Int) : WithTop Int) ≤
        ord K (c ^ 2 + (b.binaryParameter : K)) := by
      rw [hdiagzero, ord_zero]
      exact le_top
    exact no_model_order_one_of_cross_diag_ge_two
      b.binaryParameter c x hx hcrossLower hdiagLower hmodelOrder

/-- Every nonzero value of a binary BONG, divided by its first diagonal
value, is represented by the norm form with parameter `-a`. -/
private theorem quadraticValueRatioUnit_isQuadraticNorm_binary
    (b : BONG V q L 2) {z : V} (hz : q.quadratic z ≠ 0) :
    let w : Kˣ := Units.mk0 (q.quadratic z / b.value 0)
      (div_ne_zero hz (b.value_ne_zero 0))
    IsQuadraticNorm K (-b.binaryParameter) w := by
  let x₀ : K := b.basis.repr z 0
  let x₁ : K := b.basis.repr z 1
  have hzDecomposition :
      x₀ • b.ambientVector 0 + x₁ • b.ambientVector 1 = z := by
    have h := b.basis.sum_repr z
    rw [Fin.sum_univ_two] at h
    exact h
  have horthogonal :
      q.bilin (b.ambientVector 0) (b.ambientVector 1) = 0 := by
    apply (LinearMap.BilinForm.iIsOrtho_def.mp b.ambientVector_iIsOrtho)
    norm_num
  have hquadratic :
      q.quadratic z = x₀ ^ 2 * b.value 0 + x₁ ^ 2 * b.value 1 := by
    rw [← hzDecomposition, q.quadratic_add, q.quadratic_smul,
      q.quadratic_smul, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right, horthogonal,
      b.quadratic_ambientVector, b.quadratic_ambientVector]
    ring
  dsimp only
  refine ⟨x₀, x₁, ?_⟩
  simp only [Units.val_mk0, Units.val_neg]
  rw [hquadratic, b.coe_binaryParameter]
  field_simp [b.value_ne_zero 0]
  ring

/-- Corollary 5.15, in the numerical form used in the collision branch of
Beli (2019): if a binary lattice represents a value exactly one order above
its first BONG value and the order gap is even, then either the half-gap
candidate is nonpositive or the low defect exponent is exactly one. -/
theorem represented_order_succ_implies_half_nonpos_or_defect_eq_one
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    (b : BONG V q L 2)
    (heven : Even b.binaryOrderGap)
    {z : V} (hzL : z ∈ L)
    (hzOrder : ord K (q.quadratic z) =
      (((b.order 0 + 1 : Int)) : WithTop Int)) :
    (ramificationIndex K : Int) + b.binaryOrderGap / 2 ≤ 0 ∨
      (beliParameterDefect K b.binaryParameter ≠ ⊤ ∧
        b.binaryOrderGap +
          (beliParameterDefectNat K b.binaryParameter : Int) = 1) := by
  by_cases hhalf :
      (ramificationIndex K : Int) + b.binaryOrderGap / 2 ≤ 0
  · exact Or.inl hhalf
  · right
    have hhalfPos : 0 <
        (ramificationIndex K : Int) + b.binaryOrderGap / 2 := by
      omega
    rcases represented_order_succ_finite_low_le_one_of_cross_pos
        b heven hzL hzOrder hhalfPos with ⟨hfinite, hle⟩
    refine ⟨hfinite, ?_⟩
    have hnonneg : 0 ≤ b.binaryOrderGap +
        (beliParameterDefectNat K b.binaryParameter : Int) := by
      have h := beli2009_order_add_parameterDefect_nonneg
        (K := K) b.binaryParameter_isBinaryParameterAdmissible hfinite
      have horder : ordUnit K b.binaryParameter =
          b.binaryOrderGap := by
        change b.binaryParameterOrder = b.binaryOrderGap
        exact b.binaryParameterOrder_eq_orderGap
      rw [horder] at h
      simpa [beliParameterDefectNat] using h
    have hzeroOrOne :
        b.binaryOrderGap +
            (beliParameterDefectNat K b.binaryParameter : Int) = 0 ∨
          b.binaryOrderGap +
            (beliParameterDefectNat K b.binaryParameter : Int) = 1 := by
      omega
    rcases hzeroOrOne with hzero | hone
    · exfalso
      let R : Int := b.binaryOrderGap
      let d : Nat := beliParameterDefectNat K b.binaryParameter
      let ε : Kˣ := normalizedUnitPart K b.binaryParameter
      have hεUnit : IsValuationUnit K (ε : K) := by
        simpa [ε] using
          normalizedUnitPart_isValuationUnit K b.binaryParameter
      have hfactor : uniformizerPowerUnit K R * ε =
          b.binaryParameter := by
        have h :=
          uniformizerPower_mul_normalizedUnitPart K b.binaryParameter
        have horder : ordUnit K b.binaryParameter = R := by
          change b.binaryParameterOrder = R
          simpa [R] using b.binaryParameterOrder_eq_orderGap
        rw [horder] at h
        simpa [ε] using h
      have hdefectUnit : quadraticDefect K (-ε) =
          beliParameterDefect K b.binaryParameter := by
        have h :=
          beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
            (K := K) R ε hεUnit (by simpa [R] using heven)
        rw [hfactor] at h
        exact h.symm
      have hfiniteUnit : quadraticDefect K (-ε) ≠ ⊤ := by
        rw [hdefectUnit]
        exact hfinite
      have hnegεUnit : IsValuationUnit K ((-ε : Kˣ) : K) := by
        change ord K (-((ε : Kˣ) : K)) = 0
        change ord K ((ε : Kˣ) : K) = 0 at hεUnit
        simpa only [ord_neg] using hεUnit
      have hnonsquare : ¬ IsSquare (-ε) := by
        intro hsquare
        exact hfiniteUnit
          ((quadraticDefect_eq_top_iff_isSquare (K := K) (-ε)).2 hsquare)
      have hdLeRaw := quadraticDefect_le_two_mul_e_of_not_isSquare
        (K := K) hnonsquare
      have hdLe : d ≤ 2 * ramificationIndex K := by
        rw [← ENat.coe_toNat hfiniteUnit] at hdLeRaw
        simpa [d, beliParameterDefectNat, hdefectUnit] using
          ENat.coe_le_coe.mp hdLeRaw
      have hdEq : d = 2 * ramificationIndex K := by
        by_contra hne
        have hdLt : d < 2 * ramificationIndex K := by omega
        have hdefectLt : quadraticDefect K (-ε) <
            ((2 * ramificationIndex K : Nat) : ℕ∞) := by
          rw [← ENat.coe_toNat hfiniteUnit]
          exact_mod_cast (show (quadraticDefect K (-ε)).toNat <
            2 * ramificationIndex K by
              simpa [d, beliParameterDefectNat, hdefectUnit] using hdLt)
        have hdOdd : Odd d := by
          simpa [d, beliParameterDefectNat, hdefectUnit] using
            (quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
              (K := K) (-ε) hnegεUnit hdefectLt)
        rcases heven with ⟨r, hr⟩
        rcases hdOdd with ⟨s, hs⟩
        have hsInt : (d : Int) = 2 * (s : Int) + 1 := by
          exact_mod_cast hs
        have hzero' : R + (d : Int) = 0 := by
          simpa [R, d] using hzero
        omega
      have hRend : b.binaryOrderGap =
          -(2 * (ramificationIndex K : Int)) := by
        have hzero' : R + (d : Int) = 0 := by
          simpa [R, d] using hzero
        exact_mod_cast (show R = -(2 * (ramificationIndex K : Int)) by
          omega)
      have hparameterOrderEnd : ordUnit K b.binaryParameter =
          -(2 * (ramificationIndex K : Int)) := by
        change b.binaryParameterOrder =
          -(2 * (ramificationIndex K : Int))
        rw [b.binaryParameterOrder_eq_orderGap]
        exact hRend
      rcases laws.endpoint_parameter_class b.binaryParameter
          b.binaryParameter_isBinaryParameterAdmissible
          hparameterOrderEnd with
        hquarter | hdiscriminant
      · have hsquare :=
          isSquare_neg_of_unitSquareClass_eq_negativeQuarter
            (K := K) hquarter
        have htop : beliParameterDefect K b.binaryParameter = ⊤ := by
          unfold beliParameterDefect
          exact (quadraticDefect_eq_top_iff_isSquare
            (K := K) (-b.binaryParameter)).2 hsquare
        exact hfinite htop
      · have hzNonzero : q.quadratic z ≠ 0 := by
          intro hz
          rw [hz, ord_zero] at hzOrder
          exact WithTop.top_ne_coe hzOrder
        let w : Kˣ := Units.mk0 (q.quadratic z / b.value 0)
          (div_ne_zero hzNonzero (b.value_ne_zero 0))
        have hwNorm : IsQuadraticNorm K (-b.binaryParameter) w := by
          simpa only [w] using
            quadraticValueRatioUnit_isQuadraticNorm_binary b hzNonzero
        have hwOrder : ordUnit K w = 1 := by
          apply WithTop.coe_injective
          rw [coe_ordUnit]
          change ord K (q.quadratic z / b.value 0) =
            (((1 : Int)) : WithTop Int)
          rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv,
            hzOrder, ← b.coe_order]
          norm_cast
          omega
        have hsquare :=
          isSquare_neg_mul_discriminant_of_endpointClass
            (K := K) hdiscriminant
        rcases hsquare with ⟨r, hr⟩
        let t : Kˣ := r / laws.discriminantUnit
        have hparameter : laws.discriminantUnit * t ^ 2 =
            -b.binaryParameter := by
          apply Units.ext
          change (laws.discriminantUnit : K) * (t : K) ^ 2 =
            -(b.binaryParameter : K)
          have hrVal := congrArg Units.val hr
          simp only [Units.val_neg, Units.val_mul] at hrVal
          dsimp [t]
          simp only [Units.val_div_eq_div_val]
          calc
            (laws.discriminantUnit : K) *
                ((r : K) / (laws.discriminantUnit : K)) ^ 2 =
                ((r : K) * (r : K)) /
                  (laws.discriminantUnit : K) := by
              field_simp [Units.ne_zero laws.discriminantUnit]
            _ = (-(b.binaryParameter : K) *
                  (laws.discriminantUnit : K)) /
                (laws.discriminantUnit : K) := by rw [hrVal]
            _ = -(b.binaryParameter : K) := by
              field_simp [Units.ne_zero laws.discriminantUnit]
        have hwNormDiscriminant :
            IsQuadraticNorm K laws.discriminantUnit w := by
          apply (isQuadraticNorm_mul_square_left_iff K
            laws.discriminantUnit w t).1
          rw [hparameter]
          exact hwNorm
        have hwEven : Even (ordUnit K w) :=
          (isQuadraticNorm_discriminant_iff_even_order w).1
            hwNormDiscriminant
        rw [hwOrder] at hwEven
        omega
    · exact hone

end BONG

end Bong
