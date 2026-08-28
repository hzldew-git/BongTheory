import Bong.Bong.BinaryNormGeneratorGroup
import Bong.Bong.BinaryModelIsometry
import Bong.Bong.BinaryExactRealization
import Bong.Lattice.NormGeneratorIsometry
import Bong.Lattice.FormRescale
import Bong.Dyadic.QuadraticNewtonRoot
import Bong.Bong.BinaryShearIsometry
import Bong.Bong.BeliLemma317
import Bong.Bong.Beli2009BinaryNormContainmentProof
import Bong.Bong.ResidueDefectProductProof
import Bong.Bong.Beli2019Lemma714Primitive
import Bong.Bong.BinaryEndpointProduct

/-!
# Proof of Beli's binary norm-generator value theorem

This file proves Beli (2003), Lemma 3.11 over the dyadic local-field
interfaces already established in the project.  The reverse inclusion covers
the low-defect odd and even cases, the high-defect Newton/Hensel case, and the
discriminant endpoint model.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

theorem scratch_exists_model_normGenerator_valueRatio_eq
    (b : BONG V q L 2) (y : V)
    (hy : Lattice.IsNormGenerator q L y) :
    ∃ (z : Fin 2 → K)
      (hz : Lattice.IsNormGenerator
        (QuadraticSpace.binaryModel b.binaryParameter
          b.binaryModelCoefficient)
        (binaryModelLattice (K := K)) z),
      (binaryExactModelBONG b.binaryParameter b.binaryModelCoefficient
          b.binaryModelCoefficient_isAdmissibleWitness.1
          b.binaryModelCoefficient_isAdmissibleWitness.2).normGeneratorValueRatioUnit
          z hz = b.normGeneratorValueRatioUnit y hy := by
  rcases b.normalizedBinaryModel_isIsometric with ⟨f⟩
  let z : Fin 2 → K := f.toLinearEquiv.symm y
  have hzScaled : Lattice.IsNormGenerator b.normalizedBinaryModelSpace
      (binaryModelLattice (K := K)) z := by
    exact hy.mapLatticeIsometry f.symm
  have hz : Lattice.IsNormGenerator
      (QuadraticSpace.binaryModel b.binaryParameter b.binaryModelCoefficient)
      (binaryModelLattice (K := K)) z := by
    exact (Lattice.isNormGenerator_rescaleQuadraticUnit_iff
      (q := QuadraticSpace.binaryModel b.binaryParameter b.binaryModelCoefficient)
      (L := binaryModelLattice (K := K)) (x := z) (b.valueUnit 0)).mp hzScaled
  refine ⟨z, hz, ?_⟩
  apply Units.ext
  simp only [normGeneratorValueRatioUnit, Units.val_div_eq_div_val,
    Units.val_mk0, coe_valueUnit]
  rw [binaryExactModelBONG_value_zero, div_one]
  have hmap := f.map_quadratic z
  change q.quadratic (f.toLinearEquiv z) =
    (b.valueUnit 0 : K) *
      (QuadraticSpace.binaryModel b.binaryParameter
        b.binaryModelCoefficient).quadratic z at hmap
  have hfy : f.toLinearEquiv z = y := by simp [z]
  rw [hfy, b.coe_valueUnit] at hmap
  rw [hmap]
  field_simp [b.value_ne_zero 0]

theorem scratch_exists_normGenerator_valueRatio_eq_model
    (b : BONG V q L 2) (z : Fin 2 → K)
    (hz : Lattice.IsNormGenerator
      (QuadraticSpace.binaryModel b.binaryParameter b.binaryModelCoefficient)
      (binaryModelLattice (K := K)) z) :
    ∃ (y : V) (hy : Lattice.IsNormGenerator q L y),
      b.normGeneratorValueRatioUnit y hy =
        (binaryExactModelBONG b.binaryParameter b.binaryModelCoefficient
          b.binaryModelCoefficient_isAdmissibleWitness.1
          b.binaryModelCoefficient_isAdmissibleWitness.2).normGeneratorValueRatioUnit
          z hz := by
  rcases b.normalizedBinaryModel_isIsometric with ⟨f⟩
  have hzScaled : Lattice.IsNormGenerator b.normalizedBinaryModelSpace
      (binaryModelLattice (K := K)) z :=
    (Lattice.isNormGenerator_rescaleQuadraticUnit_iff
      (q := QuadraticSpace.binaryModel b.binaryParameter b.binaryModelCoefficient)
      (L := binaryModelLattice (K := K)) (x := z) (b.valueUnit 0)).mpr hz
  let y : V := f.toLinearEquiv z
  have hy : Lattice.IsNormGenerator q L y :=
    hzScaled.mapLatticeIsometry f
  refine ⟨y, hy, ?_⟩
  apply Units.ext
  simp only [normGeneratorValueRatioUnit, Units.val_div_eq_div_val,
    Units.val_mk0, coe_valueUnit]
  rw [binaryExactModelBONG_value_zero, div_one]
  have hmap := f.map_quadratic z
  change q.quadratic (f.toLinearEquiv z) =
    (b.valueUnit 0 : K) *
      (QuadraticSpace.binaryModel b.binaryParameter
        b.binaryModelCoefficient).quadratic z at hmap
  dsimp only [y]
  rw [hmap, b.coe_valueUnit]
  field_simp [b.value_ne_zero 0]

theorem scratch_exists_normGenerator_of_shear
    (a : Kˣ) (c c' : K)
    (hc : (2 : K) * c ∈ IntegerRing K ∧
      c ^ 2 + (a : K) ∈ IntegerRing K)
    (hc' : (2 : K) * c' ∈ IntegerRing K ∧
      c' ^ 2 + (a : K) ∈ IntegerRing K)
    (z : Fin 2 → K)
    (hz : Lattice.IsNormGenerator (QuadraticSpace.binaryModel a c)
      (binaryModelLattice (K := K)) z) :
    ∃ (z' : Fin 2 → K)
      (hz' : Lattice.IsNormGenerator (QuadraticSpace.binaryModel a c')
        (binaryModelLattice (K := K)) z'),
      (QuadraticSpace.binaryModel a c').quadratic z' =
        (QuadraticSpace.binaryModel a c).quadratic z := by
  have hsub := binaryShear_sub_mem_integerRing a c c'
    hc.1 hc.2 hc'.1 hc'.2
  rcases rescaledBinaryModel_isIsometric_of_shear_sub_integral
      (1 : Kˣ) a c c' hsub with ⟨f⟩
  let z' := f.toLinearEquiv z
  have hzScaled := hz.rescaleQuadraticUnit (1 : Kˣ)
  have hz'Scaled := hzScaled.mapLatticeIsometry f
  have hz' : Lattice.IsNormGenerator (QuadraticSpace.binaryModel a c')
      (binaryModelLattice (K := K)) z' := by
    simpa [QuadraticSpace.rescaleUnit, z'] using hz'Scaled
  refine ⟨z', hz', ?_⟩
  have hmap := f.map_quadratic z
  simpa [QuadraticSpace.rescaleUnit, z'] using hmap

/-- A shear whose two correction terms have the exact orders used in
Beli's even-parameter calculation. -/
def ScratchDefectAdaptedShearData (a : Kˣ) : Prop :=
  ∃ c : K,
    (2 : K) * c ∈ IntegerRing K ∧
    c ^ 2 + (a : K) ∈ IntegerRing K ∧
    ord K ((2 : K) * c) =
      (((ramificationIndex K : Int) + ordUnit K a / 2 : Int) : WithTop Int) ∧
    ((beliParameterDefect K a = ⊤ ∧ c ^ 2 + (a : K) = 0) ∨
      (beliParameterDefect K a ≠ ⊤ ∧
        ord K (c ^ 2 + (a : K)) =
          ((ordUnit K a +
            (beliParameterDefectNat K a : Int) : Int) : WithTop Int)))

theorem scratch_exists_defectAdaptedShear
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    (a : Kˣ) (ha : IsBinaryParameterAdmissible a)
    (hEven : Even (ordUnit K a)) :
    ScratchDefectAdaptedShearData a := by
  let R : Int := ordUnit K a
  let d : Nat := (quadraticDefect K (-a)).toNat
  have hRlower : -(2 * (ramificationIndex K : Int)) ≤ R := by
    exact ha.ordUnit_ge_neg_two_mul_e
  have hRDouble : R = 2 * (R / 2) := by
    rcases hEven with ⟨r, hr⟩
    omega
  have hmNonneg : 0 ≤ (ramificationIndex K : Int) + R / 2 := by
    omega
  by_cases htop : quadraticDefect K (-a) = ⊤
  · rcases (quadraticDefect_eq_top_iff_isSquare (K := K) (-a)).1 htop with
      ⟨s, hs⟩
    have hnegOrder : ordUnit K (-a) = R := by
      apply WithTop.coe_injective
      rw [coe_ordUnit, coe_ordUnit]
      simpa only [Units.val_neg, ord_neg]
    have hsOrder : ordUnit K s = R / 2 := by
      have h := congrArg (ordUnit K) hs
      rw [ordUnit_mul, hnegOrder] at h
      omega
    let c : K := (s : K)
    have htwoOrder : ord K ((2 : K) * c) =
        (((ramificationIndex K : Int) + R / 2 : Int) : WithTop Int) := by
      dsimp [c]
      rw [ord_mul, ← ramificationIndex_spec, ← coe_ordUnit, hsOrder]
      norm_cast
    have htwoIntegral : (2 : K) * c ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      rw [Dyadic.IsIntegral, htwoOrder]
      exact_mod_cast hmNonneg
    have hdiag : c ^ 2 + (a : K) = 0 := by
      have hsVal := congrArg Units.val hs
      dsimp [c]
      simp only [Units.val_mul, Units.val_neg] at hsVal
      rw [pow_two, ← hsVal]
      ring
    refine ⟨c, htwoIntegral, ?_, ?_, Or.inl ?_⟩
    · rw [hdiag]
      exact (IntegerRing K).zero_mem
    · change ord K ((2 : K) * c) =
        (((ramificationIndex K : Int) + ordUnit K a / 2 : Int) : WithTop Int)
      simpa only [R] using htwoOrder
    · exact ⟨by simpa [beliParameterDefect] using htop, hdiag⟩
  · have hfinite : quadraticDefect K (-a) ≠ ⊤ := htop
    have hdefectEq : quadraticDefect K (-a) = (d : ℕ∞) := by
      simpa [d] using (ENat.coe_toNat hfinite).symm
    let ε : Kˣ := normalizedUnitPart K a
    have hε : IsValuationUnit K (ε : K) :=
      normalizedUnitPart_isValuationUnit K a
    have hfactor : uniformizerPowerUnit K R * ε = a := by
      simpa [R, ε] using uniformizerPower_mul_normalizedUnitPart K a
    have hdefectUnit : quadraticDefect K (-ε) = quadraticDefect K (-a) := by
      have h := beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
        (K := K) R ε hε (by simpa [R] using hEven)
      rw [hfactor] at h
      simpa [beliParameterDefect] using h.symm
    have hfiniteUnit : quadraticDefect K (-ε) ≠ ⊤ := by
      rw [hdefectUnit]
      exact hfinite
    have hnegεUnit : IsValuationUnit K ((-ε : Kˣ) : K) := by
      change ord K (-(ε : K)) = 0
      simpa only [ord_neg] using (show ord K (ε : K) = 0 from hε)
    have hdPos : 0 < d := by
      have hpos := quadraticDefect_toNat_pos_of_unit_of_ne_top
        (-ε) hnegεUnit hfiniteUnit
      rw [hdefectUnit] at hpos
      simpa [d] using hpos
    rcases exists_quadraticApproximation_exact_order (-a) hfinite with
      ⟨x, hxError⟩
    let err : K := 1 - x ^ 2 / ((-a : Kˣ) : K)
    have herrOrder : ord K err = ((d : Int) : WithTop Int) := by
      simpa [err, d] using hxError
    have herrPos : 0 < ord K err := by
      rw [herrOrder]
      exact_mod_cast hdPos
    have hratioOrder : ord K (x ^ 2 / ((-a : Kˣ) : K)) = 0 := by
      have hlt : ord K (1 : K) < ord K err := by
        simpa only [ord_one] using herrPos
      have hsub := (ord K).map_sub_eq_of_lt_left hlt
      have heq : 1 - err = x ^ 2 / ((-a : Kˣ) : K) := by
        dsimp [err]
        ring
      rw [heq] at hsub
      simpa using hsub
    have hxNe : x ≠ 0 := by
      intro hx
      rw [hx] at hratioOrder
      simp at hratioOrder
    let xu : Kˣ := Units.mk0 x hxNe
    have hnegOrder : ordUnit K (-a) = R := by
      apply WithTop.coe_injective
      rw [coe_ordUnit, coe_ordUnit]
      simpa only [Units.val_neg, ord_neg]
    have hratioUnitOrder : ordUnit K (xu ^ 2 * (-a)⁻¹) = 0 := by
      apply (isValuationUnit_iff_ordUnit_eq_zero K _).1
      rw [IsValuationUnit]
      have hval : ((xu ^ 2 * (-a)⁻¹ : Kˣ) : K) =
          x ^ 2 / ((-a : Kˣ) : K) := by
        simp [xu, div_eq_mul_inv]
      rw [hval]
      exact hratioOrder
    have hxOrder : ordUnit K xu = R / 2 := by
      rw [ordUnit_mul, ordUnit_pow, ordUnit_inv, hnegOrder]
        at hratioUnitOrder
      omega
    let c : K := x
    have hcOrder : ord K c = ((R / 2 : Int) : WithTop Int) := by
      dsimp [c]
      rw [← show (xu : K) = x by rfl, ← coe_ordUnit, hxOrder]
    have htwoOrder : ord K ((2 : K) * c) =
        (((ramificationIndex K : Int) + R / 2 : Int) : WithTop Int) := by
      rw [ord_mul, ← ramificationIndex_spec, hcOrder]
      norm_cast
    let D : K := c ^ 2 + (a : K)
    have hDEq : D = (a : K) * err := by
      dsimp [D, c, err]
      field_simp [Units.ne_zero a]
      ring
    have hDOrder : ord K D =
        ((R + (d : Int) : Int) : WithTop Int) := by
      rw [hDEq, ord_mul, ← coe_ordUnit, herrOrder]
      norm_cast
    have hDNonneg : 0 ≤ R + (d : Int) := by
      have hbase := order_add_defect_nonneg_of_admissible_even
        (K := K) R ε hε (by simpa [hfactor] using ha)
        hfiniteUnit (by simpa [R] using hEven)
      rw [hdefectUnit] at hbase
      simpa [d] using hbase
    have htwoIntegral : (2 : K) * c ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      rw [Dyadic.IsIntegral, htwoOrder]
      exact_mod_cast hmNonneg
    have hDIntegral : D ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      rw [Dyadic.IsIntegral, hDOrder]
      exact_mod_cast hDNonneg
    refine ⟨c, htwoIntegral, ?_, ?_, Or.inr ?_⟩
    · simpa [D] using hDIntegral
    · change ord K ((2 : K) * c) =
        (((ramificationIndex K : Int) + ordUnit K a / 2 : Int) : WithTop Int)
      simpa only [R] using htwoOrder
    · refine ⟨by simpa [beliParameterDefect] using hfinite, ?_⟩
      simpa [D, R, d, beliParameterDefectNat, beliParameterDefect] using hDOrder

theorem scratch_isQuadraticNorm_of_unitClass_mem
    (parameter : Kˣ) (u : valuationUnitSubgroup K)
    (hmem : valuationUnitClassHom K u ∈
      quadraticNormValuationClassSubgroup K parameter) :
    IsQuadraticNorm K parameter (u : Kˣ) := by
  rcases hmem with ⟨v, hv, hclass⟩
  change IsQuadraticNorm K parameter (v : Kˣ) at hv
  change
    QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K)) v =
      QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K)) u
    at hclass
  rw [QuotientGroup.mk'_eq_mk'] at hclass
  rcases hclass with ⟨s, hs, hvsu⟩
  change IsSquare s at hs
  rcases hs with ⟨t, hst⟩
  have hsSquare : IsSquare (s : Kˣ) := by
    refine ⟨(t : Kˣ), ?_⟩
    have hstK := congrArg
      (fun z : valuationUnitSubgroup K => (z : Kˣ)) hst
    simpa [pow_two] using hstK
  have hproduct : IsQuadraticNorm K parameter ((v : Kˣ) * (s : Kˣ)) :=
    hv.mul K (isQuadraticNorm_of_isSquare_right K hsSquare)
  have hvsuK := congrArg
    (fun z : valuationUnitSubgroup K => (z : Kˣ)) hvsu
  simpa using hvsuK ▸ hproduct

theorem scratch_mem_binaryModelLattice_iff (z : Fin 2 → K) :
    z ∈ binaryModelLattice (K := K) ↔
      ∀ i, z i ∈ IntegerRing K := by
  exact mem_binaryModelLattice_iff z

theorem scratch_quadraticDefect_ge_of_binaryModel_value
    [QuadraticDefectLaws K]
    (a : Kˣ) (c : K) (z : Fin 2 → K)
    (hz : z ∈ binaryModelLattice (K := K))
    (u : valuationUnitSubgroup K)
    (hvalue : (QuadraticSpace.binaryModel a c).quadratic z =
      ((u : Kˣ) : K))
    (m : Nat)
    (hcross : ((m : Int) : WithTop Int) ≤ ord K ((2 : K) * c))
    (hdiag : ((m : Int) : WithTop Int) ≤
      ord K (c ^ 2 + (a : K))) :
    (m : ℕ∞) ≤ quadraticDefect K (u : Kˣ) := by
  have hzCoords := (scratch_mem_binaryModelLattice_iff z).1 hz
  have hz0 : (0 : WithTop Int) ≤ ord K (z 0) :=
    (mem_integerRing_iff K).1 (hzCoords 0)
  have hz1 : (0 : WithTop Int) ≤ ord K (z 1) :=
    (mem_integerRing_iff K).1 (hzCoords 1)
  let crossTerm : K := ((2 : K) * c) * (z 0 * z 1)
  let diagonalTerm : K := (c ^ 2 + (a : K)) * z 1 ^ 2
  have hcrossTerm : ((m : Int) : WithTop Int) ≤ ord K crossTerm := by
    dsimp [crossTerm]
    rw [ord_mul, ord_mul]
    have hcoords : (0 : WithTop Int) ≤ ord K (z 0) + ord K (z 1) :=
      add_nonneg hz0 hz1
    simpa using add_le_add hcross hcoords
  have hdiagonalTerm : ((m : Int) : WithTop Int) ≤
      ord K diagonalTerm := by
    dsimp [diagonalTerm]
    rw [ord_mul, ord_pow]
    have hcoord : (0 : WithTop Int) ≤ 2 • ord K (z 1) :=
      nsmul_nonneg hz1 2
    simpa using add_le_add hdiag hcoord
  have herrorOrder : ((m : Int) : WithTop Int) ≤
      ord K (crossTerm + diagonalTerm) :=
    (le_min hcrossTerm hdiagonalTerm).trans
      (min_ord_le_ord_add K crossTerm diagonalTerm)
  apply natCast_le_quadraticDefect K
  refine ⟨z 0, ?_⟩
  have herrorEq :
      1 - (z 0) ^ 2 / ((u : Kˣ) : K) =
        (crossTerm + diagonalTerm) / ((u : Kˣ) : K) := by
    calc
      1 - (z 0) ^ 2 / ((u : Kˣ) : K) =
          (((u : Kˣ) : K) - (z 0) ^ 2) / ((u : Kˣ) : K) := by
            field_simp [Units.ne_zero (u : Kˣ)]
      _ = (crossTerm + diagonalTerm) / ((u : Kˣ) : K) := by
        congr 1
        rw [← hvalue, QuadraticSpace.binaryModel_quadratic_apply]
        dsimp [crossTerm, diagonalTerm]
        ring
  rw [herrorEq, div_eq_mul_inv, ord_mul, AddValuation.map_inv,
    u.property]
  simpa using herrorOrder

theorem scratch_isNormGenerator_binaryModel_of_mem_of_unit_value
    (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K)
    (z : Fin 2 → K) (hz : z ∈ binaryModelLattice (K := K))
    (u : valuationUnitSubgroup K)
    (hvalue : (QuadraticSpace.binaryModel a c).quadratic z =
      ((u : Kˣ) : K)) :
    Lattice.IsNormGenerator (QuadraticSpace.binaryModel a c)
      (binaryModelLattice (K := K)) z := by
  have hzAnisotropic :
      (QuadraticSpace.binaryModel a c).IsAnisotropic z := by
    rw [QuadraticSpace.IsAnisotropic, hvalue]
    exact Units.ne_zero (u : Kˣ)
  apply ((binaryModelFirst_isNormGenerator a c htwo hdiag).iff_isValuationUnit_quadratic_of_value_one
      (binaryModelFirst_isAnisotropic a c)
      (QuadraticSpace.binaryModel_quadratic_first a c)
      hz hzAnisotropic).2
  rw [hvalue]
  exact u.property

theorem scratch_exists_high_binaryModel_normGenerator
    (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K)
    (m : Nat)
    (hcross : ord K ((2 : K) * c) =
      ((m : Int) : WithTop Int))
    (hdiagonal : c ^ 2 + (a : K) = 0 ∨
      (c ^ 2 + (a : K) ≠ 0 ∧
        ((m : Int) : WithTop Int) < ord K (c ^ 2 + (a : K))))
    (u : valuationUnitSubgroup K)
    (hu : (u : Kˣ) ∈ principalUnitSubgroup K m) :
    ∃ (z : Fin 2 → K)
      (hz : Lattice.IsNormGenerator (QuadraticSpace.binaryModel a c)
        (binaryModelLattice (K := K)) z),
      (QuadraticSpace.binaryModel a c).quadratic z = ((u : Kˣ) : K) := by
  let d : K := (2 : K) * c
  let D : K := c ^ 2 + (a : K)
  let t : K := 1 - ((u : Kˣ) : K)
  have hdNe : d ≠ 0 := by
    intro hzero
    have h := hcross
    rw [show (2 : K) * c = d by rfl, hzero, ord_zero] at h
    exact WithTop.top_ne_coe h
  have htOrder : ((m : Int) : WithTop Int) ≤ ord K t := by
    have huError :=
      (Lattice.mem_powerIdeal_iff (K := K) (m : Int)
        (((u : Kˣ) : K) - 1)).1 hu.2
    have hneg : t = -(((u : Kˣ) : K) - 1) := by
      dsimp [t]
      ring
    rw [hneg, ord_neg]
    exact huError
  have hdOrder : ord K d = ((m : Int) : WithTop Int) := by
    simpa [d] using hcross
  by_cases htZero : t = 0
  · let z : Fin 2 → K := ![1, 0]
    have hzMem : z ∈ binaryModelLattice (K := K) := by
      rw [scratch_mem_binaryModelLattice_iff]
      intro i
      fin_cases i <;> simp [z]
    have huOne : ((u : Kˣ) : K) = 1 := by
      have hone := sub_eq_zero.mp htZero
      simpa [t] using hone.symm
    have hzValue : (QuadraticSpace.binaryModel a c).quadratic z =
        ((u : Kˣ) : K) := by
      rw [QuadraticSpace.binaryModel_quadratic_apply, huOne]
      simp [z]
    exact ⟨z,
      scratch_isNormGenerator_binaryModel_of_mem_of_unit_value
        a c htwo hdiag z hzMem u hzValue,
      hzValue⟩
  · rcases hdiagonal with hDZero | hDlarge
    · let b : K := (((u : Kˣ) : K) - 1) / d
      have hbIntegral : 0 ≤ ord K b := by
        dsimp [b]
        rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv, hdOrder]
        have hnumerator : ((m : Int) : WithTop Int) ≤
            ord K (((u : Kˣ) : K) - 1) := by
          have hneg : (((u : Kˣ) : K) - 1) = -t := by
            dsimp [t]
            ring
          rw [hneg, ord_neg]
          exact htOrder
        have hadd := add_le_add_right hnumerator
          (-((m : Int) : WithTop Int))
        simpa [add_comm] using hadd
      let z : Fin 2 → K := ![1, b]
      have hzMem : z ∈ binaryModelLattice (K := K) := by
        rw [scratch_mem_binaryModelLattice_iff]
        intro i
        fin_cases i
        · simp [z]
        · apply (mem_integerRing_iff K).2
          change 0 ≤ ord K b
          exact hbIntegral
      have hzValue : (QuadraticSpace.binaryModel a c).quadratic z =
          ((u : Kˣ) : K) := by
        rw [QuadraticSpace.binaryModel_quadratic_apply]
        dsimp [z]
        rw [hDZero]
        simp only [one_pow, one_mul, zero_mul, add_zero]
        change 1 + d * b = ((u : Kˣ) : K)
        dsimp [b]
        field_simp [hdNe]
        ring
      exact ⟨z,
        scratch_isNormGenerator_binaryModel_of_mem_of_unit_value
          a c htwo hdiag z hzMem u hzValue,
        hzValue⟩
    · rcases hDlarge with ⟨hDNeRaw, hDlarge⟩
      have hDNe : D ≠ 0 := by
        simpa [D] using hDNeRaw
      change ((m : Int) : WithTop Int) < ord K D at hDlarge
      let DU : Kˣ := Units.mk0 D hDNe
      let dU : Kˣ := Units.mk0 (-d) (neg_ne_zero.mpr hdNe)
      let tU : Kˣ := Units.mk0 t htZero
      have hdUOrder : ordUnit K dU = (m : Int) := by
        apply WithTop.coe_injective
        rw [coe_ordUnit]
        simpa [dU, ord_neg] using hdOrder
      have hdt : ordUnit K dU ≤ ordUnit K tU := by
        apply WithTop.coe_le_coe.mp
        rw [coe_ordUnit, coe_ordUnit]
        simpa [dU, tU, ord_neg, hdOrder] using htOrder
      have hDUlarge : (m : Int) < ordUnit K DU := by
        apply WithTop.coe_lt_coe.mp
        rw [coe_ordUnit]
        simpa [DU, D] using hDlarge
      have hnewton :
          2 * ordUnit K dU < ordUnit K DU + ordUnit K tU := by
        have htLower : (m : Int) ≤ ordUnit K tU := by
          simpa [hdUOrder] using hdt
        rw [hdUOrder]
        omega
      rcases exists_integral_quadratic_root_of_newton K DU dU tU
          hdt hnewton with ⟨b, hbIntegral, hbEquation⟩
      let z : Fin 2 → K := ![1, b]
      have hzMem : z ∈ binaryModelLattice (K := K) := by
        rw [scratch_mem_binaryModelLattice_iff]
        intro i
        fin_cases i
        · simp [z]
        · apply (mem_integerRing_iff K).2
          change 0 ≤ ord K b
          exact hbIntegral
      have hbEquation' :
          D * b ^ 2 + d * b + t = 0 := by
        simpa [DU, dU, tU] using hbEquation
      have hzValue : (QuadraticSpace.binaryModel a c).quadratic z =
          ((u : Kˣ) : K) := by
        rw [QuadraticSpace.binaryModel_quadratic_apply]
        dsimp [z, d, D, t] at hbEquation' ⊢
        linear_combination hbEquation'
      exact ⟨z,
        scratch_isNormGenerator_binaryModel_of_mem_of_unit_value
          a c htwo hdiag z hzMem u hzValue,
        hzValue⟩

theorem scratch_ord_add_add_eq_min_of_middle_gt
    (A B C : K) (hAC : ord K A ≠ ord K C)
    (hB : min (ord K A) (ord K C) < ord K B) :
    ord K (A + B + C) = min (ord K A) (ord K C) := by
  rcases lt_or_gt_of_ne hAC with hAlt | hClt
  · have hAB : ord K A < ord K B := by
      simpa [min_eq_left hAlt.le] using hB
    have hABOrder : ord K (A + B) = ord K A :=
      (ord K).map_add_eq_of_lt_left hAB
    rw [(ord K).map_add_eq_of_lt_left (by simpa [hABOrder] using hAlt),
      hABOrder, min_eq_left hAlt.le]
  · have hCB : ord K C < ord K B := by
      simpa [min_eq_right hClt.le] using hB
    have hBCOrder : ord K (B + C) = ord K C :=
      (ord K).map_add_eq_of_lt_right hCB
    rw [show A + B + C = A + (B + C) by ring,
      (ord K).map_add_eq_of_lt_right (by simpa [hBCOrder] using hClt),
      hBCOrder, min_eq_right hClt.le]

theorem scratch_low_binaryModel_coordinates_integral
    [QuadraticDefectLaws K]
    (a : Kˣ) (c : K) (m : Nat) (s : Int)
    (hcross : ord K ((2 : K) * c) = (s : WithTop Int))
    (hdiag : ord K (c ^ 2 + (a : K)) =
      ((m : Int) : WithTop Int))
    (hmPos : 0 < m) (hmOdd : Odd m)
    (hmLtTwoE : m < 2 * ramificationIndex K)
    (hmLtTwoS : (m : Int) < 2 * s)
    (hmLeS : (m : Int) ≤ s)
    (x y : K) (u : valuationUnitSubgroup K)
    (hvalue : (QuadraticSpace.binaryModel a c).quadratic ![x, y] =
      ((u : Kˣ) : K))
    (hdefect : (m : ℕ∞) ≤ quadraticDefect K (u : Kˣ)) :
    x ∈ IntegerRing K ∧ y ∈ IntegerRing K := by
  have hxNe : x ≠ 0 := by
    intro hxZero
    by_cases hyZero : y = 0
    · have hzeroValue : (0 : K) = ((u : Kˣ) : K) := by
        rw [QuadraticSpace.binaryModel_quadratic_apply] at hvalue
        simpa [hxZero, hyZero] using hvalue
      exact Units.ne_zero (u : Kˣ) hzeroValue.symm
    · let yu : Kˣ := Units.mk0 y hyZero
      have hyOrder : ord K y = (ordUnit K yu : WithTop Int) := by
        simpa [yu] using (coe_ordUnit K yu).symm
      have htermValue : (c ^ 2 + (a : K)) * y ^ 2 =
          ((u : Kˣ) : K) := by
        rw [QuadraticSpace.binaryModel_quadratic_apply] at hvalue
        simpa [hxZero] using hvalue
      have hqOrder := congrArg (ord K) htermValue
      rw [ord_mul, hdiag, ord_pow, hyOrder, u.property] at hqOrder
      have hzeroInt : (m : Int) + 2 * ordUnit K yu = 0 := by
        exact_mod_cast hqOrder
      rcases hmOdd with ⟨k, hk⟩
      omega
  by_cases hyZero : y = 0
  · subst y
    have hxValue : x ^ 2 = ((u : Kˣ) : K) := by
      rw [QuadraticSpace.binaryModel_quadratic_apply] at hvalue
      simpa using hvalue
    have hqOrder := congrArg (ord K) hxValue
    rw [u.property] at hqOrder
    let xu : Kˣ := Units.mk0 x hxNe
    have hxOrder : ord K x = (ordUnit K xu : WithTop Int) := by
      simpa [xu] using (coe_ordUnit K xu).symm
    rw [ord_pow, hxOrder] at hqOrder
    have hxUnitOrder : ordUnit K xu = 0 := by
      have htwice : 2 * ordUnit K xu = 0 := by exact_mod_cast hqOrder
      omega
    constructor
    · apply (mem_integerRing_iff K).2
      rw [Dyadic.IsIntegral, hxOrder, hxUnitOrder]
      simp
    · exact (IntegerRing K).zero_mem
  · let xu : Kˣ := Units.mk0 x hxNe
    let yu : Kˣ := Units.mk0 y hyZero
    let X : Int := ordUnit K xu
    let Y : Int := ordUnit K yu
    have hxOrder : ord K x = (X : WithTop Int) := by
      simpa [X, xu] using (coe_ordUnit K xu).symm
    have hyOrder : ord K y = (Y : WithTop Int) := by
      simpa [Y, yu] using (coe_ordUnit K yu).symm
    let A : K := x ^ 2
    let B : K := ((2 : K) * c) * (x * y)
    let C : K := (c ^ 2 + (a : K)) * y ^ 2
    have hAOrder : ord K A = ((2 * X : Int) : WithTop Int) := by
      dsimp [A]
      rw [ord_pow, hxOrder]
      norm_cast
    have hBOrder : ord K B = ((s + X + Y : Int) : WithTop Int) := by
      dsimp [B]
      calc
        ord K (((2 : K) * c) * (x * y)) =
            ord K ((2 : K) * c) + ord K (x * y) := ord_mul K _ _
        _ = (s : WithTop Int) + (ord K x + ord K y) := by
          rw [hcross, ord_mul]
        _ = ((s + X + Y : Int) : WithTop Int) := by
          rw [hxOrder, hyOrder]
          norm_cast
          ring
    have hCOrder : ord K C =
        (((m : Int) + 2 * Y : Int) : WithTop Int) := by
      dsimp [C]
      rw [ord_mul, hdiag, ord_pow, hyOrder]
      norm_cast
    have hACNe : ord K A ≠ ord K C := by
      rw [hAOrder, hCOrder]
      intro heq
      have heqInt : 2 * X = (m : Int) + 2 * Y := by
        exact_mod_cast heq
      rcases hmOdd with ⟨k, hk⟩
      omega
    have hBMin : min (ord K A) (ord K C) < ord K B := by
      rw [hAOrder, hBOrder, hCOrder]
      have hneInt : 2 * X ≠ (m : Int) + 2 * Y := by
        intro heq
        rcases hmOdd with ⟨k, hk⟩
        omega
      have hminInt : min (2 * X) ((m : Int) + 2 * Y) < s + X + Y := by
        rcases lt_or_gt_of_ne hneInt with hlt | hgt
        · rw [min_eq_left hlt.le]
          omega
        · rw [min_eq_right hgt.le]
          omega
      exact_mod_cast hminInt
    have hsumOrder := scratch_ord_add_add_eq_min_of_middle_gt
      A B C hACNe hBMin
    have hsumValue : A + B + C = ((u : Kˣ) : K) := by
      rw [← hvalue, QuadraticSpace.binaryModel_quadratic_apply]
      rfl
    rw [hsumValue, u.property, hAOrder, hCOrder] at hsumOrder
    have hminInt : min (2 * X) ((m : Int) + 2 * Y) = 0 := by
      exact_mod_cast hsumOrder.symm
    have hXZero : X = 0 := by
      by_cases hle : 2 * X ≤ (m : Int) + 2 * Y
      · rw [min_eq_left hle] at hminInt
        omega
      · rw [min_eq_right (le_of_not_ge hle)] at hminInt
        rcases hmOdd with ⟨k, hk⟩
        omega
    have hxIntegral : x ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      rw [Dyadic.IsIntegral, hxOrder, hXZero]
      norm_num
    refine ⟨hxIntegral, ?_⟩
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, hyOrder]
    by_contra hYNotNonneg
    have hYNeg : Y < 0 := by
      exact lt_of_not_ge (by exact_mod_cast hYNotNonneg)
    have hC_lt_B : ord K C < ord K B := by
      rw [hCOrder, hBOrder, hXZero]
      norm_cast
      omega
    have hBCOrder : ord K (B + C) = ord K C :=
      (ord K).map_add_eq_of_lt_right hC_lt_B
    let E : K := B + C
    have hEOrder : ord K E =
        (((m : Int) + 2 * Y : Int) : WithTop Int) := by
      simpa [E, hCOrder] using hBCOrder
    have hAZero : ord K A = 0 := by rw [hAOrder, hXZero]; norm_num
    have hAEValue : A + E = ((u : Kˣ) : K) := by
      dsimp [E]
      rw [← hsumValue]
      ring
    have hrNonneg : 0 ≤ (m : Int) + 2 * Y := by
      by_contra hrNot
      have hrNeg : (m : Int) + 2 * Y < 0 := lt_of_not_ge hrNot
      have hEA : ord K E < ord K A := by
        rw [hEOrder, hAZero]
        exact_mod_cast hrNeg
      have horder := (ord K).map_add_eq_of_lt_right hEA
      rw [hAEValue, u.property, hEOrder] at horder
      have : (0 : Int) = (m : Int) + 2 * Y := by exact_mod_cast horder
      omega
    have hrOdd : Odd ((m : Int) + 2 * Y) := by
      rcases hmOdd with ⟨k, hk⟩
      refine ⟨(k : Int) + Y, ?_⟩
      omega
    have hrPos : 0 < (m : Int) + 2 * Y := by
      have hrNe : (m : Int) + 2 * Y ≠ 0 := by
        intro hrZero
        rcases hrOdd with ⟨k, hk⟩
        omega
      omega
    have hrLtM : (m : Int) + 2 * Y < m := by omega
    let r : Nat := Int.toNat ((m : Int) + 2 * Y)
    have hrCast : (r : Int) = (m : Int) + 2 * Y := by
      dsimp [r]
      rw [Int.toNat_of_nonneg hrNonneg]
    have hrNatPos : 0 < r := by exact_mod_cast (hrCast.symm ▸ hrPos)
    have hrNatOdd : Odd r := by
      have habs : Int.natAbs ((m : Int) + 2 * Y) = r := by
        dsimp [r]
        apply Int.ofNat_injective
        exact (Int.natAbs_of_nonneg hrNonneg).trans
          (Int.toNat_of_nonneg hrNonneg).symm
      rw [← habs]
      exact hrOdd.natAbs
    have hrNatLtTwoE : r < 2 * ramificationIndex K := by
      exact_mod_cast (show (r : Int) < 2 * (ramificationIndex K : Int) by
        rw [hrCast]
        have hmLt : (m : Int) < 2 * (ramificationIndex K : Int) := by
          exact_mod_cast hmLtTwoE
        omega)
    let v : Kˣ := (u : Kˣ) / xu ^ 2
    let error : K := E / x ^ 2
    have hvField : (v : K) = 1 + error := by
      have hAEValue' : x ^ 2 + E = ((u : Kˣ) : K) := by
        simpa [A] using hAEValue
      dsimp [v, error]
      simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
        Units.val_mk0]
      rw [← hAEValue']
      have hxuVal : (xu : K) = x := rfl
      rw [hxuVal]
      field_simp [hxNe]
    have herrorOrder : ord K error = ((r : Int) : WithTop Int) := by
      dsimp [error]
      rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv, hEOrder,
        ord_pow, hxOrder, hXZero]
      norm_num
      have hcast : (((m : Int) + 2 * Y : Int) : WithTop Int) =
          ((r : Int) : WithTop Int) :=
        congrArg (fun z : Int => (z : WithTop Int)) hrCast.symm
      convert hcast using 1 <;> norm_cast
    have hvDefect : quadraticDefect K v = (r : ℕ∞) :=
      quadraticDefect_eq_of_principal_exact_odd v error r hvField
        herrorOrder hrNatPos hrNatOdd hrNatLtTwoE
    have hfactor : v * xu ^ 2 = (u : Kˣ) := by
      dsimp [v]
      simp
    have hdefectEq : quadraticDefect K (u : Kˣ) = quadraticDefect K v := by
      rw [← hfactor, quadraticDefect_mul_square]
    rw [hdefectEq, hvDefect] at hdefect
    have hmr : m ≤ r := by exact_mod_cast hdefect
    have hrm : r < m := by
      have hrmInt : (r : Int) < (m : Int) := by
        rw [hrCast]
        exact hrLtM
      exact_mod_cast hrmInt
    omega

theorem scratch_odd_diagonal_coordinates_integral
    [QuadraticDefectLaws K]
    (a : Kˣ) (R : Nat)
    (haOrder : ordUnit K a = (R : Int))
    (hROdd : Odd R) (hRLtTwoE : R < 2 * ramificationIndex K)
    (x y : K) (u : valuationUnitSubgroup K)
    (hvalue : x ^ 2 + (a : K) * y ^ 2 = ((u : Kˣ) : K))
    (hdefect : (R : ℕ∞) ≤ quadraticDefect K (u : Kˣ)) :
    x ∈ IntegerRing K ∧ y ∈ IntegerRing K := by
  have hxNe : x ≠ 0 := by
    intro hxZero
    by_cases hyZero : y = 0
    · rw [hxZero, hyZero] at hvalue
      have hzero : (0 : K) = ((u : Kˣ) : K) := by simpa using hvalue
      exact Units.ne_zero (u : Kˣ) hzero.symm
    · let yu : Kˣ := Units.mk0 y hyZero
      have hyOrder : ord K y = (ordUnit K yu : WithTop Int) := by
        simpa [yu] using (coe_ordUnit K yu).symm
      have htermValue : (a : K) * y ^ 2 = ((u : Kˣ) : K) := by
        simpa [hxZero] using hvalue
      have horder := congrArg (ord K) htermValue
      rw [ord_mul, ← coe_ordUnit, haOrder, ord_pow, hyOrder,
        u.property] at horder
      have hzero : (R : Int) + 2 * ordUnit K yu = 0 := by
        exact_mod_cast horder
      rcases hROdd with ⟨k, hk⟩
      omega
  by_cases hyZero : y = 0
  · subst y
    have hxValue : x ^ 2 = ((u : Kˣ) : K) := by simpa using hvalue
    have horder := congrArg (ord K) hxValue
    let xu : Kˣ := Units.mk0 x hxNe
    have hxOrder : ord K x = (ordUnit K xu : WithTop Int) := by
      simpa [xu] using (coe_ordUnit K xu).symm
    rw [ord_pow, hxOrder, u.property] at horder
    have hxZeroOrder : ordUnit K xu = 0 := by
      have htwice : 2 * ordUnit K xu = 0 := by exact_mod_cast horder
      omega
    constructor
    · apply (mem_integerRing_iff K).2
      rw [Dyadic.IsIntegral, hxOrder, hxZeroOrder]
      simp
    · exact (IntegerRing K).zero_mem
  · let xu : Kˣ := Units.mk0 x hxNe
    let yu : Kˣ := Units.mk0 y hyZero
    let X : Int := ordUnit K xu
    let Y : Int := ordUnit K yu
    have hxOrder : ord K x = (X : WithTop Int) := by
      simpa [X, xu] using (coe_ordUnit K xu).symm
    have hyOrder : ord K y = (Y : WithTop Int) := by
      simpa [Y, yu] using (coe_ordUnit K yu).symm
    let A : K := x ^ 2
    let C : K := (a : K) * y ^ 2
    have hAOrder : ord K A = ((2 * X : Int) : WithTop Int) := by
      dsimp [A]
      rw [ord_pow, hxOrder]
      norm_cast
    have hCOrder : ord K C =
        (((R : Int) + 2 * Y : Int) : WithTop Int) := by
      dsimp [C]
      rw [ord_mul, ← coe_ordUnit, haOrder, ord_pow, hyOrder]
      norm_cast
    have hACNe : ord K A ≠ ord K C := by
      rw [hAOrder, hCOrder]
      intro heq
      have heqInt : 2 * X = (R : Int) + 2 * Y := by exact_mod_cast heq
      rcases hROdd with ⟨k, hk⟩
      omega
    have hsumOrder : ord K (A + C) = min (ord K A) (ord K C) := by
      rcases lt_or_gt_of_ne hACNe with hlt | hgt
      · rw [(ord K).map_add_eq_of_lt_left hlt, min_eq_left hlt.le]
      · rw [(ord K).map_add_eq_of_lt_right hgt, min_eq_right hgt.le]
    have hsumValue : A + C = ((u : Kˣ) : K) := by
      simpa [A, C] using hvalue
    rw [hsumValue, u.property, hAOrder, hCOrder] at hsumOrder
    have hminInt : min (2 * X) ((R : Int) + 2 * Y) = 0 := by
      exact_mod_cast hsumOrder.symm
    have hXZero : X = 0 := by
      by_cases hle : 2 * X ≤ (R : Int) + 2 * Y
      · rw [min_eq_left hle] at hminInt
        omega
      · rw [min_eq_right (le_of_not_ge hle)] at hminInt
        rcases hROdd with ⟨k, hk⟩
        omega
    have hrNonneg : 0 ≤ (R : Int) + 2 * Y := by
      by_contra hnot
      have hneg : (R : Int) + 2 * Y < 0 := lt_of_not_ge hnot
      rw [hXZero] at hminInt
      simp only [mul_zero, min_eq_right (by omega)] at hminInt
      omega
    have hxIntegral : x ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      rw [Dyadic.IsIntegral, hxOrder, hXZero]
      simp
    refine ⟨hxIntegral, ?_⟩
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, hyOrder]
    by_contra hYNotNonneg
    have hYNeg : Y < 0 :=
      lt_of_not_ge (by exact_mod_cast hYNotNonneg)
    have hrOdd : Odd ((R : Int) + 2 * Y) := by
      rcases hROdd with ⟨k, hk⟩
      refine ⟨(k : Int) + Y, ?_⟩
      omega
    have hrPos : 0 < (R : Int) + 2 * Y := by
      have hrNe : (R : Int) + 2 * Y ≠ 0 := by
        intro hrZero
        rcases hrOdd with ⟨k, hk⟩
        omega
      omega
    have hrLtR : (R : Int) + 2 * Y < R := by omega
    let r : Nat := Int.toNat ((R : Int) + 2 * Y)
    have hrCast : (r : Int) = (R : Int) + 2 * Y := by
      dsimp [r]
      rw [Int.toNat_of_nonneg hrNonneg]
    have hrNatPos : 0 < r := by exact_mod_cast (hrCast.symm ▸ hrPos)
    have hrNatOdd : Odd r := by
      have habs : Int.natAbs ((R : Int) + 2 * Y) = r := by
        dsimp [r]
        apply Int.ofNat_injective
        exact (Int.natAbs_of_nonneg hrNonneg).trans
          (Int.toNat_of_nonneg hrNonneg).symm
      rw [← habs]
      exact hrOdd.natAbs
    have hrNatLtTwoE : r < 2 * ramificationIndex K := by
      have hrLt : r < R := by
        have : (r : Int) < (R : Int) := by rw [hrCast]; exact hrLtR
        exact_mod_cast this
      exact hrLt.trans hRLtTwoE
    let v : Kˣ := (u : Kˣ) / xu ^ 2
    let error : K := C / x ^ 2
    have hvField : (v : K) = 1 + error := by
      have hsumValue' : x ^ 2 + C = ((u : Kˣ) : K) := by
        simpa [A] using hsumValue
      dsimp [v, error]
      simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
      rw [← hsumValue']
      have hxuVal : (xu : K) = x := rfl
      rw [hxuVal]
      field_simp [hxNe]
    have herrorOrder : ord K error = ((r : Int) : WithTop Int) := by
      dsimp [error]
      rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv, hCOrder,
        ord_pow, hxOrder, hXZero]
      norm_num
      have hcast : (((R : Int) + 2 * Y : Int) : WithTop Int) =
          ((r : Int) : WithTop Int) :=
        congrArg (fun z : Int => (z : WithTop Int)) hrCast.symm
      convert hcast using 1 <;> norm_cast
    have hvDefect : quadraticDefect K v = (r : ℕ∞) :=
      quadraticDefect_eq_of_principal_exact_odd v error r hvField
        herrorOrder hrNatPos hrNatOdd hrNatLtTwoE
    have hfactor : v * xu ^ 2 = (u : Kˣ) := by
      dsimp [v]
      simp
    have hdefectEq : quadraticDefect K (u : Kˣ) = quadraticDefect K v := by
      rw [← hfactor, quadraticDefect_mul_square]
    rw [hdefectEq, hvDefect] at hdefect
    have hRr : R ≤ r := by exact_mod_cast hdefect
    have hrR : r < R := by
      have : (r : Int) < (R : Int) := by rw [hrCast]; exact hrLtR
      exact_mod_cast this
    omega

theorem scratch_discriminantEndpoint_coordinates_integral
    [laws : DyadicDiscriminantClassLaws K]
    (x y : K) (u : valuationUnitSubgroup K)
    (hvalue :
      (QuadraticSpace.binaryModel
        (negativeQuarterUnit K * laws.discriminantUnit)
        (standardEndpointShear (K := K))).quadratic ![x, y] =
          ((u : Kˣ) : K)) :
    x ∈ IntegerRing K ∧ y ∈ IntegerRing K := by
  have hpoly : x ^ 2 + x * y + laws.rho * y ^ 2 =
      ((u : Kˣ) : K) := by
    rw [← hvalue]
    exact (discriminantEndpoint_quadratic_apply (K := K) ![x, y]).symm
  by_cases hxZero : x = 0
  · by_cases hyZero : y = 0
    · have hzero : (0 : K) = ((u : Kˣ) : K) := by
        simpa [hxZero, hyZero] using hpoly
      exact (Units.ne_zero (u : Kˣ) hzero.symm).elim
    · let yu : Kˣ := Units.mk0 y hyZero
      have hyOrder : ord K y = (ordUnit K yu : WithTop Int) := by
        simpa [yu] using (coe_ordUnit K yu).symm
      have hterm : laws.rho * y ^ 2 = ((u : Kˣ) : K) := by
        simpa [hxZero] using hpoly
      have horder := congrArg (ord K) hterm
      rw [ord_mul, laws.rho_isValuationUnit, ord_pow, hyOrder,
        u.property] at horder
      have hyZeroOrder : ordUnit K yu = 0 := by
        have htwice : (0 : Int) + 2 • ordUnit K yu = 0 := by
          exact_mod_cast horder
        simp only [zero_add, two_nsmul] at htwice
        omega
      constructor
      · rw [hxZero]
        exact (IntegerRing K).zero_mem
      · apply (mem_integerRing_iff K).2
        rw [Dyadic.IsIntegral, hyOrder, hyZeroOrder]
        simp
  · by_cases hyZero : y = 0
    · let xu : Kˣ := Units.mk0 x hxZero
      have hxOrder : ord K x = (ordUnit K xu : WithTop Int) := by
        simpa [xu] using (coe_ordUnit K xu).symm
      have hterm : x ^ 2 = ((u : Kˣ) : K) := by
        simpa [hyZero] using hpoly
      have horder := congrArg (ord K) hterm
      rw [ord_pow, hxOrder, u.property] at horder
      have hxZeroOrder : ordUnit K xu = 0 := by
        have htwice : 2 * ordUnit K xu = 0 := by exact_mod_cast horder
        omega
      constructor
      · apply (mem_integerRing_iff K).2
        rw [Dyadic.IsIntegral, hxOrder, hxZeroOrder]
        simp
      · rw [hyZero]
        exact (IntegerRing K).zero_mem
    · let xu : Kˣ := Units.mk0 x hxZero
      let yu : Kˣ := Units.mk0 y hyZero
      let X : Int := ordUnit K xu
      let Y : Int := ordUnit K yu
      let k : Int := min X Y
      let pU : Kˣ := uniformizerPowerUnit K (-k)
      let xp : K := (pU : K) * x
      let yp : K := (pU : K) * y
      let z : Fin 2 → K := ![xp, yp]
      have hxOrder : ord K x = (X : WithTop Int) := by
        simpa [X, xu] using (coe_ordUnit K xu).symm
      have hyOrder : ord K y = (Y : WithTop Int) := by
        simpa [Y, yu] using (coe_ordUnit K yu).symm
      have hpOrder : ord K (pU : K) = ((-k : Int) : WithTop Int) := by
        rw [← coe_ordUnit, ordUnit_uniformizerPowerUnit]
      have hxpOrder : ord K xp = ((X - k : Int) : WithTop Int) := by
        dsimp [xp]
        rw [ord_mul, hpOrder, hxOrder]
        norm_cast
        omega
      have hypOrder : ord K yp = ((Y - k : Int) : WithTop Int) := by
        dsimp [yp]
        rw [ord_mul, hpOrder, hyOrder]
        norm_cast
        omega
      have hxpk : 0 ≤ X - k := by
        dsimp [k]
        exact sub_nonneg.mpr (min_le_left X Y)
      have hypk : 0 ≤ Y - k := by
        dsimp [k]
        exact sub_nonneg.mpr (min_le_right X Y)
      have hzMem : z ∈ binaryModelLattice (K := K) := by
        rw [scratch_mem_binaryModelLattice_iff]
        intro i
        fin_cases i
        · apply (mem_integerRing_iff K).2
          rw [Dyadic.IsIntegral]
          simpa [z, hxpOrder] using
            (show (0 : WithTop Int) ≤ ((X - k : Int) : WithTop Int) by
              exact_mod_cast hxpk)
        · apply (mem_integerRing_iff K).2
          rw [Dyadic.IsIntegral]
          simpa [z, hypOrder] using
            (show (0 : WithTop Int) ≤ ((Y - k : Int) : WithTop Int) by
              exact_mod_cast hypk)
      have hzPrimitive : z ∉ Lattice.rescale (uniformizerUnit K)
          (binaryModelLattice (K := K)) := by
        intro hzScaled
        rcases (Lattice.mem_rescale_iff (uniformizerUnit K)
          (binaryModelLattice (K := K)) z).1 hzScaled with
          ⟨w, hw, hwz⟩
        have hwCoords := (scratch_mem_binaryModelLattice_iff w).1 hw
        have hcoordLower (i : Fin 2) :
            (1 : WithTop Int) ≤ ord K (z i) := by
          have hi := congrArg (fun v : Fin 2 → K => v i) hwz
          have hwi : (0 : WithTop Int) ≤ ord K (w i) :=
            (mem_integerRing_iff K).1 (hwCoords i)
          rw [← hi, Pi.smul_apply, smul_eq_mul, ord_mul,
            coe_uniformizerUnit, ord_uniformizer]
          simpa [add_comm] using add_le_add_left hwi (1 : WithTop Int)
        by_cases hXY : X ≤ Y
        · have hkX : k = X := by simp [k, min_eq_left hXY]
          have hzeroOrder : ord K (z 0) = 0 := by
            simpa [z, hxpOrder, hkX]
          have hzeroImpossible := hcoordLower 0
          rw [hzeroOrder] at hzeroImpossible
          exact (not_le_of_gt (by norm_num : (0 : WithTop Int) < 1))
            hzeroImpossible
        · have hkY : k = Y := by simp [k, min_eq_right (le_of_not_ge hXY)]
          have hzeroOrder : ord K (z 1) = 0 := by
            simpa [z, hypOrder, hkY]
          have hone := hcoordLower 1
          rw [hzeroOrder] at hone
          exact (not_le_of_gt (by norm_num : (0 : WithTop Int) < 1)) hone
      have hzUnit := discriminantEndpoint_quadratic_isValuationUnit
        z hzMem hzPrimitive
      have hzValue :
          (QuadraticSpace.binaryModel
            (negativeQuarterUnit K * laws.discriminantUnit)
            (standardEndpointShear (K := K))).quadratic z =
          (pU : K) ^ 2 * ((u : Kˣ) : K) := by
        dsimp [z, xp, yp]
        have hsmul : ![(pU : K) * x, (pU : K) * y] =
            (pU : K) • ![x, y] := by
          funext i
          fin_cases i <;> rfl
        rw [hsmul,
          (QuadraticSpace.binaryModel
            (negativeQuarterUnit K * laws.discriminantUnit)
            (standardEndpointShear (K := K))).quadratic_smul,
          hvalue]
      have hkZero : k = 0 := by
        have horder := congrArg (ord K) hzValue
        rw [hzUnit, ord_mul, ord_pow, hpOrder, u.property] at horder
        have htwice : (0 : Int) = 2 • (-k) + 0 := by
          exact_mod_cast horder
        simp only [add_zero, two_nsmul] at htwice
        omega
      constructor
      · apply (mem_integerRing_iff K).2
        rw [Dyadic.IsIntegral, hxOrder]
        exact_mod_cast (show 0 ≤ X by
          have := min_le_left X Y
          simpa [k, hkZero] using this)
      · apply (mem_integerRing_iff K).2
        rw [Dyadic.IsIntegral, hyOrder]
        exact_mod_cast (show 0 ≤ Y by
          have := min_le_right X Y
          simpa [k, hkZero] using this)

theorem scratch_quadraticDefect_ge_of_mem_integralSquareResidueSet
    [QuadraticDefectLaws K]
    (u : valuationUnitSubgroup K) (m : Nat)
    (hmem : ((u : Kˣ) : K) ∈
      Lattice.integralSquareResidueSet
        (Lattice.powerIdeal (K := K) (m : Int))) :
    (m : ℕ∞) ≤ quadraticDefect K (u : Kˣ) := by
  rcases hmem with ⟨x, hx⟩
  have herror : ((m : Int) : WithTop Int) ≤
      ord K (((u : Kˣ) : K) - (x : K) ^ 2) :=
    (Lattice.mem_powerIdeal_iff (K := K) (m : Int)
      (((u : Kˣ) : K) - (x : K) ^ 2)).1 hx
  apply natCast_le_quadraticDefect K
  refine ⟨(x : K), ?_⟩
  have heq :
      1 - (x : K) ^ 2 / ((u : Kˣ) : K) =
        (((u : Kˣ) : K) - (x : K) ^ 2) / ((u : Kˣ) : K) := by
    field_simp [Units.ne_zero (u : Kˣ)]
  rw [heq, div_eq_mul_inv, ord_mul, AddValuation.map_inv, u.property]
  simpa using herror

theorem scratch_normGeneratorRatio_defect_ge_of_parameterOrder_pos
    [QuadraticDefectLaws K]
    (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K)
    (z : Fin 2 → K)
    (hz : Lattice.IsNormGenerator (QuadraticSpace.binaryModel a c)
      (binaryModelLattice (K := K)) z)
    (hR : 0 < ordUnit K a) :
    ((Int.toNat (ordUnit K a) : Nat) : ℕ∞) ≤
      quadraticDefect K
        ((binaryExactModelBONG a c htwo hdiag).normGeneratorValueRatioUnit z hz) := by
  let b₀ := binaryExactModelBONG a c htwo hdiag
  let u₀ : valuationUnitSubgroup K :=
    b₀.normGeneratorValueRatioValuationUnit z hz
  have hgapEq : b₀.binaryOrderGap = ordUnit K a := by
    rw [← b₀.binaryParameterOrder_eq_orderGap]
    simp [b₀, binaryParameterOrder, ordUnit]
  have hgapPos : 0 < b₀.binaryOrderGap := by
    rw [hgapEq]
    omega
  have hzValueSet :
      (QuadraticSpace.binaryModel a c).quadratic z ∈
        Lattice.normGeneratorValueSet (QuadraticSpace.binaryModel a c)
          (binaryModelLattice (K := K)) := ⟨z, hz, rfl⟩
  have hresidue :=
    b₀.normGeneratorValueSet_subset_of_normalized_binaryOrderGap_pos
      (by simp [b₀]) hgapPos hzValueSet
  have hvalueOne : b₀.value 1 = (a : K) := by simp [b₀]
  rw [hvalueOne, Lattice.principalIdeal_eq_powerIdeal] at hresidue
  have hratioField :
      ((u₀ : valuationUnitSubgroup K) : Kˣ) =
        b₀.normGeneratorValueRatioUnit z hz := rfl
  have hratioValue :
      (((u₀ : valuationUnitSubgroup K) : Kˣ) : K) =
        (QuadraticSpace.binaryModel a c).quadratic z := by
    simp only [hratioField, normGeneratorValueRatioUnit,
      Units.val_div_eq_div_val, Units.val_mk0, coe_valueUnit]
    simp [b₀]
  let R : Nat := Int.toNat (ordUnit K a)
  have hRnonneg : 0 ≤ ordUnit K a := by omega
  have hRcast : (R : Int) = ordUnit K a := by
    simp [R, Int.toNat_of_nonneg hRnonneg]
  have hresidue' : (((u₀ : valuationUnitSubgroup K) : Kˣ) : K) ∈
      Lattice.integralSquareResidueSet
        (Lattice.powerIdeal (K := K) (R : Int)) := by
    rw [hratioValue, hRcast]
    exact hresidue
  have hdefect : (R : ℕ∞) ≤
      quadraticDefect K ((u₀ : valuationUnitSubgroup K) : Kˣ) :=
    scratch_quadraticDefect_ge_of_mem_integralSquareResidueSet u₀ R hresidue'
  simpa [R, u₀, b₀, normGeneratorValueRatioValuationUnit] using hdefect

theorem scratch_isSquare_normGeneratorRatio_of_twoE_lt_parameterOrder
    [QuadraticDefectLaws K]
    (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K)
    (z : Fin 2 → K)
    (hz : Lattice.IsNormGenerator (QuadraticSpace.binaryModel a c)
      (binaryModelLattice (K := K)) z)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    IsSquare
      ((binaryExactModelBONG a c htwo hdiag).normGeneratorValueRatioUnit z hz) := by
  let u₀ : Kˣ :=
    (binaryExactModelBONG a c htwo hdiag).normGeneratorValueRatioUnit z hz
  have hRpos : 0 < ordUnit K a := by
    have he : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  have hdefect :=
    scratch_normGeneratorRatio_defect_ge_of_parameterOrder_pos
      a c htwo hdiag z hz hRpos
  let R : Nat := Int.toNat (ordUnit K a)
  have hRcast : (R : Int) = ordUnit K a := by
    simp [R, Int.toNat_of_nonneg hRpos.le]
  have hdefectGt : ((2 * ramificationIndex K : Nat) : ℕ∞) <
      quadraticDefect K u₀ := by
    exact (show ((2 * ramificationIndex K : Nat) : ℕ∞) < (R : ℕ∞) by
      exact_mod_cast (show (2 * ramificationIndex K : Nat) < R by
        exact_mod_cast (hRcast.symm ▸ hR))).trans_le hdefect
  change IsSquare u₀
  exact isSquare_of_quadraticDefect_gt_two_mul_e K _ hdefectGt

theorem scratch_normGeneratorRatio_defect_ge_of_even_parameter
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K)
    (z : Fin 2 → K)
    (hz : Lattice.IsNormGenerator (QuadraticSpace.binaryModel a c)
      (binaryModelLattice (K := K)) z)
    (hEven : Even (ordUnit K a)) (m : Nat)
    (hcrossBound : (m : Int) ≤
      (ramificationIndex K : Int) + ordUnit K a / 2)
    (hdiagBound : beliParameterDefect K a ≠ ⊤ →
      (m : Int) ≤ ordUnit K a + (beliParameterDefectNat K a : Int)) :
    (m : ℕ∞) ≤
      quadraticDefect K
        ((binaryExactModelBONG a c htwo hdiag).normGeneratorValueRatioUnit z hz) := by
  rcases scratch_exists_defectAdaptedShear a ⟨c, htwo, hdiag⟩ hEven with
    ⟨c', htwo', hdiag', hcross', hdiagonal'⟩
  rcases scratch_exists_normGenerator_of_shear a c c'
      ⟨htwo, hdiag⟩ ⟨htwo', hdiag'⟩ z hz with
    ⟨z', hz', hz'Value⟩
  let b₀ := binaryExactModelBONG a c htwo hdiag
  let u₀ : valuationUnitSubgroup K :=
    b₀.normGeneratorValueRatioValuationUnit z hz
  have hzValue : (QuadraticSpace.binaryModel a c).quadratic z =
      (((u₀ : valuationUnitSubgroup K) : Kˣ) : K) := by
    simp [u₀, b₀, normGeneratorValueRatioValuationUnit,
      normGeneratorValueRatioUnit]
  have hz'Value' : (QuadraticSpace.binaryModel a c').quadratic z' =
      (((u₀ : valuationUnitSubgroup K) : Kˣ) : K) := by
    rw [hz'Value, hzValue]
  have hcrossLower : ((m : Int) : WithTop Int) ≤
      ord K ((2 : K) * c') := by
    rw [hcross']
    exact_mod_cast hcrossBound
  have hdiagLower : ((m : Int) : WithTop Int) ≤
      ord K (c' ^ 2 + (a : K)) := by
    rcases hdiagonal' with htop | hfinite
    · rw [htop.2, ord_zero]
      exact le_top
    · rw [hfinite.2]
      exact_mod_cast hdiagBound hfinite.1
  have hdefect := scratch_quadraticDefect_ge_of_binaryModel_value
    a c' z' hz'.mem u₀ hz'Value' m hcrossLower hdiagLower
  simpa [u₀, b₀, normGeneratorValueRatioValuationUnit] using hdefect

theorem scratch_beliDefectCutoff_cast
    (a : Kˣ)
    (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a) :
    (beliDefectCutoff K a : Int) =
      2 * (ramificationIndex K : Int) - ordUnit K a := by
  unfold beliDefectCutoff
  rw [Int.toNat_of_nonneg]
  omega

theorem scratch_beliLowDefectExponent_cast
    (a : Kˣ) (ha : IsBinaryParameterAdmissible a)
    (hfinite : beliParameterDefect K a ≠ ⊤) :
    (beliLowDefectExponent K a : Int) =
      ordUnit K a + (beliParameterDefectNat K a : Int) := by
  unfold beliLowDefectExponent
  rw [Int.toNat_of_nonneg]
  exact beli2009_order_add_parameterDefect_nonneg (K := K) ha hfinite

theorem scratch_beliHighDefectExponent_cast
    (a : Kˣ) (ha : IsBinaryParameterAdmissible a)
    (hEven : Even (ordUnit K a)) :
    (beliHighDefectExponent K a : Int) =
      (ramificationIndex K : Int) + ordUnit K a / 2 := by
  unfold beliHighDefectExponent
  rw [Int.toNat_of_nonneg]
  rcases hEven with ⟨r, hr⟩
  have hlower := ha.ordUnit_ge_neg_two_mul_e
  omega

theorem scratch_beliLowExponent_le_highCoefficient
    (a : Kˣ) (ha : IsBinaryParameterAdmissible a)
    (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hd : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞))
    (hEven : Even (ordUnit K a)) :
    (beliLowDefectExponent K a : Int) ≤
      (ramificationIndex K : Int) + ordUnit K a / 2 := by
  have hfinite : beliParameterDefect K a ≠ ⊤ := by
    intro htop
    rw [htop] at hd
    simp at hd
  have hdefectEq : beliParameterDefect K a =
      (beliParameterDefectNat K a : ℕ∞) := by
    simpa [beliParameterDefectNat] using
      (ENat.coe_toNat hfinite).symm
  have hdNat : 2 * beliParameterDefectNat K a ≤
      beliDefectCutoff K a := by
    rw [hdefectEq] at hd
    exact_mod_cast hd
  have hlowCast := scratch_beliLowDefectExponent_cast a ha hfinite
  have hcutoffCast := scratch_beliDefectCutoff_cast a hR
  rcases hEven with ⟨r, hr⟩
  have hdInt : 2 * (beliParameterDefectNat K a : Int) ≤
      (beliDefectCutoff K a : Int) := by exact_mod_cast hdNat
  rw [hlowCast, hcutoffCast] at *
  omega

theorem scratch_beliHighExponent_le_lowCoefficient_of_finite
    (a : Kˣ) (ha : IsBinaryParameterAdmissible a)
    (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hd : ¬2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞))
    (hEven : Even (ordUnit K a))
    (hfinite : beliParameterDefect K a ≠ ⊤) :
    (beliHighDefectExponent K a : Int) ≤
      ordUnit K a + (beliParameterDefectNat K a : Int) := by
  have hdefectEq : beliParameterDefect K a =
      (beliParameterDefectNat K a : ℕ∞) := by
    simpa [beliParameterDefectNat] using
      (ENat.coe_toNat hfinite).symm
  have hdNat : beliDefectCutoff K a <
      2 * beliParameterDefectNat K a := by
    have hd' : (beliDefectCutoff K a : ℕ∞) <
        2 * beliParameterDefect K a := lt_of_not_ge hd
    rw [hdefectEq] at hd'
    exact_mod_cast hd'
  have hhighCast := scratch_beliHighDefectExponent_cast a ha hEven
  have hcutoffCast := scratch_beliDefectCutoff_cast a hR
  rcases hEven with ⟨r, hr⟩
  have hdInt : (beliDefectCutoff K a : Int) <
      2 * (beliParameterDefectNat K a : Int) := by exact_mod_cast hdNat
  rw [hhighCast, hcutoffCast] at *
  omega

theorem scratch_beliHighExponent_lt_lowCoefficient_of_finite
    (a : Kˣ) (ha : IsBinaryParameterAdmissible a)
    (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hd : ¬2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞))
    (hEven : Even (ordUnit K a))
    (hfinite : beliParameterDefect K a ≠ ⊤) :
    (beliHighDefectExponent K a : Int) <
      ordUnit K a + (beliParameterDefectNat K a : Int) := by
  have hdefectEq : beliParameterDefect K a =
      (beliParameterDefectNat K a : ℕ∞) := by
    simpa [beliParameterDefectNat] using
      (ENat.coe_toNat hfinite).symm
  have hdNat : beliDefectCutoff K a <
      2 * beliParameterDefectNat K a := by
    have hd' : (beliDefectCutoff K a : ℕ∞) <
        2 * beliParameterDefect K a := lt_of_not_ge hd
    rw [hdefectEq] at hd'
    exact_mod_cast hd'
  have hhighCast := scratch_beliHighDefectExponent_cast a ha hEven
  have hcutoffCast := scratch_beliDefectCutoff_cast a hR
  rcases hEven with ⟨r, hr⟩
  have hdInt : (beliDefectCutoff K a : Int) <
      2 * (beliParameterDefectNat K a : Int) := by exact_mod_cast hdNat
  rw [hhighCast, hcutoffCast] at *
  omega

theorem scratch_normGeneratorValueRatioClass_mem_beliNormGeneratorGroup
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    (b : BONG V q L 2) (y : V)
    (hy : Lattice.IsNormGenerator q L y) :
    b.normGeneratorValueRatioClass y hy ∈
      beliNormGeneratorGroup K b.binaryParameter := by
  let u : valuationUnitSubgroup K :=
    b.normGeneratorValueRatioValuationUnit y hy
  have hnormClass : b.normGeneratorValueRatioClass y hy ∈
      quadraticNormValuationClassSubgroup K (-b.binaryParameter) := by
    refine ⟨u, ?_, rfl⟩
    exact b.normGeneratorValueRatioUnit_isQuadraticNorm_binary y hy
  rcases scratch_exists_model_normGenerator_valueRatio_eq b y hy with
    ⟨z, hz, hratio⟩
  have ha := b.binaryParameter_isBinaryParameterAdmissible
  have hc := b.binaryModelCoefficient_isAdmissibleWitness
  by_cases hR : 2 * (ramificationIndex K : Int) <
      ordUnit K b.binaryParameter
  · rw [beliNormGeneratorGroup_of_two_e_lt K b.binaryParameter hR]
    change b.normGeneratorValueRatioClass y hy = 1
    have hsquareModel :=
      scratch_isSquare_normGeneratorRatio_of_twoE_lt_parameterOrder
        b.binaryParameter b.binaryModelCoefficient hc.1 hc.2 z hz hR
    rw [hratio] at hsquareModel
    apply valuationUnitClassToSquareClass_injective K
    change squareClass K (b.normGeneratorValueRatioUnit y hy) =
      squareClass K 1
    rcases hsquareModel with ⟨s, hs⟩
    rw [hs]
    simpa [pow_two] using squareClass_mul_square K (1 : Kˣ) s
  · by_cases hd : 2 * beliParameterDefect K b.binaryParameter ≤
        (beliDefectCutoff K b.binaryParameter : ℕ∞)
    · rw [beliNormGeneratorGroup_of_low_defect K b.binaryParameter hR hd]
      refine ⟨?_, hnormClass⟩
      rcases Int.even_or_odd (ordUnit K b.binaryParameter) with hEven | hOdd
      · have hfinite : beliParameterDefect K b.binaryParameter ≠ ⊤ := by
          intro htop
          rw [htop] at hd
          simp at hd
        have hcrossBound :=
          scratch_beliLowExponent_le_highCoefficient
            b.binaryParameter ha hR hd hEven
        have hlowCast := scratch_beliLowDefectExponent_cast
          b.binaryParameter ha hfinite
        have hdefectModel :=
          scratch_normGeneratorRatio_defect_ge_of_even_parameter
            b.binaryParameter b.binaryModelCoefficient hc.1 hc.2 z hz
            hEven (beliLowDefectExponent K b.binaryParameter)
            hcrossBound (fun _ => by omega)
        rw [hratio] at hdefectModel
        apply
          valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
        simpa [u, normGeneratorValueRatioValuationUnit] using hdefectModel
      · have hordNeg : ordUnit K (-b.binaryParameter) =
            ordUnit K b.binaryParameter := by
          apply WithTop.coe_injective
          rw [coe_ordUnit, coe_ordUnit]
          simpa only [Units.val_neg] using
            ord_neg K (b.binaryParameter : K)
        have hOddNeg : Odd (ordUnit K (-b.binaryParameter)) := by
          rwa [hordNeg]
        have hzero : beliParameterDefect K b.binaryParameter = 0 := by
          exact quadraticDefect_eq_zero_of_odd_ordUnit
            (K := K) (-b.binaryParameter) hOddNeg
        have hzeroNat : beliParameterDefectNat K b.binaryParameter = 0 := by
          simp [beliParameterDefectNat, hzero]
        have hlowEq : beliLowDefectExponent K b.binaryParameter =
            Int.toNat (ordUnit K b.binaryParameter) := by
          simp [beliLowDefectExponent, hzeroNat]
        by_cases hpos : 0 < ordUnit K b.binaryParameter
        · have hdefectModel :=
            scratch_normGeneratorRatio_defect_ge_of_parameterOrder_pos
              b.binaryParameter b.binaryModelCoefficient hc.1 hc.2 z hz hpos
          rw [hratio] at hdefectModel
          apply
            valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
          rw [hlowEq]
          simpa [u, normGeneratorValueRatioValuationUnit] using hdefectModel
        · have hlowZero : beliLowDefectExponent K b.binaryParameter = 0 := by
            rw [hlowEq]
            exact Int.toNat_eq_zero.mpr (le_of_not_gt hpos)
          rw [hlowZero]
          apply
            valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
          simp
    · rw [beliNormGeneratorGroup_of_high_defect K b.binaryParameter hR hd]
      have hEven := beli2009BinaryHighDefect_even_order
        (K := K) b.binaryParameter hd
      have hhighCast := scratch_beliHighDefectExponent_cast
        b.binaryParameter ha hEven
      have hdefectModel :=
        scratch_normGeneratorRatio_defect_ge_of_even_parameter
          b.binaryParameter b.binaryModelCoefficient hc.1 hc.2 z hz
          hEven (beliHighDefectExponent K b.binaryParameter)
          (by omega)
          (fun hfinite =>
            scratch_beliHighExponent_le_lowCoefficient_of_finite
              b.binaryParameter ha hR hd hEven hfinite)
      rw [hratio] at hdefectModel
      apply
        valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
      simpa [u, normGeneratorValueRatioValuationUnit] using hdefectModel

theorem scratch_exists_normGeneratorValueRatioUnit_eq_of_shear_value
    (b : BONG V q L 2) (c' : K)
    (htwo' : (2 : K) * c' ∈ IntegerRing K)
    (hdiag' : c' ^ 2 + (b.binaryParameter : K) ∈ IntegerRing K)
    (z' : Fin 2 → K)
    (hz' : Lattice.IsNormGenerator
      (QuadraticSpace.binaryModel b.binaryParameter c')
      (binaryModelLattice (K := K)) z')
    (u : valuationUnitSubgroup K)
    (hvalue : (QuadraticSpace.binaryModel b.binaryParameter c').quadratic z' =
      ((u : Kˣ) : K)) :
    ∃ (y : V) (hy : Lattice.IsNormGenerator q L y),
      b.normGeneratorValueRatioUnit y hy = (u : Kˣ) := by
  have hc := b.binaryModelCoefficient_isAdmissibleWitness
  rcases scratch_exists_normGenerator_of_shear
      b.binaryParameter c' b.binaryModelCoefficient
      ⟨htwo', hdiag'⟩ hc z' hz' with ⟨z, hz, hzValue⟩
  have hzValue' :
      (QuadraticSpace.binaryModel b.binaryParameter
        b.binaryModelCoefficient).quadratic z = ((u : Kˣ) : K) := by
    rw [hzValue, hvalue]
  rcases scratch_exists_normGenerator_valueRatio_eq_model b z hz with
    ⟨y, hy, hratio⟩
  refine ⟨y, hy, hratio.trans ?_⟩
  apply Units.ext
  simp only [normGeneratorValueRatioUnit, Units.val_div_eq_div_val,
    Units.val_mk0, coe_valueUnit]
  rw [binaryExactModelBONG_value_zero, div_one, hzValue']

theorem scratch_exists_normGeneratorValueRatioUnit_eq_of_highBranch
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    (b : BONG V q L 2) (u : valuationUnitSubgroup K)
    (hR : ¬2 * (ramificationIndex K : Int) <
      ordUnit K b.binaryParameter)
    (hd : ¬2 * beliParameterDefect K b.binaryParameter ≤
      (beliDefectCutoff K b.binaryParameter : ℕ∞))
    (hu : (u : Kˣ) ∈ principalUnitSubgroup K
      (beliHighDefectExponent K b.binaryParameter)) :
    ∃ (y : V) (hy : Lattice.IsNormGenerator q L y),
      b.normGeneratorValueRatioUnit y hy = (u : Kˣ) := by
  have ha := b.binaryParameter_isBinaryParameterAdmissible
  have hEven := beli2009BinaryHighDefect_even_order
    (K := K) b.binaryParameter hd
  rcases scratch_exists_defectAdaptedShear b.binaryParameter ha hEven with
    ⟨c, htwo, hdiag, hcross, hdiagonal⟩
  have hhighCast := scratch_beliHighDefectExponent_cast
    b.binaryParameter ha hEven
  have hcross' : ord K ((2 : K) * c) =
      (((beliHighDefectExponent K b.binaryParameter : Nat) : Int) :
        WithTop Int) := by
    rw [hcross]
    exact_mod_cast hhighCast.symm
  have hdiagonal' : c ^ 2 + (b.binaryParameter : K) = 0 ∨
      (c ^ 2 + (b.binaryParameter : K) ≠ 0 ∧
        (((beliHighDefectExponent K b.binaryParameter : Nat) : Int) :
          WithTop Int) <
          ord K (c ^ 2 + (b.binaryParameter : K))) := by
    rcases hdiagonal with htop | hfinite
    · exact Or.inl htop.2
    · right
      constructor
      · intro hzero
        have horder := hfinite.2
        rw [hzero, ord_zero] at horder
        exact WithTop.top_ne_coe horder
      · rw [hfinite.2]
        exact_mod_cast
          scratch_beliHighExponent_lt_lowCoefficient_of_finite
            b.binaryParameter ha hR hd hEven hfinite.1
  rcases scratch_exists_high_binaryModel_normGenerator
      b.binaryParameter c htwo hdiag
      (beliHighDefectExponent K b.binaryParameter) hcross' hdiagonal' u hu with
    ⟨z, hz, hvalue⟩
  exact scratch_exists_normGeneratorValueRatioUnit_eq_of_shear_value
    b c htwo hdiag z hz u hvalue

theorem scratch_quadraticDefect_ge_of_mem_principalUnitSubgroup
    [QuadraticDefectLaws K]
    (u : valuationUnitSubgroup K) (m : Nat)
    (hu : (u : Kˣ) ∈ principalUnitSubgroup K m) :
    (m : ℕ∞) ≤ quadraticDefect K (u : Kˣ) := by
  apply natCast_le_quadraticDefect K
  refine ⟨1, ?_⟩
  have herror : ((m : Int) : WithTop Int) ≤
      ord K (((u : Kˣ) : K) - 1) :=
    (Lattice.mem_powerIdeal_iff (K := K) (m : Int)
      (((u : Kˣ) : K) - 1)).1 hu.2
  have heq : 1 - (1 : K) ^ 2 / ((u : Kˣ) : K) =
      (((u : Kˣ) : K) - 1) / ((u : Kˣ) : K) := by
    field_simp [Units.ne_zero (u : Kˣ)]
  rw [heq, div_eq_mul_inv, ord_mul, AddValuation.map_inv, u.property]
  simpa using herror

theorem scratch_beliLowBranch_arithmetic
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    (a : Kˣ) (ha : IsBinaryParameterAdmissible a)
    (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hd : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞))
    (hEven : Even (ordUnit K a))
    (hnotEndpoint : ordUnit K a ≠
      -(2 * (ramificationIndex K : Int))) :
    0 < beliLowDefectExponent K a ∧
      Odd (beliLowDefectExponent K a) ∧
      beliLowDefectExponent K a < 2 * ramificationIndex K ∧
      (beliLowDefectExponent K a : Int) <
        2 * ((ramificationIndex K : Int) + ordUnit K a / 2) ∧
      (beliLowDefectExponent K a : Int) ≤
        (ramificationIndex K : Int) + ordUnit K a / 2 := by
  have hfinite : beliParameterDefect K a ≠ ⊤ := by
    intro htop
    rw [htop] at hd
    simp at hd
  let R : Int := ordUnit K a
  let d : Nat := beliParameterDefectNat K a
  let ε : Kˣ := normalizedUnitPart K a
  have hε : IsValuationUnit K (ε : K) :=
    normalizedUnitPart_isValuationUnit K a
  have hfactor : uniformizerPowerUnit K R * ε = a := by
    simpa [R, ε] using uniformizerPower_mul_normalizedUnitPart K a
  have hdefectUnit : quadraticDefect K (-ε) = beliParameterDefect K a := by
    have h := beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
      (K := K) R ε hε (by simpa [R] using hEven)
    rw [hfactor] at h
    exact h.symm
  have hfiniteUnit : quadraticDefect K (-ε) ≠ ⊤ := by
    rw [hdefectUnit]
    exact hfinite
  have hnegεUnit : IsValuationUnit K ((-ε : Kˣ) : K) := by
    change ord K (-(ε : K)) = 0
    change ord K (ε : K) = 0 at hε
    simpa only [ord_neg] using hε
  have hdPos : 0 < d := by
    have h := quadraticDefect_toNat_pos_of_unit_of_ne_top
      (-ε) hnegεUnit hfiniteUnit
    simpa [d, beliParameterDefectNat, hdefectUnit] using h
  have hnonsquare : ¬IsSquare (-ε) := by
    intro hsquare
    exact hfiniteUnit
      ((quadraticDefect_eq_top_iff_isSquare (K := K) (-ε)).2 hsquare)
  have hdLeRaw := quadraticDefect_le_two_mul_e_of_not_isSquare
    (K := K) hnonsquare
  have hdLe : d ≤ 2 * ramificationIndex K := by
    rw [← ENat.coe_toNat hfiniteUnit] at hdLeRaw
    simpa [d, beliParameterDefectNat, hdefectUnit] using
      ENat.coe_le_coe.mp hdLeRaw
  have hRlower : -(2 * (ramificationIndex K : Int)) ≤ R := by
    simpa [R] using ha.ordUnit_ge_neg_two_mul_e
  have hRstrictLower : -(2 * (ramificationIndex K : Int)) < R := by
    have hne : R ≠ -(2 * (ramificationIndex K : Int)) := by
      simpa [R] using hnotEndpoint
    omega
  have hcutoffCast := scratch_beliDefectCutoff_cast a hR
  have hdefectEq : beliParameterDefect K a = (d : ℕ∞) := by
    simpa [d, beliParameterDefectNat] using (ENat.coe_toNat hfinite).symm
  have hdCut : 2 * d ≤ beliDefectCutoff K a := by
    rw [hdefectEq] at hd
    exact_mod_cast hd
  have hdLt : d < 2 * ramificationIndex K := by
    by_contra hnot
    have heq : d = 2 * ramificationIndex K := by omega
    have hdCutInt : 2 * (d : Int) ≤
        (beliDefectCutoff K a : Int) := by exact_mod_cast hdCut
    rw [hcutoffCast, heq] at hdCutInt
    omega
  have hdefectLt : quadraticDefect K (-ε) <
      ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    rw [← ENat.coe_toNat hfiniteUnit]
    exact_mod_cast (show (quadraticDefect K (-ε)).toNat <
      2 * ramificationIndex K by
        simpa [d, beliParameterDefectNat, hdefectUnit] using hdLt)
  have hdOdd : Odd d :=
    by
      simpa [d, beliParameterDefectNat, hdefectUnit] using
        (quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
          (K := K) (-ε) hnegεUnit hdefectLt)
  have hlowCast := scratch_beliLowDefectExponent_cast a ha hfinite
  have hcrossBound := scratch_beliLowExponent_le_highCoefficient
    a ha hR hd hEven
  have hRltUpper : R < 2 * (ramificationIndex K : Int) := by
    by_contra hnot
    have hRupper : R ≤ 2 * (ramificationIndex K : Int) := by
      dsimp [R]
      omega
    have heq : R = 2 * (ramificationIndex K : Int) := by
      omega
    have hdCutInt : 2 * (d : Int) ≤
        (beliDefectCutoff K a : Int) := by exact_mod_cast hdCut
    have hcutoffCastR : (beliDefectCutoff K a : Int) =
        2 * (ramificationIndex K : Int) - R := by
      simpa [R] using hcutoffCast
    rw [hcutoffCastR, heq] at hdCutInt
    omega
  have hcrossLt : (ramificationIndex K : Int) + R / 2 <
      2 * (ramificationIndex K : Int) := by
    rcases hEven with ⟨r, hr⟩
    omega
  have hlowInt : (beliLowDefectExponent K a : Int) = R + d := by
    simpa [R, d] using hlowCast
  have hlowPosInt : 0 < (beliLowDefectExponent K a : Int) := by
    have hnonneg : 0 ≤ R + (d : Int) := by
      simpa [R, d, beliParameterDefectNat] using
        (beli2009_order_add_parameterDefect_nonneg
          (K := K) ha hfinite)
    by_contra hnot
    have hzero : R + (d : Int) = 0 := by rw [hlowInt] at hnot; omega
    rcases hEven with ⟨r, hr⟩
    rcases hdOdd with ⟨s, hs⟩
    have hsInt : (d : Int) = 2 * (s : Int) + 1 := by exact_mod_cast hs
    omega
  have hlowOdd : Odd (beliLowDefectExponent K a) := by
    rcases hEven with ⟨r, hr⟩
    rcases hdOdd with ⟨s, hs⟩
    have hsInt : (d : Int) = 2 * (s : Int) + 1 := by exact_mod_cast hs
    have hformula : (beliLowDefectExponent K a : Int) =
        2 * (r + (s : Int)) + 1 := by omega
    have hrs : 0 ≤ r + (s : Int) := by omega
    refine ⟨Int.toNat (r + (s : Int)), ?_⟩
    have hcast : (Int.toNat (r + (s : Int)) : Int) =
        r + (s : Int) := by rw [Int.toNat_of_nonneg hrs]
    exact_mod_cast (hcast ▸ hformula)
  have hlowLtTwoE : beliLowDefectExponent K a <
      2 * ramificationIndex K := by
    exact_mod_cast hcrossBound.trans_lt hcrossLt
  have hcrossPos : 0 < (ramificationIndex K : Int) + R / 2 :=
    lt_of_lt_of_le hlowPosInt hcrossBound
  refine ⟨by exact_mod_cast hlowPosInt, hlowOdd, hlowLtTwoE, ?_, ?_⟩
  · simpa [R] using (show (beliLowDefectExponent K a : Int) <
        2 * ((ramificationIndex K : Int) + R / 2) by omega)
  · simpa [R] using hcrossBound

theorem scratch_exists_normGeneratorValueRatioUnit_eq_of_lowEvenNonendpoint
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    (b : BONG V q L 2) (u : valuationUnitSubgroup K)
    (hR : ¬2 * (ramificationIndex K : Int) <
      ordUnit K b.binaryParameter)
    (hd : 2 * beliParameterDefect K b.binaryParameter ≤
      (beliDefectCutoff K b.binaryParameter : ℕ∞))
    (hEven : Even (ordUnit K b.binaryParameter))
    (hnotEndpoint : ordUnit K b.binaryParameter ≠
      -(2 * (ramificationIndex K : Int)))
    (hu : (u : Kˣ) ∈ principalUnitSubgroup K
      (beliLowDefectExponent K b.binaryParameter))
    (hnorm : IsQuadraticNorm K (-b.binaryParameter) (u : Kˣ)) :
    ∃ (y : V) (hy : Lattice.IsNormGenerator q L y),
      b.normGeneratorValueRatioUnit y hy = (u : Kˣ) := by
  have ha := b.binaryParameter_isBinaryParameterAdmissible
  have hfinite : beliParameterDefect K b.binaryParameter ≠ ⊤ := by
    intro htop
    rw [htop] at hd
    simp at hd
  rcases scratch_exists_defectAdaptedShear b.binaryParameter ha hEven with
    ⟨c, htwo, hdiag, hcross, hdiagonal⟩
  have hdiagOrder : ord K (c ^ 2 + (b.binaryParameter : K)) =
      ((ordUnit K b.binaryParameter +
        (beliParameterDefectNat K b.binaryParameter : Int) : Int) :
        WithTop Int) := by
    rcases hdiagonal with htop | hfiniteCase
    · exact (hfinite htop.1).elim
    · exact hfiniteCase.2
  have hlowCast := scratch_beliLowDefectExponent_cast
    b.binaryParameter ha hfinite
  have hdiagOrder' : ord K (c ^ 2 + (b.binaryParameter : K)) =
      (((beliLowDefectExponent K b.binaryParameter : Nat) : Int) :
        WithTop Int) := by
    rw [hdiagOrder]
    exact_mod_cast hlowCast.symm
  have harith := scratch_beliLowBranch_arithmetic
    b.binaryParameter ha hR hd hEven hnotEndpoint
  rcases harith with ⟨hmPos, hmOdd, hmLtTwoE, hmLtTwoS, hmLeS⟩
  have hdefect := scratch_quadraticDefect_ge_of_mem_principalUnitSubgroup
    u (beliLowDefectExponent K b.binaryParameter) hu
  rcases hnorm with ⟨x, y, hnormValueRaw⟩
  have hnormValue : x ^ 2 + (b.binaryParameter : K) * y ^ 2 =
      ((u : Kˣ) : K) := by
    simpa only [Units.val_neg, neg_mul, sub_neg_eq_add] using hnormValueRaw
  let x' : K := x - c * y
  let z : Fin 2 → K := ![x', y]
  have hvalue :
      (QuadraticSpace.binaryModel b.binaryParameter c).quadratic z =
        ((u : Kˣ) : K) := by
    rw [QuadraticSpace.binaryModel_quadratic_apply]
    dsimp [z, x']
    calc
      (x - c * y) ^ 2 + (2 * c) * ((x - c * y) * y) +
          (c ^ 2 + (b.binaryParameter : K)) * y ^ 2 =
          x ^ 2 + (b.binaryParameter : K) * y ^ 2 := by ring
      _ = ((u : Kˣ) : K) := hnormValue
  have hcoords := scratch_low_binaryModel_coordinates_integral
    b.binaryParameter c (beliLowDefectExponent K b.binaryParameter)
    ((ramificationIndex K : Int) + ordUnit K b.binaryParameter / 2)
    hcross hdiagOrder' hmPos hmOdd hmLtTwoE hmLtTwoS hmLeS
    x' y u hvalue hdefect
  have hzMem : z ∈ binaryModelLattice (K := K) := by
    rw [scratch_mem_binaryModelLattice_iff]
    intro i
    fin_cases i
    · exact hcoords.1
    · exact hcoords.2
  have hz : Lattice.IsNormGenerator
      (QuadraticSpace.binaryModel b.binaryParameter c)
      (binaryModelLattice (K := K)) z :=
    scratch_isNormGenerator_binaryModel_of_mem_of_unit_value
      b.binaryParameter c htwo hdiag z hzMem u hvalue
  exact scratch_exists_normGeneratorValueRatioUnit_eq_of_shear_value
    b c htwo hdiag z hz u hvalue

theorem scratch_exists_normGeneratorValueRatioUnit_eq_of_lowOdd
    [QuadraticDefectLaws K]
    (b : BONG V q L 2) (u : valuationUnitSubgroup K)
    (hR : ¬2 * (ramificationIndex K : Int) <
      ordUnit K b.binaryParameter)
    (hOdd : Odd (ordUnit K b.binaryParameter))
    (hu : (u : Kˣ) ∈ principalUnitSubgroup K
      (beliLowDefectExponent K b.binaryParameter))
    (hnorm : IsQuadraticNorm K (-b.binaryParameter) (u : Kˣ)) :
    ∃ (y : V) (hy : Lattice.IsNormGenerator q L y),
      b.normGeneratorValueRatioUnit y hy = (u : Kˣ) := by
  have ha := b.binaryParameter_isBinaryParameterAdmissible
  have hRnonneg : 0 ≤ ordUnit K b.binaryParameter :=
    order_nonneg_of_admissible_of_odd
      b.binaryParameter (ordUnit K b.binaryParameter) rfl ha hOdd
  have hRpos : 0 < ordUnit K b.binaryParameter := by
    rcases hOdd with ⟨r, hr⟩
    omega
  let R : Nat := Int.toNat (ordUnit K b.binaryParameter)
  have hRcast : (R : Int) = ordUnit K b.binaryParameter := by
    simp [R, Int.toNat_of_nonneg hRnonneg]
  have hROdd : Odd R := by
    rcases hOdd with ⟨r, hr⟩
    have hrNonneg : 0 ≤ r := by omega
    refine ⟨Int.toNat r, ?_⟩
    have hrcast : (Int.toNat r : Int) = r := by
      rw [Int.toNat_of_nonneg hrNonneg]
    exact_mod_cast (show (R : Int) = 2 * (Int.toNat r : Int) + 1 by
      rw [hRcast, hr, hrcast])
  have hRLtTwoE : R < 2 * ramificationIndex K := by
    have hRle : ordUnit K b.binaryParameter ≤
        2 * (ramificationIndex K : Int) := by omega
    have hRne : ordUnit K b.binaryParameter ≠
        2 * (ramificationIndex K : Int) := by
      intro heq
      rcases hOdd with ⟨r, hr⟩
      omega
    have hltInt : (R : Int) < 2 * (ramificationIndex K : Int) := by
      rw [hRcast]
      omega
    exact_mod_cast hltInt
  have hordNeg : ordUnit K (-b.binaryParameter) =
      ordUnit K b.binaryParameter := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, coe_ordUnit]
    simpa only [Units.val_neg] using ord_neg K (b.binaryParameter : K)
  have hzero : beliParameterDefect K b.binaryParameter = 0 := by
    apply quadraticDefect_eq_zero_of_odd_ordUnit
    rw [hordNeg]
    exact hOdd
  have hzeroNat : beliParameterDefectNat K b.binaryParameter = 0 := by
    simp [beliParameterDefectNat, hzero]
  have hlowEq : beliLowDefectExponent K b.binaryParameter = R := by
    simp [beliLowDefectExponent, hzeroNat, R]
  have hdefect : (R : ℕ∞) ≤ quadraticDefect K (u : Kˣ) := by
    rw [← hlowEq]
    exact scratch_quadraticDefect_ge_of_mem_principalUnitSubgroup
      u (beliLowDefectExponent K b.binaryParameter) hu
  have haIntegral : (b.binaryParameter : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, ← coe_ordUnit]
    exact_mod_cast hRnonneg
  have htwo : (2 : K) * 0 ∈ IntegerRing K := by simp
  have hdiag : (0 : K) ^ 2 + (b.binaryParameter : K) ∈ IntegerRing K := by
    simpa using haIntegral
  rcases hnorm with ⟨x, y, hnormValueRaw⟩
  have hnormValue : x ^ 2 + (b.binaryParameter : K) * y ^ 2 =
      ((u : Kˣ) : K) := by
    simpa only [Units.val_neg, neg_mul, sub_neg_eq_add] using hnormValueRaw
  have hcoords := scratch_odd_diagonal_coordinates_integral
    b.binaryParameter R hRcast.symm hROdd hRLtTwoE x y u hnormValue hdefect
  let z : Fin 2 → K := ![x, y]
  have hzMem : z ∈ binaryModelLattice (K := K) := by
    rw [scratch_mem_binaryModelLattice_iff]
    intro i
    fin_cases i
    · exact hcoords.1
    · exact hcoords.2
  have hvalue : (QuadraticSpace.binaryModel b.binaryParameter 0).quadratic z =
      ((u : Kˣ) : K) := by
    rw [QuadraticSpace.binaryModel_quadratic_apply]
    simpa [z] using hnormValue
  have hz : Lattice.IsNormGenerator
      (QuadraticSpace.binaryModel b.binaryParameter 0)
      (binaryModelLattice (K := K)) z :=
    scratch_isNormGenerator_binaryModel_of_mem_of_unit_value
      b.binaryParameter 0 htwo hdiag z hzMem u hvalue
  exact scratch_exists_normGeneratorValueRatioUnit_eq_of_shear_value
    b 0 htwo hdiag z hz u hvalue

theorem scratch_exists_normGeneratorValueRatioUnit_eq_of_discriminantEndpoint
    [laws : DyadicDiscriminantClassLaws K]
    (b : BONG V q L 2) (u : valuationUnitSubgroup K)
    (hclass : b.binaryUnitSquareClass = unitSquareClass K
      (negativeQuarterUnit K * laws.discriminantUnit))
    (hnorm : IsQuadraticNorm K (-b.binaryParameter) (u : Kˣ)) :
    ∃ (y : V) (hy : Lattice.IsNormGenerator q L y),
      b.normGeneratorValueRatioUnit y hy = (u : Kˣ) := by
  have hsquare := isSquare_neg_mul_discriminant_of_endpointClass
    (K := K) hclass
  rcases hsquare with ⟨r, hr⟩
  let t : Kˣ := r / laws.discriminantUnit
  have hparameter : laws.discriminantUnit * t ^ 2 = -b.binaryParameter := by
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
          ((r : K) * (r : K)) / (laws.discriminantUnit : K) := by
            field_simp [Units.ne_zero laws.discriminantUnit]
      _ = (-(b.binaryParameter : K) * (laws.discriminantUnit : K)) /
          (laws.discriminantUnit : K) := by rw [hrVal]
      _ = -(b.binaryParameter : K) := by
        field_simp [Units.ne_zero laws.discriminantUnit]
  have hnormDelta : IsQuadraticNorm K laws.discriminantUnit (u : Kˣ) := by
    apply (isQuadraticNorm_mul_square_left_iff K laws.discriminantUnit
      (u : Kˣ) t).1
    rw [hparameter]
    exact hnorm
  rcases hnormDelta with ⟨x, y, hnormValue⟩
  let α : K := x - y
  let β : K := 2 * y
  let z : Fin 2 → K := ![α, β]
  have hpoly : α ^ 2 + α * β + laws.rho * β ^ 2 =
      ((u : Kˣ) : K) := by
    dsimp [α, β]
    calc
      (x - y) ^ 2 + (x - y) * (2 * y) + laws.rho * (2 * y) ^ 2 =
          x ^ 2 - (1 - 4 * laws.rho) * y ^ 2 := by ring
      _ = x ^ 2 - (laws.discriminantUnit : K) * y ^ 2 := by
        rw [laws.discriminant_eq_one_sub_four_mul_rho]
      _ = ((u : Kˣ) : K) := hnormValue
  have hvalue :
      (QuadraticSpace.binaryModel
        (negativeQuarterUnit K * laws.discriminantUnit)
        (standardEndpointShear (K := K))).quadratic z =
          ((u : Kˣ) : K) := by
    rw [discriminantEndpoint_quadratic_apply]
    simpa [z] using hpoly
  have hcoords := scratch_discriminantEndpoint_coordinates_integral
    α β u (by simpa [z] using hvalue)
  have hzMem : z ∈ binaryModelLattice (K := K) := by
    rw [scratch_mem_binaryModelLattice_iff]
    intro i
    fin_cases i
    · exact hcoords.1
    · exact hcoords.2
  have hz : Lattice.IsNormGenerator
      (QuadraticSpace.binaryModel
        (negativeQuarterUnit K * laws.discriminantUnit)
        (standardEndpointShear (K := K)))
      (binaryModelLattice (K := K)) z :=
    scratch_isNormGenerator_binaryModel_of_mem_of_unit_value
      (negativeQuarterUnit K * laws.discriminantUnit)
      (standardEndpointShear (K := K))
      standardEndpointShear_two_integral
      discriminant_standardEndpointShear_diagonal_integral
      z hzMem u hvalue
  rcases b.isIsometric_standardEndpointModel
      (negativeQuarterUnit K * laws.discriminantUnit) hclass
      standardEndpointShear_two_integral
      discriminant_standardEndpointShear_diagonal_integral with ⟨f⟩
  have hzScaled : Lattice.IsNormGenerator
      (b.standardEndpointModelSpace
        (negativeQuarterUnit K * laws.discriminantUnit))
      (binaryModelLattice (K := K)) z := by
    simpa [standardEndpointModelSpace] using
      hz.rescaleQuadraticUnit (b.valueUnit 0)
  let yV : V := f.toLinearEquiv.symm z
  have hy : Lattice.IsNormGenerator q L yV :=
    hzScaled.mapLatticeIsometry f.symm
  refine ⟨yV, hy, ?_⟩
  apply Units.ext
  simp only [normGeneratorValueRatioUnit, Units.val_div_eq_div_val,
    Units.val_mk0, coe_valueUnit]
  have hmap := f.symm.map_quadratic z
  change q.quadratic yV =
      (b.valueUnit 0 : K) *
        (QuadraticSpace.binaryModel
          (negativeQuarterUnit K * laws.discriminantUnit)
          (standardEndpointShear (K := K))).quadratic z at hmap
  rw [hvalue] at hmap
  rw [hmap, b.coe_valueUnit]
  field_simp [b.value_ne_zero 0]

theorem scratch_exists_normGeneratorValueRatioUnit_eq_of_lowEndpoint
    [QuadraticDefectLaws K] [laws : DyadicDiscriminantClassLaws K]
    (b : BONG V q L 2) (u : valuationUnitSubgroup K)
    (horder : ordUnit K b.binaryParameter =
      -(2 * (ramificationIndex K : Int)))
    (hd : 2 * beliParameterDefect K b.binaryParameter ≤
      (beliDefectCutoff K b.binaryParameter : ℕ∞))
    (hnorm : IsQuadraticNorm K (-b.binaryParameter) (u : Kˣ)) :
    ∃ (y : V) (hy : Lattice.IsNormGenerator q L y),
      b.normGeneratorValueRatioUnit y hy = (u : Kˣ) := by
  have hfinite : beliParameterDefect K b.binaryParameter ≠ ⊤ := by
    intro htop
    rw [htop] at hd
    simp at hd
  rcases laws.endpoint_parameter_class b.binaryParameter
      b.binaryParameter_isBinaryParameterAdmissible horder with
    hquarter | hdiscriminant
  · have hsquare :=
      isSquare_neg_of_unitSquareClass_eq_negativeQuarter (K := K) hquarter
    have htop : beliParameterDefect K b.binaryParameter = ⊤ := by
      unfold beliParameterDefect
      exact quadraticDefect_eq_top_of_isSquare K hsquare
    exact (hfinite htop).elim
  · exact scratch_exists_normGeneratorValueRatioUnit_eq_of_discriminantEndpoint
      b u hdiscriminant hnorm

theorem scratch_exists_normGenerator_of_mem_beliNormGeneratorGroup
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    [DyadicDiscriminantClassLaws K]
    (b : BONG V q L 2) {c : ValuationUnitClass K}
    (hc : c ∈ beliNormGeneratorGroup K b.binaryParameter) :
    ∃ (y : V) (hy : Lattice.IsNormGenerator q L y),
      b.normGeneratorValueRatioClass y hy = c := by
  by_cases hR : 2 * (ramificationIndex K : Int) <
      ordUnit K b.binaryParameter
  · rw [beliNormGeneratorGroup_of_two_e_lt K b.binaryParameter hR] at hc
    have hcOne : c = 1 := by simpa using hc
    subst c
    refine ⟨b.head, b.head_isNormGenerator, ?_⟩
    change valuationUnitClassHom K
      (b.normGeneratorValueRatioValuationUnit b.head b.head_isNormGenerator) = 1
    have hratio : b.normGeneratorValueRatioUnit b.head
        b.head_isNormGenerator = 1 := by
      apply Units.ext
      simp only [normGeneratorValueRatioUnit, Units.val_div_eq_div_val,
        Units.val_mk0, coe_valueUnit, Units.val_one]
      rw [b.value_zero_eq_quadratic_head]
      exact div_self b.head_isAnisotropic
    have hsub : b.normGeneratorValueRatioValuationUnit b.head
        b.head_isNormGenerator = 1 := by
      apply Subtype.ext
      exact hratio
    rw [hsub]
    exact map_one (valuationUnitClassHom K)
  · by_cases hd : 2 * beliParameterDefect K b.binaryParameter ≤
        (beliDefectCutoff K b.binaryParameter : ℕ∞)
    · rw [beliNormGeneratorGroup_of_low_defect K b.binaryParameter hR hd]
        at hc
      rcases hc with ⟨hprincipalClass, hnormClass⟩
      rcases hprincipalClass with ⟨u, hu, hclass⟩
      change (u : Kˣ) ∈ principalUnitSubgroup K
        (beliLowDefectExponent K b.binaryParameter) at hu
      have hnormClass' : valuationUnitClassHom K u ∈
          quadraticNormValuationClassSubgroup K (-b.binaryParameter) := by
        rw [hclass]
        exact hnormClass
      have hnorm := scratch_isQuadraticNorm_of_unitClass_mem
        (-b.binaryParameter) u hnormClass'
      rcases Int.even_or_odd (ordUnit K b.binaryParameter) with hEven | hOdd
      · by_cases hendpoint : ordUnit K b.binaryParameter =
            -(2 * (ramificationIndex K : Int))
        · rcases scratch_exists_normGeneratorValueRatioUnit_eq_of_lowEndpoint
              b u hendpoint hd hnorm with ⟨y, hy, hratio⟩
          refine ⟨y, hy, ?_⟩
          change valuationUnitClassHom K
              (b.normGeneratorValueRatioValuationUnit y hy) = c
          rw [← hclass]
          apply congrArg (valuationUnitClassHom K)
          apply Subtype.ext
          exact hratio
        · rcases
              scratch_exists_normGeneratorValueRatioUnit_eq_of_lowEvenNonendpoint
                b u hR hd hEven hendpoint hu hnorm with ⟨y, hy, hratio⟩
          refine ⟨y, hy, ?_⟩
          change valuationUnitClassHom K
              (b.normGeneratorValueRatioValuationUnit y hy) = c
          rw [← hclass]
          apply congrArg (valuationUnitClassHom K)
          apply Subtype.ext
          exact hratio
      · rcases scratch_exists_normGeneratorValueRatioUnit_eq_of_lowOdd
            b u hR hOdd hu hnorm with ⟨y, hy, hratio⟩
        refine ⟨y, hy, ?_⟩
        change valuationUnitClassHom K
            (b.normGeneratorValueRatioValuationUnit y hy) = c
        rw [← hclass]
        apply congrArg (valuationUnitClassHom K)
        apply Subtype.ext
        exact hratio
    · rw [beliNormGeneratorGroup_of_high_defect K b.binaryParameter hR hd]
        at hc
      rcases hc with ⟨u, hu, hclass⟩
      change (u : Kˣ) ∈ principalUnitSubgroup K
        (beliHighDefectExponent K b.binaryParameter) at hu
      rcases scratch_exists_normGeneratorValueRatioUnit_eq_of_highBranch
          b u hR hd hu with ⟨y, hy, hratio⟩
      refine ⟨y, hy, ?_⟩
      change valuationUnitClassHom K
          (b.normGeneratorValueRatioValuationUnit y hy) = c
      rw [← hclass]
      apply congrArg (valuationUnitClassHom K)
      apply Subtype.ext
      exact hratio

theorem normGeneratorValueRatioClassSet_eq_beliNormGeneratorGroup_proved
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    [DyadicDiscriminantClassLaws K]
    (b : BONG V q L 2) :
    b.normGeneratorValueRatioClassSet =
      (beliNormGeneratorGroup K b.binaryParameter :
        Set (ValuationUnitClass K)) := by
  ext c
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact scratch_normGeneratorValueRatioClass_mem_beliNormGeneratorGroup b y hy
  · intro hc
    exact scratch_exists_normGenerator_of_mem_beliNormGeneratorGroup b hc

end BONG

theorem binaryNormGeneratorLocalLawsProved
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    [DyadicDiscriminantClassLaws K] :
    BinaryNormGeneratorLocalLaws.{u, v} K where
  valueRatioClassSet_eq b :=
    BONG.normGeneratorValueRatioClassSet_eq_beliNormGeneratorGroup_proved b

end Bong
