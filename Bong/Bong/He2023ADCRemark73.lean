/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCTheorem72Published
import Bong.Bong.He2023ADCQuaternaryMaximal
import Bong.Bong.BeliLemma317
import Bong.Bong.BinaryShearIsometry
import Bong.Lattice.OmearaGeneralPlane
import Bong.Lattice.OrthogonalProductIsometry

/-!
# He (2025), Remark 7.3

The three named maximal lattices in Theorem 7.2 are identified with the
literal scaled `A(alpha,beta)` presentations printed in Remark 7.3.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The general plane `A(pi^l,-(delta-1)pi^-l)` in Remark 7.3 is
nondegenerate. -/
theorem heADC2025Remark73_plane_nondegenerate (delta : Kˣ) (l : Int) :
    (uniformizerPowerUnit K l : K) *
        (-((delta : K) - 1) * (uniformizerPowerUnit K (-l) : K)) ≠ 1 := by
  intro h
  have hpower : (uniformizerPowerUnit K l : K) *
      (uniformizerPowerUnit K (-l) : K) = 1 := by
    have hpowerUnits : uniformizerPowerUnit K l *
        uniformizerPowerUnit K (-l) = 1 := by
      simp [uniformizerPowerUnit]
    exact congrArg Units.val hpowerUnits
  have hdelta : -(delta : K) + 1 = 1 := by
    calc
      -(delta : K) + 1 = -((delta : K) - 1) := by ring
      _ = ((uniformizerPowerUnit K l : K) *
          (uniformizerPowerUnit K (-l) : K)) *
          -((delta : K) - 1) := by rw [hpower, one_mul]
      _ = (uniformizerPowerUnit K l : K) *
          (-((delta : K) - 1) *
            (uniformizerPowerUnit K (-l) : K)) := by ring
      _ = 1 := h
  have hzero : (delta : K) = 0 := by
    calc
      (delta : K) = -(-(delta : K) + 1 - 1) := by ring
      _ = 0 := by simp [hdelta]
  exact Units.ne_zero delta hzero

/-- The literal binary plane in Remark 7.3. -/
noncomputable def heADC2025Remark73Plane (delta : Kˣ) (l : Int) :
    QuadraticSpace K (Fin 2 → K) :=
  QuadraticSpace.omearaGeneralPlane
    (uniformizerPowerUnit K l : K)
    (-((delta : K) - 1) * (uniformizerPowerUnit K (-l) : K))
    (heADC2025Remark73_plane_nondegenerate delta l)

/-- Normalization of a published unit representative identifies the order
of `delta-1` with its finite quadratic defect. -/
theorem heADC2025Remark73_normalized_sub_order {I : Type u} [Fintype I]
    (U : I → Kˣ) (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (i : I)
    (hlt : quadraticDefect K (U i) <
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    let D := heADC2025Lemma719_unitDefectData (U i) (hU.isUnit i) hlt
    ord K ((U i : K) - 1) = ((D.d : Int) : WithTop Int) := by
  dsimp only
  have hfinite : quadraticDefect K (U i) ≠ ⊤ := ne_top_of_lt hlt
  have hd :
      (heADC2025Lemma719_unitDefectData (U i) (hU.isUnit i) hlt).d =
        (quadraticDefect K (U i)).toNat := by
    simp [heADC2025Lemma719_unitDefectData]
  rw [hd]
  have hnormalized := (hU.normalized i).2.2
  rw [quadraticDefectIntOrder, ← ENat.coe_toNat hfinite] at hnormalized
  change ((((quadraticDefect K (U i)).toNat : Nat) : Int) : WithTop Int) =
    ord K ((U i : K) - 1) at hnormalized
  exact hnormalized.symm

/-- The normalized determinant parameter of the binary tail in Remark 7.3. -/
noncomputable def heADC2025Remark73Parameter (delta : Kˣ) (l : Int) : Kˣ :=
  -(delta * uniformizerPowerUnit K (-2 * l))

/-- The two integrality statements for the prescribed shear `pi^-l` are
exactly the off-diagonal and second diagonal entries of the printed plane. -/
theorem heADC2025Remark73_prescribedShear_conditions (delta : Kˣ) (l : Int)
    (hsub : ord K ((delta : K) - 1) =
      (((2 * l + 1 : Int) : Int) : WithTop Int))
    (hlt : l < (ramificationIndex K : Int)) :
    (2 : K) * (uniformizerPowerUnit K (-l) : K) ∈ IntegerRing K ∧
      (uniformizerPowerUnit K (-l) : K) ^ 2 +
        (heADC2025Remark73Parameter delta l : K) ∈ IntegerRing K := by
  let shear : K := uniformizerPowerUnit K (-l)
  change (2 : K) * shear ∈ IntegerRing K ∧
    shear ^ 2 + (heADC2025Remark73Parameter delta l : K) ∈ IntegerRing K
  constructor
  · rw [mem_integerRing_iff, Dyadic.IsIntegral, ord_mul,
      ← ramificationIndex_spec, ← coe_ordUnit,
      ordUnit_uniformizerPowerUnit]
    exact_mod_cast (show (0 : Int) ≤ (ramificationIndex K : Int) - l by omega)
  · have hpowerUnits : uniformizerPowerUnit K (-2 * l) =
        uniformizerPowerUnit K (-l) ^ 2 := by
      unfold uniformizerPowerUnit
      rw [pow_two, ← zpow_add]
      congr 1
      omega
    have hpower : (uniformizerPowerUnit K (-2 * l) : K) = shear ^ 2 := by
      simpa only [shear, Units.val_pow_eq_pow_val] using
        congrArg Units.val hpowerUnits
    have hfactor : shear ^ 2 +
        (heADC2025Remark73Parameter delta l : K) =
          -((delta : K) - 1) * (uniformizerPowerUnit K (-2 * l) : K) := by
      simp only [heADC2025Remark73Parameter, Units.val_neg, Units.val_mul]
      rw [hpower]
      ring
    rw [hfactor, mem_integerRing_iff, Dyadic.IsIntegral, ord_mul, ord_neg,
      hsub, ← coe_ordUnit, ordUnit_uniformizerPowerUnit]
    norm_cast
    omega

/-- The prescribed shear `pi^-l` makes the parameter from Remark 7.3
admissible. -/
theorem heADC2025Remark73_parameter_admissible (delta : Kˣ) (l : Int)
    (hsub : ord K ((delta : K) - 1) =
      (((2 * l + 1 : Int) : Int) : WithTop Int))
    (hlt : l < (ramificationIndex K : Int)) :
    BONG.IsBinaryParameterAdmissible
      (heADC2025Remark73Parameter delta l) :=
  ⟨(uniformizerPowerUnit K (-l) : K),
    heADC2025Remark73_prescribedShear_conditions delta l hsub hlt⟩

/-- With the prescribed shear `pi^-l`, the binary model is literally the
scaled general plane printed in Remark 7.3. -/
noncomputable def heADC2025Remark73_prescribedShearPlaneIsometry
    (a delta : Kˣ) (l : Int) :
    Lattice.Isometry
      (QuadraticSpace.rescaleUnit a
        (QuadraticSpace.binaryModel
          (heADC2025Remark73Parameter delta l)
          (uniformizerPowerUnit K (-l) : K)))
      ((heADC2025Remark73Plane delta l).rescaleUnit
        (a * uniformizerPowerUnit K (-l)))
      (BONG.binaryModelLattice (K := K))
      (Lattice.hyperbolicPlaneLattice (K := K)) := by
  have hcancelUnits : uniformizerPowerUnit K (-l) *
      uniformizerPowerUnit K l = 1 := by
    simp [uniformizerPowerUnit]
  have hcancel : (uniformizerPowerUnit K (-l) : K) *
      (uniformizerPowerUnit K l : K) = 1 :=
    congrArg Units.val hcancelUnits
  have hpowerUnits : uniformizerPowerUnit K (-2 * l) =
      uniformizerPowerUnit K (-l) ^ 2 := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    congr 1
    omega
  have hpower : (uniformizerPowerUnit K (-2 * l) : K) =
      (uniformizerPowerUnit K (-l) : K) ^ 2 := by
    simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val hpowerUnits
  refine
    { toLinearEquiv := LinearEquiv.refl K (Fin 2 → K)
      map_bilin := ?_
      map_mem := ?_ }
  · intro x y
    simp only [QuadraticSpace.rescaleUnit_bilin_apply,
      heADC2025Remark73Plane]
    rw [QuadraticSpace.omearaGeneralPlane_bilin_apply,
      QuadraticSpace.binaryModel, Matrix.toBilin'_apply]
    simp only [Fin.sum_univ_two,
      QuadraticSpace.binaryModelMatrix_zero_zero,
      QuadraticSpace.binaryModelMatrix_zero_one,
      QuadraticSpace.binaryModelMatrix_one_zero,
      QuadraticSpace.binaryModelMatrix_one_one,
      heADC2025Remark73Parameter, Units.val_mul, Units.val_neg]
    calc
      ((a : K) * (uniformizerPowerUnit K (-l) : K)) *
          ((uniformizerPowerUnit K l : K) * x 0 * y 0 + x 0 * y 1 +
            x 1 * y 0 +
            (-((delta : K) - 1) * (uniformizerPowerUnit K (-l) : K)) *
              x 1 * y 1) =
        (a : K) *
          (((uniformizerPowerUnit K (-l) : K) *
              (uniformizerPowerUnit K l : K)) * x 0 * y 0 +
            (uniformizerPowerUnit K (-l) : K) * x 0 * y 1 +
            (uniformizerPowerUnit K (-l) : K) * x 1 * y 0 +
            (-((delta : K) - 1) *
              (uniformizerPowerUnit K (-l) : K) ^ 2) * x 1 * y 1) := by ring
      _ = (a : K) *
          (1 * x 0 * y 0 +
            (uniformizerPowerUnit K (-l) : K) * x 0 * y 1 +
            (uniformizerPowerUnit K (-l) : K) * x 1 * y 0 +
            (-((delta : K) - 1) *
              (uniformizerPowerUnit K (-2 * l) : K)) * x 1 * y 1) := by
        rw [hcancel, ← hpower]
      _ = (a : K) *
          (1 * x 0 * y 0 +
            (uniformizerPowerUnit K (-l) : K) * x 0 * y 1 +
            ((uniformizerPowerUnit K (-l) : K) * x 1) * y 0 +
            ((uniformizerPowerUnit K (-l) : K) ^ 2 -
              (delta : K) * (uniformizerPowerUnit K (-2 * l) : K)) *
                x 1 * y 1) := by
        rw [← hpower]
        ring
      _ = (a : K) *
          (x 0 * 1 * y 0 +
            x 0 * (uniformizerPowerUnit K (-l) : K) * y 1 +
            (x 1 * (uniformizerPowerUnit K (-l) : K) * y 0 +
              x 1 * ((uniformizerPowerUnit K (-l) : K) ^ 2 +
                (-((delta : K) *
                  (uniformizerPowerUnit K (-2 * l) : K)))) * y 1)) := by ring
  · intro x
    rfl

/-- The choice of admissible shear used by the canonical binary model does
not affect the integral lattice: it is integrally isometric to the literal
scaled `A(alpha,beta)` plane of Remark 7.3. -/
theorem heADC2025Remark73_binaryParameter_isIsometric
    (a delta : Kˣ) (l : Int)
    (hadmissible : BONG.IsBinaryParameterAdmissible
      (heADC2025Remark73Parameter delta l))
    (hsub : ord K ((delta : K) - 1) =
      (((2 * l + 1 : Int) : Int) : WithTop Int))
    (hlt : l < (ramificationIndex K : Int)) :
    Lattice.IsIsometric
      (QuadraticSpace.rescaleUnit a
        (QuadraticSpace.binaryModel
          (heADC2025Remark73Parameter delta l)
          (BONG.admissibleBinaryShear
            (heADC2025Remark73Parameter delta l) hadmissible)))
      ((heADC2025Remark73Plane delta l).rescaleUnit
        (a * uniformizerPowerUnit K (-l)))
      (BONG.binaryModelLattice (K := K))
      (Lattice.hyperbolicPlaneLattice (K := K)) := by
  let prescribed : K := uniformizerPowerUnit K (-l)
  have hprescribed :=
    heADC2025Remark73_prescribedShear_conditions delta l hsub hlt
  have hshearSub :
      BONG.admissibleBinaryShear
          (heADC2025Remark73Parameter delta l) hadmissible - prescribed ∈
        IntegerRing K := by
    exact BONG.binaryShear_sub_mem_integerRing
      (heADC2025Remark73Parameter delta l)
      (BONG.admissibleBinaryShear
        (heADC2025Remark73Parameter delta l) hadmissible)
      prescribed
      (BONG.two_mul_admissibleBinaryShear_mem
        (heADC2025Remark73Parameter delta l) hadmissible)
      (BONG.admissibleBinaryShear_sq_add_mem
        (heADC2025Remark73Parameter delta l) hadmissible)
      (by simpa only [prescribed] using hprescribed.1)
      (by simpa only [prescribed] using hprescribed.2)
  obtain ⟨f⟩ := BONG.rescaledBinaryModel_isIsometric_of_shear_sub_integral
    a (heADC2025Remark73Parameter delta l)
    (BONG.admissibleBinaryShear
      (heADC2025Remark73Parameter delta l) hadmissible)
    prescribed hshearSub
  exact ⟨f.trans (heADC2025Remark73_prescribedShearPlaneIsometry a delta l)⟩

/-- The odd defect `d` determines the integer `l` used in Remark 7.3, with
the full printed range `2l = d - 1 <= 2e - 2`. -/
theorem HeADC719UnitDefectData.exists_remark73Exponent {delta : Kˣ}
    (D : HeADC719UnitDefectData (K := K) delta) :
    ∃ l : Int, 2 * l = D.d - 1 ∧ 0 ≤ l ∧
      2 * l ≤ 2 * (ramificationIndex K : Int) - 2 := by
  rcases D.odd with ⟨l, hl⟩
  have hdNonnegative : 0 ≤ D.d := D.nonnegative
  have hdLt : D.d < 2 * (ramificationIndex K : Int) := D.ltTwoE
  refine ⟨l, ?_, ?_, ?_⟩ <;> omega

/-- Rewriting the generic tail by `2l = d - 1` gives the exact normalized
determinant parameter used by the printed `A(alpha,beta)` plane. -/
theorem heADC2025Remark73_tailParameter_eq (a delta : Kˣ) (d l : Int)
    (hl : 2 * l = d - 1) :
    heHuUnitDefectTailValues (K := K) a delta d 1 /
        heHuUnitDefectTailValues (K := K) a delta d 0 =
      heADC2025Remark73Parameter delta l := by
  rw [heHuUnitDefectTail_parameter]
  unfold heADC2025Remark73Parameter
  have hexponent : 1 - d = -2 * l := by omega
  rw [hexponent]

/-- The generic binary tail in Lemma 7.19 is integrally isometric to the
literal scaled `A(alpha,beta)` model in Remark 7.3. -/
theorem heADC2025Remark73_binaryTail_isIsometric
    (a delta : Kˣ) (d l : Int)
    (ha : IsValuationUnit K (a : K))
    (hdelta : IsValuationUnit K (delta : K))
    (hdOdd : Odd d) (hdNonnegative : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hdefect : defectOrder (K := K) delta =
      (((d : Int) : ℚ) : WithTop ℚ))
    (hl : 2 * l = d - 1)
    (hsub : ord K ((delta : K) - 1) = ((d : Int) : WithTop Int)) :
    Lattice.IsIsometric
      (heADC719BinarySpace a delta d ha hdelta hdOdd
        hdNonnegative hdLt hdefect)
      ((heADC2025Remark73Plane delta l).rescaleUnit
        (a * uniformizerPowerUnit K (-l)))
      (BONG.binaryDiagonalModelLattice (K := K))
      (Lattice.hyperbolicPlaneLattice (K := K)) := by
  have hdEq : d = 2 * l + 1 := by omega
  have hsub' : ord K ((delta : K) - 1) =
      (((2 * l + 1 : Int) : Int) : WithTop Int) := by
    rw [← hdEq]
    exact hsub
  have hlt : l < (ramificationIndex K : Int) := by omega
  let hadmissible := heADC2025Remark73_parameter_admissible delta l hsub' hlt
  have H := heADC2025Remark73_binaryParameter_isIsometric
    a delta l hadmissible hsub' hlt
  have hparameter := heADC2025Remark73_tailParameter_eq a delta d l hl
  have hparameter' :
      heHuUnitDefectTailValues (K := K) a delta d 1 / a =
        heADC2025Remark73Parameter delta l := by
    simpa only [heHuUnitDefectTailValues_zero] using hparameter
  simpa only [heADC719BinarySpace, BONG.binaryDiagonalModelSpace,
    BONG.binaryDiagonalModelLattice, heHuUnitDefectTailValues_zero,
    hparameter'] using H

/-- The discriminant binary block in the unit row is the literal
`pi * (1/2) A(2,2rho)` block printed in the third formula of Remark 7.3. -/
theorem heADC2025Remark73_discriminantBinary_isIsometric_scaledA :
    Lattice.IsIsometric
      (BONG.binaryDiagonalModelSpace
        (uniformizerPowerUnit K 1)
        (uniformizerPowerUnit K 1 *
          lemma712DiscriminantParameter (K := K))
        (lemma712_sourceBinaryAdmissible
          (uniformizerPowerUnit K 1)))
      ((heADCAForm (K := K)).rescaleUnit (uniformizerPowerUnit K 1))
      (BONG.binaryDiagonalModelLattice (K := K))
      (BONG.binaryModelLattice (K := K)) := by
  letI : DyadicDiscriminantClassLaws K :=
    dyadicDiscriminantClassLawsProved (K := K)
  let p := uniformizerPowerUnit K 1
  let d := lemma712DiscriminantParameter (K := K)
  let hadmissible := lemma712_sourceBinaryAdmissible (K := K) p
  have hstandard :
      (2 : K) * BONG.standardEndpointShear (K := K) ∈ IntegerRing K ∧
        BONG.standardEndpointShear (K := K) ^ 2 + (d : K) ∈
          IntegerRing K := by
    exact ⟨BONG.standardEndpointShear_two_integral (K := K),
      BONG.discriminant_standardEndpointShear_diagonal_integral (K := K)⟩
  have hshearSub :
      BONG.admissibleBinaryShear ((p * d) / p) hadmissible -
          BONG.standardEndpointShear (K := K) ∈ IntegerRing K := by
    exact BONG.binaryShear_sub_mem_integerRing ((p * d) / p)
      (BONG.admissibleBinaryShear ((p * d) / p) hadmissible)
      (BONG.standardEndpointShear (K := K))
      (BONG.two_mul_admissibleBinaryShear_mem ((p * d) / p) hadmissible)
      (BONG.admissibleBinaryShear_sq_add_mem ((p * d) / p) hadmissible)
      hstandard.1 (by simpa only [mul_div_cancel_left] using hstandard.2)
  have H := BONG.rescaledBinaryModel_isIsometric_of_shear_sub_integral
    p ((p * d) / p)
    (BONG.admissibleBinaryShear ((p * d) / p) hadmissible)
    (BONG.standardEndpointShear (K := K)) hshearSub
  simpa only [p, d, hadmissible, BONG.binaryDiagonalModelSpace,
    BONG.binaryDiagonalModelLattice, heADCAForm,
    lemma712DiscriminantParameter, mul_div_cancel_left] using H

/-- The unit-row ternary tail is the ordered product
`pi * (1/2) A(2,2rho) perp <Delta * epsilon>` used in Remark 7.3. -/
theorem heADC2025Remark73_ternaryTail_isIsometric (epsilon : Kˣ) :
    Lattice.IsIsometric
      (unaryBinaryModelSpace
        (heHuLemma39iiiSourceUnary (K := K) epsilon)
        (uniformizerPowerUnit K 1)
        (uniformizerPowerUnit K 1 *
          lemma712DiscriminantParameter (K := K))
        (lemma712_sourceBinaryAdmissible
          (uniformizerPowerUnit K 1)))
      (((heADCAForm (K := K)).rescaleUnit (uniformizerPowerUnit K 1))
        |>.orthogonalSum
          ((QuadraticSpace.line K).rescaleUnit
            ((dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit *
              epsilon)))
      (unaryBinaryModelLattice (K := K))
      (Lattice.product (BONG.binaryModelLattice (K := K))
        (BONG.unaryModelLattice (K := K))) := by
  letI : DyadicDiscriminantClassLaws K :=
    dyadicDiscriminantClassLawsProved (K := K)
  obtain ⟨g⟩ :=
    heADC2025Remark73_discriminantBinary_isIsometric_scaledA (K := K)
  let lineForm := (QuadraticSpace.line K).rescaleUnit
    ((dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit * epsilon)
  let lineIdentity := Lattice.Isometry.refl lineForm
    (BONG.unaryModelLattice (K := K))
  let combined := lineIdentity.orthogonalProductBasic g
  let swap := Lattice.orthogonalProductSwap
    (q := lineForm)
    (r := (heADCAForm (K := K)).rescaleUnit (uniformizerPowerUnit K 1))
    (L := BONG.unaryModelLattice (K := K))
    (M := BONG.binaryModelLattice (K := K))
  exact ⟨by
    simpa only [combined, lineIdentity, lineForm, unaryBinaryModelSpace,
      unaryBinaryModelLattice, heHuLemma39iiiSourceUnary] using
        combined.trans swap⟩

/-- An integral isometry of tail lattices extends through a common tower of
literal half-hyperbolic planes. -/
noncomputable def heADC2025Remark73_halfHyperbolicExtensionIsometry
    {V W : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W}
    (f : Lattice.Isometry q r L M) :
    (k : Nat) → Lattice.Isometry
      (Lattice.halfHyperbolicExtensionForm q k)
      (Lattice.halfHyperbolicExtensionForm r k)
      (Lattice.halfHyperbolicExtensionLattice L k)
      (Lattice.halfHyperbolicExtensionLattice M k)
  | 0 => f
  | k + 1 =>
      (Lattice.Isometry.refl
        ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
          (Lattice.dyadicHalfUnit (K := K)))
        (Lattice.hyperbolicPlaneLattice (K := K))).orthogonalProductBasic
          (heADC2025Remark73_halfHyperbolicExtensionIsometry f k)

/-- The literal unit-row tower is the named maximal lattice
`N_2^(2k+5)(epsilon)`. -/
theorem heADC2025Remark73_thirdBasePublishedData
    (epsilon : Kˣ) (hepsilon : IsValuationUnit K (epsilon : K)) (k : Nat) :
    Lattice.IsIsometric
      (Lattice.halfHyperbolicExtensionForm
        (unaryBinaryModelSpace
          (heHuLemma39iiiSourceUnary (K := K) epsilon)
          (uniformizerPowerUnit K 1)
          (uniformizerPowerUnit K 1 *
            lemma712DiscriminantParameter (K := K))
          (lemma712_sourceBinaryAdmissible
            (uniformizerPowerUnit K 1))) (k + 1))
      (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) epsilon))
      (Lattice.halfHyperbolicExtensionLattice
        (unaryBinaryModelLattice (K := K)) (k + 1))
      (heADCN2Odd (k + 1) epsilon).lattice := by
  letI : GoodBONGClassificationLaws.{u, u, u} K :=
    goodBONGClassificationLawsProved K
  obtain ⟨kappa, hkappa, hkappaDefect⟩ :=
    exists_unit_defectOrder_eq_twoE_sub_one (K := K)
  let b := heHuLemma311OddSecondUnitTail epsilon kappa
    hepsilon hkappa hkappaDefect
  have hIntegral : Lattice.IsIntegral
      (unaryBinaryModelSpace
        (heHuLemma39iiiSourceUnary (K := K) epsilon)
        (uniformizerPowerUnit K 1)
        (uniformizerPowerUnit K 1 *
          lemma712DiscriminantParameter (K := K))
        (lemma712_sourceBinaryAdmissible
          (uniformizerPowerUnit K 1)))
      (unaryBinaryModelLattice (K := K)) := by
    apply heHuIntegral_of_firstOrder_nonneg b
    rw [heHuLemma311OddSecondUnitTail_order]
    norm_num
  have hmax := heHu2022Proposition37OddSecondUnit epsilon kappa
    hepsilon hkappa hkappaDefect (k + 1)
  have hepsilonEven : Even (ordUnit K epsilon) := by
    rw [(isValuationUnit_iff_ordUnit_eq_zero K epsilon).1 hepsilon]
    exact ⟨0, by omega⟩
  have htail :=
    heHuLemma311OddSecondUnitTail_represents_oddSecondTailEven
      epsilon kappa hepsilon hkappa hkappaDefect
  let base := heHu2022Lemma310BONG b hIntegral (k + 1)
  have hrep := heHuLemma511LiftEvenTail_represents_oddSecond
    b hIntegral epsilon hepsilonEven (k + 1) htail
  have hambient := base.ambientIsometric_of_diagonalRepresents
    (heADCW2Odd (k + 1) epsilon) (by omega) hrep
  exact Lattice.oMaximal_isIsometric_of_isometric hmax
    (heHuOMaximalLattice_isOMaximal _) hambient

/-- The first displayed isometry in Remark 7.3, on the literal normalized
published parameter system. -/
theorem heADC2025Remark73_firstPublished
    {I : Type u} [Fintype I]
    (U : I → Kˣ) (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (hDelta : ∃ i,
      U i = (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (k : Nat) (b : HeADC2025Theorem72BaseIndex (K := K) U) :
    let hs := b.sharp U hU hDelta
    let hlt := heADC2025Theorem72_defectLt_of_sharpDomain (U b.index) hs
    let D := heADC2025Lemma719_unitDefectData
      (U b.index) (hU.isUnit b.index) hlt
    ∃ l : Int, 2 * l = D.d - 1 ∧ 0 ≤ l ∧
      2 * l ≤ 2 * (ramificationIndex K : Int) - 2 ∧
        Lattice.IsIsometric
          (BONG.coefficientDiagonalSpace
            (heADCW1Even (k + 1) (U b.index)))
          (Lattice.halfHyperbolicExtensionForm
            ((heADC2025Remark73Plane (U b.index) l).rescaleUnit
              (uniformizerPowerUnit K (-l))) (k + 1))
          (heADCN1Even (k + 1) (U b.index)).lattice
          (Lattice.halfHyperbolicExtensionLattice
            (Lattice.hyperbolicPlaneLattice (K := K)) (k + 1)) := by
  dsimp only
  let hs := b.sharp U hU hDelta
  let hlt := heADC2025Theorem72_defectLt_of_sharpDomain (U b.index) hs
  let D := heADC2025Lemma719_unitDefectData
    (U b.index) (hU.isUnit b.index) hlt
  obtain ⟨l, hl, hlNonnegative, hlBound⟩ := D.exists_remark73Exponent
  refine ⟨l, hl, hlNonnegative, hlBound, ?_⟩
  have hsub := heADC2025Remark73_normalized_sub_order U hU b.index hlt
  have hbinary := heADC2025Remark73_binaryTail_isIsometric
    (1 : Kˣ) (U b.index) D.d l (by simp [IsValuationUnit])
    (hU.isUnit b.index) D.odd D.nonnegative D.ltTwoE D.defect hl hsub
  obtain ⟨g⟩ := hbinary
  have g' : Lattice.Isometry
      (heADC719BinarySpace (1 : Kˣ) (U b.index) D.d
        (by simp [IsValuationUnit]) (hU.isUnit b.index) D.odd
        D.nonnegative D.ltTwoE D.defect)
      ((heADC2025Remark73Plane (U b.index) l).rescaleUnit
        (uniformizerPowerUnit K (-l)))
      (BONG.binaryDiagonalModelLattice (K := K))
      (Lattice.hyperbolicPlaneLattice (K := K)) := by
    simpa using g
  obtain ⟨f⟩ := heADC2025Lemma719FirstBasePublishedData
    k (U b.index) D.d (hU.isUnit b.index) D.odd
    D.nonnegative D.ltTwoE D.defect
  exact ⟨f.symm.trans
    (heADC2025Remark73_halfHyperbolicExtensionIsometry g' (k + 1))⟩

/-- The second displayed isometry in Remark 7.3, including the literal sharp
factor `delta#` outside the general plane. -/
theorem heADC2025Remark73_secondPublished
    {I : Type u} [Fintype I]
    (U : I → Kˣ) (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (hDelta : ∃ i,
      U i = (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (k : Nat) (b : HeADC2025Theorem72BaseIndex (K := K) U) :
    let hs := b.sharp U hU hDelta
    let hlt := heADC2025Theorem72_defectLt_of_sharpDomain (U b.index) hs
    let D := heADC2025Lemma719_unitDefectData
      (U b.index) (hU.isUnit b.index) hlt
    ∃ l : Int, 2 * l = D.d - 1 ∧ 0 ≤ l ∧
      2 * l ≤ 2 * (ramificationIndex K : Int) - 2 ∧
        Lattice.IsIsometric
          (BONG.coefficientDiagonalSpace
            (heADCW2Even (k + 1) (U b.index)
              (Or.inr hs.notSquare)))
          (Lattice.halfHyperbolicExtensionForm
            ((heADC2025Remark73Plane (U b.index) l).rescaleUnit
              (heHuSharp (U b.index) hs *
                uniformizerPowerUnit K (-l))) (k + 1))
          (heADCN2Even (k + 1) (U b.index)
            (Or.inr hs.notSquare)).lattice
          (Lattice.halfHyperbolicExtensionLattice
            (Lattice.hyperbolicPlaneLattice (K := K)) (k + 1)) := by
  dsimp only
  let hs := b.sharp U hU hDelta
  let hlt := heADC2025Theorem72_defectLt_of_sharpDomain (U b.index) hs
  let D := heADC2025Lemma719_unitDefectData
    (U b.index) (hU.isUnit b.index) hlt
  obtain ⟨l, hl, hlNonnegative, hlBound⟩ := D.exists_remark73Exponent
  refine ⟨l, hl, hlNonnegative, hlBound, ?_⟩
  have hsub := heADC2025Remark73_normalized_sub_order U hU b.index hlt
  have ha : IsValuationUnit K ((heHuSharp (U b.index) hs : Kˣ) : K) :=
    (heHu2022Proposition32 (U b.index) hs).1
  have hbinary := heADC2025Remark73_binaryTail_isIsometric
    (heHuSharp (U b.index) hs) (U b.index) D.d l ha
    (hU.isUnit b.index) D.odd D.nonnegative D.ltTwoE D.defect hl hsub
  obtain ⟨g⟩ := hbinary
  obtain ⟨f⟩ := heADC2025Lemma719SecondBasePublishedData
    k (U b.index) hs D.d (hU.isUnit b.index) D.odd
    D.nonnegative D.ltTwoE D.defect
  exact ⟨f.symm.trans
    (heADC2025Remark73_halfHyperbolicExtensionIsometry g (k + 1))⟩

/-- The third displayed isometry in Remark 7.3:
`N_2^(n+2)(epsilon) = H^((n-1)/2) perp pi A perp <Delta epsilon>`. -/
theorem heADC2025Remark73_thirdPublished
    (epsilon : Kˣ) (hepsilon : IsValuationUnit K (epsilon : K)) (k : Nat) :
    Lattice.IsIsometric
      (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) epsilon))
      (Lattice.halfHyperbolicExtensionForm
        (((heADCAForm (K := K)).rescaleUnit (uniformizerPowerUnit K 1))
          |>.orthogonalSum
            ((QuadraticSpace.line K).rescaleUnit
              ((dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit *
                epsilon))) (k + 1))
      (heADCN2Odd (k + 1) epsilon).lattice
      (Lattice.halfHyperbolicExtensionLattice
        (Lattice.product (BONG.binaryModelLattice (K := K))
          (BONG.unaryModelLattice (K := K))) (k + 1)) := by
  obtain ⟨f⟩ := heADC2025Remark73_thirdBasePublishedData
    epsilon hepsilon k
  obtain ⟨g⟩ :=
    heADC2025Remark73_ternaryTail_isIsometric (K := K) epsilon
  exact ⟨f.symm.trans
    (heADC2025Remark73_halfHyperbolicExtensionIsometry g (k + 1))⟩

/-- The exact published parameter domain of the third formula, with
`epsilon` chosen from the finite normalized representative system `U`. -/
theorem heADC2025Remark73_thirdPublishedRepresentative
    {I : Type u} [Fintype I]
    (U : I → Kˣ) (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (i : I) (k : Nat) :
    Lattice.IsIsometric
      (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) (U i)))
      (Lattice.halfHyperbolicExtensionForm
        (((heADCAForm (K := K)).rescaleUnit (uniformizerPowerUnit K 1))
          |>.orthogonalSum
            ((QuadraticSpace.line K).rescaleUnit
              ((dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit *
                U i))) (k + 1))
      (heADCN2Odd (k + 1) (U i)).lattice
      (Lattice.halfHyperbolicExtensionLattice
        (Lattice.product (BONG.binaryModelLattice (K := K))
          (BONG.unaryModelLattice (K := K))) (k + 1)) :=
  heADC2025Remark73_thirdPublished (U i) (hU.isUnit i) k

end BONG.GoodBONG

end Bong
