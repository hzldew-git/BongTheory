/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328AdjacentNormOrderDeterminantCorrection

/-!
# O'Meara 93:28, Step 7: the gap-two scale-one inequalities

This file isolates the numerical part of Step 7.  When the normalized norm
orders differ by two and the adjacent Jordan scales differ by one, failure
of the condition-(iii) trigger places both rho-twists of the determinant-one
quaternary model in the normalized second norm group.  Consequently the
double 93:19 absorption already constructed for Steps 4 and 6 applies
without an additional local law.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

namespace QuadraticSpace

universe u

variable {K : Type u} [Field K]

/-- Multiplication by `u⁻¹` identifies the line with coefficient
`u⁻² a` with the line with coefficient `a`. -/
noncomputable def scaledLineInverseSquareIsometry (u a : Kˣ) :
    Isometry (scaledLine (u⁻¹ ^ 2 * a)) (scaledLine a) where
  toLinearEquiv :=
    { toFun := fun x ↦ ((u⁻¹ : Kˣ) : K) * x
      invFun := fun x ↦ (u : K) * x
      left_inv := by
        intro x
        simp
      right_inv := by
        intro x
        simp
      map_add' := by
        intro x y
        ring
      map_smul' := by
        intro c x
        simp only [smul_eq_mul, RingHom.id_apply]
        ring }
  map_bilin := by
    intro x y
    change (a : K) * (((u⁻¹ : Kˣ) : K) * x) *
        (((u⁻¹ : Kˣ) : K) * y) =
      ((u⁻¹ ^ 2 * a : Kˣ) : K) * x * y
    simp only [Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero u]

end QuadraticSpace

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- The coherent first fundamental norm generator after division by the
first Jordan scale. -/
noncomputable def firstNormalizedNormGeneratorWith
    (A : FundamentalNormGeneratorChoice S.sourceJordan) : Kˣ :=
  S.firstScale⁻¹ * A.value 0

theorem firstNormalizedNormGeneratorWith_source
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    IsNormGeneratorValue S.sourceFirstNormalized
      (S.sourceJordan.component 0).lattice
      (S.firstNormalizedNormGeneratorWith A) := by
  have hcomponent : IsNormGeneratorValue
      (S.sourceJordan.component 0).space
      (S.sourceJordan.component 0).lattice (A.value 0) :=
    isNormGeneratorValue_of_normGroupSet_eq
      (A.spec 0) (S.sourceJordan_isSaturated 0).symm
      ⟨S.firstScale * S.firstNormGenerator,
        S.firstNormGenerator_source_unscaled⟩
  simpa only [sourceFirstNormalized,
    firstNormalizedNormGeneratorWith] using
      hcomponent.rescaleQuadraticUnit S.firstScale⁻¹

theorem firstNormalizedNormGeneratorWith_target
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    IsNormGeneratorValue S.targetFirstNormalized
      (S.targetJordan.component 0).lattice
      (S.firstNormalizedNormGeneratorWith A) := by
  exact isNormGeneratorValue_of_normGroupSet_eq
    (S.firstNormalizedNormGeneratorWith_source A)
    S.firstNormalized_normGroupSet_eq
    ⟨S.firstNormGenerator, S.firstNormGenerator_target⟩

theorem firstNormalizedNormGeneratorWith_order_eq
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    ordUnit K (S.firstNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator := by
  apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
  exact (S.firstNormalizedNormGeneratorWith_source A).2.symm.trans
    S.firstNormGenerator_source.2

/-- The gap-two formula of 93:27 with the coherent first generator used in
condition 93:28(iii). -/
theorem firstFundamentalIdeal_eq_leftChoice_mul_rightWeight_gapTwo
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1) :
    S.sourceJordan.fundamentalIdeal 0 =
      scalarIdeal
        (((S.firstScale⁻¹ *
          S.firstNormalizedNormGeneratorWith A : Kˣ) : K))
        (S.sourceJordan.fundamentalWeightIdeal 1) := by
  have hcanonicalGap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator + 2 := by
    rw [← S.secondNormalizedNormGeneratorWith_order_eq A]
    exact hgap
  calc
    S.sourceJordan.fundamentalIdeal 0 =
        scalarIdeal
          (((S.firstScale⁻¹ ^ 2 *
            S.sourceJordan.fundamentalNormGenerator 0 : Kˣ) : K))
          (S.sourceJordan.fundamentalWeightIdeal 1) :=
      S.firstFundamentalIdeal_eq_leftNorm_mul_rightWeight_of_normalized_gap_two
        hcanonicalGap hscale
    _ = scalarIdeal
          (((S.firstScale⁻¹ *
            S.firstNormalizedNormGeneratorWith A : Kˣ) : K))
          (S.sourceJordan.fundamentalWeightIdeal 1) := by
      apply scalarIdeal_units_eq_of_ordUnit_eq
      simp only [firstNormalizedNormGeneratorWith, ordUnit_mul,
        ordUnit_pow, ordUnit_inv]
      have hchoice : ordUnit K (A.value 0) =
          ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) := by
        apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
        exact (A.spec 0).2.symm.trans
          (S.sourceJordan.fundamentalNormGenerator_spec 0).2
      rw [hchoice]
      ring

/-- Scalar package for the determinant correction in Step 7.  In contrast
to Steps 4 and 6, the error is divided by the normalized first generator;
the quotient comes from the second fundamental weight and hence belongs to
both normalized component norm groups. -/
structure GapTwoErrorData (z : K) where
  firstGenerator : Kˣ
  secondGenerator : Kˣ
  coefficient : K
  error_eq : z = (firstGenerator : K) * coefficient
  coefficient_integral : coefficient ∈ IntegerRing K
  coefficient_mem_sourceFirst : coefficient ∈
    normGroupSet S.sourceFirstNormalized
      (S.sourceJordan.component 0).lattice
  coefficient_mem_targetFirst : coefficient ∈
    normGroupSet S.targetFirstNormalized
      (S.targetJordan.component 0).lattice
  coefficient_mem_sourceSecond : coefficient ∈
    normGroupSet S.sourceSecondNormalized
      (S.sourceJordan.component 1).lattice
  coefficient_mem_targetSecond : coefficient ∈
    normGroupSet S.targetSecondNormalized
      (S.targetJordan.component 1).lattice
  coefficient_mem_firstGeneratorIdeal : coefficient ∈
    principalIdeal (K := K) (firstGenerator : K)
  coefficient_mem_secondGeneratorIdeal : coefficient ∈
    principalIdeal (K := K) (secondGenerator : K)
  firstGenerator_mul_relativeScale_sq_mem_secondGeneratorIdeal :
    (firstGenerator : K) * (S.relativeSecondScale : K) ^ 2 ∈
      principalIdeal (K := K) (secondGenerator : K)
  firstGenerator_integral : (firstGenerator : K) ∈ IntegerRing K
  firstGenerator_sourceFirst : IsNormGeneratorValue
    S.sourceFirstNormalized (S.sourceJordan.component 0).lattice
      firstGenerator
  firstGenerator_targetFirst : IsNormGeneratorValue
    S.targetFirstNormalized (S.targetJordan.component 0).lattice
      firstGenerator
  secondGenerator_sourceSecond : IsNormGeneratorValue
    S.sourceSecondNormalized (S.sourceJordan.component 1).lattice
      secondGenerator
  secondGenerator_targetSecond : IsNormGeneratorValue
    S.targetSecondNormalized (S.targetJordan.component 1).lattice
      secondGenerator

/-- Construct the Step-7 error data from condition 93:28(i) and the third
formula of 93:27. -/
noncomputable def gapTwoErrorData
    (A : FundamentalNormGeneratorChoice S.sourceJordan) (z : K)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1)
    (hz : z ∈ S.sourceJordan.fundamentalIdeal 0) :
    S.GapTwoErrorData z := by
  let delta := S.firstNormalizedNormGeneratorWith A
  have hz' := hz
  rw [S.firstFundamentalIdeal_eq_leftChoice_mul_rightWeight_gapTwo
    A hgap hscale] at hz'
  let lambda : K := Classical.choose hz'
  have hlambda : lambda ∈ S.sourceJordan.fundamentalWeightIdeal 1 :=
    (Classical.choose_spec hz').1
  have hzEq :
      (((S.firstScale⁻¹ * S.firstNormalizedNormGeneratorWith A : Kˣ) : K)) *
        lambda = z :=
    (Classical.choose_spec hz').2
  let coefficient : K := ((S.firstScale⁻¹ : Kˣ) : K) * lambda
  have hlambdaSourceSecond : lambda ∈
      normGroupSet (S.sourceJordan.component 1).space
        (S.sourceJordan.component 1).lattice := by
    rw [S.sourceJordan_isSaturated 1]
    exact weightIdeal_subset_normGroupSet (A.value 1) (A.spec 1) hlambda
  have hlambdaTargetSecond : lambda ∈
      normGroupSet (S.targetJordan.component 1).space
        (S.targetJordan.component 1).lattice := by
    rw [S.targetJordan_isSaturated 1]
    have hgroups : S.targetJordan.fundamentalNormGroup 1 =
        S.sourceJordan.fundamentalNormGroup 1 := by
      simpa only [S.residualFundamentalType.indexEquiv_apply_eq_self] using
        S.residualFundamentalType.normGroup_eq (1 : Fin (n + 2))
    rw [hgroups]
    exact weightIdeal_subset_normGroupSet (A.value 1) (A.spec 1) hlambda
  have hcoefficientSourceSecond : coefficient ∈
      normGroupSet S.sourceSecondNormalized
        (S.sourceJordan.component 1).lattice := by
    rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
    simpa only [coefficient, Units.val_inv_eq_inv_val,
      inv_inv, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero S.firstScale),
      one_mul] using hlambdaSourceSecond
  have hcoefficientTargetSecond : coefficient ∈
      normGroupSet S.targetSecondNormalized
        (S.targetJordan.component 1).lattice := by
    rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
    simpa only [coefficient, Units.val_inv_eq_inv_val,
      inv_inv, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero S.firstScale),
      one_mul] using hlambdaTargetSecond
  have hlambdaSourceFirst : lambda ∈
      normGroupSet (S.sourceJordan.component 0).space
        (S.sourceJordan.component 0).lattice := by
    rw [S.sourceJordan_isSaturated 0]
    exact S.sourceJordan.fundamentalNormGroup_anti
      (show (0 : Fin (n + 2)) ≤ 1 by simp)
      (weightIdeal_subset_normGroupSet (A.value 1) (A.spec 1) hlambda)
  have hcoefficientSourceFirst : coefficient ∈
      normGroupSet S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice := by
    rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
    simpa only [coefficient, Units.val_inv_eq_inv_val,
      inv_inv, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero S.firstScale),
      one_mul] using hlambdaSourceFirst
  have hcoefficientTargetFirst : coefficient ∈
      normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice := by
    rw [← S.firstNormalized_normGroupSet_eq]
    exact hcoefficientSourceFirst
  have hlambdaPrincipal : lambda ∈
      principalIdeal (K := K) (A.value 1 : K) :=
    weightIdeal_le_principalIdeal (A.value 1) (A.spec 1) hlambda
  have hcoefficientSecondPrincipal : coefficient ∈
      principalIdeal (K := K)
        ((S.secondNormalizedNormGeneratorWith A : Kˣ) : K) := by
    change coefficient ∈ principalIdeal (K := K)
      (((S.firstScale⁻¹ * A.value 1 : Kˣ) : K))
    rw [← scalarIdeal_principalIdeal_units]
    exact ⟨lambda, hlambdaPrincipal, rfl⟩
  have hsecondLeFirst : principalIdeal (K := K)
        ((S.secondNormalizedNormGeneratorWith A : Kˣ) : K) ≤
      principalIdeal (K := K) (delta : K) := by
    rw [principalIdeal_eq_powerIdeal, principalIdeal_eq_powerIdeal,
      powerIdeal_le_iff]
    rw [hgap, S.firstNormalizedNormGeneratorWith_order_eq A]
    omega
  have hcoefficientPrincipal : coefficient ∈
      principalIdeal (K := K) (delta : K) :=
    hsecondLeFirst hcoefficientSecondPrincipal
  have hdeltaIntegral : (delta : K) ∈ IntegerRing K := by
    rw [mem_integerRing_iff, Dyadic.IsIntegral, ← coe_ordUnit]
    rw [S.firstNormalizedNormGeneratorWith_order_eq A]
    have h := S.firstNormGenerator_integral
    rw [mem_integerRing_iff, Dyadic.IsIntegral, ← coe_ordUnit] at h
    exact h
  have hcoefficientIntegral : coefficient ∈ IntegerRing K := by
    rw [mem_integerRing_iff]
    exact ((mem_integerRing_iff K).1 hdeltaIntegral).trans
      (ord_le_of_mem_principalIdeal (Units.ne_zero delta)
        hcoefficientPrincipal)
  exact
    { firstGenerator := delta
      secondGenerator := S.secondNormalizedNormGeneratorWith A
      coefficient := coefficient
      error_eq := by
        rw [← hzEq]
        dsimp only [delta, coefficient, firstNormalizedNormGeneratorWith]
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        ring
      coefficient_integral := hcoefficientIntegral
      coefficient_mem_sourceFirst := hcoefficientSourceFirst
      coefficient_mem_targetFirst := hcoefficientTargetFirst
      coefficient_mem_sourceSecond := hcoefficientSourceSecond
      coefficient_mem_targetSecond := hcoefficientTargetSecond
      coefficient_mem_firstGeneratorIdeal := hcoefficientPrincipal
      coefficient_mem_secondGeneratorIdeal := hcoefficientSecondPrincipal
      firstGenerator_mul_relativeScale_sq_mem_secondGeneratorIdeal := by
        apply mem_principalIdeal_of_ord_le
          (Units.ne_zero (S.secondNormalizedNormGeneratorWith A))
        rw [ord_mul, ord_pow, ← coe_ordUnit, ← coe_ordUnit,
          ← coe_ordUnit]
        apply WithTop.coe_le_coe.mpr
        dsimp only [delta]
        rw [hgap, S.firstNormalizedNormGeneratorWith_order_eq A, hscale]
        simp only [two_nsmul]
        omega
      firstGenerator_integral := hdeltaIntegral
      firstGenerator_sourceFirst :=
        S.firstNormalizedNormGeneratorWith_source A
      firstGenerator_targetFirst :=
        S.firstNormalizedNormGeneratorWith_target A
      secondGenerator_sourceSecond :=
        S.secondNormalizedNormGeneratorWith_source A
      secondGenerator_targetSecond :=
        S.secondNormalizedNormGeneratorWith_target A }

namespace GapTwoErrorData

variable {S : Omeara9328RankFourReductionSystem J H}
  {z : K} (D : S.GapTwoErrorData z)

/-- The Step-7 exchange on the unimodular first component.  The exchanged
determinant is supplied directly by the congruence unit, so 93:19 does not
need the stronger auxiliary hypothesis that the modular scale itself lie in
the maximal ideal. -/
noncomputable def headExchangeSetup
    (hunit : IsValuationUnit K (1 + z)) :
    Omeara9319ExchangeSetup S.targetFirstNormalized
      (S.targetJordan.component 0).lattice (1 : Kˣ) := by
  exact
    { alpha := 0
      beta := D.coefficient
      delta := -(D.firstGenerator : K)
      gamma := -(D.firstGenerator : K)
      alpha_integral := (IntegerRing K).zero_mem
      beta_integral := D.coefficient_integral
      gamma_integral :=
        (IntegerRing K).neg_mem (D.firstGenerator : K)
          D.firstGenerator_integral
      scale_integral := (IntegerRing K).one_mem
      old_determinant_unit := by
        simp [IsValuationUnit]
      new_determinant_unit := by
        have heq :
            ((0 : K) + (1 : K) * (-(D.firstGenerator : K))) *
                D.coefficient - 1 = -(1 + z) := by
          calc
            ((0 : K) + (1 : K) * (-(D.firstGenerator : K))) *
                  D.coefficient - 1 =
                -(1 + (D.firstGenerator : K) * D.coefficient) := by ring
            _ = -(1 + z) :=
              congrArg (fun t : K ↦ -(1 + t)) D.error_eq.symm
        change IsValuationUnit K
          (((0 : K) + (1 : K) * (-(D.firstGenerator : K))) *
            D.coefficient - 1)
        rw [heq, IsValuationUnit, ord_neg]
        exact hunit
      delta_mem := neg_mem_normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice
        D.firstGenerator_targetFirst.1
      delta_eq := by simp }

@[simp]
theorem headExchangeSetup_alpha
    (hunit : IsValuationUnit K (1 + z)) :
    (D.headExchangeSetup hunit).alpha = 0 :=
  rfl

@[simp]
theorem headExchangeSetup_beta
    (hunit : IsValuationUnit K (1 + z)) :
    (D.headExchangeSetup hunit).beta = D.coefficient :=
  rfl

@[simp]
theorem headExchangeSetup_gamma
    (hunit : IsValuationUnit K (1 + z)) :
    (D.headExchangeSetup hunit).gamma = -(D.firstGenerator : K) :=
  rfl

@[simp]
theorem headExchangeSetup_newCoefficient
    (hunit : IsValuationUnit K (1 + z)) :
    (D.headExchangeSetup hunit).alpha +
        ((1 : Kˣ) : K) * (D.headExchangeSetup hunit).gamma =
      -(D.firstGenerator : K) := by
  simp

/-- The 93:19 output on the normalized first component. -/
noncomputable def headShift
    (hunit : IsValuationUnit K (1 + z)) :
    Omeara9319ExchangeSetup.Omeara9319Data
      (D.headExchangeSetup hunit) :=
  (D.headExchangeSetup hunit).coefficientShift
    S.targetFirstNormalized_unimodular
    (by rw [S.targetFirstNormalized_finrank]; omega)

noncomputable abbrev correctedHead
    (hunit : IsValuationUnit K (1 + z)) : QuadraticSpace K
      ((D.headShift hunit).splitting.decomposition.component 1).carrier :=
  (D.headShift hunit).splitting.decomposition.component 1 |>.space

noncomputable abbrev correctedHeadLattice
    (hunit : IsValuationUnit K (1 + z)) : Lattice K
      ((D.headShift hunit).splitting.decomposition.component 1).carrier :=
  (D.headShift hunit).splitting.decomposition.component 1 |>.lattice

theorem exchangeComplement_normIdeal_eq
    (hunit : IsValuationUnit K (1 + z)) :
    normIdeal (D.headExchangeSetup hunit).exchangeComplement
        (hyperbolicPlaneLattice (K := K)) =
      principalIdeal (K := K) (D.firstGenerator : K) := by
  have hnegGenerator : IsNormGeneratorValue S.targetFirstNormalized
      (S.targetJordan.component 0).lattice (-D.firstGenerator) := by
    constructor
    · exact neg_mem_normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice
        D.firstGenerator_targetFirst.1
    · rw [D.firstGenerator_targetFirst.2]
      simpa only [Units.val_neg] using
        (principalIdeal_neg (K := K) (D.firstGenerator : K)).symm
  have hnegCoefficient : -D.coefficient ∈
      principalIdeal (K := K) (-(D.firstGenerator : K)) := by
    rw [principalIdeal_neg]
    exact (principalIdeal (K := K) (D.firstGenerator : K)).neg_mem
      D.coefficient_mem_firstGeneratorIdeal
  have h :=
    Lattice.Omeara9319ExchangeSetup.exchangeComplement_normIdeal_eq_of_zeroLeft
      (D.headExchangeSetup hunit)
      S.targetFirstNormalized_unimodular
      (by rw [S.targetFirstNormalized_finrank]; omega)
      (-D.coefficient) (-D.firstGenerator) hnegGenerator
      (by rfl) (by simp) (by simp) (by simpa using hnegCoefficient)
  simpa only [Units.val_neg, principalIdeal_neg] using h

noncomputable abbrev headExchangeAmbient
    (hunit : IsValuationUnit K (1 + z)) : QuadraticSpace K
      ((Fin 2 → K) × (S.targetJordan.component 0).carrier) :=
  (D.headExchangeSetup hunit).exchangeComplement.orthogonalSum
    S.targetFirstNormalized

noncomputable abbrev headExchangeAmbientLattice
    (D : S.GapTwoErrorData z)
    (_hunit : IsValuationUnit K (1 + z)) : Lattice K
      ((Fin 2 → K) × (S.targetJordan.component 0).carrier) :=
  product (hyperbolicPlaneLattice (K := K))
    (S.targetJordan.component 0).lattice

theorem headExchangeAmbient_normIdeal_eq
    (hunit : IsValuationUnit K (1 + z)) :
    normIdeal (D.headExchangeAmbient hunit)
        (D.headExchangeAmbientLattice hunit) =
      principalIdeal (K := K) (D.firstGenerator : K) := by
  rw [normIdeal_orthogonalProduct,
    D.exchangeComplement_normIdeal_eq hunit,
    D.firstGenerator_targetFirst.2, sup_idem]

theorem headShift_complement_finrank
    (hunit : IsValuationUnit K (1 + z)) :
    finrank K ((D.headShift hunit).splitting.decomposition.component 1).carrier =
      4 := by
  rw [(D.headShift hunit).splitting.complement_finrank]
  letI : Module.Finite K (S.targetJordan.component 0).carrier :=
    (S.targetJordan.component 0).lattice.moduleFinite
  rw [Module.finrank_prod, Module.finrank_fin_fun,
    S.targetFirstNormalized_finrank]

theorem headShift_complement_normGroupSet_eq
    (hunit : IsValuationUnit K (1 + z)) :
    normGroupSet (D.correctedHead hunit) (D.correctedHeadLattice hunit) =
      normGroupSet (D.headExchangeAmbient hunit)
        (D.headExchangeAmbientLattice hunit) := by
  exact (D.headShift hunit).splitting.complement_normGroupSet_eq
    (by rw [D.headShift_complement_finrank hunit]; omega)

theorem correctedHead_normIdeal_eq
    (hunit : IsValuationUnit K (1 + z)) :
    normIdeal (D.correctedHead hunit) (D.correctedHeadLattice hunit) =
      principalIdeal (K := K) (D.firstGenerator : K) := by
  have hdeltaAmbient : (D.firstGenerator : K) ∈
      normGroupSet (D.headExchangeAmbient hunit)
        (D.headExchangeAmbientLattice hunit) := by
    rw [mem_normGroupSet_orthogonalProduct_iff]
    exact ⟨0,
      zero_mem_normGroupSet (D.headExchangeSetup hunit).exchangeComplement
        (hyperbolicPlaneLattice (K := K)),
      (D.firstGenerator : K), D.firstGenerator_targetFirst.1, by simp⟩
  have hgenAmbient : IsNormGeneratorValue
      (D.headExchangeAmbient hunit) (D.headExchangeAmbientLattice hunit)
      D.firstGenerator :=
    ⟨hdeltaAmbient, D.headExchangeAmbient_normIdeal_eq hunit⟩
  have hexists : ∃ a : Kˣ, IsNormGeneratorValue
      (D.correctedHead hunit) (D.correctedHeadLattice hunit) a := by
    rcases exists_isNormGenerator_of_finrank_pos
        (D.correctedHead hunit) (D.correctedHeadLattice hunit)
        (by rw [D.headShift_complement_finrank hunit]; omega) with
      ⟨x, hx, hne⟩
    exact ⟨Units.mk0 ((D.correctedHead hunit).quadratic x) hne,
      hx.isNormGeneratorValue hne⟩
  exact (isNormGeneratorValue_of_normGroupSet_eq hgenAmbient
    (D.headShift_complement_normGroupSet_eq hunit).symm hexists).2

theorem correctedHead_firstGenerator
    (hunit : IsValuationUnit K (1 + z)) :
    IsNormGeneratorValue (D.correctedHead hunit)
      (D.correctedHeadLattice hunit) D.firstGenerator := by
  constructor
  · exact (D.headShift hunit).normGroup_subset
      D.firstGenerator_targetFirst.1
  · exact D.correctedHead_normIdeal_eq hunit

end GapTwoErrorData

namespace EqualNormOrderErrorData

variable {S : Omeara9328RankFourReductionSystem J H}
  {z : K} (D : S.EqualNormOrderErrorData z)

/-- The exchanged plane represents the line obtained by dividing its first
coefficient by the square of the relative Jordan scale.  In Step 7 the
chosen second generator is precisely that square times the coherent first
generator, so this is the line occurring in condition 93:28(iii). -/
theorem newPlaneRepresentsDescaledSecondGenerator :
    D.exchangeSetup.newPlane.Represents
      (QuadraticSpace.scaledLine
        (S.relativeSecondScale⁻¹ ^ 2 * D.secondGenerator)) := by
  have hbase : D.exchangeSetup.newPlane.Represents
      (QuadraticSpace.scaledLine D.secondGenerator) :=
    D.newPlaneRepresentsSecondGenerator
  have hline : (QuadraticSpace.scaledLine D.secondGenerator).Represents
      (QuadraticSpace.scaledLine
        (S.relativeSecondScale⁻¹ ^ 2 * D.secondGenerator)) :=
    ⟨(QuadraticSpace.scaledLineInverseSquareIsometry
      S.relativeSecondScale D.secondGenerator).toRepresentation⟩
  exact hbase.trans hline

end EqualNormOrderErrorData

/-- The non-condition-(iii) inequality is exactly the weight bound needed
for the Step-7 coefficient shifts. -/
theorem gapTwo_nontriggerIII_weight_order
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0)) :
    S.sourceJordan.fundamentalWeightOrder 1 ≤
      2 * (ramificationIndex K : Int) +
        2 * S.sourceJordan.fundamentalScaleOrder 0 -
          S.sourceJordan.fundamentalWeightOrder 0 := by
  rw [S.firstFundamentalIdeal_eq_leftNorm_mul_rightWeight_of_normalized_gap_two
    hgap hscale] at hnontrigger
  unfold fourNormOverWeightIdealWith at hnontrigger
  rw [show boundaryLeftIndex (0 : Fin (n + 1)) =
      (0 : Fin (n + 2)) by ext; rfl,
    fundamentalWeightIdeal, weightIdeal_eq_powerIdeal,
    scalarIdeal_powerIdeal_units, powerIdeal_lt_iff] at hnontrigger
  have hchoice : ordUnit K (A.value 0) =
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) := by
    apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact (A.spec 0).2.symm.trans
      (S.sourceJordan.fundamentalNormGenerator_spec 0).2
  rw [ordUnit_mul, ordUnit_pow, ordUnit_inv, hchoice] at hnontrigger
  unfold fundamentalWeightOrder at hnontrigger ⊢
  unfold fundamentalScaleOrder
  simp only [Omeara9328RankFourReductionSystem.firstScale,
    S.sourceJordan_scaleGenerator] at hnontrigger ⊢
  omega

/-- The rho-twist attached to a first-weight generator belongs to the
normalized second norm group in the nontrigger branch. -/
theorem gapTwo_neg_weightTwist_mem_targetSecondNormalized
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0))
    (b : Kˣ)
    (hb : ordUnit K b =
      weightIdealOrder S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice) :
    ((-Lattice.scratch_omearaRhoTwistUnit b : Kˣ) : K) ∈
      normGroupSet S.targetSecondNormalized
        (S.targetJordan.component 1).lattice := by
  apply S.scratch_mem_targetSecondNormalized_of_weight_order_le
  have hnon := S.gapTwo_nontriggerIII_weight_order A hgap hscale hnontrigger
  have hfirst := S.scratch_firstNormalized_weightIdealOrder_eq
  rw [Lattice.scratch_neg_omearaRhoTwistUnit_order, hb, hfirst]
  omega

/-- The rho-twist attached to the first norm generator belongs to the
normalized second norm group in the nontrigger branch. -/
theorem gapTwo_neg_normTwist_mem_targetSecondNormalized
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1)
    (hnontrigger : ¬ S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0)) :
    ((-Lattice.scratch_omearaRhoTwistUnit S.firstNormGenerator : Kˣ) : K) ∈
      normGroupSet S.targetSecondNormalized
        (S.targetJordan.component 1).lattice := by
  apply S.scratch_mem_targetSecondNormalized_of_weight_order_le
  have hnon := S.gapTwo_nontriggerIII_weight_order A hgap hscale hnontrigger
  have hfirst := S.scratch_firstNormalized_weightIdealOrder_eq
  have hnormLe := normGeneratorOrder_le_weightIdealOrder
    S.firstNormGenerator S.firstNormGenerator_source
  rw [Lattice.scratch_neg_omearaRhoTwistUnit_order]
  rw [hfirst] at hnormLe
  omega

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
