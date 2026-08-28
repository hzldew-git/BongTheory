import Bong.Lattice.Omeara9328FirstFundamentalIdealCases

/-!
# Coherent second-generator data for O'Meara 93:28

The scalar used in condition 93:28(ii) must be the same second norm
generator used by the determinant correction and 93:19 exchange.  This
file generalizes the equal-order error construction from the canonical
`Classical.choose` value to any explicit norm generator satisfying the
same normalized order condition.
-/

namespace Bong

open Dyadic Module

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

/-- The explicitly chosen normalized second generator belongs to the
normalized first source norm group. -/
theorem secondNormalizedNormGeneratorWith_mem_sourceFirst
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    (S.secondNormalizedNormGeneratorWith A : K) ∈
      normGroupSet S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice := by
  have hunscaled : (A.value 1 : K) ∈
      S.sourceJordan.fundamentalNormGroup 0 :=
    S.sourceJordan.fundamentalNormGroup_anti
      (show (0 : Fin (n + 2)) ≤ 1 by simp) (A.spec 1).1
  have hcomponent : (A.value 1 : K) ∈
      normGroupSet (S.sourceJordan.component 0).space
        (S.sourceJordan.component 0).lattice := by
    rw [S.sourceJordan_isSaturated 0]
    exact hunscaled
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  simpa only [secondNormalizedNormGeneratorWith, Units.val_mul,
    Units.val_inv_eq_inv_val, inv_inv, ← mul_assoc,
    mul_inv_cancel₀ (Units.ne_zero S.firstScale), one_mul] using hcomponent

/-- The same explicit normalized generator belongs to the normalized first
target norm group. -/
theorem secondNormalizedNormGeneratorWith_mem_targetFirst
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    (S.secondNormalizedNormGeneratorWith A : K) ∈
      normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice := by
  have hunscaledSource : (A.value 1 : K) ∈
      S.sourceJordan.fundamentalNormGroup 0 :=
    S.sourceJordan.fundamentalNormGroup_anti
      (show (0 : Fin (n + 2)) ≤ 1 by simp) (A.spec 1).1
  have hgroups : S.targetJordan.fundamentalNormGroup 0 =
      S.sourceJordan.fundamentalNormGroup 0 := by
    simpa only [S.residualFundamentalType.indexEquiv_apply_eq_self] using
      S.residualFundamentalType.normGroup_eq (0 : Fin (n + 2))
  have hcomponent : (A.value 1 : K) ∈
      normGroupSet (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice := by
    rw [S.targetJordan_isSaturated 0, hgroups]
    exact hunscaledSource
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  simpa only [secondNormalizedNormGeneratorWith, Units.val_mul,
    Units.val_inv_eq_inv_val, inv_inv, ← mul_assoc,
    mul_inv_cancel₀ (Units.ne_zero S.firstScale), one_mul] using hcomponent

theorem firstFundamentalIdeal_eq_withSecondGenerator
    (delta : Kˣ)
    (hdelta : IsNormGeneratorValue S.sourceSecondNormalized
      (S.sourceJordan.component 1).lattice delta)
    (hgap : ordUnit K delta = ordUnit K S.firstNormGenerator) :
    S.sourceJordan.fundamentalIdeal 0 =
      scalarIdeal (((S.firstScale⁻¹ * delta : Kˣ) : K))
        (S.sourceJordan.fundamentalWeightIdeal 0) := by
  have hdeltaCanonical : ordUnit K delta =
      ordUnit K S.secondNormalizedNormGenerator := by
    apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact hdelta.2.symm.trans
      S.secondNormalizedNormGenerator_source.2
  have hcanonicalGap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator := hdeltaCanonical.symm.trans hgap
  calc
    S.sourceJordan.fundamentalIdeal 0 =
        scalarIdeal
          (((S.firstScale⁻¹ * S.secondNormalizedNormGenerator : Kˣ) : K))
          (S.sourceJordan.fundamentalWeightIdeal 0) :=
      S.firstFundamentalIdeal_eq_rightNorm_mul_leftWeight_of_normalized_eq
        hcanonicalGap
    _ = scalarIdeal (((S.firstScale⁻¹ * delta : Kˣ) : K))
          (S.sourceJordan.fundamentalWeightIdeal 0) := by
      apply scalarIdeal_units_eq_of_ordUnit_eq
      simp only [ordUnit_mul, ordUnit_inv]
      rw [hdeltaCanonical]

theorem exists_leftWeight_factor_withSecondGenerator
    {z : K} (delta : Kˣ)
    (hdelta : IsNormGeneratorValue S.sourceSecondNormalized
      (S.sourceJordan.component 1).lattice delta)
    (hgap : ordUnit K delta = ordUnit K S.firstNormGenerator)
    (hz : z ∈ S.sourceJordan.fundamentalIdeal 0) :
    ∃ lambda : K,
      lambda ∈ S.sourceJordan.fundamentalWeightIdeal 0 ∧
      z = ((S.firstScale⁻¹ * delta : Kˣ) : K) * lambda := by
  rw [S.firstFundamentalIdeal_eq_withSecondGenerator
    delta hdelta hgap] at hz
  rcases hz with ⟨lambda, hlambda, hz⟩
  exact ⟨lambda, hlambda, hz.symm⟩

noncomputable def equalNormOrderErrorDataOfSecondGenerator
    (z : K) (delta : Kˣ)
    (hdeltaSourceSecond : IsNormGeneratorValue S.sourceSecondNormalized
      (S.sourceJordan.component 1).lattice delta)
    (hdeltaTargetSecond : IsNormGeneratorValue S.targetSecondNormalized
      (S.targetJordan.component 1).lattice delta)
    (hdeltaSourceFirst : (delta : K) ∈
      normGroupSet S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice)
    (hdeltaTargetFirst : (delta : K) ∈
      normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice)
    (hgap : ordUnit K delta = ordUnit K S.firstNormGenerator)
    (hz : z ∈ S.sourceJordan.fundamentalIdeal 0) :
    S.EqualNormOrderErrorData z := by
  let hexists := S.exists_leftWeight_factor_withSecondGenerator
    delta hdeltaSourceSecond hgap hz
  let lambda : K := Classical.choose hexists
  have hlambda : lambda ∈
      S.sourceJordan.fundamentalWeightIdeal 0 :=
    (Classical.choose_spec hexists).1
  have hzEq : z = ((S.firstScale⁻¹ * delta : Kˣ) : K) * lambda :=
    (Classical.choose_spec hexists).2
  let coefficient : K := ((S.firstScale⁻¹ : Kˣ) : K) * lambda
  have hdeltaCanonical : ordUnit K delta =
      ordUnit K S.secondNormalizedNormGenerator := by
    apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact hdeltaSourceSecond.2.symm.trans
      S.secondNormalizedNormGenerator_source.2
  have hcanonicalGap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator := hdeltaCanonical.symm.trans hgap
  have hlambdaGroupSource : lambda ∈
      S.sourceJordan.fundamentalNormGroup 0 :=
    weightIdeal_subset_normGroupSet
      (S.sourceJordan.fundamentalNormGenerator 0)
      (S.sourceJordan.fundamentalNormGenerator_spec 0) hlambda
  have hlambdaGroupTarget : lambda ∈
      normGroupSet (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice := by
    rw [S.targetJordan_isSaturated 0]
    have hgroups : S.targetJordan.fundamentalNormGroup 0 =
        S.sourceJordan.fundamentalNormGroup 0 := by
      simpa only [S.residualFundamentalType.indexEquiv_apply_eq_self] using
        S.residualFundamentalType.normGroup_eq (0 : Fin (n + 2))
    rw [hgroups]
    exact hlambdaGroupSource
  have hlambdaGroupSourceComponent : lambda ∈
      normGroupSet (S.sourceJordan.component 0).space
        (S.sourceJordan.component 0).lattice := by
    rw [S.sourceJordan_isSaturated 0]
    exact hlambdaGroupSource
  have hcoefficientSource : coefficient ∈
      normGroupSet S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice := by
    rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
    simpa only [coefficient, Units.val_inv_eq_inv_val,
      inv_inv, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero S.firstScale),
      one_mul] using hlambdaGroupSourceComponent
  have hcoefficientTarget : coefficient ∈
      normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice := by
    rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
    simpa only [coefficient, Units.val_inv_eq_inv_val,
      inv_inv, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero S.firstScale),
      one_mul] using hlambdaGroupTarget
  have hlambdaPrincipal : lambda ∈ principalIdeal (K := K)
      (S.sourceJordan.fundamentalNormGenerator 0 : K) :=
    weightIdeal_le_principalIdeal
      (S.sourceJordan.fundamentalNormGenerator 0)
      (S.sourceJordan.fundamentalNormGenerator_spec 0) hlambda
  have hcoefficientPrincipal0 : coefficient ∈ principalIdeal (K := K)
      (((S.firstScale⁻¹ *
        S.sourceJordan.fundamentalNormGenerator 0 : Kˣ) : K)) := by
    rw [← scalarIdeal_principalIdeal_units]
    exact ⟨lambda, hlambdaPrincipal, rfl⟩
  have hprincipalEq : principalIdeal (K := K)
        (((S.firstScale⁻¹ *
          S.sourceJordan.fundamentalNormGenerator 0 : Kˣ) : K)) =
      principalIdeal (K := K) (delta : K) := by
    apply (principalIdeal_eq_iff_ordUnit_eq _ _).mpr
    simp only [ordUnit_mul, ordUnit_inv]
    rw [hgap, S.firstNormGenerator_order]
    unfold fundamentalScaleOrder
    simp only [S.sourceJordan_scaleGenerator,
      Omeara9328RankFourReductionSystem.firstScale]
    omega
  have hcoefficientPrincipal : coefficient ∈
      principalIdeal (K := K) (delta : K) := by
    rw [← hprincipalEq]
    exact hcoefficientPrincipal0
  have hdeltaIntegral : (delta : K) ∈ IntegerRing K := by
    have hdeltaOrder : 0 ≤ ordUnit K delta := by
      have hfirst := S.firstNormGenerator_integral
      rw [mem_integerRing_iff, Dyadic.IsIntegral, ← coe_ordUnit] at hfirst
      rw [hgap]
      exact WithTop.coe_nonneg.mp hfirst
    rw [mem_integerRing_iff, Dyadic.IsIntegral, ← coe_ordUnit]
    exact WithTop.coe_nonneg.mpr hdeltaOrder
  have hcoefficientIntegral : coefficient ∈ IntegerRing K := by
    have hlower := ord_le_of_mem_principalIdeal
      (Units.ne_zero delta) hcoefficientPrincipal
    have hdeltaNonneg : (0 : WithTop Int) ≤ ord K (delta : K) := by
      rw [← coe_ordUnit]
      simpa only [Dyadic.IsIntegral, coe_ordUnit] using
        (mem_integerRing_iff K).1 hdeltaIntegral
    rw [mem_integerRing_iff]
    exact hdeltaNonneg.trans hlower
  exact
    { secondGenerator := delta
      coefficient := coefficient
      error_eq := by
        dsimp only [coefficient]
        rw [hzEq]
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        ring
      coefficient_integral := hcoefficientIntegral
      coefficient_mem_sourceFirst := hcoefficientSource
      coefficient_mem_targetFirst := hcoefficientTarget
      coefficient_mul_relativeScale_sq_mem_secondGeneratorIdeal := by
        let c : IntegerRing K :=
          ⟨(S.relativeSecondScale : K) ^ 2,
            (IntegerRing K).toSubring.pow_mem
              ((mem_integerRing_iff K).2
                (le_of_lt S.relativeSecondScale_isInMaximalIdeal)) 2⟩
        have h := (principalIdeal (K := K) (delta : K)).smul_mem c
          hcoefficientPrincipal
        change (S.relativeSecondScale : K) ^ 2 * coefficient ∈
          principalIdeal (K := K) (delta : K) at h
        simpa only [mul_comm] using h
      secondGenerator_integral := hdeltaIntegral
      secondGenerator_sourceSecond := hdeltaSourceSecond
      secondGenerator_targetSecond := hdeltaTargetSecond
      secondGenerator_mem_sourceFirst := hdeltaSourceFirst
      secondGenerator_mem_targetFirst := hdeltaTargetFirst }

/-- Construct the equal-order error package using the exact coherent
generator choice occurring in conditions 93:28(ii)--(iii). -/
noncomputable def equalNormOrderErrorDataWith
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (z : K)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator)
    (hz : z ∈ S.sourceJordan.fundamentalIdeal 0) :
    S.EqualNormOrderErrorData z :=
  S.equalNormOrderErrorDataOfSecondGenerator z
    (S.secondNormalizedNormGeneratorWith A)
    (S.secondNormalizedNormGeneratorWith_source A)
    (S.secondNormalizedNormGeneratorWith_target A)
    (S.secondNormalizedNormGeneratorWith_mem_sourceFirst A)
    (S.secondNormalizedNormGeneratorWith_mem_targetFirst A)
    hgap hz

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
