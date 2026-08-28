/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328NormalizedSecondComponents
import Bong.Lattice.OmearaModularNormClassification
import Bong.Lattice.Omeara9328GeneratorChoice
import Bong.Lattice.WeightIdealRescale
import Bong.Lattice.OmearaCoefficientShift

/-!
# Norm-generator orders after the first-scale normalization

The notation in O'Meara 93:28 uses the orders `U₁,U₂` of norm
generators after the first Jordan scale has been normalized to one.  This
file identifies those normalized generators with the fundamental norm
generators of the saturated rank-four Jordan system.  Consequently the
difference `U₂ - U₁` is exactly the corresponding difference of
fundamental norm orders and can be used without an additional choice axiom.
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

private theorem exists_source_component_normGeneratorValue
    (i : Fin (n + 2)) :
    ∃ a : Kˣ, IsNormGeneratorValue
      (S.sourceJordan.component i).space
      (S.sourceJordan.component i).lattice a := by
  rcases exists_isNormGenerator_of_finrank_pos
      (S.sourceJordan.component i).space
      (S.sourceJordan.component i).lattice
      (by
        change 0 < S.sourceJordan.componentRank i
        rw [S.sourceJordan_componentRank]
        omega) with
    ⟨x, hx, hne⟩
  exact ⟨Units.mk0 ((S.sourceJordan.component i).space.quadratic x) hne,
    hx.isNormGeneratorValue hne⟩

private theorem exists_target_normalizedSecond_normGeneratorValue :
    ∃ a : Kˣ, IsNormGeneratorValue S.targetSecondNormalized
      (S.targetJordan.component 1).lattice a := by
  rcases exists_isNormGenerator_of_finrank_pos
      S.targetSecondNormalized (S.targetJordan.component 1).lattice
      (by rw [S.targetSecondNormalized_finrank]; omega) with
    ⟨x, hx, hne⟩
  exact ⟨Units.mk0 (S.targetSecondNormalized.quadratic x) hne,
    hx.isNormGeneratorValue hne⟩

/-- Undoing the first-scale normalization turns the chosen normalized first
norm generator into a norm generator on the original first component. -/
theorem firstNormGenerator_source_unscaled :
    IsNormGeneratorValue (S.sourceJordan.component 0).space
      (S.sourceJordan.component 0).lattice
      (S.firstScale * S.firstNormGenerator) := by
  have h := S.firstNormGenerator_source.unscaleQuadraticUnit
  simpa only [sourceFirstNormalized, inv_inv] using h

/-- The unscaled chosen first generator also generates the first fundamental
norm ideal, because the rank-four Jordan splitting is saturated. -/
theorem firstNormGenerator_fundamental :
    IsNormGeneratorValue
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (S.sourceJordan.fundamentalLattice 0)
      (S.firstScale * S.firstNormGenerator) := by
  exact isNormGeneratorValue_of_normGroupSet_eq
    S.firstNormGenerator_source_unscaled
    (S.sourceJordan_isSaturated 0)
    (S.sourceJordan.exists_fundamentalNormGenerator 0)

/-- The order of the normalized first generator is the first fundamental
norm order minus the first scale order. -/
theorem firstNormGenerator_order :
    ordUnit K S.firstNormGenerator =
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) -
        S.sourceJordan.fundamentalScaleOrder 0 := by
  have hideal : principalIdeal (K := K)
        ((S.firstScale * S.firstNormGenerator : Kˣ) : K) =
      principalIdeal (K := K)
        (S.sourceJordan.fundamentalNormGenerator 0 : K) :=
    S.firstNormGenerator_fundamental.2.symm.trans
      (S.sourceJordan.fundamentalNormGenerator_spec 0).2
  have hord :=
    (principalIdeal_eq_iff_ordUnit_eq
      (S.firstScale * S.firstNormGenerator)
      (S.sourceJordan.fundamentalNormGenerator 0)).mp hideal
  unfold fundamentalScaleOrder
  simp only [sourceJordan_scaleGenerator]
  rw [ordUnit_mul] at hord
  apply eq_sub_iff_add_eq.mpr
  simpa only [firstScale, add_comm] using hord

/-- Normalizing the first Jordan scale subtracts that scale order from the
intrinsic first fundamental weight order. -/
theorem sourceFirstNormalized_weightIdealOrder_eq_fundamental :
    weightIdealOrder S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice =
      S.sourceJordan.fundamentalWeightOrder 0 -
        S.sourceJordan.fundamentalScaleOrder 0 := by
  have hcomponentWeight :
      weightIdeal (S.sourceJordan.component 0).space
          (S.sourceJordan.component 0).lattice =
        S.sourceJordan.fundamentalWeightIdeal 0 := by
    exact weightIdeal_eq_of_normGroupSet_eq_of_twoScaleIdeal_eq
      S.firstNormGenerator_source_unscaled
      ⟨S.firstScale * S.firstNormGenerator,
        S.firstNormGenerator_fundamental⟩
      (S.sourceJordan_isSaturated 0)
      (S.sourceJordan.componentTwoScaleIdeal_eq_fundamental 0)
  have hcomponentOrder :
      weightIdealOrder (S.sourceJordan.component 0).space
          (S.sourceJordan.component 0).lattice =
        S.sourceJordan.fundamentalWeightOrder 0 := by
    apply powerIdeal_order_eq_of_eq (K := K)
    calc
      powerIdeal (K := K)
          (weightIdealOrder (S.sourceJordan.component 0).space
            (S.sourceJordan.component 0).lattice) =
          weightIdeal (S.sourceJordan.component 0).space
            (S.sourceJordan.component 0).lattice :=
        (weightIdeal_eq_powerIdeal _ _).symm
      _ = S.sourceJordan.fundamentalWeightIdeal 0 := hcomponentWeight
      _ = powerIdeal (K := K)
          (S.sourceJordan.fundamentalWeightOrder 0) := by
        unfold fundamentalWeightIdeal fundamentalWeightOrder
        exact weightIdeal_eq_powerIdeal _ _
  have hrescale := weightIdealOrder_rescaleQuadraticUnit
    (S.firstScale * S.firstNormGenerator) S.firstScale⁻¹
      S.firstNormGenerator_source_unscaled
  change weightIdealOrder S.sourceFirstNormalized
      (S.sourceJordan.component 0).lattice = _
  rw [hrescale, ordUnit_inv, hcomponentOrder]
  unfold fundamentalScaleOrder
  simp only [S.sourceJordan_scaleGenerator, firstScale]
  omega

/-- The weight order of the normalized unimodular first component is at
most the ramification index, since its weight contains twice its scale. -/
theorem sourceFirstNormalized_weightIdealOrder_le_ramificationIndex :
    weightIdealOrder S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice ≤
      (ramificationIndex K : Int) := by
  have h := twoScaleIdeal_le_weightIdeal S.sourceFirstNormalized
    (S.sourceJordan.component 0).lattice
  rw [twoScaleIdeal_eq_principalIdeal_two_of_unimodular
    S.sourceFirstNormalized_unimodular
      (by rw [S.sourceFirstNormalized_finrank]; omega),
    weightIdeal_eq_powerIdeal] at h
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  have htwo : principalIdeal (K := K) (2 : K) =
      powerIdeal (K := K) (ramificationIndex K : Int) := by
    calc
      principalIdeal (K := K) (2 : K) =
          principalIdeal (K := K) (two : K) := rfl
      _ = powerIdeal (K := K) (ordUnit K two) :=
        principalIdeal_eq_powerIdeal two
      _ = powerIdeal (K := K) (ramificationIndex K : Int) := by
        congr 1
        apply WithTop.coe_injective
        rw [coe_ordUnit]
        exact (ramificationIndex_spec K).symm
  rw [htwo, powerIdeal_le_iff] at h
  exact h

/-- The normalized second generator is obtained from the second fundamental
norm generator by the same first-scale normalization. -/
noncomputable def secondNormalizedNormGenerator : Kˣ :=
  S.firstScale⁻¹ * S.sourceJordan.fundamentalNormGenerator 1

theorem secondNormalizedNormGenerator_source :
    IsNormGeneratorValue S.sourceSecondNormalized
      (S.sourceJordan.component 1).lattice
      S.secondNormalizedNormGenerator := by
  have hcomponent : IsNormGeneratorValue
      (S.sourceJordan.component 1).space
      (S.sourceJordan.component 1).lattice
      (S.sourceJordan.fundamentalNormGenerator 1) :=
    isNormGeneratorValue_of_normGroupSet_eq
      (S.sourceJordan.fundamentalNormGenerator_spec 1)
      (S.sourceJordan_isSaturated 1).symm
      (S.exists_source_component_normGeneratorValue 1)
  simpa only [sourceSecondNormalized, secondNormalizedNormGenerator] using
    hcomponent.rescaleQuadraticUnit S.firstScale⁻¹

theorem secondNormalizedNormGenerator_target :
    IsNormGeneratorValue S.targetSecondNormalized
      (S.targetJordan.component 1).lattice
      S.secondNormalizedNormGenerator := by
  exact isNormGeneratorValue_of_normGroupSet_eq
    S.secondNormalizedNormGenerator_source
    S.secondNormalized_normGroupSet_eq
    S.exists_target_normalizedSecond_normGeneratorValue

/-- Normalize the explicitly chosen second fundamental norm generator by
the first Jordan scale.  This is the paper's fixed scalar `a₂`; keeping it
explicit ensures that 93:28(ii) and the later 93:19 exchange use the same
line coefficient. -/
noncomputable def secondNormalizedNormGeneratorWith
    (A : FundamentalNormGeneratorChoice S.sourceJordan) : Kˣ :=
  S.firstScale⁻¹ * A.value 1

theorem secondNormalizedNormGeneratorWith_source
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    IsNormGeneratorValue S.sourceSecondNormalized
      (S.sourceJordan.component 1).lattice
      (S.secondNormalizedNormGeneratorWith A) := by
  have hcomponent : IsNormGeneratorValue
      (S.sourceJordan.component 1).space
      (S.sourceJordan.component 1).lattice (A.value 1) :=
    isNormGeneratorValue_of_normGroupSet_eq
      (A.spec 1) (S.sourceJordan_isSaturated 1).symm
      (S.exists_source_component_normGeneratorValue 1)
  simpa only [sourceSecondNormalized,
    secondNormalizedNormGeneratorWith] using
      hcomponent.rescaleQuadraticUnit S.firstScale⁻¹

theorem secondNormalizedNormGeneratorWith_target
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    IsNormGeneratorValue S.targetSecondNormalized
      (S.targetJordan.component 1).lattice
      (S.secondNormalizedNormGeneratorWith A) := by
  exact isNormGeneratorValue_of_normGroupSet_eq
    (S.secondNormalizedNormGeneratorWith_source A)
    S.secondNormalized_normGroupSet_eq
    S.exists_target_normalizedSecond_normGeneratorValue

/-- The two normalized second components have the same doubled scale.
Both are modular for the common relative second scale. -/
theorem secondNormalized_twoScaleIdeal_eq :
    twoScaleIdeal S.sourceSecondNormalized
        (S.sourceJordan.component 1).lattice =
      twoScaleIdeal S.targetSecondNormalized
        (S.targetJordan.component 1).lattice := by
  rw [Omeara9319ExchangeSetup.twoScaleIdeal_eq_principalIdeal_two_mul_of_modular
      S.sourceSecondNormalized_modular
      (by rw [S.sourceSecondNormalized_finrank]; omega),
    Omeara9319ExchangeSetup.twoScaleIdeal_eq_principalIdeal_two_mul_of_modular
      S.targetSecondNormalized_modular
      (by rw [S.targetSecondNormalized_finrank]; omega)]

/-- Equality of normalized second norm groups and doubled scales also
identifies their weight ideals. -/
theorem secondNormalized_weightIdeal_eq
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    weightIdeal S.sourceSecondNormalized
        (S.sourceJordan.component 1).lattice =
      weightIdeal S.targetSecondNormalized
        (S.targetJordan.component 1).lattice := by
  exact weightIdeal_eq_of_normGroupSet_eq_of_twoScaleIdeal_eq
    (S.secondNormalizedNormGeneratorWith_source A)
    ⟨S.secondNormalizedNormGeneratorWith A,
      S.secondNormalizedNormGeneratorWith_target A⟩
    S.secondNormalized_normGroupSet_eq S.secondNormalized_twoScaleIdeal_eq

/-- Consequently the normalized second weight orders agree. -/
theorem secondNormalized_weightIdealOrder_eq
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    weightIdealOrder S.sourceSecondNormalized
        (S.sourceJordan.component 1).lattice =
      weightIdealOrder S.targetSecondNormalized
        (S.targetJordan.component 1).lattice := by
  apply powerIdeal_order_eq_of_eq (K := K)
  calc
    powerIdeal (K := K)
        (weightIdealOrder S.sourceSecondNormalized
          (S.sourceJordan.component 1).lattice) =
        weightIdeal S.sourceSecondNormalized
          (S.sourceJordan.component 1).lattice :=
      (weightIdeal_eq_powerIdeal _ _).symm
    _ = weightIdeal S.targetSecondNormalized
          (S.targetJordan.component 1).lattice :=
      S.secondNormalized_weightIdeal_eq A
    _ = powerIdeal (K := K)
        (weightIdealOrder S.targetSecondNormalized
          (S.targetJordan.component 1).lattice) :=
      weightIdeal_eq_powerIdeal _ _

/-- Normalizing the second component by the first scale subtracts the
first fundamental scale order from its intrinsic weight order. -/
theorem sourceSecondNormalized_weightIdealOrder_eq_fundamental :
    weightIdealOrder S.sourceSecondNormalized
        (S.sourceJordan.component 1).lattice =
      S.sourceJordan.fundamentalWeightOrder 1 -
        S.sourceJordan.fundamentalScaleOrder 0 := by
  have hcomponentNorm : IsNormGeneratorValue
      (S.sourceJordan.component 1).space
      (S.sourceJordan.component 1).lattice
      (S.sourceJordan.fundamentalNormGenerator 1) :=
    isNormGeneratorValue_of_normGroupSet_eq
      (S.sourceJordan.fundamentalNormGenerator_spec 1)
      (S.sourceJordan_isSaturated 1).symm
      (S.exists_source_component_normGeneratorValue 1)
  have hcomponentWeight :
      weightIdeal (S.sourceJordan.component 1).space
          (S.sourceJordan.component 1).lattice =
        S.sourceJordan.fundamentalWeightIdeal 1 := by
    exact weightIdeal_eq_of_normGroupSet_eq_of_twoScaleIdeal_eq
      hcomponentNorm
      ⟨S.sourceJordan.fundamentalNormGenerator 1,
        S.sourceJordan.fundamentalNormGenerator_spec 1⟩
      (S.sourceJordan_isSaturated 1)
      (S.sourceJordan.componentTwoScaleIdeal_eq_fundamental 1)
  have hcomponentOrder :
      weightIdealOrder (S.sourceJordan.component 1).space
          (S.sourceJordan.component 1).lattice =
        S.sourceJordan.fundamentalWeightOrder 1 := by
    apply powerIdeal_order_eq_of_eq (K := K)
    calc
      powerIdeal (K := K)
          (weightIdealOrder (S.sourceJordan.component 1).space
            (S.sourceJordan.component 1).lattice) =
          weightIdeal (S.sourceJordan.component 1).space
            (S.sourceJordan.component 1).lattice :=
        (weightIdeal_eq_powerIdeal _ _).symm
      _ = S.sourceJordan.fundamentalWeightIdeal 1 := hcomponentWeight
      _ = powerIdeal (K := K)
          (S.sourceJordan.fundamentalWeightOrder 1) := by
        unfold fundamentalWeightIdeal fundamentalWeightOrder
        exact weightIdeal_eq_powerIdeal _ _
  have hrescale := weightIdealOrder_rescaleQuadraticUnit
    (S.sourceJordan.fundamentalNormGenerator 1) S.firstScale⁻¹
      hcomponentNorm
  change weightIdealOrder S.sourceSecondNormalized
      (S.sourceJordan.component 1).lattice = _
  rw [hrescale, ordUnit_inv, hcomponentOrder]
  unfold fundamentalScaleOrder
  simp only [S.sourceJordan_scaleGenerator,
    Omeara9328RankFourReductionSystem.firstScale]
  omega

/-- Any coherent choice has the same normalized second norm order as the
canonical choice, since both generate the same norm ideal. -/
theorem secondNormalizedNormGeneratorWith_order_eq
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.secondNormalizedNormGenerator := by
  have hchoice : ordUnit K (A.value 1) =
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 1) := by
    apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact (A.spec 1).2.symm.trans
      (S.sourceJordan.fundamentalNormGenerator_spec 1).2
  unfold secondNormalizedNormGeneratorWith
    secondNormalizedNormGenerator
  simp only [ordUnit_mul, ordUnit_inv]
  rw [hchoice]

/-- The order of the normalized second generator is the second fundamental
norm order minus the first scale order. -/
theorem secondNormalizedNormGenerator_order :
    ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 1) -
        S.sourceJordan.fundamentalScaleOrder 0 := by
  unfold secondNormalizedNormGenerator fundamentalScaleOrder
  simp only [ordUnit_mul, ordUnit_inv, firstScale,
    sourceJordan_scaleGenerator]
  omega

/-- O'Meara's normalized gap `U₂-U₁` is intrinsic: it is the gap of
the first two fundamental norm-generator orders. -/
theorem normalizedNormOrderGap_eq_fundamentalGap :
    ordUnit K S.secondNormalizedNormGenerator -
        ordUnit K S.firstNormGenerator =
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 1) -
        ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) := by
  rw [S.secondNormalizedNormGenerator_order,
    S.firstNormGenerator_order]
  omega

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
