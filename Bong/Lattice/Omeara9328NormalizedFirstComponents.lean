/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328RankFourConditionTransfer
import Bong.Lattice.Omeara9318RankFourOdd
import Bong.Lattice.Omeara9318EvenParity

/-!
# Normalized first components in the rank-four reduction of O'Meara 93:28

After Step 2 of the proof, both first components have rank four and the
same scale and norm group.  We normalize their common scale to one and make
one norm-generator choice on the source.  The same scalar is then proved to
be a norm generator on the target, and the two normalized weight ideals and
parities agree.  This is the coherent input for the 93:18(iii)/(vi) models
used in Steps 4--7.
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

/-- The common scale of the two first residual components. -/
noncomputable abbrev firstScale
    (_S : Omeara9328RankFourReductionSystem J H) : Kˣ :=
  J.scaleGenerator 0

/-- Source first component after normalizing its modular scale to one. -/
noncomputable abbrev sourceFirstNormalized :
    QuadraticSpace K (S.sourceJordan.component 0).carrier :=
  (S.sourceJordan.component 0).space.rescaleUnit S.firstScale⁻¹

/-- Target first component after the same normalization. -/
noncomputable abbrev targetFirstNormalized :
    QuadraticSpace K (S.targetJordan.component 0).carrier :=
  (S.targetJordan.component 0).space.rescaleUnit S.firstScale⁻¹

theorem sourceFirstNormalized_unimodular :
    IsUnimodular S.sourceFirstNormalized
      (S.sourceJordan.component 0).lattice := by
  have h := (S.sourceJordan.modular 0).isUnimodular_rescaleQuadraticInverse
  simpa only [sourceFirstNormalized, firstScale,
    sourceJordan_scaleGenerator] using h

theorem targetFirstNormalized_unimodular :
    IsUnimodular S.targetFirstNormalized
      (S.targetJordan.component 0).lattice := by
  have h := (S.targetJordan.modular 0).isUnimodular_rescaleQuadraticInverse
  simpa only [targetFirstNormalized, firstScale,
    targetJordan_scaleGenerator] using h

theorem sourceFirstNormalized_finrank :
    finrank K (S.sourceJordan.component 0).carrier = 4 := by
  simpa only [componentRank] using S.sourceJordan_componentRank 0

theorem targetFirstNormalized_finrank :
    finrank K (S.targetJordan.component 0).carrier = 4 := by
  simpa only [componentRank] using S.targetJordan_componentRank 0

/-- Common normalized norm group of the two first components. -/
theorem firstNormalized_normGroupSet_eq :
    normGroupSet S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice =
      normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice := by
  ext z
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff,
    mem_normGroupSet_rescaleQuadraticUnit_iff,
    S.sourceJordan_component_normGroupSet,
    S.targetJordan_component_normGroupSet]

/-- A chosen vector realizing a norm generator on the normalized source
first component. -/
noncomputable def sourceFirstNormGeneratorVector :
    (S.sourceJordan.component 0).carrier :=
  Classical.choose <| exists_isNormGenerator_of_finrank_pos
    S.sourceFirstNormalized (S.sourceJordan.component 0).lattice
      (by rw [S.sourceFirstNormalized_finrank]; omega)

theorem sourceFirstNormGeneratorVector_spec :
    IsNormGenerator S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice
        S.sourceFirstNormGeneratorVector ∧
      S.sourceFirstNormalized.IsAnisotropic
        S.sourceFirstNormGeneratorVector :=
  Classical.choose_spec <| exists_isNormGenerator_of_finrank_pos
    S.sourceFirstNormalized (S.sourceJordan.component 0).lattice
      (by rw [S.sourceFirstNormalized_finrank]; omega)

/-- The coherent normalized norm generator used on both sides. -/
noncomputable def firstNormGenerator : Kˣ :=
  Units.mk0
    (S.sourceFirstNormalized.quadratic S.sourceFirstNormGeneratorVector)
    (S.sourceFirstNormGeneratorVector_spec).2

theorem firstNormGenerator_source :
    IsNormGeneratorValue S.sourceFirstNormalized
      (S.sourceJordan.component 0).lattice S.firstNormGenerator :=
  (S.sourceFirstNormGeneratorVector_spec).1.isNormGeneratorValue
    (S.sourceFirstNormGeneratorVector_spec).2

theorem firstNormGenerator_target :
    IsNormGeneratorValue S.targetFirstNormalized
      (S.targetJordan.component 0).lattice S.firstNormGenerator := by
  apply isNormGeneratorValue_of_normGroupSet_eq
    (S.firstNormGenerator_source) (S.firstNormalized_normGroupSet_eq)
  let hxExists := exists_isNormGenerator_of_finrank_pos
    S.targetFirstNormalized (S.targetJordan.component 0).lattice
      (by rw [S.targetFirstNormalized_finrank]; omega)
  let x := Classical.choose hxExists
  have hx := Classical.choose_spec hxExists
  let b : Kˣ := Units.mk0 (S.targetFirstNormalized.quadratic x) hx.2
  exact ⟨b, hx.1.isNormGeneratorValue hx.2⟩

theorem firstNormalized_twoScaleIdeal_eq :
    twoScaleIdeal S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice =
      twoScaleIdeal S.targetFirstNormalized
        (S.targetJordan.component 0).lattice := by
  rw [twoScaleIdeal_eq_principalIdeal_two_of_unimodular
      S.sourceFirstNormalized_unimodular
      (by rw [S.sourceFirstNormalized_finrank]; omega),
    twoScaleIdeal_eq_principalIdeal_two_of_unimodular
      S.targetFirstNormalized_unimodular
      (by rw [S.targetFirstNormalized_finrank]; omega)]

theorem firstNormalized_weightIdeal_eq :
    weightIdeal S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice =
      weightIdeal S.targetFirstNormalized
        (S.targetJordan.component 0).lattice := by
  exact weightIdeal_eq_of_normGroupSet_eq_of_twoScaleIdeal_eq
    S.firstNormGenerator_source
    ⟨S.firstNormGenerator, S.firstNormGenerator_target⟩
    S.firstNormalized_normGroupSet_eq S.firstNormalized_twoScaleIdeal_eq

theorem firstNormalized_weightIdealOrder_eq :
    weightIdealOrder S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice =
      weightIdealOrder S.targetFirstNormalized
        (S.targetJordan.component 0).lattice := by
  apply powerIdeal_order_eq_of_eq (K := K)
  calc
    powerIdeal (K := K)
        (weightIdealOrder S.sourceFirstNormalized
          (S.sourceJordan.component 0).lattice) =
        weightIdeal S.sourceFirstNormalized
          (S.sourceJordan.component 0).lattice :=
      (weightIdeal_eq_powerIdeal _ _).symm
    _ = weightIdeal S.targetFirstNormalized
          (S.targetJordan.component 0).lattice :=
      S.firstNormalized_weightIdeal_eq
    _ = powerIdeal (K := K)
        (weightIdealOrder S.targetFirstNormalized
          (S.targetJordan.component 0).lattice) :=
      weightIdeal_eq_powerIdeal _ _

/-- The parity used by 93:18 is literally common to the two normalized
first components. -/
theorem firstNormalized_parity_iff :
    Odd (ordUnit K S.firstNormGenerator +
      weightIdealOrder S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice) ↔
    Odd (ordUnit K S.firstNormGenerator +
      weightIdealOrder S.targetFirstNormalized
        (S.targetJordan.component 0).lattice) := by
  rw [S.firstNormalized_weightIdealOrder_eq]

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
