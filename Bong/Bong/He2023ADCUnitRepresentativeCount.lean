/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022PublishedTestingSet

/-!
# Finite representatives and the unit square-class quotient

This file removes the representative-dependent part of the cardinality input
used in He (2025), Corollary 7.21.  A complete irredundant system `U` is
canonically equivalent, as a finite type, to
`O_F^times / O_F^{times 2}`.  Consequently its size depends only on the
unit square-class quotient and not on the chosen normalized representatives.

The arithmetic formula for the quotient itself is proved separately from the
principal-unit filtration in `Bong.Dyadic.UnitSquareClassCount`.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The unit square class selected by one entry of a published complete
representative system. -/
noncomputable def heADC2025UnitRepresentativeClass
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (i : I) : ValuationUnitClass K :=
  valuationUnitClassHom K ⟨U i, hU.isUnit i⟩

theorem heADC2025UnitRepresentativeClass_injective
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    Function.Injective (heADC2025UnitRepresentativeClass U hU) := by
  intro i j hij
  change QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K))
      ⟨U i, hU.isUnit i⟩ =
    QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K))
      ⟨U j, hU.isUnit j⟩ at hij
  rw [QuotientGroup.mk'_eq_mk'] at hij
  obtain ⟨t, htSquare, hitj⟩ := hij
  have htField : IsSquare (t : Kˣ) := by
    change (t : Kˣ) ∈ Subgroup.square Kˣ
    apply valuationUnitSubgroup_square_map_le_square K
    exact ⟨t, htSquare, rfl⟩
  have hiSquare : IsSquare (U i ^ 2) := ⟨U i, pow_two (U i)⟩
  apply hU.irredundant
  have hproduct : IsSquare (U i ^ 2 * (t : Kˣ)) :=
    hiSquare.mul htField
  have hitjField : U i * (t : Kˣ) = U j := by
    exact congrArg Subtype.val hitj
  rw [← hitjField]
  simpa only [pow_two, mul_assoc] using hproduct

theorem heADC2025UnitRepresentativeClass_surjective
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    Function.Surjective (heADC2025UnitRepresentativeClass U hU) := by
  intro c
  obtain ⟨u, rfl⟩ := Quotient.exists_rep c
  obtain ⟨i, s, hsUnit, hus⟩ := hU.complete (u : Kˣ) u.property
  refine ⟨i, ?_⟩
  change QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K))
      ⟨U i, hU.isUnit i⟩ =
    QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K)) u
  rw [QuotientGroup.mk'_eq_mk']
  let su : valuationUnitSubgroup K := ⟨s, hsUnit⟩
  refine ⟨su ^ 2, (Subgroup.mem_square).2 ⟨su, pow_two su⟩, ?_⟩
  apply Subtype.ext
  exact hus.symm

/-- A complete irredundant normalized representative system is exactly a
finite presentation of the unit square-class quotient. -/
noncomputable def heADC2025UnitRepresentativeEquiv
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    I ≃ ValuationUnitClass K :=
  Equiv.ofBijective (heADC2025UnitRepresentativeClass U hU)
    ⟨heADC2025UnitRepresentativeClass_injective U hU,
      heADC2025UnitRepresentativeClass_surjective U hU⟩

/-- The number of representatives is the intrinsic cardinality of
`O_F^times / O_F^{times 2}`. -/
theorem card_heHuCompleteUnitRepresentativeSystem
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    Fintype.card I = Nat.card (ValuationUnitClass K) := by
  rw [Fintype.card_eq_nat_card]
  exact Nat.card_congr (heADC2025UnitRepresentativeEquiv U hU)

end Bong
