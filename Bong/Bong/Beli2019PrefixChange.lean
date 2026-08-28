/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006SectionFourInvariants
import Bong.Bong.Basis

/-!
# Beli (2019), prefix-change bounds

This file discharges the temporary `Beli2006PrefixChangeLaws` interface.  At
internal boundaries the estimate is condition (iii) of the already isolated
classification theorem.  At the two exterior boundaries it follows from the
empty product and from the square of the full change-of-basis determinant.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- A prefix beyond the rank is the complete value product. -/
theorem prefixProduct_eq_valueProduct_of_rank_le (b : GoodBONG q L n)
    (i : Nat) (hi : n ≤ i) :
    b.prefixProduct i = b.toBONG.valueProduct := by
  unfold prefixProduct BONG.valueProduct BONG.prefixProduct
  apply Finset.prod_congr
  · ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro
      exact j.isLt
    · intro
      omega
  · intros
    rfl

/-- The product of the complete value products of two BONG bases is a square. -/
theorem isSquare_valueProduct_mul {M : Lattice K V}
    (a : GoodBONG q L n) (a' : GoodBONG q M n) :
    IsSquare (a.toBONG.valueProduct * a'.toBONG.valueProduct) := by
  rcases BONG.exists_valueProduct_eq_mul_square a.toBONG a'.toBONG with
    ⟨p, hp⟩
  refine ⟨a.toBONG.valueProduct * p, ?_⟩
  rw [hp]
  simp only [pow_two]
  ac_rfl

/-- The complete comparison product has infinite quadratic defect. -/
theorem defectOrder_fullPrefixProduct_mul_eq_top
    {M : Lattice K V} (a : GoodBONG q L n) (a' : GoodBONG q M n) :
    defectOrder (K := K)
        (a.toBONG.valueProduct * a'.toBONG.valueProduct) = ⊤ := by
  unfold defectOrder
  rw [quadraticDefect_eq_top_of_isSquare K (isSquare_valueProduct_mul a a')]
  rfl

/-- The prefix-change estimate derived from classification and determinant
change of basis, including both endpoint conventions. -/
theorem prefixChangeDefectBound_of_classification
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a a' : GoodBONG q L (n + 1)) (i : Nat) :
    a.prefixAlphaCap i ≤
      defectOrder (K := K) (a.prefixProduct i * a'.prefixProduct i) := by
  by_cases hinternal : 0 < i ∧ i < n + 1
  · have hconditions :=
      (isometric_iff_classificationConditions
        (QuadraticSpace.isIsometric_refl q) a a').mp
          (Lattice.isIsometric_refl q L)
    have hbound := hconditions.prefixDefectBounds ⟨i - 1, by omega⟩
    rw [a.prefixAlphaCap_of_internal hinternal.1 hinternal.2]
    simpa only [comparisonPrefixProduct, Nat.sub_add_cancel hinternal.1]
      using hbound
  · by_cases hi0 : i = 0
    · subst i
      rw [a.prefixAlphaCap_zero]
      simp only [prefixProduct, BONG.prefixProduct_zero, one_mul]
      rw [defectOrder_one]
    · have hirank : n + 1 ≤ i := by omega
      rw [prefixAlphaCap]
      simp only [hinternal, ↓reduceDIte]
      rw [a.prefixProduct_eq_valueProduct_of_rank_le i hirank,
        a'.prefixProduct_eq_valueProduct_of_rank_le i hirank,
        defectOrder_fullPrefixProduct_mul_eq_top]

end BONG.GoodBONG

/-- No extra prefix-change law is needed once classification is available. -/
noncomputable instance prefixChangeLawsOfClassification
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [GoodBONGClassificationLaws.{u, v, v} K] :
    Beli2006PrefixChangeLaws.{u, v} K where
  prefixChangeDefectBound :=
    BONG.GoodBONG.prefixChangeDefectBound_of_classification

end Bong
