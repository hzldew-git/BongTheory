/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma62
import Bong.Bong.BinaryNormGeneratorGroup
import Bong.Bong.Structural

/-!
# Beli (2003), Definition 11 and Lemma 6.3

Definition 11 enlarges the binary norm-generator group `g(a)` to `g'(a)`.
Lemma 6.3 compares these groups with all norm-generator value ratios of a
higher-rank lattice.
-/

namespace Bong

open Dyadic

universe u v

namespace Dyadic

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Beli (2003), Definition 11: the upper norm-generator group `g'(a)`. -/
noncomputable def beliNormGeneratorUpperGroup (a : Kˣ) :
    Subgroup (ValuationUnitClass K) :=
  if 2 * (ramificationIndex K : Int) < ordUnit K a then
    ⊥
  else if 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞) then
    principalUnitValuationClassSubgroup K
      (beliLowDefectExponent K a)
  else
    principalUnitValuationClassSubgroup K
      (beliHighDefectExponent K a)

/-- Definition 11(I). -/
theorem beliNormGeneratorUpperGroup_of_two_e_lt
    (a : Kˣ) (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    beliNormGeneratorUpperGroup K a = ⊥ := by
  simp [beliNormGeneratorUpperGroup, hR]

/-- Definition 11(II)(ii). -/
theorem beliNormGeneratorUpperGroup_of_low_defect
    (a : Kˣ)
    (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hd : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)) :
    beliNormGeneratorUpperGroup K a =
      principalUnitValuationClassSubgroup K
        (beliLowDefectExponent K a) := by
  simp [beliNormGeneratorUpperGroup, hR, hd]

/-- Definition 11(II)(iii). -/
theorem beliNormGeneratorUpperGroup_of_high_defect
    (a : Kˣ)
    (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hd : ¬2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)) :
    beliNormGeneratorUpperGroup K a =
      principalUnitValuationClassSubgroup K
        (beliHighDefectExponent K a) := by
  simp [beliNormGeneratorUpperGroup, hR, hd]

/-- The group `g(a)` is always contained in `g'(a)`. -/
theorem beliNormGeneratorGroup_le_upperGroup (a : Kˣ) :
    beliNormGeneratorGroup K a ≤ beliNormGeneratorUpperGroup K a := by
  unfold beliNormGeneratorGroup beliNormGeneratorUpperGroup
  split_ifs <;> simp_all

end Dyadic

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

variable [BinaryNormGeneratorLocalLaws.{u, v} K]

/-- The first binary group is represented by norm generators of the full
lattice.  This is the left inclusion in Lemma 6.3(i). -/
theorem beliNormGeneratorGroup_subset_normGeneratorValueRatioClassSet
    (b : BONG V q L (n + 2)) :
    (beliNormGeneratorGroup K (b.adjacentParameter 0 (by simp)) :
        Set (ValuationUnitClass K)) ⊆
      b.normGeneratorValueRatioClassSet := by
  let w := b.prefixWitness 2 (by omega)
  have hparameter : w.bong.binaryParameter =
      b.adjacentParameter 0 (by simp) := by
    unfold binaryParameter adjacentParameter
    rw [w.valueUnit_eq, w.valueUnit_eq]
    rfl
  intro c hc
  have hcBinary : c ∈
      beliNormGeneratorGroup K w.bong.binaryParameter := by
    rwa [hparameter]
  rcases w.bong.exists_normGenerator_of_mem_beliNormGeneratorGroup
      hcBinary with ⟨y, hy, hclass⟩
  have hyFull : Lattice.IsNormGenerator q L (y : V) := by
    refine ⟨w.contained y hy.mem, ?_⟩
    have hfull : Lattice.normIdeal q L =
        Lattice.principalIdeal (K := K) (b.value 0) := by
      simpa [b.value_zero_eq_quadratic_head] using
        b.head_isNormGenerator.normIdeal_eq
    have hsegment :
        Lattice.principalIdeal (K := K) (q.quadratic (y : V)) =
          Lattice.principalIdeal (K := K) (b.value 0) := by
      calc
        _ = Lattice.normIdeal
              (q.restrict w.carrier w.nondegenerate) w.lattice :=
            hy.normIdeal_eq.symm
        _ = Lattice.principalIdeal (K := K)
              ((q.restrict w.carrier w.nondegenerate).quadratic
                w.bong.head) :=
            w.bong.head_isNormGenerator.normIdeal_eq
        _ = Lattice.principalIdeal (K := K) (b.value 0) := by
          rw [← w.bong.value_zero_eq_quadratic_head, w.value_eq]
          rfl
    exact hfull.trans hsegment.symm
  refine ⟨(y : V), hyFull, ?_⟩
  have hratio :
      b.normGeneratorValueRatioClass (y : V) hyFull =
        w.bong.normGeneratorValueRatioClass y hy := by
    unfold normGeneratorValueRatioClass
      normGeneratorValueRatioValuationUnit normGeneratorValueRatioUnit
    apply congrArg (valuationUnitClassHom K)
    apply Subtype.ext
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mk0, coe_valueUnit]
    rw [w.value_eq]
    rfl
  exact hratio.trans hclass

end BONG

/-- The value-set bounds from Beli (2003), Lemma 6.3.  The lower inclusion
is proved above from the binary theorem; this interface contains only the two
higher-rank value estimates.  It has no default instance. -/
class BeliLemma63Laws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  valueRatioClassSet_subset_upper
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 2)) (w : BONG.HeadInverseRescaleWitness b)
    (hB : b.HasPropertyBOrInverse w) :
    b.normGeneratorValueRatioClassSet ⊆
      (beliNormGeneratorUpperGroup K
        (b.adjacentParameter 0 (by simp)) : Set (ValuationUnitClass K))
  valueRatioClassSet_subset_group_of_propertyB
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 2)) (hB : b.HasPropertyB) :
    b.normGeneratorValueRatioClassSet ⊆
      (beliNormGeneratorGroup K
        (b.adjacentParameter 0 (by simp)) : Set (ValuationUnitClass K))

namespace BONG

variable [BinaryNormGeneratorLocalLaws.{u, v} K]
  [BeliLemma63Laws.{u, v} K]

/-- Beli (2003), Lemma 6.3(i). -/
theorem beliLemma63_i (b : BONG V q L (n + 2))
    (w : b.HeadInverseRescaleWitness) (hB : b.HasPropertyBOrInverse w) :
    (beliNormGeneratorGroup K (b.adjacentParameter 0 (by simp)) :
        Set (ValuationUnitClass K)) ⊆
        b.normGeneratorValueRatioClassSet ∧
      b.normGeneratorValueRatioClassSet ⊆
        (beliNormGeneratorUpperGroup K
          (b.adjacentParameter 0 (by simp)) :
            Set (ValuationUnitClass K)) :=
  ⟨b.beliNormGeneratorGroup_subset_normGeneratorValueRatioClassSet,
    BeliLemma63Laws.valueRatioClassSet_subset_upper b w hB⟩

/-- Beli (2003), Lemma 6.3(ii). -/
theorem beliLemma63_ii (b : BONG V q L (n + 2))
    (hB : b.HasPropertyB) :
    b.normGeneratorValueRatioClassSet =
      (beliNormGeneratorGroup K
        (b.adjacentParameter 0 (by simp)) : Set (ValuationUnitClass K)) :=
  Set.Subset.antisymm
    (BeliLemma63Laws.valueRatioClassSet_subset_group_of_propertyB b hB)
    b.beliNormGeneratorGroup_subset_normGeneratorValueRatioClassSet

end BONG

end Bong
