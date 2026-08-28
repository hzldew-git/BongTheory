/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Corollary311
import Bong.Bong.GoodBONGScalarAgreement

/-!
# Scalar transport of Beli's representation conditions

All four conditions in Beli's representation criterion are expressions in
the scalar values of the two selected good BONGs.  This file proves that the
conditions transport simultaneously when both scalar sequences are moved to
possibly different ambient quadratic spaces.

Unlike Corollary 3.11, this result does not change the good BONG of a fixed
lattice.  Consequently it needs neither classification laws nor a local
representation interface: equality of the coefficient families transports
the prefix diagonal representations literally.
-/

namespace Bong

open Dyadic

universe u v w x y

namespace BONG.GoodBONG
namespace ScalarAgreement

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {X : Type x} [AddCommGroup X] [Module K X]
  {Y : Type y} [AddCommGroup Y] [Module K Y]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {q' : QuadraticSpace K X} {r' : QuadraticSpace K Y}
  {L : Lattice K V} {M : Lattice K W}
  {L' : Lattice K X} {M' : Lattice K Y}
  {m n : Nat}
  {a : GoodBONG q L (m + 1)} {a' : GoodBONG q' L' (m + 1)}
  {b : GoodBONG r M (n + 1)} {b' : GoodBONG r' M' (n + 1)}

/-- Capped prefix defects depend only on the two scalar sequences. -/
theorem truncatedPrefixDefect_eq
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (epsilon : Kˣ) (i j : Nat) :
    a.truncatedPrefixDefect b epsilon i j =
      a'.truncatedPrefixDefect b' epsilon i j := by
  unfold truncatedPrefixDefect
  rw [ha.prefixProduct_eq i, hb.prefixProduct_eq j,
    ha.prefixAlphaCap_eq i, hb.prefixAlphaCap_eq j]

/-- The half-gap candidate for `A_i` is scalar invariant. -/
theorem representationHalfGap_eq
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationHalfGap b i = a'.representationHalfGap b' i := by
  unfold representationHalfGap
  rw [ha.order_eq, hb.order_eq]

/-- The primary defect candidate for `A_i` is scalar invariant. -/
theorem representationPrimaryDefect_eq
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationPrimaryDefect b i =
      a'.representationPrimaryDefect b' i := by
  unfold representationPrimaryDefect
  rw [ha.order_eq, hb.order_eq,
    ha.truncatedPrefixDefect_eq hb (-1) (i.val + 1) (i.val - 1)]

/-- The secondary defect candidate for `A_i` is scalar invariant. -/
theorem representationSecondaryDefect_eq
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) :
    a.representationSecondaryDefect b i hi =
      a'.representationSecondaryDefect b' i hi := by
  unfold representationSecondaryDefect
  rw [ha.order_eq, ha.order_eq, hb.order_eq, hb.order_eq,
    ha.truncatedPrefixDefect_eq hb 1 (i.val + 2) (i.val - 2)]

/-- The complete candidate set defining `A_i` is scalar invariant. -/
theorem representationAlphaCandidates_eq
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlphaCandidates b i =
      a'.representationAlphaCandidates b' i := by
  unfold representationAlphaCandidates
  rw [ha.representationHalfGap_eq hb i,
    ha.representationPrimaryDefect_eq hb i]
  split_ifs with hi
  · rw [ha.representationSecondaryDefect_eq hb i hi]
  · rfl

/-- Beli's representation invariant `A_i` is scalar invariant. -/
theorem representationAlpha_eq
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlpha b i = a'.representationAlpha b' i := by
  have hcandidates := ha.representationAlphaCandidates_eq hb i
  unfold representationAlpha
  apply le_antisymm
  · apply Finset.le_min'
    intro z hz
    apply Finset.min'_le
    simpa only [hcandidates] using hz
  · apply Finset.le_min'
    intro z hz
    apply Finset.min'_le
    simpa only [← hcandidates] using hz

/-- The rational value of `A_i` is scalar invariant. -/
theorem representationAlphaValue_eq
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlphaValue b i =
      a'.representationAlphaValue b' i := by
  apply WithTop.coe_injective
  rw [coe_representationAlphaValue, coe_representationAlphaValue,
    ha.representationAlpha_eq hb i]

/-- The first terminal candidate is scalar invariant. -/
theorem terminalAdjustedPrimary_eq
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (hgap : n + 2 < m + 1) :
    a.terminalAdjustedPrimary b hgap =
      a'.terminalAdjustedPrimary b' hgap := by
  unfold terminalAdjustedPrimary
  rw [ha.order_eq,
    ha.truncatedPrefixDefect_eq hb (-1) (n + 3) (n + 1)]

/-- The second terminal candidate is scalar invariant. -/
theorem terminalAdjustedSecondary_eq
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (hinner : n + 3 < m + 1) :
    a.terminalAdjustedSecondary b hinner =
      a'.terminalAdjustedSecondary b' hinner := by
  unfold terminalAdjustedSecondary
  rw [ha.order_eq, ha.order_eq, hb.order_eq,
    ha.truncatedPrefixDefect_eq hb 1 (n + 4) n]

/-- The terminal candidate set is scalar invariant. -/
theorem terminalAdjustedCandidates_eq
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (hgap : n + 2 < m + 1) :
    a.terminalAdjustedCandidates b hgap =
      a'.terminalAdjustedCandidates b' hgap := by
  unfold terminalAdjustedCandidates
  rw [ha.terminalAdjustedPrimary_eq hb hgap]
  split_ifs with hinner
  · rw [ha.terminalAdjustedSecondary_eq hb hinner]
  · rfl

/-- The exceptional terminal value is scalar invariant. -/
theorem terminalAdjustedAlpha_eq
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (hgap : n + 2 < m + 1) :
    a.terminalAdjustedAlpha b hgap =
      a'.terminalAdjustedAlpha b' hgap := by
  have hcandidates := ha.terminalAdjustedCandidates_eq hb hgap
  unfold terminalAdjustedAlpha
  apply le_antisymm
  · apply Finset.le_min'
    intro z hz
    apply Finset.min'_le
    simpa only [hcandidates] using hz
  · apply Finset.le_min'
    intro z hz
    apply Finset.min'_le
    simpa only [← hcandidates] using hz

/-- The adjusted central value in condition (iii) is scalar invariant. -/
theorem centralAdjustedAlpha_eq
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (i : CentralRepresentationIndex (m + 1) (n + 1)) :
    a.centralAdjustedAlpha b i = a'.centralAdjustedAlpha b' i := by
  unfold centralAdjustedAlpha
  split_ifs with hi
  · rw [hb.order_eq, ha.representationAlphaValue_eq hb (i.current hi)]
  · rw [ha.terminalAdjustedAlpha_eq hb]

/-- Condition (i) transports with the two scalar sequences. -/
theorem representationOrderCondition_transport
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    {hRank : n ≤ m} (h : a.RepresentationOrderCondition b hRank) :
    a'.RepresentationOrderCondition b' hRank := by
  intro i
  simpa only [ha.order_eq, hb.order_eq] using h i

/-- Condition (ii) transports with the two scalar sequences. -/
theorem representationDefectCondition_transport
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (h : a.RepresentationDefectCondition b) :
    a'.RepresentationDefectCondition b' := by
  intro i
  simpa only [ha.representationAlphaValue_eq hb i,
    ha.truncatedPrefixDefect_eq hb 1 i.val i.val] using h i

/-- The original numerical trigger in condition (iii) is scalar invariant. -/
theorem centralAlphaTrigger_iff
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (i : CentralRepresentationIndex (m + 1) (n + 1)) :
    a.centralAlphaTrigger b i ↔ a'.centralAlphaTrigger b' i := by
  unfold centralAlphaTrigger
  rw [hb.order_eq, ha.order_eq, ha.order_eq,
    ha.representationAlphaValue_eq hb i.previous,
    ha.centralAdjustedAlpha_eq hb i]

/-- The v2 previous capped defect is scalar invariant. -/
theorem centralPreviousDefect_eq
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (i : CentralRepresentationIndex (m + 1) (n + 1)) :
    a.centralPreviousDefect b i = a'.centralPreviousDefect b' i := by
  exact ha.truncatedPrefixDefect_eq hb (-1) i.val (i.val - 2)

/-- The v2 current capped defect is scalar invariant. -/
theorem centralCurrentDefect_eq
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (i : CentralRepresentationIndex (m + 1) (n + 1)) :
    a.centralCurrentDefect b i = a'.centralCurrentDefect b' i := by
  exact ha.truncatedPrefixDefect_eq hb (-1) (i.val + 1) (i.val - 1)

/-- The revised v2 trigger in condition (iii') is scalar invariant. -/
theorem centralDefectTrigger_iff
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (i : CentralRepresentationIndex (m + 1) (n + 1)) :
    a.centralDefectTrigger b i ↔ a'.centralDefectTrigger b' i := by
  unfold centralDefectTrigger
  simp only [hb.order_eq, ha.order_eq,
    ha.centralPreviousDefect_eq hb i, ha.centralCurrentDefect_eq hb i]

/-- The numerical trigger in condition (iv) is scalar invariant. -/
theorem longRepresentationTrigger_iff
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (i : LongRepresentationIndex (m + 1) (n + 1)) :
    a.longRepresentationTrigger b i ↔
      a'.longRepresentationTrigger b' i := by
  unfold longRepresentationTrigger
  rw [ha.order_eq, hb.order_eq, ha.order_eq]
  split_ifs with hi
  · rw [hb.order_eq]
  · rfl

/-- The prefix representations in original condition (iii) transport by
literal equality of their diagonal coefficient families. -/
theorem centralRepresentationConditions_transport
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (h : a.CentralRepresentationConditions b) :
    a'.CentralRepresentationConditions b' := by
  rw [a.centralRepresentationConditions_iff_forall_alphaTrigger b] at h
  rw [a'.centralRepresentationConditions_iff_forall_alphaTrigger b']
  intro i htrigger'
  have hrep := h i ((ha.centralAlphaTrigger_iff hb i).mpr htrigger')
  simpa only [hb.prefixValues_eq, ha.prefixValues_eq] using hrep

/-- The prefix representations in revised condition (iii') transport by
literal equality of their diagonal coefficient families. -/
theorem centralRepresentationConditionsPrime_transport
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (h : a.CentralRepresentationConditionsPrime b) :
    a'.CentralRepresentationConditionsPrime b' := by
  intro i htrigger'
  have hrep := h i ((ha.centralDefectTrigger_iff hb i).mpr htrigger')
  simpa only [hb.prefixValues_eq, ha.prefixValues_eq] using hrep

/-- The prefix representations in condition (iv) transport by literal
equality of their diagonal coefficient families. -/
theorem longRepresentationConditions_transport
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (h : a.LongRepresentationConditions b) :
    a'.LongRepresentationConditions b' := by
  rw [a.longRepresentationConditions_iff_forall_generalTrigger b] at h
  rw [a'.longRepresentationConditions_iff_forall_generalTrigger b']
  intro i htrigger'
  have hrep := h i ((ha.longRepresentationTrigger_iff hb i).mpr htrigger')
  simpa only [hb.prefixValues_eq, ha.prefixValues_eq] using hrep

/-- Simultaneous scalar transport of all four original conditions. -/
theorem representationConditions_transport
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    {hRank : n ≤ m} (h : RepresentationConditions a b hRank) :
    RepresentationConditions a' b' hRank where
  orderCondition := ha.representationOrderCondition_transport hb h.orderCondition
  defectCondition := ha.representationDefectCondition_transport hb h.defectCondition
  centralRepresentations :=
    ha.centralRepresentationConditions_transport hb h.centralRepresentations
  longRepresentations :=
    ha.longRepresentationConditions_transport hb h.longRepresentations

/-- The original four-condition package is invariant under simultaneous
scalar transport. -/
theorem representationConditions_iff
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (hRank : n ≤ m) :
    RepresentationConditions a b hRank ↔
      RepresentationConditions a' b' hRank := by
  constructor
  · exact ha.representationConditions_transport hb
  · exact ha.symm.representationConditions_transport hb.symm

/-- Simultaneous scalar transport of all four revised v2 conditions. -/
theorem representationConditionsPrime_transport
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    {hRank : n ≤ m} (h : RepresentationConditionsPrime a b hRank) :
    RepresentationConditionsPrime a' b' hRank where
  orderCondition := ha.representationOrderCondition_transport hb h.orderCondition
  defectCondition := ha.representationDefectCondition_transport hb h.defectCondition
  centralRepresentations :=
    ha.centralRepresentationConditionsPrime_transport hb h.centralRepresentations
  longRepresentations :=
    ha.longRepresentationConditions_transport hb h.longRepresentations

/-- The revised v2 four-condition package is invariant under simultaneous
scalar transport. -/
theorem representationConditionsPrime_iff
    (ha : ScalarAgreement a a') (hb : ScalarAgreement b b')
    (hRank : n ≤ m) :
    RepresentationConditionsPrime a b hRank ↔
      RepresentationConditionsPrime a' b' hRank := by
  constructor
  · exact ha.representationConditionsPrime_transport hb
  · exact ha.symm.representationConditionsPrime_transport hb.symm

end ScalarAgreement
end BONG.GoodBONG

end Bong
