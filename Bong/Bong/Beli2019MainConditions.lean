/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019DefectMin
import Bong.Bong.Beli2019PrefixChange

/-!
# Beli (2019), Theorem 2.1 and the revised condition (iii')

The original condition (iii) is already part of `RepresentationConditions`.
The revised arXiv v2 adds condition (iii'), whose trigger is expressed by two
truncated defects.  This file defines that trigger and isolates the exact
pointwise equivalence proved later as Lemma 2.16.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- The first defect in the v2 condition (iii'):
`d[-a_(1,i)b_(1,i-2)]`. -/
noncomputable def centralPreviousDefect
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1)) : WithTop ℚ :=
  a.truncatedPrefixDefect b (-1) i.val (i.val - 2)

/-- The second defect in the v2 condition (iii'):
`d[-a_(1,i+1)b_(1,i-1)]`. -/
noncomputable def centralCurrentDefect
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1)) : WithTop ℚ :=
  a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1)

/-- The trigger occurring in Theorem 2.1(iii), including
`R_(i+1) > S_(i-1)`. -/
noncomputable def centralAlphaTrigger
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1)) : Prop :=
  b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ <
      a.order ⟨i.val, by
        have := i.lt_large
        omega⟩ ∧
    ((2 * (ramificationIndex K : ℚ) +
        (a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
      ((a.representationAlphaValue b i.previous : ℚ) : WithTop ℚ) +
        a.centralAdjustedAlpha b i

/-- The revised v2 trigger in Theorem 2.1(iii'). -/
noncomputable def centralDefectTrigger
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1)) : Prop :=
  b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ <
      a.order ⟨i.val, by
        have := i.lt_large
        omega⟩ ∧
    ((2 * (ramificationIndex K : ℚ) +
        (b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : ℚ) -
        (a.order ⟨i.val, by
          have := i.lt_large
          omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
      a.centralPreviousDefect b i + a.centralCurrentDefect b i

/-- Condition (iii') of the revised 2019 paper. -/
noncomputable def CentralRepresentationConditionsPrime
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1)) : Prop :=
  ∀ i : CentralRepresentationIndex (m + 1) (n + 1),
    a.centralDefectTrigger b i →
      DiagonalRepresents
        (b.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega))
        (a.prefixValues i.val (by
          have := i.lt_large
          omega))

/-- The precise pointwise content of Lemma 2.16 needed to replace (iii) by
(iii').  Its hypotheses will be discharged from conditions (i) and (ii). -/
noncomputable def CentralTriggerEquivalence
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1)) : Prop :=
  ∀ i : CentralRepresentationIndex (m + 1) (n + 1),
    a.centralAlphaTrigger b i ↔ a.centralDefectTrigger b i

theorem centralRepresentationConditions_iff_forall_alphaTrigger
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1)) :
    a.CentralRepresentationConditions b ↔
      ∀ i : CentralRepresentationIndex (m + 1) (n + 1),
        a.centralAlphaTrigger b i →
          DiagonalRepresents
            (b.prefixValues (i.val - 1) (by
              have := i.le_small_succ
              omega))
            (a.prefixValues i.val (by
              have := i.lt_large
              omega)) := by
  rfl

/-- Once Lemma 2.16 is available pointwise, conditions (iii) and (iii') are
logically interchangeable. -/
theorem centralRepresentationConditions_iff_prime
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (htrigger : a.CentralTriggerEquivalence b) :
    a.CentralRepresentationConditions b ↔
      a.CentralRepresentationConditionsPrime b := by
  rw [a.centralRepresentationConditions_iff_forall_alphaTrigger b]
  unfold CentralRepresentationConditionsPrime
  constructor
  · intro h i hi
    exact h i ((htrigger i).mpr hi)
  · intro h i hi
    exact h i ((htrigger i).mp hi)

end BONG.GoodBONG

/-- The four conditions of Theorem 2.1 with revised condition (iii'). -/
structure RepresentationConditionsPrime
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (a : BONG.GoodBONG q L (m + 1)) (b : BONG.GoodBONG r M (n + 1))
    (hRank : n ≤ m) : Prop where
  orderCondition : a.RepresentationOrderCondition b hRank
  defectCondition : a.RepresentationDefectCondition b
  centralRepresentations : a.CentralRepresentationConditionsPrime b
  longRepresentations : a.LongRepresentationConditions b

/-- The original and revised four-condition packages are equivalent exactly
when the pointwise Lemma 2.16 trigger equivalence has been proved. -/
theorem representationConditions_iff_prime
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (a : BONG.GoodBONG q L (m + 1)) (b : BONG.GoodBONG r M (n + 1))
    (hRank : n ≤ m) (htrigger : a.CentralTriggerEquivalence b) :
    RepresentationConditions a b hRank ↔
      RepresentationConditionsPrime a b hRank := by
  constructor
  · intro h
    exact ⟨h.orderCondition, h.defectCondition,
      (a.centralRepresentationConditions_iff_prime b htrigger).mp
        h.centralRepresentations,
      h.longRepresentations⟩
  · intro h
    exact ⟨h.orderCondition, h.defectCondition,
      (a.centralRepresentationConditions_iff_prime b htrigger).mpr
        h.centralRepresentations,
      h.longRepresentations⟩

end Bong
