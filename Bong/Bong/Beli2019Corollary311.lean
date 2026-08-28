/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Reflexivity
import Bong.Bong.Beli2019PrefixChange

/-!
# Beli (2019), Lemma 3.10 and Corollary 3.11

This file proves that conditions (i) and (ii) are unchanged when either good
BONG is replaced.  Orders are handled by the good-BONG classification theorem;
the representation invariant and capped defect are handled by Lemma 4.2.

The numerical triggers in conditions (iii) and (iv) are also proved invariant.
The only remaining content of Lemma 3.10 is therefore the pointwise transport
of the corresponding prefix representations.  It is exposed by
`Beli2019Lemma310PrefixLaws`, from which Corollary 3.11 is derived.
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

/-- Condition (i) is independent of both choices of good BONG. -/
theorem representationOrderCondition_changeBONG_iff
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1)) (hRank : n ≤ m) :
    a.RepresentationOrderCondition b hRank ↔
      a'.RepresentationOrderCondition b' hRank := by
  have ha : a.SameOrders a' := by
    letI := classificationV
    exact a.order_invariant a'
  have hb : b.SameOrders b' := by
    letI := classificationW
    exact b.order_invariant b'
  unfold SameOrders at ha hb
  unfold RepresentationOrderCondition
  constructor
  · intro h i
    simpa only [ha, hb] using h i
  · intro h i
    simpa only [← ha _, ← hb _] using h i

/-- Condition (ii) is independent of both choices of good BONG. -/
theorem representationDefectCondition_changeBONG_iff
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1)) :
    a.RepresentationDefectCondition b ↔
      a'.RepresentationDefectCondition b' := by
  let prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K := by
    exact @prefixChangeLawsOfClassification K _ _ _ _ _ classificationV
  let prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K := by
    exact @prefixChangeLawsOfClassification K _ _ _ _ _ classificationW
  unfold RepresentationDefectCondition
  constructor
  · intro h i
    rw [← a.representationAlphaValue_invariant
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV)
        (prefixChangeW := prefixChangeW) a' b b' i,
      ← a.truncatedPrefixDefect_invariant
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV)
        (prefixChangeW := prefixChangeW) a' b b' 1 i.val i.val]
    exact h i
  · intro h i
    rw [a.representationAlphaValue_invariant
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV)
        (prefixChangeW := prefixChangeW) a' b b' i,
      a.truncatedPrefixDefect_invariant
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV)
        (prefixChangeW := prefixChangeW) a' b b' 1 i.val i.val]
    exact h i

/-- Definition 4's quantity `S_i + A_i`, including its exceptional endpoint,
is independent of both choices of good BONG. -/
theorem centralAdjustedAlpha_invariant
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1)) :
    a.centralAdjustedAlpha b i = a'.centralAdjustedAlpha b' i := by
  let prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K := by
    exact @prefixChangeLawsOfClassification K _ _ _ _ _ classificationV
  let prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K := by
    exact @prefixChangeLawsOfClassification K _ _ _ _ _ classificationW
  have hb : b.SameOrders b' := by
    letI := classificationW
    exact b.order_invariant b'
  unfold centralAdjustedAlpha
  split_ifs with hi
  · rw [hb ⟨i.val - 1, by have := i.one_lt; have := hi; omega⟩,
      a.representationAlphaValue_invariant
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV)
        (prefixChangeW := prefixChangeW) a' b b' (i.current hi)]
  · rw [a.terminalAdjustedAlpha_invariant
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW) a' b b' (by
        have := i.le_small_succ
        have := i.lt_large
        omega)]

/-- The numerical trigger in condition (iii) is independent of both choices
of good BONG. -/
theorem centralAlphaTrigger_changeBONG_iff
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1)) :
    a.centralAlphaTrigger b i ↔ a'.centralAlphaTrigger b' i := by
  let prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K := by
    exact @prefixChangeLawsOfClassification K _ _ _ _ _ classificationV
  let prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K := by
    exact @prefixChangeLawsOfClassification K _ _ _ _ _ classificationW
  have ha : a.SameOrders a' := by
    letI := classificationV
    exact a.order_invariant a'
  have hb : b.SameOrders b' := by
    letI := classificationW
    exact b.order_invariant b'
  unfold centralAlphaTrigger
  rw [hb ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩,
    ha ⟨i.val, by have := i.lt_large; omega⟩,
    ha ⟨i.val - 1, by have := i.one_lt; have := i.lt_large; omega⟩,
    a.representationAlphaValue_invariant
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW) a' b b' i.previous,
    a.centralAdjustedAlpha_invariant
      (classificationV := classificationV)
      (classificationW := classificationW) a' b b' i]

/-- The numerical antecedent of condition (iv). -/
noncomputable def longRepresentationTrigger
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : LongRepresentationIndex (m + 1) (n + 1)) : Prop :=
  (if hi : i.val ≤ n + 1 then
      a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
        b.order ⟨i.val - 1, by have := i.one_lt; have := hi; omega⟩
    else True) ∧
    b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ +
        2 * (ramificationIndex K : Int) <
      a.order ⟨i.val + 1, i.succ_lt_large⟩ ∧
    a.order ⟨i.val, by have := i.succ_lt_large; omega⟩ +
        2 * (ramificationIndex K : Int) ≤
      b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ +
        2 * (ramificationIndex K : Int)

/-- Condition (iv) expressed using its named numerical trigger. -/
theorem longRepresentationConditions_iff_forall_generalTrigger
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1)) :
    a.LongRepresentationConditions b ↔
      ∀ i : LongRepresentationIndex (m + 1) (n + 1),
        a.longRepresentationTrigger b i →
          DiagonalRepresents
            (b.prefixValues (i.val - 1) (by
              have := i.le_small_succ
              omega))
            (a.prefixValues (i.val + 1) (by
              have := i.succ_lt_large
              omega)) := by
  rfl

/-- The numerical trigger in condition (iv) is independent of both choices
of good BONG. -/
theorem longRepresentationTrigger_changeBONG_iff
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1))
    (i : LongRepresentationIndex (m + 1) (n + 1)) :
    a.longRepresentationTrigger b i ↔
      a'.longRepresentationTrigger b' i := by
  have ha : a.SameOrders a' := by
    letI := classificationV
    exact a.order_invariant a'
  have hb : b.SameOrders b' := by
    letI := classificationW
    exact b.order_invariant b'
  unfold longRepresentationTrigger
  rw [ha ⟨i.val + 1, i.succ_lt_large⟩,
    hb ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩,
    ha ⟨i.val, by have := i.succ_lt_large; omega⟩]
  split_ifs with hi
  · rw [hb ⟨i.val - 1, by have := i.one_lt; have := hi; omega⟩]
  · rfl

end BONG.GoodBONG

/-- The pointwise representation-theoretic core of Beli (2019), Lemma 3.10.
The numerical triggers are now concrete invariants, so the remaining local
input transports only the individual prefix-space representation. -/
class Beli2019Lemma310PrefixLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  central
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (a a' : BONG.GoodBONG q L (m + 1))
    (b b' : BONG.GoodBONG r M (n + 1)) (hRank : n ≤ m)
    (horder : a.RepresentationOrderCondition b hRank)
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger b i)
    (hrep : DiagonalRepresents
      (b.prefixValues (i.val - 1) (by
        have := i.le_small_succ
        omega))
      (a.prefixValues i.val (by
        have := i.lt_large
        omega))) :
    DiagonalRepresents
      (b'.prefixValues (i.val - 1) (by
        have := i.le_small_succ
        omega))
      (a'.prefixValues i.val (by
        have := i.lt_large
        omega))
  long
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (a a' : BONG.GoodBONG q L (m + 1))
    (b b' : BONG.GoodBONG r M (n + 1)) (hRank : n ≤ m)
    (horder : a.RepresentationOrderCondition b hRank)
    (i : LongRepresentationIndex (m + 1) (n + 1))
    (htrigger : a.longRepresentationTrigger b i)
    (hrep : DiagonalRepresents
      (b.prefixValues (i.val - 1) (by
        have := i.le_small_succ
        omega))
      (a.prefixValues (i.val + 1) (by
        have := i.succ_lt_large
        omega))) :
    DiagonalRepresents
      (b'.prefixValues (i.val - 1) (by
        have := i.le_small_succ
        omega))
      (a'.prefixValues (i.val + 1) (by
        have := i.succ_lt_large
        omega))

/-- The representation-theoretic remainder of Beli (2019), Lemma 3.10.
The central clause uses conditions (i)--(ii), while the long clause uses
condition (i); together they transport the prefix representations occurring
in conditions (iii) and (iv). -/
class Beli2019Lemma310RepresentationLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  central_iff
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (a a' : BONG.GoodBONG q L (m + 1))
    (b b' : BONG.GoodBONG r M (n + 1)) (hRank : n ≤ m)
    (horder : a.RepresentationOrderCondition b hRank)
    (hdefect : a.RepresentationDefectCondition b) :
    a.CentralRepresentationConditions b ↔
      a'.CentralRepresentationConditions b'
  long_iff
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (a a' : BONG.GoodBONG q L (m + 1))
    (b b' : BONG.GoodBONG r M (n + 1)) (hRank : n ≤ m)
    (horder : a.RepresentationOrderCondition b hRank) :
    a.LongRepresentationConditions b ↔
      a'.LongRepresentationConditions b'

/-- The pointwise prefix laws imply the packaged remainder of Lemma 3.10. -/
noncomputable instance lemma310RepresentationLawsOfPrefixLaws
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310PrefixLaws.{u, v, w} K] :
    Beli2019Lemma310RepresentationLaws.{u, v, w} K where
  central_iff a a' b b' hRank horder hdefect := by
    rw [a.centralRepresentationConditions_iff_forall_alphaTrigger b,
      a'.centralRepresentationConditions_iff_forall_alphaTrigger b']
    constructor
    · intro h i htrigger'
      have htrigger :=
        (a.centralAlphaTrigger_changeBONG_iff
          (classificationV := classificationV)
          (classificationW := classificationW) a' b b' i).mpr htrigger'
      exact Beli2019Lemma310PrefixLaws.central
        a a' b b' hRank horder hdefect i htrigger (h i htrigger)
    · intro h i htrigger
      have horder' : a'.RepresentationOrderCondition b' hRank :=
        (a.representationOrderCondition_changeBONG_iff
          (classificationV := classificationV)
          (classificationW := classificationW) a' b b' hRank).mp horder
      have htrigger' :=
        (a.centralAlphaTrigger_changeBONG_iff
          (classificationV := classificationV)
          (classificationW := classificationW) a' b b' i).mp htrigger
      have hdefect' : a'.RepresentationDefectCondition b' :=
        (a.representationDefectCondition_changeBONG_iff
          (classificationV := classificationV)
          (classificationW := classificationW) a' b b').mp hdefect
      exact Beli2019Lemma310PrefixLaws.central
        a' a b' b hRank horder' hdefect' i htrigger' (h i htrigger')
  long_iff a a' b b' hRank horder := by
    rw [a.longRepresentationConditions_iff_forall_generalTrigger b,
      a'.longRepresentationConditions_iff_forall_generalTrigger b']
    constructor
    · intro h i htrigger'
      have htrigger :=
        (a.longRepresentationTrigger_changeBONG_iff
          (classificationV := classificationV)
          (classificationW := classificationW) a' b b' i).mpr htrigger'
      exact Beli2019Lemma310PrefixLaws.long
        a a' b b' hRank horder i htrigger (h i htrigger)
    · intro h i htrigger
      have horder' : a'.RepresentationOrderCondition b' hRank :=
        (a.representationOrderCondition_changeBONG_iff
          (classificationV := classificationV)
          (classificationW := classificationW) a' b b' hRank).mp horder
      have htrigger' :=
        (a.longRepresentationTrigger_changeBONG_iff
          (classificationV := classificationV)
          (classificationW := classificationW) a' b b' i).mp htrigger
      exact Beli2019Lemma310PrefixLaws.long
        a' a b' b hRank horder' i htrigger' (h i htrigger')

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Lemma 3.10 gives invariance of the complete four-condition package once
its two prefix-representation clauses are supplied. -/
theorem representationConditions_changeBONG_iff
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1)) (hRank : n ≤ m) :
    RepresentationConditions a b hRank ↔
      RepresentationConditions a' b' hRank := by
  constructor
  · intro h
    refine ⟨(a.representationOrderCondition_changeBONG_iff
        (classificationV := classificationV)
        (classificationW := classificationW)
        a' b b' hRank).mp h.orderCondition,
      (a.representationDefectCondition_changeBONG_iff
        (classificationV := classificationV)
        (classificationW := classificationW)
        a' b b').mp h.defectCondition, ?_, ?_⟩
    · exact (Beli2019Lemma310RepresentationLaws.central_iff
        a a' b b' hRank h.orderCondition h.defectCondition).mp
          h.centralRepresentations
    · exact (Beli2019Lemma310RepresentationLaws.long_iff
        a a' b b' hRank h.orderCondition).mp h.longRepresentations
  · intro h
    have horder : a.RepresentationOrderCondition b hRank :=
      (a.representationOrderCondition_changeBONG_iff
        (classificationV := classificationV)
        (classificationW := classificationW)
        a' b b' hRank).mpr h.orderCondition
    refine ⟨horder,
      (a.representationDefectCondition_changeBONG_iff
        (classificationV := classificationV)
        (classificationW := classificationW)
        a' b b').mpr h.defectCondition, ?_, ?_⟩
    · exact (Beli2019Lemma310RepresentationLaws.central_iff
        a a' b b' hRank horder
          ((a.representationDefectCondition_changeBONG_iff
            (classificationV := classificationV)
            (classificationW := classificationW)
            a' b b').mpr h.defectCondition)).mpr h.centralRepresentations
    · exact (Beli2019Lemma310RepresentationLaws.long_iff
        a a' b b' hRank horder).mpr h.longRepresentations

end BONG.GoodBONG

/-- Corollary 3.11 follows from Lemma 3.10 and good-BONG classification. -/
noncomputable instance corollary311LawsOfLemma310
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K] :
    Beli2019Corollary311Laws.{u, v, w} K where
  conditions_iff a a' b b' hRank :=
    BONG.GoodBONG.representationConditions_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW) a a' b b' hRank

end Bong
