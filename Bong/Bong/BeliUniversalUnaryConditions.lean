/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalRepresentation

/-!
# Unary specialization of the revised representation conditions

This file removes the finite-index bureaucracy from Beli's Lemma 2.3.  For a
unary target there is one order coordinate, one ordinary boundary when the
source has rank at least two, one central boundary when it has rank at least
three, and one long boundary when it has rank at least four.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The unique ordinary representation boundary for a unary target. -/
def unaryRepresentationIndex (m : Nat) :
    RepresentationIndex (m + 2) 1 where
  val := 1
  pos := by omega
  lt_large := by omega
  le_small := by omega

theorem representationIndex_eq_unaryRepresentationIndex
    {m : Nat} (i : RepresentationIndex (m + 2) 1) :
    i = unaryRepresentationIndex m := by
  apply RepresentationIndex.ext
  have := i.pos
  have := i.le_small
  change i.val = 1
  omega

/-- The unique central representation boundary for a unary target and a
source of rank at least three. -/
def unaryCentralRepresentationIndex (m : Nat) :
    CentralRepresentationIndex (m + 3) 1 where
  val := 2
  one_lt := by omega
  lt_large := by omega
  le_small_succ := by omega

theorem centralRepresentationIndex_eq_unary
    {m : Nat} (i : CentralRepresentationIndex (m + 3) 1) :
    i = unaryCentralRepresentationIndex m := by
  cases i with
  | mk val one_lt lt_large le_small_succ =>
      have hval : val = 2 := by omega
      subst val
      rfl

/-- The unique long representation boundary for a unary target and a source
of rank at least four. -/
def unaryLongRepresentationIndex (m : Nat) :
    LongRepresentationIndex (m + 4) 1 where
  val := 2
  one_lt := by omega
  succ_lt_large := by omega
  le_small_succ := by omega

theorem longRepresentationIndex_eq_unary
    {m : Nat} (i : LongRepresentationIndex (m + 4) 1) :
    i = unaryLongRepresentationIndex m := by
  cases i with
  | mk val one_lt succ_lt_large le_small_succ =>
      have hval : val = 2 := by omega
      subst val
      rfl

/-- Condition (i) of Lemma 2.3 is exactly `R₁ ≤ S₁`. -/
theorem unary_representationOrderCondition_iff
    {m : Nat} (a : GoodBONG q L (m + 2)) (b : Kˣ) :
    a.RepresentationOrderCondition (BONG.unaryModelGoodBONG b)
        (by omega) ↔
      a.order 0 ≤ ordUnit K b := by
  unfold RepresentationOrderCondition
  constructor
  · intro h
    rcases h 0 with horder | ⟨hi0, _hiLarge, _hpair⟩
    · simpa using horder
    · omega
  · intro h i
    left
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simpa using h

/-- Condition (ii) of Lemma 2.3 is the single first-boundary defect
inequality. -/
theorem unary_representationDefectCondition_iff
    {m : Nat} (a : GoodBONG q L (m + 2)) (b : Kˣ) :
    a.RepresentationDefectCondition (BONG.unaryModelGoodBONG b) ↔
      (a.representationAlphaValue (BONG.unaryModelGoodBONG b)
          (unaryRepresentationIndex m) : WithTop ℚ) ≤
        a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) 1 1 1 := by
  unfold RepresentationDefectCondition
  constructor
  · intro h
    exact h (unaryRepresentationIndex m)
  · intro h i
    rw [representationIndex_eq_unaryRepresentationIndex i]
    exact h

/-- For a source of rank at least three, revised condition (iii') is the
single implication at `i = 2`. -/
theorem unary_centralRepresentationConditionsPrime_iff
    {m : Nat} (a : GoodBONG q L (m + 3)) (b : Kˣ) :
    a.CentralRepresentationConditionsPrime (BONG.unaryModelGoodBONG b) ↔
      (a.centralDefectTrigger (BONG.unaryModelGoodBONG b)
          (unaryCentralRepresentationIndex m) →
        DiagonalRepresents
          ((BONG.unaryModelGoodBONG b).prefixValues 1 (by omega))
          (a.prefixValues 2 (by omega))) := by
  unfold CentralRepresentationConditionsPrime
  constructor
  · intro h
    exact h (unaryCentralRepresentationIndex m)
  · intro h i
    rw [centralRepresentationIndex_eq_unary i]
    exact h

/-- For a source of rank at least four, condition (iv) is the single
implication at `i = 2`. -/
theorem unary_longRepresentationConditions_iff
    {m : Nat} (a : GoodBONG q L (m + 4)) (b : Kˣ) :
    a.LongRepresentationConditions (BONG.unaryModelGoodBONG b) ↔
      (((if hi : 2 ≤ 1 then
          a.order ⟨3, by omega⟩ ≤
            (BONG.unaryModelGoodBONG b).order ⟨1, by omega⟩
        else True) ∧
        (BONG.unaryModelGoodBONG b).order 0 +
            2 * (ramificationIndex K : Int) < a.order ⟨3, by omega⟩ ∧
        a.order ⟨2, by omega⟩ + 2 * (ramificationIndex K : Int) ≤
          (BONG.unaryModelGoodBONG b).order 0 +
            2 * (ramificationIndex K : Int)) →
        DiagonalRepresents
          ((BONG.unaryModelGoodBONG b).prefixValues 1 (by omega))
          (a.prefixValues 3 (by omega))) := by
  unfold LongRepresentationConditions
  constructor
  · intro h
    exact h (unaryLongRepresentationIndex m)
  · intro h i
    rw [longRepresentationIndex_eq_unary i]
    exact h

end BONG.GoodBONG

end Bong
