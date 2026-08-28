/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralPrefix

/-!
# Beli (2019), Lemma 7.9(iii): the ten profile regions

The two alternatives of Lemma 2.18 are each split at the canonical indices
`t`, `t'`, and `u`.  In zero-based order coordinates these are the first
switch, the second switch, and the final unequal coordinate.  This file
records the exhaustive, nonoverlapping arithmetic partition used by cases
1--10 of the printed proof.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The three canonical intervals underlying cases 1--4 and 5--10.

For type I the paper's `t,t',u` correspond respectively to one past the two
even switches and one past the final unequal zero-based coordinate.  For
types II and III, `t` is one past `lastZero`, while `t'` is `firstTwo`.
-/
inductive Lemma79CentralRegion
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2)) : Prop
  | typeIEarly (D : Lemma67TypeI a b)
      (C : Lemma67TypeICanonicalData a b D)
      (first_eq_zero : D.profile.first = 0)
      (bound : i.val ≤ C.leftSwitch)
  | typeIMiddle (D : Lemma67TypeI a b)
      (C : Lemma67TypeICanonicalData a b D)
      (first_eq_zero : D.profile.first = 0)
      (left : C.leftSwitch < i.val)
      (right : i.val ≤ C.rightSwitch)
  | typeIRight (D : Lemma67TypeI a b)
      (C : Lemma67TypeICanonicalData a b D)
      (first_eq_zero : D.profile.first = 0)
      (right : C.rightSwitch < i.val)
      (last : i.val ≤ D.profile.last)
  | typeIIEarly (D : Lemma67TypeII a b)
      (first_eq_zero : D.outer.first = 0)
      (bound : i.val ≤ D.outer.transition.lastZero + 1)
  | typeIIMiddle (D : Lemma67TypeII a b)
      (first_eq_zero : D.outer.first = 0)
      (left : D.outer.transition.lastZero + 1 < i.val)
      (right : i.val < D.outer.transition.firstTwo)
  | typeIIRight (D : Lemma67TypeII a b)
      (first_eq_zero : D.outer.first = 0)
      (right : D.outer.transition.firstTwo ≤ i.val)
      (last : i.val ≤ D.outer.last)
  | typeIIIEarly (D : Lemma67TypeIII a b)
      (first_eq_zero : D.outer.first = 0)
      (bound : i.val ≤ D.outer.transition.lastZero + 1)
  | typeIIIMiddle (D : Lemma67TypeIII a b)
      (first_eq_zero : D.outer.first = 0)
      (left : D.outer.transition.lastZero + 1 < i.val)
      (right : i.val < D.outer.transition.firstTwo)
  | typeIIIRight (D : Lemma67TypeIII a b)
      (first_eq_zero : D.outer.first = 0)
      (right : D.outer.transition.firstTwo ≤ i.val)
      (last : i.val ≤ D.outer.last)

/-- Every index in the difference prefix belongs to exactly one of the three
printed regions for its normalized profile. -/
theorem Lemma79NormalizedClassification.centralRegion_of_differencePrefix
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hprefix : D.IsDifferencePrefixAt i) :
    Lemma79CentralRegion a b i := by
  rcases hprefix with ⟨last, hlast, hiLast⟩
  cases D with
  | typeI E hfirst =>
      have hlastEq : last = E.profile.last :=
        hlast.eq E.profile.lastDifference
      have hiProfileLast : i.val ≤ E.profile.last := by omega
      rcases a.lemma67TypeICanonicalData b E hfirst with ⟨C⟩
      by_cases hearly : i.val ≤ C.leftSwitch
      · exact .typeIEarly E C hfirst hearly
      · by_cases hmiddle : i.val ≤ C.rightSwitch
        · exact .typeIMiddle E C hfirst (by omega) hmiddle
        · exact .typeIRight E C hfirst (by omega) hiProfileLast
  | typeII E hfirst =>
      have hlastEq : last = E.outer.last :=
        hlast.eq E.outer.lastDifference
      have hiProfileLast : i.val ≤ E.outer.last := by omega
      by_cases hearly : i.val ≤ E.outer.transition.lastZero + 1
      · exact .typeIIEarly E hfirst hearly
      · by_cases hmiddle : i.val < E.outer.transition.firstTwo
        · exact .typeIIMiddle E hfirst (by omega) hmiddle
        · exact .typeIIRight E hfirst (by omega) hiProfileLast
  | typeIII E hfirst _ =>
      have hlastEq : last = E.outer.last :=
        hlast.eq E.outer.lastDifference
      have hiProfileLast : i.val ≤ E.outer.last := by omega
      by_cases hearly : i.val ≤ E.outer.transition.lastZero + 1
      · exact .typeIIIEarly E hfirst hearly
      · by_cases hmiddle : i.val < E.outer.transition.firstTwo
        · exact .typeIIIMiddle E hfirst (by omega) hmiddle
        · exact .typeIIIRight E hfirst (by omega) hiProfileLast

/-- The nominal type-III middle interval is empty because its two transition
indices are adjacent. -/
theorem Lemma79CentralRegion.not_typeIIIMiddle
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {i : CentralRepresentationIndex (n + 2) (n + 2)}
    (D : Lemma67TypeIII a b)
    (left : D.outer.transition.lastZero + 1 < i.val)
    (right : i.val < D.outer.transition.firstTwo) : False := by
  rw [D.adjacent] at right
  omega

/-- On a nonterminal difference-prefix boundary, the ten-case region split
comes with the left-or-right strict two-step target growth forced by Lemma
2.18 and P6. -/
theorem Lemma79NormalizedClassification.centralRegion_and_twoStepAlternative
    [Beli2006AlphaLaws.{u, v} K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hprefix : D.IsDifferencePrefixAt i)
    (hiNext : i.val + 1 < n + 2)
    (htrigger : b.centralAlphaTrigger c i) :
    Lemma79CentralRegion a b i ∧
      (b.order ⟨i.val - 2, by omega⟩ < b.order ⟨i.val, i.lt_large⟩ ∨
        b.order ⟨i.val - 1, by omega⟩ <
          b.order ⟨i.val + 1, hiNext⟩) := by
  exact ⟨D.centralRegion_of_differencePrefix i hprefix,
    b.centralTrigger_targetTwoStepAlternative c hdefectBC i hiNext htrigger⟩

end BONG.GoodBONG

end Bong
