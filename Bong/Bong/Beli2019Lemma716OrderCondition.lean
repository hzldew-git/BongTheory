/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716OrdersBasic

/-!
# Beli (2019), Lemma 7.16: reduction of condition 2.1(i)

The elementary ranges of condition 2.1(i) leave exactly the exceptional
coordinates listed in the paper:

* type I: zero-based coordinates `s - 2` and `s - 1`;
* type II: zero-based coordinate `s - 1`.

This module packages a single coordinate clause explicitly and proves that
those finite obligations, together with the results of Lemma 7.15, assemble
the complete order condition.  No representation or geometric conclusion is
stored in a typeclass.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The pointwise disjunction appearing in representation condition 2.1(i)
for two equal-rank good BONGs. -/
def Beli2019Lemma716OrderClause
    (b : GoodBONG q M (n + 3)) (c : GoodBONG q N (n + 3))
    (i : Fin (n + 3)) : Prop :=
  b.order i ≤ c.order i ∨
    ∃ (hi0 : 0 < i.val) (hiLarge : i.val + 1 < n + 3),
      b.order i + b.order ⟨i.val + 1, hiLarge⟩ ≤
        c.order ⟨i.val - 1, by omega⟩ + c.order i

/-- The early range, unchanged tail, and two exceptional coordinates
assemble condition 2.1(i). -/
theorem lemma716_orderCondition_of_two_exception_clauses
    (b : GoodBONG q M (n + 3)) (c : GoodBONG q N (n + 3))
    (s : Nat) (hsTwo : 2 ≤ s) (hsRank : s ≤ n + 3)
    (hearly : ∀ i, i.val < s - 2 →
      Beli2019Lemma716OrderClause b c i)
    (htail : ∀ i, s ≤ i.val →
      Beli2019Lemma716OrderClause b c i)
    (hleft : Beli2019Lemma716OrderClause b c
      ⟨s - 2, by omega⟩)
    (hright : Beli2019Lemma716OrderClause b c
      ⟨s - 1, by omega⟩) :
    b.RepresentationOrderCondition c le_rfl := by
  intro i
  change Beli2019Lemma716OrderClause b c i
  by_cases hiEarly : i.val < s - 2
  · exact hearly i hiEarly
  by_cases hiLeft : i.val = s - 2
  · let left : Fin (n + 3) := ⟨s - 2, by omega⟩
    have hi : i = left := Fin.ext hiLeft
    simpa only [hi, left] using hleft
  by_cases hiRight : i.val = s - 1
  · let right : Fin (n + 3) := ⟨s - 1, by omega⟩
    have hi : i = right := Fin.ext hiRight
    simpa only [hi, right] using hright
  exact htail i (by omega)

/-- The larger elementary type-II prefix, unchanged tail, and its single
exceptional coordinate assemble condition 2.1(i). -/
theorem lemma716_orderCondition_of_one_exception_clause
    (b : GoodBONG q M (n + 3)) (c : GoodBONG q N (n + 3))
    (s : Nat) (hsTwo : 2 ≤ s) (hsRank : s ≤ n + 3)
    (hearly : ∀ i, i.val < s - 1 →
      Beli2019Lemma716OrderClause b c i)
    (htail : ∀ i, s ≤ i.val →
      Beli2019Lemma716OrderClause b c i)
    (hexception : Beli2019Lemma716OrderClause b c
      ⟨s - 1, by omega⟩) :
    b.RepresentationOrderCondition c le_rfl := by
  intro i
  change Beli2019Lemma716OrderClause b c i
  by_cases hiEarly : i.val < s - 1
  · exact hearly i hiEarly
  by_cases hiException : i.val = s - 1
  · let exceptional : Fin (n + 3) := ⟨s - 1, by omega⟩
    have hi : i = exceptional := Fin.ext hiException
    simpa only [hi, exceptional] using hexception
  exact htail i (by omega)

/-- In type I, all of condition 2.1(i) follows from the two printed
exceptional-coordinate calculations. -/
theorem lemma716_typeI_orderCondition_of_exception_clauses
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (hleft : Beli2019Lemma716OrderClause b c
      ⟨s - 2, by
        have := D.le_rank
        omega⟩)
    (hright : Beli2019Lemma716OrderClause b c
      ⟨s - 1, by
        have := D.le_rank
        omega⟩) :
    b.RepresentationOrderCondition c le_rfl := by
  apply lemma716_orderCondition_of_two_exception_clauses b c s
    D.two_le D.le_rank
  · intro i hi
    exact Or.inl (lemma716_typeI_prefix_order_le a b c R s D hfirst
      hthird hnorm hvalues i hi)
  · intro i hi
    exact lemma716_orderClause_of_tail_order_eq a b c s hac horders i hi
  · exact hleft
  · exact hright

variable [DyadicDiscriminantClassLaws K]

/-- In type II, all of condition 2.1(i) follows from the single printed
exceptional-coordinate calculation. -/
theorem lemma716_typeII_orderCondition_of_exception_clause
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hII : Lemma714IsTypeII a R s) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η j)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (hexception : Beli2019Lemma716OrderClause b c
      ⟨s - 1, by
        have := D.le_rank
        omega⟩) :
    b.RepresentationOrderCondition c le_rfl := by
  apply lemma716_orderCondition_of_one_exception_clause b c s
    D.two_le D.le_rank
  · intro i hi
    exact Or.inl (lemma716_typeII_early_order_le a b c R s D hfirst
      hthird hnorm hII ε η hεUnit hηUnit hvalues i hi)
  · intro i hi
    exact lemma716_orderClause_of_tail_order_eq a b c s hac horders i hi
  · exact hexception

end BONG.GoodBONG

end Bong
