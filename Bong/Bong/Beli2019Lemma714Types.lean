/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714Plateau

/-!
# Beli (2019), the type-I/type-II split after Lemma 7.14

At the minimal even endpoint `s`, the next same-parity order is at least
`R + 1`.  Hence an interior endpoint has exactly the two alternatives used
in the paper: equality gives type II, while a further jump gives type I.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Case 1 following Lemma 7.14: the alternating segment reaches the end,
or the next entry has order at least `R + 2`. -/
def Lemma714IsTypeI
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat) : Prop :=
  s = n + 3 ∨
    ∃ hs : s < n + 3, R + 2 ≤ b.order ⟨s, hs⟩

/-- Case 2 following Lemma 7.14: the segment is interior and the next
entry has the exceptional order `R + 1`. -/
def Lemma714IsTypeII
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat) : Prop :=
  ∃ hs : s < n + 3, b.order ⟨s, hs⟩ = R + 1

/-- The order at the first position after the selected even segment is at
least `R + 1`, whenever that position exists. -/
theorem lemma714_nextOrder_ge
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714MinimalityData b R s)
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hs : s < n + 3) :
    R + 1 ≤ b.order ⟨s, hs⟩ := by
  have htwoBound : 2 < n + 3 := D.two_le.trans_lt hs
  have hparity : Even (s - 2) := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hmono := b.orderSequence.entryOrZero_le_of_evenGap
    2 s D.two_le hs hparity
  rw [b.orderSequence_entryOrZero_eq_order ⟨2, htwoBound⟩,
    b.orderSequence_entryOrZero_eq_order ⟨s, hs⟩] at hmono
  exact hthird.trans hmono

/-- The type-I/type-II alternatives after Lemma 7.14 are exhaustive. -/
theorem beli2019Lemma714_type_dichotomy
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714MinimalityData b R s)
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩) :
    Lemma714IsTypeI b R s ∨ Lemma714IsTypeII b R s := by
  by_cases hend : s = n + 3
  · exact Or.inl (Or.inl hend)
  · have hs : s < n + 3 := lt_of_le_of_ne D.le_rank hend
    have hlower := b.lemma714_nextOrder_ge R s D hthird hs
    by_cases heq : b.order ⟨s, hs⟩ = R + 1
    · exact Or.inr ⟨hs, heq⟩
    · exact Or.inl (Or.inr ⟨hs, by omega⟩)

/-- The two cases following Lemma 7.14 cannot overlap. -/
theorem lemma714_type_disjoint
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat) :
    ¬(Lemma714IsTypeI b R s ∧ Lemma714IsTypeII b R s) := by
  rintro ⟨hI, hII⟩
  rcases hII with ⟨hs, horder⟩
  rcases hI with hend | ⟨hs', hjump⟩
  · omega
  · have hfin : (⟨s, hs⟩ : Fin (n + 3)) = ⟨s, hs'⟩ := by
      apply Fin.ext
      rfl
    rw [← hfin, horder] at hjump
    omega

end BONG.GoodBONG

end Bong
