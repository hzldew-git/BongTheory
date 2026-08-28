/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Representation

/-!
# Beli (2019), the ordered set of valuation sequences

This file formalizes Definitions 2 and 3 and Lemmas 1.6--1.8 from the
preliminary section of Beli's representation paper. Indices are zero based;
the rank-changing relation is the one used by condition 2.1(i).
-/

namespace Bong

/-- A sequence in Beli's set `B_n`: entries two places apart are increasing.
The coefficient type defaults to `Int`, the value group used by BONG orders,
but is kept general so that the rational-valued `W`-sequence can use the same
ordered-set API. -/
structure BeliOrderSequence (n : Nat) (Gamma : Type := Int) [LE Gamma] where
  value : Fin n → Gamma
  twoStep (i : Nat) (hi : i + 2 < n) :
    value ⟨i, by omega⟩ ≤ value ⟨i + 2, hi⟩

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Access an entry using a natural-number index and an explicit bound. -/
def entry {n : Nat} (x : BeliOrderSequence n Gamma)
    (i : Nat) (hi : i < n) : Gamma :=
  x.value ⟨i, hi⟩

omit [AddCommGroup Gamma] [IsOrderedAddMonoid Gamma] in
@[ext]
theorem ext {n : Nat} {x y : BeliOrderSequence n Gamma}
    (h : x.value = y.value) : x = y := by
  cases x
  cases y
  cases h
  rfl

theorem adjacentSum_mono {n : Nat} (x : BeliOrderSequence n Gamma)
    (i : Nat) (hi : i + 2 < n) :
    x.entry i (by omega) + x.entry (i + 1) (by omega) ≤
      x.entry (i + 1) (by omega) + x.entry (i + 2) hi := by
  have h := x.twoStep i hi
  change x.entry i (by omega) ≤ x.entry (i + 2) hi at h
  calc
    x.entry i (by omega) + x.entry (i + 1) (by omega) =
        x.entry (i + 1) (by omega) + x.entry i (by omega) := add_comm _ _
    _ ≤ x.entry (i + 1) (by omega) + x.entry (i + 2) hi :=
      add_le_add_right h _

end BeliOrderSequence

/-- Beli's rank-changing relation on valuation sequences. -/
structure BeliOrderLE {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
    [IsOrderedAddMonoid Gamma] {m n : Nat}
    (x : BeliOrderSequence m Gamma) (y : BeliOrderSequence n Gamma) : Prop where
  rank : n ≤ m
  compare (i : Nat) (hi : i < n) :
    x.entry i (hi.trans_le rank) ≤ y.entry i hi ∨
      ∃ (hi0 : 0 < i) (hiNext : i + 1 < m),
        x.entry i (hi.trans_le rank) + x.entry (i + 1) hiNext ≤
          y.entry (i - 1) (by omega) + y.entry i hi

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

theorem pairSum_le {m n : Nat} {x : BeliOrderSequence m Gamma}
    {y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    (i : Nat) (hi : i + 1 < n) :
    x.entry i (Nat.lt_of_lt_of_le (by omega) h.rank) +
        x.entry (i + 1) (hi.trans_le h.rank) ≤
      y.entry i (by omega) + y.entry (i + 1) hi := by
  rcases h.compare i (by omega) with hxi | ⟨hi0, hiNext, hpair⟩
  · rcases h.compare (i + 1) hi with hnext | ⟨_, hiNextNext, hpairNext⟩
    · exact add_le_add hxi hnext
    · have hxTwo := x.twoStep i (by omega)
      change x.entry i (by omega) ≤ x.entry (i + 2) (by omega) at hxTwo
      have hiEq : i + 1 + 1 = i + 2 := by omega
      have hPrev : i + 1 - 1 = i := by omega
      simp only [hiEq, hPrev] at hpairNext
      exact (x.adjacentSum_mono i (by omega)).trans hpairNext
  · have hyTwo := y.twoStep (i - 1) (by omega)
    have hiEq : i - 1 + 2 = i + 1 := by omega
    have hyTwo' : y.entry (i - 1) (by omega) ≤ y.entry (i + 1) hi := by
      simpa only [BeliOrderSequence.entry, hiEq] using hyTwo
    calc
      x.entry i (Nat.lt_of_lt_of_le (by omega) h.rank) +
          x.entry (i + 1) (hi.trans_le h.rank) ≤
        y.entry (i - 1) (by omega) + y.entry i (by omega) := hpair
      _ = y.entry i (by omega) + y.entry (i - 1) (by omega) := add_comm _ _
      _ ≤ y.entry i (by omega) + y.entry (i + 1) hi :=
        add_le_add_right hyTwo' _

/-- Lemma 1.6(ii). -/
theorem next_gt_previous_of_pair_gt {m n : Nat}
    {x : BeliOrderSequence m Gamma} {y : BeliOrderSequence n Gamma}
    (h : BeliOrderLE x y)
    (i : Nat) (hi0 : 0 < i) (hi : i < n) (hiNext : i + 1 < m)
    (hpair : y.entry (i - 1) (by omega) + y.entry i hi <
      x.entry i (hi.trans_le h.rank) + x.entry (i + 1) hiNext) :
    y.entry (i - 1) (by omega) < x.entry (i + 1) hiNext := by
  rcases h.compare i hi with hcurrent | ⟨_, _, hbound⟩
  · apply lt_of_add_lt_add_left
    calc
      x.entry i (hi.trans_le h.rank) + y.entry (i - 1) (by omega) =
          y.entry (i - 1) (by omega) +
            x.entry i (hi.trans_le h.rank) := add_comm _ _
      _ ≤ y.entry (i - 1) (by omega) + y.entry i hi :=
        add_le_add_right hcurrent _
      _ < x.entry i (hi.trans_le h.rank) + x.entry (i + 1) hiNext := hpair
  · exact (not_lt_of_ge hbound hpair).elim

/-- Lemma 1.6(iii). -/
theorem current_le_of_next_ge_previous {m n : Nat}
    {x : BeliOrderSequence m Gamma} {y : BeliOrderSequence n Gamma}
    (h : BeliOrderLE x y) (i : Nat) (hi0 : 0 < i) (hi : i < n)
    (hiNext : i + 1 < m)
    (hnext : y.entry (i - 1) (by omega) ≤ x.entry (i + 1) hiNext) :
    x.entry i (hi.trans_le h.rank) ≤ y.entry i hi := by
  rcases h.compare i hi with hcurrent | ⟨_, _, hpair⟩
  · exact hcurrent
  · apply le_of_add_le_add_right
    calc
      x.entry i (hi.trans_le h.rank) + x.entry (i + 1) hiNext ≤
          y.entry (i - 1) (by omega) + y.entry i hi := hpair
      _ ≤ x.entry (i + 1) hiNext + y.entry i hi :=
        add_le_add_left hnext _
      _ = y.entry i hi + x.entry (i + 1) hiNext := add_comm _ _

theorem first_le {m n : Nat} {x : BeliOrderSequence m Gamma}
    {y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y) (hn : 0 < n) :
    x.entry 0 (hn.trans_le h.rank) ≤ y.entry 0 hn := by
  rcases h.compare 0 hn with hfirst | ⟨hpos, _, _⟩
  · exact hfirst
  · exact (Nat.lt_irrefl 0 hpos).elim

theorem current_le_of_previous_eq {m n : Nat}
    {x : BeliOrderSequence m Gamma} {y : BeliOrderSequence n Gamma}
    (h : BeliOrderLE x y) (i : Nat) (hi0 : 0 < i) (hi : i < n)
    (hprevious : x.entry (i - 1) (Nat.lt_of_lt_of_le (by omega) h.rank) =
      y.entry (i - 1) (by omega)) :
    x.entry i (hi.trans_le h.rank) ≤ y.entry i hi := by
  rcases h.compare i hi with hcurrent | ⟨_, hiNext, hpair⟩
  · exact hcurrent
  · have hxTwo := x.twoStep (i - 1) (by omega)
    have hiEq : i - 1 + 2 = i + 1 := by omega
    have hxTwo' :
        x.entry (i - 1) (Nat.lt_of_lt_of_le (by omega) h.rank) ≤
          x.entry (i + 1) hiNext := by
      simpa only [BeliOrderSequence.entry, hiEq] using hxTwo
    have hyPrevious : y.entry (i - 1) (by omega) ≤
        x.entry (i + 1) hiNext := by
      rw [← hprevious]
      exact hxTwo'
    apply le_of_add_le_add_right
    calc
      x.entry i (hi.trans_le h.rank) + x.entry (i + 1) hiNext ≤
          y.entry (i - 1) (by omega) + y.entry i hi := hpair
      _ ≤ x.entry (i + 1) hiNext + y.entry i hi :=
        add_le_add_left hyPrevious _
      _ = y.entry i hi + x.entry (i + 1) hiNext := add_comm _ _

theorem refl {n : Nat} (x : BeliOrderSequence n Gamma) : BeliOrderLE x x where
  rank := le_rfl
  compare := by
    intro i hi
    exact Or.inl le_rfl

theorem trans {l m n : Nat} {x : BeliOrderSequence l Gamma}
    {y : BeliOrderSequence m Gamma} {z : BeliOrderSequence n Gamma}
    (hxy : BeliOrderLE x y) (hyz : BeliOrderLE y z) : BeliOrderLE x z where
  rank := hyz.rank.trans hxy.rank
  compare := by
    intro i hi
    have him : i < m := hi.trans_le hyz.rank
    rcases hxy.compare i him with hxyCurrent | ⟨hi0, hiNext, hxyPair⟩
    · rcases hyz.compare i hi with hyzCurrent | ⟨hi0, hiNextY, hyzPair⟩
      · exact Or.inl (hxyCurrent.trans hyzCurrent)
      · refine Or.inr ⟨hi0, hiNextY.trans_le hxy.rank, ?_⟩
        have hpair := hxy.pairSum_le i (by omega)
        exact hpair.trans hyzPair
    · refine Or.inr ⟨hi0, hiNext, ?_⟩
      have hpair := hyz.pairSum_le (i - 1) (by omega)
      have hiEq : i - 1 + 1 = i := by omega
      have hpair' :
          y.entry (i - 1) (by omega) + y.entry i him ≤
            z.entry (i - 1) (by omega) + z.entry i hi := by
        simpa only [hiEq] using hpair
      exact hxyPair.trans hpair'

theorem antisymm {n : Nat} {x y : BeliOrderSequence n Gamma}
    (hxy : BeliOrderLE x y) (hyx : BeliOrderLE y x) : x = y := by
  apply BeliOrderSequence.ext
  funext i
  have hpoint : ∀ k : Nat, ∀ hk : k < n, x.entry k hk = y.entry k hk := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact le_antisymm (hxy.first_le hk) (hyx.first_le hk)
    | succ k ih =>
        intro hk
        have hprevious := ih (by omega)
        apply le_antisymm
        · exact hxy.current_le_of_previous_eq (k + 1) (by omega) hk hprevious
        · exact hyx.current_le_of_previous_eq (k + 1) (by omega) hk hprevious.symm
  exact hpoint i.val i.isLt

end BeliOrderLE

/-- The disjoint union `B = ⋃ B_n` from Definition 2. -/
def BeliOrderFamily (Gamma : Type := Int) [AddCommGroup Gamma]
    [LinearOrder Gamma] [IsOrderedAddMonoid Gamma] :=
  Σ n, BeliOrderSequence n Gamma

instance {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
    [IsOrderedAddMonoid Gamma] :
    PartialOrder (BeliOrderFamily Gamma) where
  le x y := BeliOrderLE x.2 y.2
  le_refl x := BeliOrderLE.refl x.2
  le_trans _ _ _ := BeliOrderLE.trans
  le_antisymm := by
    rintro ⟨m, x⟩ ⟨n, y⟩ hxy hyx
    have hmn : m = n := Nat.le_antisymm hyx.rank hxy.rank
    subst n
    have hsequence := BeliOrderLE.antisymm hxy hyx
    cases hsequence
    rfl

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Definition 3: the additional adjacent bound defining `B_n(κ)`. -/
def IsKappaBounded {n : Nat} (x : BeliOrderSequence n Gamma)
    (κ : Gamma) : Prop :=
  ∀ (i : Nat) (hi : i + 1 < n), x.entry i (by omega) ≤ x.entry (i + 1) hi + κ

/-- Lemma 1.8(i), using a large forward gap in the first sequence. -/
theorem le_of_large_forwardGap {m n : Nat}
    {x : BeliOrderSequence m Gamma} {y : BeliOrderSequence n Gamma}
    {κ : Gamma} (hxy : BeliOrderLE x y)
    (hy : y.IsKappaBounded κ) (i : Nat) (hi : i < n)
    (hiNext : i + 1 < m)
    (hgap : κ ≤ x.entry (i + 1) hiNext - x.entry i (hi.trans_le hxy.rank)) :
    x.entry i (hi.trans_le hxy.rank) ≤ y.entry i hi := by
  rcases hxy.compare i hi with hcurrent | ⟨hi0, _, hpair⟩
  · exact hcurrent
  · have hyBound := hy (i - 1) (by omega)
    have hiEq : i - 1 + 1 = i := by omega
    simp only [hiEq] at hyBound
    by_cases hcurrent : x.entry i (hi.trans_le hxy.rank) ≤ y.entry i hi
    · exact hcurrent
    · have hyCurrent : y.entry i hi ≤
          x.entry i (hi.trans_le hxy.rank) := (lt_of_not_ge hcurrent).le
      have hxGap : x.entry i (hi.trans_le hxy.rank) + κ ≤
          x.entry (i + 1) hiNext := by
        simpa only [add_comm] using add_le_of_le_sub_right hgap
      have hprevious : y.entry (i - 1) (by omega) ≤
          x.entry (i + 1) hiNext :=
        hyBound.trans <| (add_le_add_left hyCurrent κ).trans hxGap
      exact hxy.current_le_of_next_ge_previous i hi0 hi hiNext hprevious

/-- Lemma 1.8(i), using a large backward gap in the second sequence. -/
theorem le_of_large_backwardGap {m n : Nat}
    {x : BeliOrderSequence m Gamma} {y : BeliOrderSequence n Gamma}
    {κ : Gamma} (hxy : BeliOrderLE x y)
    (hx : x.IsKappaBounded κ) (i : Nat) (hi0 : 0 < i) (hi : i < n)
    (hgap : κ ≤ y.entry i hi - y.entry (i - 1) (by omega)) :
    x.entry i (hi.trans_le hxy.rank) ≤ y.entry i hi := by
  rcases hxy.compare i hi with hcurrent | ⟨_, hiNext, hpair⟩
  · exact hcurrent
  · have hxBound := hx i hiNext
    by_cases hcurrent : x.entry i (hi.trans_le hxy.rank) ≤ y.entry i hi
    · exact hcurrent
    · have hyCurrent : y.entry i hi ≤
          x.entry i (hi.trans_le hxy.rank) := (lt_of_not_ge hcurrent).le
      have hyGap : y.entry (i - 1) (by omega) + κ ≤ y.entry i hi := by
        simpa only [add_comm] using add_le_of_le_sub_right hgap
      have hpreviousWithKappa : y.entry (i - 1) (by omega) + κ ≤
          x.entry (i + 1) hiNext + κ :=
        hyGap.trans <| hyCurrent.trans hxBound
      have hprevious : y.entry (i - 1) (by omega) ≤
          x.entry (i + 1) hiNext :=
        le_of_add_le_add_right hpreviousWithKappa
      exact hxy.current_le_of_next_ge_previous i hi0 hi hiNext hprevious

/-- Lemma 1.8(ii). -/
theorem le_pair_of_large_crossGap {m n : Nat}
    {x : BeliOrderSequence m Gamma} {y : BeliOrderSequence n Gamma}
    {κ : Gamma} (hxy : BeliOrderLE x y)
    (hx : x.IsKappaBounded κ) (hy : y.IsKappaBounded κ)
    (i : Nat) (hi : i < n) (hiNext : i + 1 < m)
    (hgap : κ ≤ x.entry (i + 1) hiNext - y.entry i hi) :
    x.entry i (hi.trans_le hxy.rank) ≤ y.entry i hi ∧
      ∀ hiSmallNext : i + 1 < n,
        x.entry (i + 1) (hiSmallNext.trans_le hxy.rank) ≤
          y.entry (i + 1) hiSmallNext := by
  constructor
  · rcases hxy.compare i hi with hcurrent | ⟨hi0, _, hpair⟩
    · exact hcurrent
    · have hyBound := hy (i - 1) (by omega)
      have hiEq : i - 1 + 1 = i := by omega
      simp only [hiEq] at hyBound
      have hxGap : y.entry i hi + κ ≤ x.entry (i + 1) hiNext := by
        simpa only [add_comm] using add_le_of_le_sub_right hgap
      have hprevious : y.entry (i - 1) (by omega) ≤
          x.entry (i + 1) hiNext := hyBound.trans hxGap
      exact hxy.current_le_of_next_ge_previous i hi0 hi hiNext hprevious
  · intro hiSmallNext
    rcases hxy.compare (i + 1) hiSmallNext with hcurrent | ⟨_, hiTwo, hpair⟩
    · exact hcurrent
    · have hxBound := hx (i + 1) hiTwo
      have hPrev : i + 1 - 1 = i := by omega
      have hNext : i + 1 + 1 = i + 2 := by omega
      simp only [hPrev, hNext] at hpair hxBound
      have hxGap : y.entry i hi + κ ≤ x.entry (i + 1) hiNext := by
        simpa only [add_comm] using add_le_of_le_sub_right hgap
      have hmiddleWithKappa : y.entry i hi + κ ≤
          x.entry (i + 2) hiTwo + κ := hxGap.trans hxBound
      have hmiddle : y.entry i hi ≤ x.entry (i + 2) hiTwo :=
        le_of_add_le_add_right hmiddleWithKappa
      apply le_of_add_le_add_right
      calc
        x.entry (i + 1) (hiSmallNext.trans_le hxy.rank) +
            x.entry (i + 2) hiTwo ≤
          y.entry i hi + y.entry (i + 1) hiSmallNext := hpair
        _ ≤ x.entry (i + 2) hiTwo + y.entry (i + 1) hiSmallNext :=
          add_le_add_left hmiddle _
        _ = y.entry (i + 1) hiSmallNext + x.entry (i + 2) hiTwo :=
          add_comm _ _

end BeliOrderSequence

namespace BONG.GoodBONG

open BeliOrderSequence

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- The valuation sequence of a good BONG, regarded as an element of `B_n`. -/
noncomputable def orderSequence (b : GoodBONG q L n) : BeliOrderSequence n where
  value := b.order
  twoStep := by
    intro i hi
    exact b.good ⟨i, by omega⟩ hi

@[simp]
theorem orderSequence_at (b : GoodBONG q L n) (i : Nat) (hi : i < n) :
    b.orderSequence.entry i hi = b.order ⟨i, hi⟩ :=
  rfl

/-- Condition 2.1(i) is exactly Beli's order on valuation sequences. -/
theorem representationOrderCondition_iff
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hRank : n ≤ m) :
    a.RepresentationOrderCondition b hRank ↔
      BeliOrderLE a.orderSequence b.orderSequence := by
  constructor
  · intro h
    refine ⟨by omega, ?_⟩
    intro i hi
    rcases h ⟨i, hi⟩ with hcurrent | ⟨hi0, hiNext, hpair⟩
    · exact Or.inl hcurrent
    · exact Or.inr ⟨hi0, hiNext, hpair⟩
  · intro h i
    rcases h.compare i.val i.isLt with hcurrent | ⟨hi0, hiNext, hpair⟩
    · exact Or.inl hcurrent
    · exact Or.inr ⟨hi0, hiNext, hpair⟩

end BONG.GoodBONG

end Bong
