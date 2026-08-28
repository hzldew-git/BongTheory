/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019EssentialIndex

/-!
# Beli (2019), Section 4: the key-lemma interface for condition (ii)

This file records the two branches of Lemma 4.2 with the paper's endpoint
conventions and proves the complete logical assembly of condition 2.1(ii).
The remaining local arithmetic is exposed by `SectionFourDefectReduction`:
its fields are precisely Lemma 2.12 and the two uses of Lemma 2.11, rather
than a global transitivity assumption.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U}
  {n : Nat}

/-! ## Indices surrounding an ordinary representation boundary -/

/-- The essential index at the left end of an ordinary boundary `j`.
In the paper this is the index `i = j`. -/
def currentEssentialIndex
    (j : RepresentationIndex (n + 1) (n + 1)) : Fin (n + 1) :=
  ⟨j.val - 1, by have := j.pos; have := j.lt_large; omega⟩

/-- The essential index at the right end of an ordinary boundary `j`.
In the paper this is the index `i = j + 1`. -/
def nextEssentialIndex
    (j : RepresentationIndex (n + 1) (n + 1)) : Fin (n + 1) :=
  ⟨j.val, j.lt_large⟩

/-- The ordinary boundary immediately preceding `j`. -/
def previousRepresentationIndex
    (j : RepresentationIndex (n + 1) (n + 1)) (hprev : 1 < j.val) :
    RepresentationIndex (n + 1) (n + 1) where
  val := j.val - 1
  pos := by omega
  lt_large := by have := j.lt_large; omega
  le_small := by have := j.lt_large; omega

/-- The ordinary boundary immediately following `j`. -/
def nextRepresentationIndex
    (j : RepresentationIndex (n + 1) (n + 1))
    (hnext : j.val + 1 < n + 1) :
    RepresentationIndex (n + 1) (n + 1) where
  val := j.val + 1
  pos := by omega
  lt_large := hnext
  le_small := Nat.le_of_lt hnext

/-- The current essential index is the one immediately before the next one. -/
theorem currentEssentialIndex_val
    (j : RepresentationIndex (n + 1) (n + 1)) :
    (currentEssentialIndex j).val + 1 = j.val := by
  simp only [currentEssentialIndex]
  have := j.pos
  omega

@[simp]
theorem nextEssentialIndex_val
    (j : RepresentationIndex (n + 1) (n + 1)) :
    (nextEssentialIndex j).val = j.val :=
  rfl

/-- The left endpoint of `j` is essential for `a,c`. -/
def IsCurrentEssential
    (a : GoodBONG q L (n + 1)) (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1)) : Prop :=
  a.IsEssentialFor c (currentEssentialIndex j)

/-- The right endpoint of `j` is essential for `a,c`. -/
def IsNextEssential
    (a : GoodBONG q L (n + 1)) (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1)) : Prop :=
  a.IsEssentialFor c (nextEssentialIndex j)

/-! ## The two direct-branch tests in Lemma 4.2 -/

/-- Lemma 4.2(i)'s direct-branch test at an essential index.  The universal
form makes the cases `i = 2` and `i = rank` true automatically. -/
def KeyLemmaLeftDirectTrigger
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1)) (i : Fin (n + 1)) : Prop :=
  ∀ (hiTwo : 1 < i.val) (hiNext : i.val + 1 < n + 1),
    c.order ⟨i.val - 2, by omega⟩ + c.order ⟨i.val - 1, by omega⟩ <
      a.order ⟨i.val + 1, hiNext⟩ + b.order ⟨i.val, i.isLt⟩

/-- Lemma 4.2(ii)'s direct-branch test at an essential index.  The universal
form makes the cases `i = 1` and `i = rank - 1` true automatically. -/
def KeyLemmaRightDirectTrigger
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1)) (i : Fin (n + 1)) : Prop :=
  ∀ (hiPos : 0 < i.val) (hiTwo : i.val + 2 < n + 1),
    b.order ⟨i.val, by omega⟩ + c.order ⟨i.val - 1, by omega⟩ <
      a.order ⟨i.val + 1, by omega⟩ + a.order ⟨i.val + 2, by omega⟩

theorem keyLemmaLeftDirectTrigger_of_eq_one
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1)) (i : Fin (n + 1)) (hi : i.val = 1) :
    a.KeyLemmaLeftDirectTrigger b c i := by
  intro hiTwo
  omega

theorem keyLemmaLeftDirectTrigger_of_last
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1)) (i : Fin (n + 1))
    (hi : i.val + 1 = n + 1) :
    a.KeyLemmaLeftDirectTrigger b c i := by
  intro _ hiNext
  omega

theorem keyLemmaRightDirectTrigger_of_zero
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1)) (i : Fin (n + 1)) (hi : i.val = 0) :
    a.KeyLemmaRightDirectTrigger b c i := by
  intro hiPos
  omega

theorem keyLemmaRightDirectTrigger_of_penultimate
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1)) (i : Fin (n + 1))
    (hi : i.val + 2 = n + 1) :
    a.KeyLemmaRightDirectTrigger b c i := by
  intro _ hiTwo
  omega

/-! ## Shifted bounds in the fallback branches -/

/-- The bound `T_(j-1) - T_j + B_(j-1)` in Lemma 4.2(ii). -/
noncomputable def currentFallbackBound
    (_a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1)) (hprev : 1 < j.val) :
    WithTop ℚ :=
  (((c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
    b.representationAlpha c (previousRepresentationIndex j hprev)

/-- The bound `R_(j+1) - R_(j+2) + A_(j+1)` in Lemma 4.2(i). -/
noncomputable def nextFallbackBound
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hnext : j.val + 1 < n + 1) : WithTop ℚ :=
  (((a.order ⟨j.val, j.lt_large⟩ - a.order ⟨j.val + 1, hnext⟩ :
      Int) : ℚ) : WithTop ℚ) +
    a.representationAlpha b (nextRepresentationIndex j hnext)

/-- Lemma 4.2, expressed once for every ordinary boundary.  Its `current`
field is part (ii), and its `next` field is part (i) at the following
essential index. -/
structure SectionFourKeyLemmaBounds
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1)) : Prop where
  current (j : RepresentationIndex (n + 1) (n + 1)) :
    a.IsCurrentEssential c j →
      (a.KeyLemmaRightDirectTrigger b c (currentEssentialIndex j) →
        a.representationAlpha c j ≤ a.representationAlpha b j ∧
          a.representationAlpha c j ≤ b.representationAlpha c j) ∧
      (¬a.KeyLemmaRightDirectTrigger b c (currentEssentialIndex j) →
        ∃ hprev : 1 < j.val,
          a.representationAlpha c j ≤
            a.currentFallbackBound b c j hprev)
  next (j : RepresentationIndex (n + 1) (n + 1)) :
    a.IsNextEssential c j →
      (a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j) →
        a.representationAlpha c j ≤ a.representationAlpha b j ∧
          a.representationAlpha c j ≤ b.representationAlpha c j) ∧
      (¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j) →
        ∃ hnext : j.val + 1 < n + 1,
          a.representationAlpha c j ≤
            a.nextFallbackBound b j hnext)

/-! ## Reduction of the shifted branches to the target defect -/

/-- Condition 2.1(ii) at one boundary, stated directly with `A_i`. -/
noncomputable def RepresentationDefectAt
    (a : GoodBONG q L (n + 1)) (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1)) : Prop :=
  a.representationAlpha c j ≤ a.truncatedPrefixDefect c 1 j.val j.val

theorem representationDefectCondition_iff_forall_at
    (a : GoodBONG q L (n + 1)) (c : GoodBONG s N (n + 1)) :
    a.RepresentationDefectCondition c ↔
      ∀ j : RepresentationIndex (n + 1) (n + 1),
        a.RepresentationDefectAt c j := by
  unfold RepresentationDefectCondition RepresentationDefectAt
  simp only [a.coe_representationAlphaValue c]

/-- A source instance of condition (ii) bounds `A_j` by the left BONG's
internal alpha at the same prefix boundary. -/
theorem representationAlpha_le_leftAlpha
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hab : a.RepresentationDefectCondition b)
    (j : RepresentationIndex (n + 1) (n + 1)) :
    a.representationAlpha b j ≤
      (a.alphaValue ⟨j.val - 1, by
        have := j.pos
        have := j.lt_large
        omega⟩ : WithTop ℚ) := by
  have habAt : a.representationAlpha b j ≤
      a.truncatedPrefixDefect b 1 j.val j.val := by
    simpa only [← a.coe_representationAlphaValue b j] using hab j
  calc
    a.representationAlpha b j ≤
        a.truncatedPrefixDefect b 1 j.val j.val := habAt
    _ ≤ a.prefixAlphaCap j.val :=
      a.truncatedPrefixDefect_le_leftCap b 1 j.val j.val
    _ = (a.alphaValue ⟨j.val - 1, by
        have := j.pos
        have := j.lt_large
        omega⟩ : WithTop ℚ) :=
      a.prefixAlphaCap_of_internal j.pos j.lt_large

/-- A source instance of condition (ii) bounds `A_j` by the right BONG's
internal alpha at the same prefix boundary. -/
theorem representationAlpha_le_rightAlpha
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hab : a.RepresentationDefectCondition b)
    (j : RepresentationIndex (n + 1) (n + 1)) :
    a.representationAlpha b j ≤
      (b.alphaValue ⟨j.val - 1, by
        have := j.pos
        have := j.lt_large
        omega⟩ : WithTop ℚ) := by
  have habAt : a.representationAlpha b j ≤
      a.truncatedPrefixDefect b 1 j.val j.val := by
    simpa only [← a.coe_representationAlphaValue b j] using hab j
  calc
    a.representationAlpha b j ≤
        a.truncatedPrefixDefect b 1 j.val j.val := habAt
    _ ≤ b.prefixAlphaCap j.val :=
      a.truncatedPrefixDefect_le_rightCap b 1 j.val j.val
    _ = (b.alphaValue ⟨j.val - 1, by
        have := j.pos
        have := j.lt_large
        omega⟩ : WithTop ℚ) :=
      b.prefixAlphaCap_of_internal j.pos j.lt_large

/-- The alpha version of `currentFallbackBound`, obtained by applying
Lemma 2.11(ii) to the pair `a,c`. -/
noncomputable def currentFallbackAlphaBound
    (_a : GoodBONG q L (n + 1)) (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1)) (hprev : 1 < j.val) :
    WithTop ℚ :=
  (((c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
    (c.alphaValue ⟨j.val - 2, by have := j.lt_large; omega⟩ : WithTop ℚ)

/-- The alpha version of `nextFallbackBound`, obtained by applying
Lemma 2.11(i) to the pair `a,c`. -/
noncomputable def nextFallbackAlphaBound
    (a : GoodBONG q L (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hnext : j.val + 1 < n + 1) : WithTop ℚ :=
  (((a.order ⟨j.val, j.lt_large⟩ - a.order ⟨j.val + 1, hnext⟩ :
      Int) : ℚ) : WithTop ℚ) +
    (a.alphaValue ⟨j.val, by omega⟩ : WithTop ℚ)

/-- The exact local results still needed after Lemma 4.2.  `nonessential`
is Lemma 2.12.  The other fields are the two Lemma 2.11 equivalences after
the order inequalities established in Section 4's fallback cases. -/
structure SectionFourDefectReduction
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1)) : Prop where
  nonessential (j : RepresentationIndex (n + 1) (n + 1)) :
    ¬a.IsCurrentEssential c j → ¬a.IsNextEssential c j →
      a.RepresentationDefectAt c j
  currentFallback (j : RepresentationIndex (n + 1) (n + 1))
      (hprev : 1 < j.val) :
    a.IsCurrentEssential c j →
      ¬a.KeyLemmaRightDirectTrigger b c (currentEssentialIndex j) →
      (a.RepresentationDefectAt c j ↔
        a.representationAlpha c j ≤
          a.currentFallbackAlphaBound c j hprev)
  nextFallback (j : RepresentationIndex (n + 1) (n + 1))
      (hnext : j.val + 1 < n + 1) :
    a.IsNextEssential c j →
      ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j) →
      (a.RepresentationDefectAt c j ↔
        a.representationAlpha c j ≤
          a.nextFallbackAlphaBound j hnext)

/-- Lemma 4.2 plus Lemmas 2.11-2.12 imply transitivity of condition
2.1(ii).  All endpoint and essential-index cases are discharged here. -/
theorem representationDefectCondition_trans_of_keyLemma
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationDefectCondition b)
    (hbc : b.RepresentationDefectCondition c)
    (hkey : SectionFourKeyLemmaBounds a b c)
    (hreduce : SectionFourDefectReduction a b c) :
    a.RepresentationDefectCondition c := by
  rw [a.representationDefectCondition_iff_forall_at c]
  intro j
  by_cases hcurrent : a.IsCurrentEssential c j
  · have hbranches := hkey.current j hcurrent
    by_cases hdirect :
        a.KeyLemmaRightDirectTrigger b c (currentEssentialIndex j)
    · have hb := hbranches.1 hdirect
      simpa only [RepresentationDefectAt,
        ← a.coe_representationAlphaValue c j] using
        a.representationDefectAt_trans_of_bounds b c j hab hbc hb.1 hb.2
    · rcases hbranches.2 hdirect with ⟨hprev, hbound⟩
      apply (hreduce.currentFallback j hprev hcurrent hdirect).mpr
      have hAlpha := b.representationAlpha_le_rightAlpha c hbc
        (previousRepresentationIndex j hprev)
      unfold currentFallbackBound at hbound
      unfold currentFallbackAlphaBound
      apply hbound.trans
      gcongr
      simpa only [previousRepresentationIndex, Nat.sub_sub,
        Nat.reduceAdd] using hAlpha
  · by_cases hnext : a.IsNextEssential c j
    · have hbranches := hkey.next j hnext
      by_cases hdirect :
          a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)
      · have hb := hbranches.1 hdirect
        simpa only [RepresentationDefectAt,
          ← a.coe_representationAlphaValue c j] using
          a.representationDefectAt_trans_of_bounds b c j hab hbc hb.1 hb.2
      · rcases hbranches.2 hdirect with ⟨hnextIndex, hbound⟩
        apply (hreduce.nextFallback j hnextIndex hnext hdirect).mpr
        have hAlpha := a.representationAlpha_le_leftAlpha b hab
          (nextRepresentationIndex j hnextIndex)
        unfold nextFallbackBound at hbound
        unfold nextFallbackAlphaBound
        apply hbound.trans
        gcongr
        simpa only [nextRepresentationIndex, Nat.add_sub_cancel] using hAlpha
    · exact hreduce.nonessential j hcurrent hnext

end BONG.GoodBONG

end Bong
