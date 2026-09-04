/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicProposition24
import Bong.Bong.Beli2019MainConditions
import Bong.Bong.Beli2019Lemma214Bounds

/-!
# He (2024), Lemma 3.1

This file formalizes the pointwise consequences of classic integrality used
in Lemma 3.1 of Zilong He, *On classic n-universal quadratic forms over
dyadic local fields*.  The publisher version is the semantic authority.

The `val` field of each representation index is the paper's one-based index.
The coefficient arrays themselves remain zero based.  Thus, for example,
`i.val = j` addresses condition (iii) at the paper index `j`.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace BONG.GoodBONG

/-- Theorem 2.5(i) at one paper index. -/
def HeClassicOrderConditionAt {m n : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 2))
    (hRank : n + 1 ≤ m + 1) (i : Fin (n + 2)) : Prop :=
  a.order ⟨i.val, by have := i.isLt; omega⟩ ≤ b.order i ∨
    ∃ (hi0 : 0 < i.val) (hiLarge : i.val + 1 < m + 2),
      a.order ⟨i.val, by have := i.isLt; omega⟩ +
          a.order ⟨i.val + 1, hiLarge⟩ ≤
        b.order ⟨i.val - 1, by have := i.isLt; omega⟩ + b.order i

/-- Theorem 2.5(iii) at one paper index, in the original alpha-trigger
form used by `RepresentationConditions`. -/
noncomputable def HeClassicCentralConditionAt {m n : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 2))
    (i : CentralRepresentationIndex (m + 2) (n + 2)) : Prop :=
  a.centralAlphaTrigger b i →
    DiagonalRepresents
      (b.prefixValues (i.val - 1) (by
        have := i.le_small_succ
        omega))
      (a.prefixValues i.val (by
        have := i.lt_large
        omega))

/-- Theorem 2.5(iv) at one paper index. -/
def HeClassicLongConditionAt {m n : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 2))
    (i : LongRepresentationIndex (m + 2) (n + 2)) : Prop :=
  ((if hi : i.val ≤ n + 2 then
      a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
        b.order ⟨i.val - 1, by have := i.one_lt; have := hi; omega⟩
    else True) ∧
    b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ + 2 * (ramificationIndex K : Int) <
      a.order ⟨i.val + 1, i.succ_lt_large⟩ ∧
    a.order ⟨i.val, by have := i.succ_lt_large; omega⟩ +
        2 * (ramificationIndex K : Int) ≤
      b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ + 2 * (ramificationIndex K : Int)) →
    DiagonalRepresents
      (b.prefixValues (i.val - 1) (by
        have := i.le_small_succ
        omega))
      (a.prefixValues (i.val + 1) (by
        have := i.succ_lt_large
        omega))

/-- The pointwise predicates recover exactly the corresponding fields of
the full representation conditions. -/
theorem heClassicOrderCondition_iff_forall_at {m n : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 2))
    (hRank : n + 1 ≤ m + 1) :
    a.RepresentationOrderCondition b hRank ↔
      ∀ i, a.HeClassicOrderConditionAt b hRank i := by
  rfl

theorem heClassicCentralConditions_iff_forall_at {m n : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 2)) :
    a.CentralRepresentationConditions b ↔
      ∀ i, a.HeClassicCentralConditionAt b i := by
  rfl

theorem heClassicLongConditions_iff_forall_at {m n : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 2)) :
    a.LongRepresentationConditions b ↔
      ∀ i, a.HeClassicLongConditionAt b i := by
  rfl

/-- Lemma 3.1(i): at a paper-odd index, `R_j=0` gives condition (i). -/
theorem he2022ClassicLemma31i {m n : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 2))
    (hRank : n + 1 ≤ m + 1) (hBClassic : Lattice.IsClassicIntegral r M)
    (i : Fin (n + 2)) (hiPaperOdd : Even i.val)
    (hRi : a.order ⟨i.val, by have := i.isLt; omega⟩ = 0) :
    a.HeClassicOrderConditionAt b hRank i := by
  left
  rw [hRi]
  have hbounds := (b.he2022ClassicProposition24 hBClassic).oddIndexed
    0 i (Fin.zero_le i) Even.zero hiPaperOdd
  exact hbounds.1.trans hbounds.2

/-- Lemma 3.1(ii): a zero adjacent source sum at an internal index gives
the second alternative of condition (i). -/
theorem he2022ClassicLemma31ii {m n : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 2))
    (hRank : n + 1 ≤ m + 1) (hBClassic : Lattice.IsClassicIntegral r M)
    (i : Fin (n + 2)) (hi0 : 0 < i.val)
    (hiLarge : i.val + 1 < m + 2)
    (hpair :
      a.order ⟨i.val, by have := i.isLt; omega⟩ +
        a.order ⟨i.val + 1, hiLarge⟩ = 0) :
    a.HeClassicOrderConditionAt b hRank i := by
  right
  refine ⟨hi0, hiLarge, ?_⟩
  let j : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have htarget :=
    (b.he2022ClassicProposition24 hBClassic).adjacentOrderSum j
  have hleft : j.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hright : j.succ = i := by
    apply Fin.ext
    simp only [j, Fin.val_succ]
    omega
  unfold adjacentOrderSum at htarget
  rw [hleft, hright] at htarget
  omega

/-- Lemma 3.1(iii), including its stated consequence: if the paper index
`j=i.val` is even and `R_(j+1)=0`, the strict premise of condition (iii)
is impossible. -/
theorem he2022ClassicLemma31iii {m n : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 2))
    (hBClassic : Lattice.IsClassicIntegral r M)
    (i : CentralRepresentationIndex (m + 2) (n + 2))
    (hiEven : Even i.val)
    (hnext : a.order ⟨i.val, i.lt_large⟩ = 0) :
    a.HeClassicCentralConditionAt b i := by
  intro htrigger
  exfalso
  have hpreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨t, ht⟩
    have htPos : 0 < t := by
      have := i.one_lt
      omega
    exact ⟨t - 1, by omega⟩
  let previous : Fin (n + 2) := ⟨i.val - 2, by
    have := i.one_lt
    have := i.le_small_succ
    omega⟩
  have hbounds :=
    (b.he2022ClassicProposition24 hBClassic).oddIndexed
      0 previous (Fin.zero_le previous) Even.zero (by
        simpa only [previous] using hpreviousEven)
  have htargetNonnegative : 0 ≤ b.order previous :=
    hbounds.1.trans hbounds.2
  exact (not_lt_of_ge htargetNonnegative) (by
    simpa only [previous, hnext] using htrigger.1)

/-- At an ordinary central index strictly beyond the first boundary, the
alpha trigger forces the second strict inequality in Beli's definition of
an essential index.  This is the unequal-rank form of the numerical
calculation used in Beli (2006), Lemma 4.9. -/
private theorem pair_lt_of_centralAlphaTrigger_of_ordinary
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    {m n : Nat} (a : GoodBONG q L (m + 2))
    (b : GoodBONG r M (n + 2))
    (i : CentralRepresentationIndex (m + 2) (n + 2))
    (hiThree : 2 < i.val) (hiOrdinary : i.val ≤ n + 2)
    (hiNext : i.val + 1 < m + 2)
    (htrigger : a.centralAlphaTrigger b i) :
    b.order ⟨i.val - 3, by omega⟩ +
        b.order ⟨i.val - 2, by omega⟩ <
      a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hiNext⟩ := by
  let previous : RepresentationIndex (m + 2) (n + 2) := i.previous
  let current : RepresentationIndex (m + 2) (n + 2) :=
    i.current hiOrdinary
  have hpreviousTwo : 1 < previous.val := by
    simp only [previous, CentralRepresentationIndex.previous]
    omega
  have hcurrentNext : current.val + 1 < m + 2 := by
    simp only [current, CentralRepresentationIndex.current]
    omega
  have hpreviousRaw := by
    letI : Beli2006AlphaLaws.{u, w} K := targetLaws
    exact (a.representationAlpha_le_prime b previous).trans
      (a.representationAlphaPrime_le_primaryRightHalfGap
        b previous hpreviousTwo)
  have hcurrentRaw :=
    (a.representationAlpha_le_prime b current).trans
      (a.representationAlphaPrime_le_primaryLeftHalfGap
        b current hcurrentNext)
  have hprevious := hpreviousRaw
  rw [← a.coe_representationAlphaValue b previous] at hprevious
  norm_cast at hprevious
  have hcurrent := hcurrentRaw
  rw [← a.coe_representationAlphaValue b current] at hcurrent
  norm_cast at hcurrent
  have hsum := htrigger.2
  unfold centralAdjustedAlpha at hsum
  rw [dif_pos hiOrdinary] at hsum
  norm_cast at hsum
  unfold halfGapValue orderGap at hprevious hcurrent
  have hprevious' :
      a.representationAlphaValue b previous ≤
        ((a.order ⟨i.val - 1, by omega⟩ : ℚ) -
          (b.order ⟨i.val - 2, by omega⟩ : ℚ)) +
          (((b.order ⟨i.val - 2, by omega⟩ : ℚ) -
            (b.order ⟨i.val - 3, by omega⟩ : ℚ)) / 2 +
            (ramificationIndex K : ℚ)) := by
    dsimp only [previous, CentralRepresentationIndex.previous] at hprevious
    push_cast at hprevious
    have htargetIndex :
        (⟨i.val - 1 - 1, by omega⟩ : Fin (n + 2)) =
          ⟨i.val - 2, by omega⟩ := by
      apply Fin.ext
      change i.val - 1 - 1 = i.val - 2
      omega
    let p : Fin (n + 1) := ⟨i.val - 1 - 2, by omega⟩
    have hpSucc : p.succ = ⟨i.val - 2, by omega⟩ := by
      apply Fin.ext
      simp only [p, Fin.val_succ]
      omega
    have hpCast : p.castSucc = ⟨i.val - 3, by omega⟩ := by
      apply Fin.ext
      simp only [p, Fin.val_castSucc]
      omega
    change a.representationAlphaValue b previous ≤
      (a.order ⟨i.val - 1, by omega⟩ : ℚ) -
          (b.order ⟨i.val - 1 - 1, by omega⟩ : ℚ) +
        (((b.order p.succ : ℚ) - (b.order p.castSucc : ℚ)) / 2 +
          (ramificationIndex K : ℚ)) at hprevious
    rw [htargetIndex, hpSucc, hpCast] at hprevious
    exact hprevious
  have hcurrent' :
      a.representationAlphaValue b current ≤
        ((a.order ⟨i.val, i.lt_large⟩ : ℚ) -
          (b.order ⟨i.val - 1, by omega⟩ : ℚ)) +
          (((a.order ⟨i.val + 1, hiNext⟩ : ℚ) -
            (a.order ⟨i.val, i.lt_large⟩ : ℚ)) / 2 +
            (ramificationIndex K : ℚ)) := by
    dsimp only [current, CentralRepresentationIndex.current] at hcurrent
    push_cast at hcurrent
    let p : Fin (m + 1) := ⟨i.val, by omega⟩
    have hpSucc : p.succ = ⟨i.val + 1, hiNext⟩ := by
      apply Fin.ext
      simp only [p, Fin.val_succ]
    have hpCast : p.castSucc = ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      simp only [p, Fin.val_castSucc]
    change a.representationAlphaValue b current ≤
      (a.order ⟨i.val, i.lt_large⟩ : ℚ) -
          (b.order ⟨i.val - 1, by omega⟩ : ℚ) +
        (((a.order p.succ : ℚ) - (a.order p.castSucc : ℚ)) / 2 +
          (ramificationIndex K : ℚ)) at hcurrent
    rw [hpSucc, hpCast] at hcurrent
    exact hcurrent
  have hsum' :
      2 * (ramificationIndex K : ℚ) +
          (a.order ⟨i.val - 1, by omega⟩ : ℚ) <
        a.representationAlphaValue b previous +
          ((b.order ⟨i.val - 1, by omega⟩ : ℚ) +
            a.representationAlphaValue b current) := by
    push_cast at hsum
    simpa only [previous, current,
      CentralRepresentationIndex.previous,
      CentralRepresentationIndex.current] using hsum
  have hordersQ :
      (b.order ⟨i.val - 3, by omega⟩ : ℚ) +
          (b.order ⟨i.val - 2, by omega⟩ : ℚ) <
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) +
          (a.order ⟨i.val + 1, hiNext⟩ : ℚ) := by
    linarith [hprevious', hcurrent', hsum']
  exact_mod_cast hordersQ

/-- Lemma 3.1(iv), in the range in which its displayed second essentiality
inequality exists.  The published lower bound `1 < j` includes `j = 2`,
where Beli's endpoint convention omits that inequality; the proof and every
later use in the paper require the corrected bound `2 < j`. -/
theorem he2022ClassicLemma31iv_corrected
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    {m n : Nat} (a : GoodBONG q L (m + 2))
    (b : GoodBONG r M (n + 2))
    (hBClassic : Lattice.IsClassicIntegral r M)
    (i : CentralRepresentationIndex (m + 2) (n + 2))
    (hiThree : 2 < i.val) (hiOrdinary : i.val ≤ n + 2)
    (hiNext : i.val + 1 < m + 2)
    (hpair :
      a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hiNext⟩ = 0) :
    a.HeClassicCentralConditionAt b i := by
  intro htrigger
  exfalso
  have hstrict := a.pair_lt_of_centralAlphaTrigger_of_ordinary
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    b i hiThree hiOrdinary hiNext htrigger
  let j : Fin (n + 1) := ⟨i.val - 3, by omega⟩
  have htarget :=
    (b.he2022ClassicProposition24 hBClassic).adjacentOrderSum j
  have hleft : j.castSucc =
      (⟨i.val - 3, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hright : j.succ =
      (⟨i.val - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [j, Fin.val_succ]
    omega
  unfold adjacentOrderSum at htarget
  rw [hleft, hright] at htarget
  omega

/-- Lemma 3.1(v): if `R_(j+2)-R_(j+1) ≤ 2e`, the strict premise
of condition (iv) is contradictory, so the pointwise implication holds. -/
theorem he2022ClassicLemma31v {m n : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 2))
    (i : LongRepresentationIndex (m + 2) (n + 2))
    (hgap :
      a.order ⟨i.val + 1, i.succ_lt_large⟩ -
          a.order ⟨i.val, by have := i.succ_lt_large; omega⟩ ≤
        2 * (ramificationIndex K : Int)) :
    a.HeClassicLongConditionAt b i := by
  rintro ⟨_, hstrict, hbound⟩
  exfalso
  omega

end BONG.GoodBONG

end Bong
