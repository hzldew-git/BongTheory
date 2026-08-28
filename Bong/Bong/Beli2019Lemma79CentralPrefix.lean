/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralAssembly

/-!
# Beli (2019), Lemma 7.9(iii): the difference-prefix trigger

Lemma 2.18 turns an active central trigger into a strict sum involving the
current target alpha.  Capping the other term by the neighboring target
alpha gives the paper's two alternatives

`beta_(i-1) + beta_i > 2e` or `beta_i + beta_(i+1) > 2e`.

For a nonterminal index, property P6 then converts these alternatives into
strict two-step growth on the left or on the right.  This is the common
entry point for the remaining profile-specific cases.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- Capped form of the two adjacent-alpha alternatives at an active target
boundary.  It remains valid at the full endpoint, where the right cap is
`top`. -/
theorem centralTrigger_targetAdjacentCapAlternative
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (hdefect : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : b.centralAlphaTrigger c i) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.prefixAlphaCap (i.val - 1) ∨
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.prefixAlphaCap (i.val + 1) := by
  rcases b.beli2019Lemma218_target c hdefect i htrigger with
    hprevious | hcurrent
  · left
    apply hprevious.trans_le
    apply add_le_add le_rfl
    calc
      b.representationAlpha c i.previous ≤
          b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1) := by
        have hraw := hdefect i.previous
        rw [← b.coe_representationAlphaValue c i.previous]
        simpa only [CentralRepresentationIndex.previous] using hraw
      _ ≤ b.prefixAlphaCap (i.val - 1) :=
        b.truncatedPrefixDefect_le_leftCap c 1
          (i.val - 1) (i.val - 1)
  · right
    apply hcurrent.trans_le
    apply add_le_add le_rfl
    unfold centralCurrentDefect
    exact b.truncatedPrefixDefect_le_leftCap c (-1)
      (i.val + 1) (i.val - 1)

/-- At a nonterminal boundary the capped alternatives are exactly the two
strict adjacent target-alpha sums printed in Lemma 7.9(iii). -/
theorem centralTrigger_targetAdjacentAlphaAlternative
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (hdefect : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (htrigger : b.centralAlphaTrigger c i) :
    2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 2, by omega⟩ +
          b.alphaValue ⟨i.val - 1, by omega⟩ ∨
      2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 1, by omega⟩ +
          b.alphaValue ⟨i.val, by omega⟩ := by
  have hcaps := b.centralTrigger_targetAdjacentCapAlternative
    c hdefect i htrigger
  rw [b.prefixAlphaCap_of_internal (by
        have := i.one_lt
        omega) i.lt_large,
    b.prefixAlphaCap_of_internal (by
        have := i.one_lt
        omega) (by
          have := i.lt_large
          omega),
    b.prefixAlphaCap_of_internal (by
        have := i.one_lt
        omega) hiNext] at hcaps
  rcases hcaps with hleft | hright
  · left
    have hleftQ :
        2 * (ramificationIndex K : ℚ) <
          b.alphaValue ⟨i.val - 1, by omega⟩ +
            b.alphaValue ⟨i.val - 1 - 1, by omega⟩ := by
      exact_mod_cast hleft
    have hprevious :
        (⟨i.val - 1 - 1, by omega⟩ : Fin (n + 1)) =
          ⟨i.val - 2, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [hprevious] at hleftQ
    simpa only [add_comm] using hleftQ
  · right
    have hrightQ :
        2 * (ramificationIndex K : ℚ) <
          b.alphaValue ⟨i.val - 1, by omega⟩ +
            b.alphaValue ⟨i.val + 1 - 1, by omega⟩ := by
      exact_mod_cast hright
    have hcurrent :
        (⟨i.val + 1 - 1, by omega⟩ : Fin (n + 1)) =
          ⟨i.val, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    simpa only [hcurrent] using hrightQ

/-- A nonterminal active boundary forces strict target-order growth across
one of its two neighboring two-step intervals. -/
theorem centralTrigger_targetTwoStepAlternative
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (hdefect : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (htrigger : b.centralAlphaTrigger c i) :
    b.order ⟨i.val - 2, by omega⟩ < b.order ⟨i.val, i.lt_large⟩ ∨
      b.order ⟨i.val - 1, by omega⟩ <
        b.order ⟨i.val + 1, hiNext⟩ := by
  rcases b.centralTrigger_targetAdjacentAlphaAlternative
      c hdefect i hiNext htrigger with hleft | hright
  · exact Or.inl (b.order_twoStep_lt_of_alphaSum_gt_twoE i hleft)
  · let j : CentralRepresentationIndex (n + 2) (n + 2) :=
      ⟨i.val + 1, by
        have := i.one_lt
        omega, hiNext, by
          have := hiNext
          omega⟩
    have hj := b.order_twoStep_lt_of_alphaSum_gt_twoE j (by
      simpa only [j, show i.val + 1 - 2 = i.val - 1 by omega,
        show i.val + 1 - 1 = i.val by omega] using hright)
    exact Or.inr (by
      simpa only [j, show i.val + 1 - 2 = i.val - 1 by omega] using hj)

end BONG.GoodBONG

end Bong
