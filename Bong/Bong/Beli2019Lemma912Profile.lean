/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019IntermediateReduction
import Bong.Bong.Beli2019Lemma93Exceptional
import Bong.Bong.Beli2019Lemma96

/-!
# Beli (2019), Lemma 9.12: the initial residual profile

This file formalizes the first paragraph of Lemma 9.12 in the v2 paper.
The hypotheses of Lemmas 9.3 and 9.6 are transparent predicates on the two
selected good BONGs.  Their negations, together with condition 2.1(i) and
`R₁ = T₁`, imply the order, parity, sharp gap, and first-defect alternatives
used by every later construction in Lemma 9.12.

No representation conclusion or index-`p` sublattice is assumed here.
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
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- The printed hypothesis of Lemma 9.3 in the rank-at-least-five range:
the five alternatives of Lemma 9.1, or the final
`T₂ = R₂ + 1 ∧ R₁ = R₅` alternative. -/
noncomputable def Beli2019Lemma93V2Hypothesis
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5)) : Prop :=
  a.Lemma91Alternative c ∨ a.Beli2019Lemma93ExceptionalCondition c

/-- The printed hypothesis of Lemma 9.6, in zero-based notation. -/
def Beli2019Lemma96V2Hypothesis
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5)) : Prop :=
  a.order (0 : Fin (N + 5)) = a.order (2 : Fin (N + 5)) ∧
    a.order (0 : Fin (N + 5)) = c.order (0 : Fin (N + 5)) ∧
    a.orderGap (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2 ∧
    a.Beli2019Lemma96DefectBound c ∧
    a.Lemma814FirstThreeAnisotropic

/-- The exact numerical and first-defect alternatives established at the
start of the proof of Lemma 9.12. -/
structure Beli2019Lemma912InitialProfile
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5)) : Prop where
  firstThird_eq :
    a.order (0 : Fin (N + 5)) = a.order (2 : Fin (N + 5))
  second_ne :
    a.order (1 : Fin (N + 5)) ≠ c.order (1 : Fin (N + 5))
  firstGap_ne_twoE :
    a.orderGap (0 : Fin (N + 4)) ≠
      2 * (ramificationIndex K : Int)
  second_lt_fourth :
    a.order (1 : Fin (N + 5)) < a.order (3 : Fin (N + 5))
  sourceSecond_eq_add_one_imp_first_lt_fifth :
    c.order (1 : Fin (N + 5)) = a.order (1 : Fin (N + 5)) + 1 →
      a.order (0 : Fin (N + 5)) < a.order (4 : Fin (N + 5))
  second_lt_sourceSecond :
    a.order (1 : Fin (N + 5)) < c.order (1 : Fin (N + 5))
  firstGap_even : Even (a.orderGap (0 : Fin (N + 4)))
  firstGap_le_twoE_sub_two :
    a.orderGap (0 : Fin (N + 4)) ≤
      2 * (ramificationIndex K : Int) - 2
  targetFirstAlpha_le_fullDefect :
    (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) ≤
      a.truncatedPrefixDefect c (-1) 3 1
  fullDefect_le_sourceFirstAlpha :
    a.truncatedPrefixDefect c (-1) 3 1 ≤
      (c.alphaValue (0 : Fin (N + 4)) : WithTop ℚ)
  fullDefectAlternative :
    (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1 ∨
      (a.truncatedPrefixDefect c (-1) 3 1 =
          (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) ∧
        a.alphaValue (0 : Fin (N + 4)) =
          c.alphaValue (0 : Fin (N + 4)))
  lemma96_exclusion_at_boundary
      (hgap : a.orderGap (0 : Fin (N + 4)) =
        2 * (ramificationIndex K : Int) - 2) :
    ¬a.Beli2019Lemma96DefectBound c ∨
      ¬a.Lemma814FirstThreeAnisotropic

private theorem even_sub_of_modEq_two {x y : Int}
    (h : Int.ModEq 2 x y) : Even (y - x) := by
  rw [Int.modEq_iff_dvd] at h
  rcases h with ⟨z, hz⟩
  exact ⟨z, by omega⟩

set_option maxHeartbeats 1200000 in
-- The defect lower bound combines condition 2.1(ii), Lemma 8.12, and capped-defect domination.
/-- The first paragraph of Beli (2019), Lemma 9.12, derived from the literal
v2 hypotheses rather than from the absence of an opaque reduction witness. -/
theorem beli2019Lemma912_initialProfile
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (conditions : RepresentationConditions a c (Nat.le_refl (N + 4)))
    (hnot93 : ¬a.Beli2019Lemma93V2Hypothesis c)
    (hnot96 : ¬a.Beli2019Lemma96V2Hypothesis c) :
    Beli2019Lemma912InitialProfile a c := by
  classical
  have hnotLemma91 : ¬a.Lemma91Alternative c := by
    intro h
    exact hnot93 (Or.inl h)
  have hnotExceptional : ¬a.Beli2019Lemma93ExceptionalCondition c := by
    intro h
    exact hnot93 (Or.inr h)
  have hfirstThird : a.order (0 : Fin (N + 5)) =
      a.order (2 : Fin (N + 5)) := by
    apply le_antisymm a.order_zero_le_two
    apply le_of_not_gt
    intro hlt
    exact hnotLemma91 (Or.inl hlt)
  have hsecondNe : a.order (1 : Fin (N + 5)) ≠
      c.order (1 : Fin (N + 5)) := by
    intro heq
    exact hnotLemma91 (Or.inr (Or.inl heq))
  have hgapNe : a.orderGap (0 : Fin (N + 4)) ≠
      2 * (ramificationIndex K : Int) := by
    intro heq
    exact hnotLemma91 (Or.inr (Or.inr (Or.inl heq)))
  have hsecondFourthLe : a.order (1 : Fin (N + 5)) ≤
      a.order (3 : Fin (N + 5)) := by
    have htail := a.tail.order_zero_le_two
    have hzeroSucc : (⟨0, by omega⟩ : Fin (N + 4)).succ =
        (1 : Fin (N + 5)) := by
      apply Fin.ext
      rfl
    have htwoSucc : (⟨2, by omega⟩ : Fin (N + 4)).succ =
        (3 : Fin (N + 5)) := by
      apply Fin.ext
      rfl
    rw [a.order_goodTail, a.order_goodTail, hzeroSucc, htwoSucc] at htail
    exact htail
  have hsecondFourthNe : a.order (1 : Fin (N + 5)) ≠
      a.order (3 : Fin (N + 5)) := by
    intro heq
    apply hnotLemma91
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, heq⟩)))
  have hsecondFourth : a.order (1 : Fin (N + 5)) <
      a.order (3 : Fin (N + 5)) :=
    lt_of_le_of_ne hsecondFourthLe hsecondFourthNe
  have hfirstFifth
      (hstep : c.order (1 : Fin (N + 5)) =
        a.order (1 : Fin (N + 5)) + 1) :
      a.order (0 : Fin (N + 5)) < a.order (4 : Fin (N + 5)) := by
    have hne : a.order (0 : Fin (N + 5)) ≠
        a.order (4 : Fin (N + 5)) := by
      intro heq
      exact hnotExceptional ⟨hstep, heq⟩
    have hzeroTwo : a.order (0 : Fin (N + 5)) ≤
        a.order (2 : Fin (N + 5)) := a.order_zero_le_two
    have htwoFour : a.order (2 : Fin (N + 5)) ≤
        a.order (4 : Fin (N + 5)) := by
      let i : Fin (N + 5) := ⟨2, by omega⟩
      have h := a.good i (by simp [i])
      change a.order i ≤
        a.order (⟨i.val + 2, by simp [i]⟩ : Fin (N + 5)) at h
      have hi : i = (2 : Fin (N + 5)) := by
        apply Fin.ext
        change 2 = 2 % (N + 5)
        exact (Nat.mod_eq_of_lt (by omega)).symm
      have hnext : (⟨i.val + 2, by simp [i]⟩ : Fin (N + 5)) =
          (4 : Fin (N + 5)) := by
        apply Fin.ext
        change 4 = 4 % (N + 5)
        exact (Nat.mod_eq_of_lt (by omega)).symm
      calc
        a.order (2 : Fin (N + 5)) = a.order i :=
          congrArg a.order hi.symm
        _ ≤ a.order (⟨i.val + 2, by simp [i]⟩ : Fin (N + 5)) := h
        _ = a.order (4 : Fin (N + 5)) := congrArg a.order hnext
    exact lt_of_le_of_ne (hzeroTwo.trans htwoFour) hne
  have hsecondLeSource : a.order (1 : Fin (N + 5)) ≤
      c.order (1 : Fin (N + 5)) := by
    rcases conditions.orderCondition (1 : Fin (N + 5)) with hdirect | hpair
    · simpa using hdirect
    · rcases hpair with ⟨_, _, hpair⟩
      change a.order (1 : Fin (N + 5)) + a.order (2 : Fin (N + 5)) ≤
        c.order (0 : Fin (N + 5)) + c.order (1 : Fin (N + 5)) at hpair
      rw [← hfirst, ← hfirstThird] at hpair
      omega
  have hsecondStrict : a.order (1 : Fin (N + 5)) <
      c.order (1 : Fin (N + 5)) :=
    lt_of_le_of_ne hsecondLeSource hsecondNe
  have hremark := a.beli2019Remark87 (0 : Fin (N + 3)) (by
    change a.order (0 : Fin (N + 5)) =
      a.order (⟨2, by omega⟩ : Fin (N + 5))
    have htwo : (2 : Fin (N + 5)) =
        (⟨2, by omega⟩ : Fin (N + 5)) := by
      apply Fin.ext
      change 2 % (N + 5) = 2
      exact Nat.mod_eq_of_lt (by omega)
    rw [← htwo]
    exact hfirstThird)
  have hgapEven : Even (a.orderGap (0 : Fin (N + 4))) := by
    unfold orderGap
    apply even_sub_of_modEq_two
    simpa [remark87PreviousValue, remark87MiddleValue] using
      hremark.previous_middle_modEq
  have h66 := a.beli2019Lemma66_i
    (⟨0, by omega⟩ : Fin (N + 5))
    (⟨2, by omega⟩ : Fin (N + 5)) (by norm_num)
    (by exact ⟨1, by norm_num⟩) hfirstThird
  have hgapLe : a.orderGap (0 : Fin (N + 4)) ≤
      2 * (ramificationIndex K : Int) := by
    simpa using h66.gap_le (⟨0, by omega⟩ : Fin (N + 4))
      (by norm_num) (by norm_num)
  have hgapSharp : a.orderGap (0 : Fin (N + 4)) ≤
      2 * (ramificationIndex K : Int) - 2 := by
    rcases hgapEven with ⟨x, hx⟩
    have htwoEven : Even (2 * (ramificationIndex K : Int)) :=
      ⟨ramificationIndex K, by ring⟩
    rcases htwoEven with ⟨y, hy⟩
    rw [hx, hy] at hgapLe hgapNe ⊢
    omega
  let first := firstRepresentationIndex (N + 3) (N + 4)
  have hcross : (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) ≤
      a.truncatedPrefixDefect c 1 1 1 := by
    have hcondition := conditions.defectCondition first
    rw [a.coe_representationAlphaValue c first,
      a.beli2019Lemma812_i c hfirst] at hcondition
    simpa only [first, firstRepresentationIndex] using hcondition
  have hself : a.truncatedPrefixDefect a (-1) 3 1 =
      (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) := by
    rw [a.truncatedPrefixDefect_comm a (-1) 3 1]
    simpa [remark87CurrentAlpha, remark87PreviousAlpha] using
      hremark.currentCappedDefect_eq
  have hdomination :=
    a.truncatedPrefixDefect_domination a c (-1) 1 3 1 1
  simp only [mul_one] at hdomination
  have hfullLower : (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) ≤
      a.truncatedPrefixDefect c (-1) 3 1 := by
    apply (le_min (le_of_eq hself.symm) hcross).trans
    exact hdomination
  have hfullUpper : a.truncatedPrefixDefect c (-1) 3 1 ≤
      (c.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_rightCap c (-1) 3 1
    rw [c.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    simpa using hcap
  have hfullAlternative :
      (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
          a.truncatedPrefixDefect c (-1) 3 1 ∨
        (a.truncatedPrefixDefect c (-1) 3 1 =
            (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) ∧
          a.alphaValue (0 : Fin (N + 4)) =
            c.alphaValue (0 : Fin (N + 4))) := by
    by_cases hstrict :
        (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
          a.truncatedPrefixDefect c (-1) 3 1
    · exact Or.inl hstrict
    · right
      have heq : a.truncatedPrefixDefect c (-1) 3 1 =
          (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) :=
        le_antisymm (le_of_not_gt hstrict) hfullLower
      refine ⟨heq, ?_⟩
      have halphaLeGamma : a.alphaValue (0 : Fin (N + 4)) ≤
          c.alphaValue (0 : Fin (N + 4)) :=
        WithTop.coe_le_coe.mp (hfullLower.trans hfullUpper)
      have hnotStrict : ¬a.alphaValue (0 : Fin (N + 4)) <
          c.alphaValue (0 : Fin (N + 4)) := by
        intro halpha
        apply hnotLemma91
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨heq, halpha⟩)))
      exact le_antisymm halphaLeGamma (le_of_not_gt hnotStrict)
  have hlemma96 (hgap : a.orderGap (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2) :
      ¬a.Beli2019Lemma96DefectBound c ∨
        ¬a.Lemma814FirstThreeAnisotropic := by
    by_cases hdefect : a.Beli2019Lemma96DefectBound c
    · exact Or.inr (by
        intro hanisotropic
        exact hnot96 ⟨hfirstThird, hfirst, hgap, hdefect, hanisotropic⟩)
    · exact Or.inl hdefect
  exact {
    firstThird_eq := hfirstThird
    second_ne := hsecondNe
    firstGap_ne_twoE := hgapNe
    second_lt_fourth := hsecondFourth
    sourceSecond_eq_add_one_imp_first_lt_fifth := hfirstFifth
    second_lt_sourceSecond := hsecondStrict
    firstGap_even := hgapEven
    firstGap_le_twoE_sub_two := hgapSharp
    targetFirstAlpha_le_fullDefect := hfullLower
    fullDefect_le_sourceFirstAlpha := hfullUpper
    fullDefectAlternative := hfullAlternative
    lemma96_exclusion_at_boundary := hlemma96 }

end BONG.GoodBONG

end Bong
