/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912Profile

/-!
# Beli (2019), Lemma 9.12: residual profile in ranks at least three

The printed proof uses the convention that inequalities involving absent
BONG coordinates are automatic.  Here that convention is represented by
conditional fields: the fourth-coordinate conclusions require `0 < T`, and
the fifth-coordinate conclusion requires `1 < T`.  Thus the structure has a
literal meaning in ranks three and four.
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
  {L : Lattice K V} {M : Lattice K W} {T : Nat}

/-- The numerical residual profile of Lemma 9.12 at its natural rank-three
lower bound. -/
structure Beli2019Lemma912InitialProfileAllRanks
    (a : GoodBONG q L (T + 3)) (c : GoodBONG r M (T + 3)) : Prop where
  firstThird_eq :
    a.order (0 : Fin (T + 3)) = a.order (2 : Fin (T + 3))
  second_ne :
    a.order (1 : Fin (T + 3)) ≠ c.order (1 : Fin (T + 3))
  firstGap_ne_twoE :
    a.orderGap (0 : Fin (T + 2)) ≠ 2 * (ramificationIndex K : Int)
  second_lt_fourth (hT : 0 < T) :
    a.order (1 : Fin (T + 3)) < a.order (⟨3, by omega⟩ : Fin (T + 3))
  sourceSecond_eq_add_one_imp_first_lt_fifth (hT : 1 < T)
      (hstep : c.order (1 : Fin (T + 3)) =
        a.order (1 : Fin (T + 3)) + 1) :
    a.order (0 : Fin (T + 3)) < a.order (⟨4, by omega⟩ : Fin (T + 3))
  second_lt_sourceSecond :
    a.order (1 : Fin (T + 3)) < c.order (1 : Fin (T + 3))
  firstGap_even : Even (a.orderGap (0 : Fin (T + 2)))
  firstGap_le_twoE_sub_two :
    a.orderGap (0 : Fin (T + 2)) ≤ 2 * (ramificationIndex K : Int) - 2
  targetFirstAlpha_le_fullDefect :
    (a.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) ≤
      a.truncatedPrefixDefect c (-1) 3 1
  fullDefect_le_sourceFirstAlpha :
    a.truncatedPrefixDefect c (-1) 3 1 ≤
      (c.alphaValue (0 : Fin (T + 2)) : WithTop ℚ)
  fullDefectAlternative :
    (a.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1 ∨
      (a.truncatedPrefixDefect c (-1) 3 1 =
          (a.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) ∧
        a.alphaValue (0 : Fin (T + 2)) =
          c.alphaValue (0 : Fin (T + 2)))
  lemma96_exclusion_at_boundary (hT : 0 < T)
      (hgap : a.orderGap (0 : Fin (T + 2)) =
        2 * (ramificationIndex K : Int) - 2) :
    ¬a.Beli2019Lemma96DefectBound c ∨
      ¬a.Lemma814FirstThreeAnisotropic

private theorem even_sub_of_modEq_two_allRanks {x y : Int}
    (h : Int.ModEq 2 x y) : Even (y - x) := by
  rw [Int.modEq_iff_dvd] at h
  rcases h with ⟨z, hz⟩
  exact ⟨z, by omega⟩

set_option maxHeartbeats 1600000 in
-- The capped-defect lower bound combines condition (ii), Lemma 8.12, and domination.
/-- Derive the all-rank profile from the exact alternatives excluded before
the construction in Lemma 9.12. -/
theorem beli2019Lemma912_initialProfile_allRanks
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (T + 3)) (c : GoodBONG r M (T + 3))
    (hfirst : a.order (0 : Fin (T + 3)) =
      c.order (0 : Fin (T + 3)))
    (conditions : RepresentationConditions a c (Nat.le_refl (T + 2)))
    (hnotLemma91 : ¬a.Lemma91Alternative c)
    (hnotFifth : ∀ hT : 1 < T,
      ¬(c.order (1 : Fin (T + 3)) = a.order (1 : Fin (T + 3)) + 1 ∧
        a.order (0 : Fin (T + 3)) =
          a.order (⟨4, by omega⟩ : Fin (T + 3))))
    (hnot96 : ∀ hT : 0 < T,
      ¬(a.order (0 : Fin (T + 3)) = a.order (2 : Fin (T + 3)) ∧
        a.order (0 : Fin (T + 3)) = c.order (0 : Fin (T + 3)) ∧
        a.orderGap (0 : Fin (T + 2)) =
          2 * (ramificationIndex K : Int) - 2 ∧
        a.Beli2019Lemma96DefectBound c ∧
        a.Lemma814FirstThreeAnisotropic)) :
    Beli2019Lemma912InitialProfileAllRanks a c := by
  classical
  have hfirstThird : a.order (0 : Fin (T + 3)) =
      a.order (2 : Fin (T + 3)) := by
    apply le_antisymm a.order_zero_le_two
    apply le_of_not_gt
    intro hlt
    exact hnotLemma91 (Or.inl hlt)
  have hsecondNe : a.order (1 : Fin (T + 3)) ≠
      c.order (1 : Fin (T + 3)) := by
    intro heq
    exact hnotLemma91 (Or.inr (Or.inl heq))
  have hgapNe : a.orderGap (0 : Fin (T + 2)) ≠
      2 * (ramificationIndex K : Int) := by
    intro heq
    exact hnotLemma91 (Or.inr (Or.inr (Or.inl heq)))
  have hsecondFourth : ∀ hT : 0 < T,
      a.order (1 : Fin (T + 3)) <
        a.order (⟨3, by omega⟩ : Fin (T + 3)) := by
    intro hT
    have hle : a.order (1 : Fin (T + 3)) ≤
        a.order (⟨3, by omega⟩ : Fin (T + 3)) := by
      let i : Fin (T + 3) := ⟨1, by omega⟩
      have hg := a.good i (by simp [i]; omega)
      have hi : i = (1 : Fin (T + 3)) := by
        apply Fin.ext
        change 1 = 1 % (T + 3)
        exact (Nat.mod_eq_of_lt (by omega)).symm
      have hnext : (⟨i.val + 2, by simp [i]; omega⟩ : Fin (T + 3)) =
          (⟨3, by omega⟩ : Fin (T + 3)) := by
        apply Fin.ext
        simp [i]
      calc
        a.order (1 : Fin (T + 3)) = a.order i := congrArg a.order hi.symm
        _ ≤ a.order (⟨i.val + 2, by simp [i]; omega⟩ : Fin (T + 3)) := hg
        _ = a.order (⟨3, by omega⟩ : Fin (T + 3)) :=
          congrArg a.order hnext
    have hne : a.order (1 : Fin (T + 3)) ≠
        a.order (⟨3, by omega⟩ : Fin (T + 3)) := by
      intro heq
      apply hnotLemma91
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, heq⟩)))
    exact lt_of_le_of_ne hle hne
  have hfirstFifth : ∀ hT : 1 < T,
      c.order (1 : Fin (T + 3)) = a.order (1 : Fin (T + 3)) + 1 →
      a.order (0 : Fin (T + 3)) <
        a.order (⟨4, by omega⟩ : Fin (T + 3)) := by
    intro hT hstep
    have hle : a.order (0 : Fin (T + 3)) ≤
        a.order (⟨4, by omega⟩ : Fin (T + 3)) := by
      let i : Fin (T + 3) := ⟨2, by omega⟩
      have htwoFour := a.good i (by simp [i]; omega)
      have hi : i = (2 : Fin (T + 3)) := by
        apply Fin.ext
        change 2 = 2 % (T + 3)
        exact (Nat.mod_eq_of_lt (by omega)).symm
      have hnext : (⟨i.val + 2, by simp [i]; omega⟩ : Fin (T + 3)) =
          (⟨4, by omega⟩ : Fin (T + 3)) := by
        apply Fin.ext
        simp [i]
      calc
        a.order (0 : Fin (T + 3)) ≤ a.order (2 : Fin (T + 3)) :=
          a.order_zero_le_two
        _ = a.order i := congrArg a.order hi.symm
        _ ≤ a.order (⟨i.val + 2, by simp [i]; omega⟩ : Fin (T + 3)) :=
          htwoFour
        _ = a.order (⟨4, by omega⟩ : Fin (T + 3)) :=
          congrArg a.order hnext
    have hne : a.order (0 : Fin (T + 3)) ≠
        a.order (⟨4, by omega⟩ : Fin (T + 3)) := by
      intro heq
      exact hnotFifth hT ⟨hstep, heq⟩
    exact lt_of_le_of_ne hle hne
  have hsecondLeSource : a.order (1 : Fin (T + 3)) ≤
      c.order (1 : Fin (T + 3)) := by
    rcases conditions.orderCondition (1 : Fin (T + 3)) with hdirect | hpair
    · exact hdirect
    · rcases hpair with ⟨_, _, hpair⟩
      change a.order (1 : Fin (T + 3)) + a.order (2 : Fin (T + 3)) ≤
        c.order (0 : Fin (T + 3)) + c.order (1 : Fin (T + 3)) at hpair
      rw [← hfirst, ← hfirstThird] at hpair
      omega
  have hsecondStrict : a.order (1 : Fin (T + 3)) <
      c.order (1 : Fin (T + 3)) :=
    lt_of_le_of_ne hsecondLeSource hsecondNe
  have hremark := a.beli2019Remark87 (0 : Fin (T + 1)) hfirstThird
  have hgapEven : Even (a.orderGap (0 : Fin (T + 2))) := by
    unfold orderGap
    apply even_sub_of_modEq_two_allRanks
    simpa [remark87PreviousValue, remark87MiddleValue] using
      hremark.previous_middle_modEq
  have h66 := a.beli2019Lemma66_i
    (⟨0, by omega⟩ : Fin (T + 3))
    (⟨2, by omega⟩ : Fin (T + 3)) (by norm_num)
    (by exact ⟨1, by norm_num⟩) hfirstThird
  have hgapLe : a.orderGap (0 : Fin (T + 2)) ≤
      2 * (ramificationIndex K : Int) := by
    simpa using h66.gap_le (⟨0, by omega⟩ : Fin (T + 2))
      (by norm_num) (by norm_num)
  have hgapSharp : a.orderGap (0 : Fin (T + 2)) ≤
      2 * (ramificationIndex K : Int) - 2 := by
    rcases hgapEven with ⟨x, hx⟩
    have htwoEven : Even (2 * (ramificationIndex K : Int)) :=
      ⟨ramificationIndex K, by ring⟩
    rcases htwoEven with ⟨y, hy⟩
    rw [hx, hy] at hgapLe hgapNe ⊢
    omega
  let first := firstRepresentationIndex (T + 1) (T + 2)
  have hcross : (a.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) ≤
      a.truncatedPrefixDefect c 1 1 1 := by
    have hcondition := conditions.defectCondition first
    rw [a.coe_representationAlphaValue c first,
      a.beli2019Lemma812_i c hfirst] at hcondition
    simpa only [first, firstRepresentationIndex] using hcondition
  have hself : a.truncatedPrefixDefect a (-1) 3 1 =
      (a.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) := by
    rw [a.truncatedPrefixDefect_comm a (-1) 3 1]
    simpa [remark87CurrentAlpha, remark87PreviousAlpha] using
      hremark.currentCappedDefect_eq
  have hdomination := a.truncatedPrefixDefect_domination a c (-1) 1 3 1 1
  simp only [mul_one] at hdomination
  have hfullLower : (a.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) ≤
      a.truncatedPrefixDefect c (-1) 3 1 := by
    apply (le_min (le_of_eq hself.symm) hcross).trans
    exact hdomination
  have hfullUpper : a.truncatedPrefixDefect c (-1) 3 1 ≤
      (c.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_rightCap c (-1) 3 1
    rw [c.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    simpa using hcap
  have hfullAlternative :
      (a.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) <
          a.truncatedPrefixDefect c (-1) 3 1 ∨
        (a.truncatedPrefixDefect c (-1) 3 1 =
            (a.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) ∧
          a.alphaValue (0 : Fin (T + 2)) =
            c.alphaValue (0 : Fin (T + 2))) := by
    by_cases hstrict : (a.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1
    · exact Or.inl hstrict
    · right
      have heq : a.truncatedPrefixDefect c (-1) 3 1 =
          (a.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) :=
        le_antisymm (le_of_not_gt hstrict) hfullLower
      refine ⟨heq, ?_⟩
      have halphaLe : a.alphaValue (0 : Fin (T + 2)) ≤
          c.alphaValue (0 : Fin (T + 2)) :=
        WithTop.coe_le_coe.mp (hfullLower.trans hfullUpper)
      have hnotStrict : ¬a.alphaValue (0 : Fin (T + 2)) <
          c.alphaValue (0 : Fin (T + 2)) := by
        intro halpha
        apply hnotLemma91
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨heq, halpha⟩)))
      exact le_antisymm halphaLe (le_of_not_gt hnotStrict)
  have hlemma96 : ∀ hT : 0 < T,
      a.orderGap (0 : Fin (T + 2)) =
        2 * (ramificationIndex K : Int) - 2 →
      ¬a.Beli2019Lemma96DefectBound c ∨
        ¬a.Lemma814FirstThreeAnisotropic := by
    intro hT hgap
    by_cases hdefect : a.Beli2019Lemma96DefectBound c
    · exact Or.inr (by
        intro hanisotropic
        exact hnot96 hT ⟨hfirstThird, hfirst, hgap, hdefect, hanisotropic⟩)
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
