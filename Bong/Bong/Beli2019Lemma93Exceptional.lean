/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93CaseTwoLowRank
import Bong.Bong.Beli2019Lemma814Complete
import Bong.Bong.Beli2019Remark87
import Bong.Bong.Beli2019OddPrefixDefect

/-!
# Beli (2019), Lemma 9.3: the final exceptional branch

This file formalizes the last branch of Lemma 9.3, beginning with the
paper's hypotheses `S₂ = R₂ + 1` and `R₁ = R₅`.  The ordinary Lemma 9.1
alternative is handled elsewhere, so the genuinely new argument is carried
out under its negation.  This first part packages the order, parity, and
low-alpha consequences used by the two BONG changes in the remainder of the
proof.
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

/-- The final alternative in the statement of Lemma 9.3, in zero-based
notation: `S₂ = R₂ + 1` and `R₁ = R₅`.  Rank five is kept explicit; no
out-of-range `Fin` index is manufactured in smaller rank. -/
def Beli2019Lemma93ExceptionalCondition
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5)) : Prop :=
  b.order (⟨1, by omega⟩ : Fin (N + 5)) =
      a.order (⟨1, by omega⟩ : Fin (N + 5)) + 1 ∧
    a.order (⟨0, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5))

/-- The numerical conclusions in the first paragraph of the final branch of
Lemma 9.3.  These are stated separately from the later BONG choices so their
dependence on `¬ Lemma91Alternative` is visible. -/
structure Beli2019Lemma93ExceptionalArithmetic
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5)) : Prop where
  firstThird_eq :
    a.order (⟨0, by omega⟩ : Fin (N + 5)) =
      a.order (⟨2, by omega⟩ : Fin (N + 5))
  firstFifth_eq :
    a.order (⟨0, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5))
  secondFourth_lt :
    a.order (⟨1, by omega⟩ : Fin (N + 5)) <
      a.order (⟨3, by omega⟩ : Fin (N + 5))
  targetOrder_modEq (i : Fin (N + 5)) (hi : i.val ≤ 4) :
    Int.ModEq 2 (a.order i) (a.order (⟨0, by omega⟩ : Fin (N + 5)))
  firstGap_even : Even (a.orderGap (⟨0, by omega⟩ : Fin (N + 4)))
  firstGap_le_twoE_sub_two :
    a.orderGap (⟨0, by omega⟩ : Fin (N + 4)) ≤
      2 * (ramificationIndex K : Int) - 2
  thirdGap_le_twoE :
    a.orderGap (⟨2, by omega⟩ : Fin (N + 4)) ≤
      2 * (ramificationIndex K : Int)
  fourth_ge_second_add_two :
    a.order (⟨1, by omega⟩ : Fin (N + 5)) + 2 ≤
      a.order (⟨3, by omega⟩ : Fin (N + 5))
  sourceFirst_eq :
    b.order (⟨0, by omega⟩ : Fin (N + 5)) =
      a.order (⟨0, by omega⟩ : Fin (N + 5))
  sourceSecond_eq :
    b.order (⟨1, by omega⟩ : Fin (N + 5)) =
      a.order (⟨1, by omega⟩ : Fin (N + 5)) + 1
  sourceFirstGap_eq :
    b.orderGap (⟨0, by omega⟩ : Fin (N + 4)) =
      a.orderGap (⟨0, by omega⟩ : Fin (N + 4)) + 1
  sourceFirstGap_odd :
    Odd (b.orderGap (⟨0, by omega⟩ : Fin (N + 4)))

private theorem even_sub_of_modEq_two {x y : Int}
    (h : Int.ModEq 2 x y) : Even (x - y) := by
  rw [Int.modEq_iff_dvd] at h
  rcases h with ⟨z, hz⟩
  exact ⟨-z, by omega⟩

set_option maxHeartbeats 800000 in
/-- Derivation of the exceptional order package from the literal hypotheses.
The exclusions `R₂ = R₄` and `R₂-R₁ = 2e` are precisely the fourth and third
alternatives of Lemma 9.1, respectively. -/
theorem exceptionalArithmetic_of_not_lemma91
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5))
    (hfirst : a.order (⟨0, by omega⟩ : Fin (N + 5)) =
      b.order (⟨0, by omega⟩ : Fin (N + 5)))
    (hexceptional : a.Beli2019Lemma93ExceptionalCondition b)
    (hnotLemma91 : ¬a.Lemma91Alternative b) :
    Beli2019Lemma93ExceptionalArithmetic a b := by
  have hfirstThird : a.order (⟨0, by omega⟩ : Fin (N + 5)) =
      a.order (⟨2, by omega⟩ : Fin (N + 5)) := by
    apply le_antisymm a.order_zero_le_two
    apply le_of_not_gt
    intro hlt
    exact hnotLemma91 (Or.inl hlt)
  have hsecondFourthLe : a.order (⟨1, by omega⟩ : Fin (N + 5)) ≤
      a.order (⟨3, by omega⟩ : Fin (N + 5)) := by
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
  have hsecondFourthNe : a.order (⟨1, by omega⟩ : Fin (N + 5)) ≠
      a.order (⟨3, by omega⟩ : Fin (N + 5)) := by
    intro heq
    apply hnotLemma91
    right; right; right; left
    exact ⟨by omega, heq⟩
  have hsecondFourth : a.order (⟨1, by omega⟩ : Fin (N + 5)) <
      a.order (⟨3, by omega⟩ : Fin (N + 5)) :=
    lt_of_le_of_ne hsecondFourthLe hsecondFourthNe
  have h66 := a.beli2019Lemma66_i
    (⟨0, by omega⟩ : Fin (N + 5))
    (⟨4, by omega⟩ : Fin (N + 5)) (by norm_num)
    (by exact ⟨2, by norm_num⟩) (by simpa using hexceptional.2)
  have hmod (i : Fin (N + 5)) (hi : i.val ≤ 4) :
      Int.ModEq 2 (a.order i)
        (a.order (⟨0, by omega⟩ : Fin (N + 5))) := by
    exact h66.order_modEq i (by change 0 ≤ i.val; omega)
      (by change i.val ≤ 4; exact hi)
  have hfirstGapEven :
      Even (a.orderGap (⟨0, by omega⟩ : Fin (N + 4))) := by
    unfold orderGap
    exact even_sub_of_modEq_two
      (hmod (⟨1, by omega⟩ : Fin (N + 5)) (by norm_num))
  have hfirstGapLe := h66.gap_le
    (⟨0, by omega⟩ : Fin (N + 4)) (by norm_num) (by norm_num)
  have hfirstGapNe : a.orderGap (⟨0, by omega⟩ : Fin (N + 4)) ≠
      2 * (ramificationIndex K : Int) := by
    intro heq
    apply hnotLemma91
    right; right; left
    exact heq
  have hfirstGapSharp : a.orderGap (⟨0, by omega⟩ : Fin (N + 4)) ≤
      2 * (ramificationIndex K : Int) - 2 := by
    rcases hfirstGapEven with ⟨x, hx⟩
    have htwoEven : Even (2 * (ramificationIndex K : Int)) :=
      ⟨ramificationIndex K, by ring⟩
    rcases htwoEven with ⟨y, hy⟩
    rw [hx, hy] at hfirstGapLe hfirstGapNe ⊢
    omega
  have hthirdGapLe := h66.gap_le (⟨2, by omega⟩ : Fin (N + 4))
    (by norm_num) (by norm_num)
  have hsecondFourthMod : Int.ModEq 2
      (a.order (⟨3, by omega⟩ : Fin (N + 5)))
      (a.order (⟨1, by omega⟩ : Fin (N + 5))) :=
    (hmod (⟨3, by omega⟩ : Fin (N + 5)) (by norm_num)).trans
      (hmod (⟨1, by omega⟩ : Fin (N + 5)) (by norm_num)).symm
  have hsecondFourthEven : Even
      (a.order (⟨3, by omega⟩ : Fin (N + 5)) -
        a.order (⟨1, by omega⟩ : Fin (N + 5))) :=
    even_sub_of_modEq_two hsecondFourthMod
  have hfourthLower : a.order (⟨1, by omega⟩ : Fin (N + 5)) + 2 ≤
      a.order (⟨3, by omega⟩ : Fin (N + 5)) := by
    rcases hsecondFourthEven with ⟨x, hx⟩
    omega
  have hsourceGap : b.orderGap (⟨0, by omega⟩ : Fin (N + 4)) =
      a.orderGap (⟨0, by omega⟩ : Fin (N + 4)) + 1 := by
    unfold orderGap
    have hsucc : (⟨0, by omega⟩ : Fin (N + 4)).succ =
        (⟨1, by omega⟩ : Fin (N + 5)) := by
      apply Fin.ext
      rfl
    have hcast : (⟨0, by omega⟩ : Fin (N + 4)).castSucc =
        (⟨0, by omega⟩ : Fin (N + 5)) := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast]
    rw [hexceptional.1, ← hfirst]
    ring
  have hsourceOdd :
      Odd (b.orderGap (⟨0, by omega⟩ : Fin (N + 4))) := by
    rcases hfirstGapEven with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [hsourceGap, hx]
    omega
  exact {
    firstThird_eq := hfirstThird
    firstFifth_eq := hexceptional.2
    secondFourth_lt := hsecondFourth
    targetOrder_modEq := hmod
    firstGap_even := hfirstGapEven
    firstGap_le_twoE_sub_two := hfirstGapSharp
    thirdGap_le_twoE := hthirdGapLe
    fourth_ge_second_add_two := hfourthLower
    sourceFirst_eq := hfirst.symm
    sourceSecond_eq := hexceptional.1
    sourceFirstGap_eq := hsourceGap
    sourceFirstGap_odd := hsourceOdd }

/-- An odd rational integer above an even integer is at least the next
integer.  This is the discrete step used in the paper's
`α₁ ≥ R₂-R₁+1` argument. -/
private theorem intCast_add_one_le_of_even_of_oddInteger
    (x : Int) (y : ℚ) (hx : Even x)
    (hy : IsOddRationalInteger y) (hxy : (x : ℚ) ≤ y) :
    ((x + 1 : Int) : ℚ) ≤ y := by
  rcases hy with ⟨z, hzOdd, rfl⟩
  have hxz : x ≤ z := by exact_mod_cast hxy
  rcases hx with ⟨p, hp⟩
  rcases hzOdd with ⟨q, hq⟩
  exact_mod_cast (show x + 1 ≤ z by omega)

/-- The low-alpha and first-defect identities derived before the two BONG
changes in the exceptional branch. -/
structure Beli2019Lemma93ExceptionalLowData
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5)) : Prop where
  arithmetic : Beli2019Lemma93ExceptionalArithmetic a b
  sourceFirstAlpha_eq_gap :
    b.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) =
      (b.orderGap (⟨0, by omega⟩ : Fin (N + 4)) : ℚ)
  targetFirstAlpha_eq_source :
    a.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) =
      b.alphaValue (⟨0, by omega⟩ : Fin (N + 4))
  targetThirdAlpha_gt_source :
    b.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) <
      a.alphaValue (⟨2, by omega⟩ : Fin (N + 4))
  targetSecondAlpha_eq_one :
    a.alphaValue (⟨1, by omega⟩ : Fin (N + 4)) = 1
  targetFirstSelfCappedDefect_eq :
    a.truncatedPrefixDefect a (-1) 1 3 =
      (a.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) : WithTop ℚ)
  firstThirdCappedDefect_eq :
    a.truncatedPrefixDefect b (-1) 3 1 =
      (a.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) : WithTop ℚ)
  sourceFirstAlpha_lt_halfGap :
    b.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) <
      b.halfGapValue (⟨0, by omega⟩ : Fin (N + 4))

set_option maxHeartbeats 1200000 in
/-- Formalization of the numerical and defect calculation in lines
9384--9393 of the paper. -/
theorem exceptionalLowData
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [targetParity : Beli2009AlphaParityLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5))
    (hfirst : a.order (⟨0, by omega⟩ : Fin (N + 5)) =
      b.order (⟨0, by omega⟩ : Fin (N + 5)))
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 4)))
    (H : Beli2019Lemma93ExceptionalArithmetic a b) :
    Beli2019Lemma93ExceptionalLowData a b := by
  let firstGap : Fin (N + 4) := ⟨0, by omega⟩
  let secondAlpha : Fin (N + 4) := ⟨1, by omega⟩
  let thirdAlpha : Fin (N + 4) := ⟨2, by omega⟩
  have HsourceGap : b.orderGap firstGap = a.orderGap firstGap + 1 := by
    simpa only [firstGap] using H.sourceFirstGap_eq
  have HsourceOdd : Odd (b.orderGap firstGap) := by
    simpa only [firstGap] using H.sourceFirstGap_odd
  have HtargetEven : Even (a.orderGap firstGap) := by
    simpa only [firstGap] using H.firstGap_even
  have HtargetSharp : a.orderGap firstGap ≤
      2 * (ramificationIndex K : Int) - 2 := by
    simpa only [firstGap] using H.firstGap_le_twoE_sub_two
  have HthirdLe : a.orderGap thirdAlpha ≤
      2 * (ramificationIndex K : Int) := by
    simpa only [thirdAlpha] using H.thirdGap_le_twoE
  have hsourceGapLe : b.orderGap firstGap ≤
      2 * (ramificationIndex K : Int) := by
    rw [HsourceGap]
    omega
  have hbeta : b.alphaValue firstGap = (b.orderGap firstGap : ℚ) := by
    letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
    letI : Beli2009AlphaParityLaws.{u, w} K := sourceParity
    exact (b.beli2009Lemma27_iii firstGap hsourceGapLe).2.mpr
      (Or.inr HsourceOdd)
  letI : Beli2006AlphaLaws.{u, v} K := targetLaws
  letI : Beli2009AlphaParityLaws.{u, v} K := targetParity
  have htargetGapLe : a.orderGap firstGap ≤
      2 * (ramificationIndex K : Int) := by
    omega
  have htargetBase : (a.orderGap firstGap : ℚ) ≤
      a.alphaValue firstGap :=
    (a.beli2009Lemma27_iii firstGap htargetGapLe).1
  have htargetNext : ((a.orderGap firstGap + 1 : Int) : ℚ) ≤
      a.alphaValue firstGap := by
    by_cases hhalf : a.alphaValue firstGap = a.halfGapValue firstGap
    · rw [hhalf]
      unfold halfGapValue
      have hsharpQ : (a.orderGap firstGap : ℚ) ≤
          2 * (ramificationIndex K : ℚ) - 2 := by
        exact_mod_cast HtargetSharp
      push_cast at hsharpQ ⊢
      linarith
    · exact intCast_add_one_le_of_even_of_oddInteger
        (a.orderGap firstGap) (a.alphaValue firstGap) HtargetEven
        (a.beli2009Lemma27_iv firstGap hhalf) htargetBase
  have htargetLeSource : a.alphaValue firstGap ≤ b.alphaValue firstGap :=
    a.firstAlpha_le_sourceFirstAlpha_of_representationConditions
      b (Nat.le_refl (N + 4)) hfirst conditions
  have halphaBeta : a.alphaValue firstGap = b.alphaValue firstGap := by
    apply le_antisymm htargetLeSource
    rw [hbeta, HsourceGap]
    exact htargetNext
  have hthirdGapLower : b.orderGap firstGap < a.orderGap thirdAlpha := by
    have hfirstOuter := H.firstThird_eq
    have hfourth := H.fourth_ge_second_add_two
    rw [HsourceGap]
    unfold orderGap
    change a.order (⟨1, by omega⟩ : Fin (N + 5)) -
          a.order (⟨0, by omega⟩ : Fin (N + 5)) + 1 <
        a.order (⟨3, by omega⟩ : Fin (N + 5)) -
          a.order (⟨2, by omega⟩ : Fin (N + 5))
    omega
  have hthirdBase : (a.orderGap thirdAlpha : ℚ) ≤
      a.alphaValue thirdAlpha :=
    (a.beli2009Lemma27_iii thirdAlpha HthirdLe).1
  have hbetaThird : b.alphaValue firstGap < a.alphaValue thirdAlpha := by
    rw [hbeta]
    have hgapQ : (b.orderGap firstGap : ℚ) <
        (a.orderGap thirdAlpha : ℚ) := by
      exact_mod_cast hthirdGapLower
    exact hgapQ.trans_le hthirdBase
  have hremark := a.beli2019Remark87
    (⟨0, by omega⟩ : Fin (N + 3)) (by
      change a.order (⟨0, by omega⟩ : Fin (N + 5)) =
        a.order (⟨2, by omega⟩ : Fin (N + 5))
      exact H.firstThird_eq)
  have htargetFirstFormula : a.alphaValue firstGap =
      ((a.orderGap firstGap + 1 : Int) : ℚ) := by
    rw [halphaBeta, hbeta, HsourceGap]
  have hsecond : a.alphaValue secondAlpha = 1 := by
    have h := hremark.currentAlpha_eq
    change a.alphaValue secondAlpha =
      ((a.order (⟨0, by omega⟩ : Fin (N + 5)) -
        a.order (⟨1, by omega⟩ : Fin (N + 5)) : Int) : ℚ) +
          a.alphaValue firstGap at h
    rw [htargetFirstFormula] at h
    unfold orderGap at h
    change a.alphaValue secondAlpha =
      ((a.order (⟨0, by omega⟩ : Fin (N + 5)) -
        a.order (⟨1, by omega⟩ : Fin (N + 5)) : Int) : ℚ) +
      (((a.order (⟨1, by omega⟩ : Fin (N + 5)) -
        a.order (⟨0, by omega⟩ : Fin (N + 5)) : Int) + 1 : Int) : ℚ) at h
    push_cast at h
    linarith
  have hselfCapped : a.truncatedPrefixDefect a (-1) 1 3 =
      (a.alphaValue firstGap : WithTop ℚ) := by
    simpa only [remark87PreviousAlpha, firstGap] using
      hremark.currentCappedDefect_eq
  let first := firstRepresentationIndex (N + 3) (N + 4)
  have hcondition := conditions.defectCondition first
  rw [a.coe_representationAlphaValue b first,
    a.beli2019Lemma812_i b hfirst] at hcondition
  have hx : (a.alphaValue firstGap : WithTop ℚ) ≤
      defectOrder (K := K) (a.prefixProduct 1 * b.prefixProduct 1) := by
    have hraw := a.truncatedPrefixDefect_le_defect b 1 1 1
    have h := hcondition.trans hraw
    have hzero : (0 : Fin (N + 4)) = firstGap := by
      apply Fin.ext
      rfl
    rw [hzero] at h
    simpa only [one_mul] using h
  have hy : (a.alphaValue firstGap : WithTop ℚ) ≤
      defectOrder (K := K) ((-1) * a.prefixProduct 1 * a.prefixProduct 3) := by
    have hraw := a.truncatedPrefixDefect_le_defect a (-1) 1 3
    exact hselfCapped ▸ hraw
  have hproductLower : (a.alphaValue firstGap : WithTop ℚ) ≤
      defectOrder (K := K)
        (((a.prefixProduct 1 * b.prefixProduct 1) *
          ((-1) * a.prefixProduct 1 * a.prefixProduct 3))) :=
    (le_min hx hy).trans (defectOrder_mul_ge_min _ _)
  have hproduct :
      (a.prefixProduct 1 * b.prefixProduct 1) *
          ((-1) * a.prefixProduct 1 * a.prefixProduct 3) =
        ((-1) * a.prefixProduct 3 * b.prefixProduct 1) *
          (a.prefixProduct 1) ^ 2 := by
    simp only [pow_two]
    ac_rfl
  have hrawLower : (a.alphaValue firstGap : WithTop ℚ) ≤
      defectOrder (K := K) ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
    rw [hproduct, defectOrder_mul_square] at hproductLower
    exact hproductLower
  have hcrossLower : (a.alphaValue firstGap : WithTop ℚ) ≤
      a.truncatedPrefixDefect b (-1) 3 1 := by
    unfold truncatedPrefixDefect
    apply le_min hrawLower
    apply le_min
    · rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
      have hindex : (⟨3 - 1, by omega⟩ : Fin (N + 4)) = thirdAlpha := by
        apply Fin.ext
        rfl
      rw [hindex]
      have halphaLe : a.alphaValue firstGap ≤ a.alphaValue thirdAlpha := by
        rw [halphaBeta]
        exact hbetaThird.le
      exact_mod_cast halphaLe
    · rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
      have hindex : (⟨1 - 1, by omega⟩ : Fin (N + 4)) = firstGap := by
        apply Fin.ext
        rfl
      rw [hindex, ← halphaBeta]
  have hcrossUpper : a.truncatedPrefixDefect b (-1) 3 1 ≤
      (a.alphaValue firstGap : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_rightCap b (-1) 3 1
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    have hindex : (⟨1 - 1, by omega⟩ : Fin (N + 4)) = firstGap := by
      apply Fin.ext
      rfl
    rw [hindex, ← halphaBeta] at hcap
    exact hcap
  have hcross : a.truncatedPrefixDefect b (-1) 3 1 =
      (a.alphaValue firstGap : WithTop ℚ) :=
    le_antisymm hcrossUpper hcrossLower
  have hbetaHalf : b.alphaValue firstGap < b.halfGapValue firstGap := by
    rw [hbeta]
    unfold halfGapValue
    have hsourceStrict : b.orderGap firstGap <
        2 * (ramificationIndex K : Int) := by
      rw [HsourceGap]
      omega
    have hsourceStrictQ : (b.orderGap firstGap : ℚ) <
        2 * (ramificationIndex K : ℚ) := by
      exact_mod_cast hsourceStrict
    push_cast at hsourceStrictQ ⊢
    linarith
  exact {
    arithmetic := H
    sourceFirstAlpha_eq_gap := hbeta
    targetFirstAlpha_eq_source := halphaBeta
    targetThirdAlpha_gt_source := hbetaThird
    targetSecondAlpha_eq_one := hsecond
    targetFirstSelfCappedDefect_eq := hselfCapped
    firstThirdCappedDefect_eq := hcross
    sourceFirstAlpha_lt_halfGap := hbetaHalf }

/-- The source BONG after the possible Lemma 8.8 first-value change in the
exceptional branch.  Its uncapped first-three comparison defect is exactly
the original `β₁`. -/
structure Beli2019Lemma93ExceptionalSourceHeadNormalization
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5)) where
  transformed : GoodBONG r M (N + 5)
  firstThirdRawDefect_eq :
    defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * transformed.prefixProduct 1) =
      (b.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) : WithTop ℚ)

/-- Lemma 8.8 supplies the source first-value normalization whenever the raw
defect is strictly larger than `β₁`; otherwise the identity BONG already has
the required property. -/
theorem exists_exceptionalSourceHeadNormalization
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5))
    (D : Beli2019Lemma93ExceptionalLowData a b) :
    Nonempty (Beli2019Lemma93ExceptionalSourceHeadNormalization a b) := by
  let beta : WithTop ℚ :=
    (b.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) : WithTop ℚ)
  let raw := defectOrder (K := K)
    ((-1) * a.prefixProduct 3 * b.prefixProduct 1)
  have hcapped : a.truncatedPrefixDefect b (-1) 3 1 = beta := by
    exact D.firstThirdCappedDefect_eq.trans
      (congrArg (fun z : ℚ => (z : WithTop ℚ))
        D.targetFirstAlpha_eq_source)
  have hrawLe : beta ≤ raw := by
    have hle := a.truncatedPrefixDefect_le_defect b (-1) 3 1
    exact hcapped ▸ hle
  by_cases hrawEq : raw = beta
  · exact ⟨{
      transformed := b
      firstThirdRawDefect_eq := hrawEq
    }⟩
  · have hnotExceptional : ¬b.Beli2019Lemma88Exceptional := by
      rintro ⟨hhalf, _⟩
      exact (ne_of_lt D.sourceFirstAlpha_lt_halfGap) hhalf
    rcases (b.beli2019Lemma88_i).mpr hnotExceptional with ⟨T⟩
    have hstrict : beta < raw :=
      lt_of_le_of_ne hrawLe (fun h => hrawEq h.symm)
    have hproduct :
        (-1 : Kˣ) * a.prefixProduct 3 * T.transformed.prefixProduct 1 =
          T.epsilon * ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
      rw [T.prefixProduct_one_eq]
      ac_rfl
    have hzero : (0 : Fin (N + 4)) =
        (⟨0, by omega⟩ : Fin (N + 4)) := by
      apply Fin.ext
      rfl
    have hepsilon : defectOrder (K := K) T.epsilon = beta := by
      have h := T.epsilon_defect
      rw [hzero] at h
      exact h
    refine ⟨{
      transformed := T.transformed
      firstThirdRawDefect_eq := ?_
    }⟩
    rw [hproduct,
      defectOrder_mul_eq_left_of_lt_right (K := K)
        (hepsilon ▸ hstrict), hepsilon]

/-- The exceptional source after the first-value choice and its Lemma 9.2
tail normalization. -/
structure Beli2019Lemma93ExceptionalSourceNormalization
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5)) where
  beforeLemma92 : GoodBONG r M (N + 5)
  transform : beforeLemma92.Beli2019Lemma92Transform
  firstThirdRawDefect_eq :
    defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * transform.transformed.prefixProduct 1) =
      (b.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) : WithTop ℚ)

/-- Lemma 9.2 preserves the source's first prefix product, hence preserves the
exact raw defect fixed by Lemma 8.8. -/
theorem Beli2019Lemma93ExceptionalSourceHeadNormalization.exists_sourceNormalization
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [DyadicDiagonalClassificationLaws K]
    {a : GoodBONG q L (N + 5)} {b : GoodBONG r M (N + 5)}
    (H : Beli2019Lemma93ExceptionalSourceHeadNormalization a b) :
    Nonempty (Beli2019Lemma93ExceptionalSourceNormalization a b) := by
  rcases H.transformed.beli2019Lemma92 with ⟨T⟩
  refine ⟨{
    beforeLemma92 := H.transformed
    transform := T
    firstThirdRawDefect_eq := ?_
  }⟩
  rw [T.prefixProduct_one_eq]
  exact H.firstThirdRawDefect_eq

/-- End-to-end existence of the normalized source used by the exceptional
branch. -/
theorem exists_exceptionalSourceNormalization
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5))
    (D : Beli2019Lemma93ExceptionalLowData a b) :
    Nonempty (Beli2019Lemma93ExceptionalSourceNormalization a b) := by
  rcases a.exists_exceptionalSourceHeadNormalization b D with ⟨H⟩
  exact H.exists_sourceNormalization

/-- In the final exceptional branch the source orders satisfy `S₁ < S₃`.
Equality would make the odd first source gap even by Lemma 6.6(i). -/
theorem sourceFirstThird_lt_of_exceptional
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5))
    (D : Beli2019Lemma93ExceptionalLowData a b) :
    b.order (⟨0, by omega⟩ : Fin (N + 5)) <
      b.order (⟨2, by omega⟩ : Fin (N + 5)) := by
  have hle := b.order_zero_le_two
  apply lt_of_le_of_ne hle
  intro heq
  let i0 : Fin (N + 5) := ⟨0, by omega⟩
  let i1 : Fin (N + 5) := ⟨1, by omega⟩
  let i2 : Fin (N + 5) := ⟨2, by omega⟩
  have houter : b.order i0 = b.order i2 := by
    simpa only [i0, i2] using heq
  have H66 := b.beli2019Lemma66_i
    i0 i2 (by change i0.val ≤ i2.val; simp only [i0, i2]; omega)
    (by exact ⟨1, by norm_num⟩) houter
  have hi01 : i0 ≤ i1 := by
    change i0.val ≤ i1.val
    simp only [i0, i1]
    omega
  have hi12 : i1 ≤ i2 := by
    change i1.val ≤ i2.val
    simp only [i1, i2]
    omega
  have hmod := H66.order_modEq i1 hi01 hi12
  have heven : Even (b.orderGap (⟨0, by omega⟩ : Fin (N + 4))) := by
    unfold orderGap
    have hsucc : (⟨0, by omega⟩ : Fin (N + 4)).succ = i1 := by
      apply Fin.ext
      rfl
    have hcast : (⟨0, by omega⟩ : Fin (N + 4)).castSucc = i0 := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast]
    exact even_sub_of_modEq_two hmod
  rcases heven with ⟨x, hx⟩
  rcases D.arithmetic.sourceFirstGap_odd with ⟨y, hy⟩
  omega

/-- The exact raw defect fixed on the source becomes the unary capped defect
required by Lemma 8.14: the only remaining target cap is `α₃`, which is
strictly larger than `α₁=β₁`. -/
theorem Beli2019Lemma93ExceptionalSourceNormalization.unaryCappedDefect_eq
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5))
    (D : Beli2019Lemma93ExceptionalLowData a b)
    (S : Beli2019Lemma93ExceptionalSourceNormalization a b) :
    a.lemma814FirstThirdCappedDefect S.beforeLemma92.firstUnarySegment =
      (a.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) : WithTop ℚ) := by
  have hraw : defectOrder (K := K)
      ((-1) * a.prefixProduct 3 *
        S.beforeLemma92.firstUnarySegment.prefixProduct 1) =
      (a.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) : WithTop ℚ) := by
    rw [S.beforeLemma92.firstUnarySegment_prefixProduct_one,
      ← S.transform.prefixProduct_one_eq]
    exact S.firstThirdRawDefect_eq.trans
      (congrArg (fun z : ℚ => (z : WithTop ℚ))
        D.targetFirstAlpha_eq_source.symm)
  unfold lemma814FirstThirdCappedDefect truncatedPrefixDefect
  rw [S.beforeLemma92.firstUnarySegment.prefixAlphaCap_last,
    min_top_right, hraw,
    a.prefixAlphaCap_of_internal (by omega) (by omega)]
  have hthird : (⟨3 - 1, by omega⟩ : Fin (N + 4)) =
      (⟨2, by omega⟩ : Fin (N + 4)) := by
    apply Fin.ext
    rfl
  rw [hthird, min_eq_left]
  exact_mod_cast (D.targetFirstAlpha_eq_source.trans_lt
    D.targetThirdAlpha_gt_source).le

/-- The complete pair selected in the final exceptional branch. -/
structure Beli2019Lemma93ExceptionalNormalizedPair
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5)) where
  normalized : Beli2019Lemma93NormalizedPair a b
  lowData : Beli2019Lemma93ExceptionalLowData a b
  sourceEarly : normalized.sourceBeforeLemma92.Lemma92EarlyAlternative
  firstThirdRawDefect_eq_sourceFirstAlpha :
    defectOrder (K := K)
        ((-1) * normalized.targetTransform.transformed.prefixProduct 3 *
          normalized.sourceTransform.transformed.prefixProduct 1) =
      (normalized.sourceTransform.transformed.alphaValue
        (⟨0, by omega⟩ : Fin (N + 4)) : WithTop ℚ)

set_option maxHeartbeats 1800000 in
/-- End-to-end construction of the two selected BONGs in the final
exceptional branch: Lemma 8.8 and Lemma 9.2 normalize the source, Lemma 8.14
prescribes the target head, and a second use of Lemma 9.2 normalizes the
target tail. -/
theorem exists_beli2019Lemma93ExceptionalNormalizedPair
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [targetParity : Beli2009AlphaParityLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [targetLocalization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [targetConstruction : BeliLemma43ConstructionLaws.{u, v} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [targetSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [targetBinaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [targetQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [targetLemma49 : BeliLemma49Laws.{u, v} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [targetLemma47 : BeliLemma47Laws.{u, v} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFiveW : Beli2019SectionFiveLaws.{u, w} K]
    [sectionFourW : Beli2019SectionFourLaws.{u, w} K]
    [sectionFourV : Beli2019SectionFourLaws.{u, v} K]
    [deepWW : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K]
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5))
    (hfirst : a.order (⟨0, by omega⟩ : Fin (N + 5)) =
      b.order (⟨0, by omega⟩ : Fin (N + 5)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 4)))
    (D : Beli2019Lemma93ExceptionalLowData a b) :
    Nonempty (Beli2019Lemma93ExceptionalNormalizedPair a b) := by
  rcases a.exists_exceptionalSourceNormalization
      (sourceLaws := sourceLaws) (sourceParity := sourceParity)
      (sourceLocalization := sourceLocalization)
      (sourceConstruction := sourceConstruction)
      (sourceSectionTwo := sourceSectionTwo)
      (classificationW := classificationW)
      (sourceBinaryScaling := sourceBinaryScaling)
      (sourceQuaternaryScaling := sourceQuaternaryScaling)
      (sourceLemma49 := sourceLemma49) (sourceLemma47 := sourceLemma47)
      b D with ⟨S⟩
  have hsourceOrders : b.SameOrders S.beforeLemma92 := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact b.order_invariant S.beforeLemma92
  have hfirstSelected : a.order (⟨0, by omega⟩ : Fin (N + 5)) =
      S.beforeLemma92.order (⟨0, by omega⟩ : Fin (N + 5)) :=
    hfirst.trans (hsourceOrders (⟨0, by omega⟩ : Fin (N + 5)))
  have selectedConditions : RepresentationConditions a S.beforeLemma92
      (Nat.le_refl (N + 4)) :=
    (a.representationConditions_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      a b S.beforeLemma92 (Nat.le_refl (N + 4))).mp conditions
  have unaryConditions :
      a.Lemma813Conditions S.beforeLemma92.firstUnarySegment :=
    lemma813Conditions_firstUnarySegment_of_lowerData_sameRank
      (alphaV := targetLaws) (alphaW := sourceLaws)
      (structuralW := structuralW) (classificationW := classificationW)
      (sectionFiveW := sectionFiveW)
      (sectionFourW := sectionFourW) (sectionFourV := sectionFourV)
      (deepWW := deepWW)
      (n := N + 3) a S.beforeLemma92 hfirstSelected ambient selectedConditions
  have hunaryOrder : a.order (⟨0, by omega⟩ : Fin (N + 5)) =
      S.beforeLemma92.firstUnarySegment.order (0 : Fin 1) :=
    hfirstSelected.trans S.beforeLemma92.firstUnarySegment_order_zero.symm
  have hunaryDefect := S.unaryCappedDefect_eq a b D
  have hnotExceptional :
      ¬a.Beli2019Lemma814Exceptional S.beforeLemma92.firstUnarySegment := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.not_lemma814Exceptional_of_firstThirdDefect_eq_firstAlpha
      S.beforeLemma92.firstUnarySegment hunaryDefect
  have hprescribed : Nonempty
      (a.Beli2019PrescribedFirstValueTransform
        S.beforeLemma92.firstUnarySegment) := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    letI : Beli2009AlphaParityLaws.{u, v} K := targetParity
    letI : Beli2009AlphaLocalizationLaws.{u, v} K := targetLocalization
    letI : BeliLemma43ConstructionLaws.{u, v} K := targetConstruction
    letI : Beli2006SectionTwoLaws.{u, v} K := targetSectionTwo
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    letI : DyadicBinaryFirstScalingLaws.{u, v} K := targetBinaryScaling
    letI : DyadicQuaternaryFirstScalingLaws.{u, v} K :=
      targetQuaternaryScaling
    letI : BeliLemma49Laws.{u, v} K := targetLemma49
    letI : BeliLemma47Laws.{u, v} K := targetLemma47
    letI : BONGStructuralLaws.{u, v} K := structuralV
    exact (a.beli2019Lemma814Explicit
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      S.beforeLemma92.firstUnarySegment hunaryOrder unaryConditions).mpr
        hnotExceptional
  rcases hprescribed with ⟨P⟩
  have hTa : Nonempty (Beli2019Lemma92Transform P.transformed) := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    letI : Beli2009AlphaParityLaws.{u, v} K := targetParity
    letI : Beli2009AlphaLocalizationLaws.{u, v} K := targetLocalization
    letI : BeliLemma43ConstructionLaws.{u, v} K := targetConstruction
    letI : Beli2006SectionTwoLaws.{u, v} K := targetSectionTwo
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    letI : DyadicBinaryFirstScalingLaws.{u, v} K := targetBinaryScaling
    letI : DyadicQuaternaryFirstScalingLaws.{u, v} K :=
      targetQuaternaryScaling
    letI : BeliLemma49Laws.{u, v} K := targetLemma49
    letI : BeliLemma47Laws.{u, v} K := targetLemma47
    exact P.transformed.beli2019Lemma92
  rcases hTa with ⟨Ta⟩
  let normalized : Beli2019Lemma93NormalizedPair a b :=
    Beli2019Lemma93NormalizedPair.ofTransforms
      (classificationV := classificationV) (classificationW := classificationW)
      a b conditions P.transformed S.beforeLemma92
      (P.firstValue_eq.trans
        S.beforeLemma92.firstUnarySegment_valueUnit_zero)
      Ta S.transform
  have hsourceEarly : S.beforeLemma92.Lemma92EarlyAlternative := by
    apply (b.lemma92EarlyAlternative_iff
      (classification := classificationW) S.beforeLemma92).mp
    exact Or.inl (sourceFirstThird_lt_of_exceptional a b D)
  have hrawFinal : defectOrder (K := K)
      ((-1) * Ta.transformed.prefixProduct 3 *
        S.transform.transformed.prefixProduct 1) =
      (b.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) : WithTop ℚ) := by
    apply firstThirdRawDefect_changeTarget_eq_of_lt_alphaThree
      (prefixChangeV := prefixChangeV)
      a Ta.transformed S.transform.transformed
      (b.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) : WithTop ℚ)
      S.firstThirdRawDefect_eq
    exact_mod_cast D.targetThirdAlpha_gt_source
  have hsourceAlpha : b.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) =
      S.transform.transformed.alphaValue
        (⟨0, by omega⟩ : Fin (N + 4)) := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact b.alpha_invariant S.transform.transformed
      (⟨0, by omega⟩ : Fin (N + 4))
  refine ⟨{
    normalized := normalized
    lowData := D
    sourceEarly := hsourceEarly
    firstThirdRawDefect_eq_sourceFirstAlpha := ?_
  }⟩
  exact hrawFinal.trans
    (congrArg (fun z : ℚ => (z : WithTop ℚ)) hsourceAlpha)

private theorem prefixSum_one_eq_order_zero
    (c : GoodBONG q L (N + 1)) :
    c.orderSequence.prefixSum 1 = c.order ⟨0, by omega⟩ := by
  rw [c.orderSequence.prefixSum_one,
    BeliOrderSequence.entryOrZero_of_lt c.orderSequence (by omega)]
  rfl

private theorem prefixSum_two_eq_orders
    (c : GoodBONG q L (N + 2)) :
    c.orderSequence.prefixSum 2 =
      c.order ⟨0, by omega⟩ + c.order ⟨1, by omega⟩ := by
  rw [c.orderSequence.prefixSum_succ 1,
    prefixSum_one_eq_order_zero c,
    BeliOrderSequence.entryOrZero_of_lt c.orderSequence (by omega)]
  rfl

private theorem prefixSum_three_eq_orders
    (c : GoodBONG q L (N + 3)) :
    c.orderSequence.prefixSum 3 =
      c.order ⟨0, by omega⟩ + c.order ⟨1, by omega⟩ +
        c.order ⟨2, by omega⟩ := by
  rw [c.orderSequence.prefixSum_succ 2,
    prefixSum_two_eq_orders c,
    BeliOrderSequence.entryOrZero_of_lt c.orderSequence (by omega)]
  rfl

private theorem prefixSum_four_eq_orders
    (c : GoodBONG q L (N + 4)) :
    c.orderSequence.prefixSum 4 =
      c.order ⟨0, by omega⟩ + c.order ⟨1, by omega⟩ +
        c.order ⟨2, by omega⟩ + c.order ⟨3, by omega⟩ := by
  rw [c.orderSequence.prefixSum_succ 3,
    prefixSum_three_eq_orders c,
    BeliOrderSequence.entryOrZero_of_lt c.orderSequence (by omega)]
  rfl

/-- At paper boundary `i = 2`, the exact raw defect selected above survives
head deletion.  On the original side the source first alpha is the active
cap; on the tail side the target cap can only increase. -/
theorem Beli2019Lemma93ExceptionalNormalizedPair.firstCoreDefect_eq_tail
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 5)} {b : GoodBONG r M (N + 5)}
    (P : Beli2019Lemma93ExceptionalNormalizedPair a b) :
    P.normalized.targetTransform.transformed.truncatedPrefixDefect
        P.normalized.sourceTransform.transformed (-1) 3 1 =
      P.normalized.targetTransform.transformed.tail.truncatedPrefixDefect
        P.normalized.sourceTransform.transformed.tail (-1) 2 0 := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let beta : WithTop ℚ :=
    (B.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) : WithTop ℚ)
  have htargetInvariant :
      a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) =
        A.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) := by
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    exact a.alpha_invariant A (⟨2, by omega⟩ : Fin (N + 4))
  have hsourceInvariant :
      b.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) =
        B.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact b.alpha_invariant B (⟨0, by omega⟩ : Fin (N + 4))
  have hbetaTarget : beta ≤
      (A.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) : WithTop ℚ) := by
    change (B.alphaValue (⟨0, by omega⟩ : Fin (N + 4)) : WithTop ℚ) ≤ _
    exact_mod_cast ((hsourceInvariant.symm.trans_lt
      P.lowData.targetThirdAlpha_gt_source).trans_eq htargetInvariant).le
  have hbetaTail : beta ≤
      (A.tail.alphaValue (⟨1, by omega⟩ : Fin (N + 3)) : WithTop ℚ) := by
    have hshift := A.alphaValue_shift_le_tail
      (⟨1, by omega⟩ : Fin (N + 3))
    have hsucc : Fin.succ (⟨1, by omega⟩ : Fin (N + 3)) =
        (⟨2, by omega⟩ : Fin (N + 4)) := by
      apply Fin.ext
      rfl
    rw [hsucc] at hshift
    exact hbetaTarget.trans hshift
  have hrawOriginal : defectOrder (K := K)
      ((-1) * A.prefixProduct 3 * B.prefixProduct 1) = beta := by
    simpa only [A, B, beta] using
      P.firstThirdRawDefect_eq_sourceFirstAlpha
  have hrawTail : defectOrder (K := K)
      ((-1) * A.tail.prefixProduct 2 * B.tail.prefixProduct 0) = beta := by
    have hshift := A.defectOrder_shiftedPrefixes_eq_tail B
      P.normalized.headValue_eq (-1) 2 0 (by omega) (by omega)
    exact hshift.symm.trans P.firstThirdRawDefect_eq_sourceFirstAlpha
  have hAOriginal : A.prefixAlphaCap 3 =
      (A.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) : WithTop ℚ) := by
    rw [A.prefixAlphaCap_of_internal (by omega) (by omega)]
  have hBOriginal : B.prefixAlphaCap 1 = beta := by
    rw [B.prefixAlphaCap_of_internal (by omega) (by omega)]
  have hATail : A.tail.prefixAlphaCap 2 =
      (A.tail.alphaValue (⟨1, by omega⟩ : Fin (N + 3)) : WithTop ℚ) := by
    rw [A.tail.prefixAlphaCap_of_internal (by omega) (by omega)]
  have hBTail : B.tail.prefixAlphaCap 0 = ⊤ := by
    exact B.tail.prefixAlphaCap_zero
  unfold truncatedPrefixDefect
  rw [hrawOriginal, hrawTail,
    hAOriginal, hBOriginal, hATail, hBTail, min_top_right]
  rw [min_eq_right hbetaTarget, min_self, min_eq_left hbetaTail]

/-- At paper boundary `i = 3`, both signed core products have odd valuation.
Consequently both capped defects vanish, exactly as in the two parity
computations in the last paragraph of Beli's proof. -/
theorem Beli2019Lemma93ExceptionalNormalizedPair.secondCoreDefects_eq_zero
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 5)} {b : GoodBONG r M (N + 5)}
    (P : Beli2019Lemma93ExceptionalNormalizedPair a b) :
    P.normalized.targetTransform.transformed.truncatedPrefixDefect
        P.normalized.sourceTransform.transformed (-1) 4 2 = 0 ∧
      P.normalized.targetTransform.transformed.tail.truncatedPrefixDefect
        P.normalized.sourceTransform.transformed.tail (-1) 3 1 = 0 := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  have hAOrders : a.SameOrders A := by
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    exact a.order_invariant A
  have hBOrders : b.SameOrders B := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact b.order_invariant B
  have hmodOne := P.lowData.arithmetic.targetOrder_modEq
    (⟨1, by omega⟩ : Fin (N + 5)) (by norm_num)
  have hmodTwo := P.lowData.arithmetic.targetOrder_modEq
    (⟨2, by omega⟩ : Fin (N + 5)) (by norm_num)
  have hmodThree := P.lowData.arithmetic.targetOrder_modEq
    (⟨3, by omega⟩ : Fin (N + 5)) (by norm_num)
  rw [Int.modEq_iff_dvd] at hmodOne hmodTwo hmodThree
  rcases hmodOne with ⟨zOne, hzOne⟩
  rcases hmodTwo with ⟨zTwo, hzTwo⟩
  rcases hmodThree with ⟨zThree, hzThree⟩
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hnegOne : ordUnit K (-1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (-1 : Kˣ) (-1)
    have hmul : (-1 : Kˣ) * (-1) = 1 := by norm_num
    rw [hmul, hone] at h
    omega
  have horderOriginal : ordUnit K
      ((-1 : Kˣ) * A.prefixProduct 4 * B.prefixProduct 2) =
        A.order ⟨0, by omega⟩ + A.order ⟨1, by omega⟩ +
          A.order ⟨2, by omega⟩ + A.order ⟨3, by omega⟩ +
            B.order ⟨0, by omega⟩ + B.order ⟨1, by omega⟩ := by
    rw [ordUnit_mul, ordUnit_mul, hnegOne, zero_add,
      A.ordUnit_prefixProduct_eq_orderSequence_prefixSum 4 (by omega),
      B.ordUnit_prefixProduct_eq_orderSequence_prefixSum 2 (by omega),
      prefixSum_four_eq_orders A, prefixSum_two_eq_orders B]
    ring
  have hsumOriginal :
      A.order ⟨0, by omega⟩ + A.order ⟨1, by omega⟩ +
          A.order ⟨2, by omega⟩ + A.order ⟨3, by omega⟩ +
            B.order ⟨0, by omega⟩ + B.order ⟨1, by omega⟩ =
        2 * a.order (⟨0, by omega⟩ : Fin (N + 5)) +
          2 * a.order (⟨1, by omega⟩ : Fin (N + 5)) +
            a.order (⟨2, by omega⟩ : Fin (N + 5)) +
              a.order (⟨3, by omega⟩ : Fin (N + 5)) + 1 := by
    rw [← hAOrders (⟨0, by omega⟩ : Fin (N + 5)),
      ← hAOrders (⟨1, by omega⟩ : Fin (N + 5)),
      ← hAOrders (⟨2, by omega⟩ : Fin (N + 5)),
      ← hAOrders (⟨3, by omega⟩ : Fin (N + 5)),
      ← hBOrders (⟨0, by omega⟩ : Fin (N + 5)),
      ← hBOrders (⟨1, by omega⟩ : Fin (N + 5)),
      P.lowData.arithmetic.sourceFirst_eq,
      P.lowData.arithmetic.sourceSecond_eq]
    ring
  have hoddOriginal : Odd (ordUnit K
      ((-1 : Kˣ) * A.prefixProduct 4 * B.prefixProduct 2)) := by
    rw [horderOriginal, hsumOriginal]
    refine ⟨3 * a.order (⟨0, by omega⟩ : Fin (N + 5)) -
      2 * zOne - zTwo - zThree, ?_⟩
    omega
  have hATailZero : A.tail.order (⟨0, by omega⟩ : Fin (N + 4)) =
      a.order (⟨1, by omega⟩ : Fin (N + 5)) := by
    rw [A.order_goodTail]
    exact (hAOrders (⟨1, by omega⟩ : Fin (N + 5))).symm
  have hATailOne : A.tail.order (⟨1, by omega⟩ : Fin (N + 4)) =
      a.order (⟨2, by omega⟩ : Fin (N + 5)) := by
    rw [A.order_goodTail]
    exact (hAOrders (⟨2, by omega⟩ : Fin (N + 5))).symm
  have hATailTwo : A.tail.order (⟨2, by omega⟩ : Fin (N + 4)) =
      a.order (⟨3, by omega⟩ : Fin (N + 5)) := by
    rw [A.order_goodTail]
    exact (hAOrders (⟨3, by omega⟩ : Fin (N + 5))).symm
  have hBTailZero : B.tail.order (⟨0, by omega⟩ : Fin (N + 4)) =
      a.order (⟨1, by omega⟩ : Fin (N + 5)) + 1 := by
    rw [B.order_goodTail]
    have hsucc : Fin.succ (⟨0, by omega⟩ : Fin (N + 4)) =
        (⟨1, by omega⟩ : Fin (N + 5)) := by
      apply Fin.ext
      rfl
    rw [hsucc, ← hBOrders (⟨1, by omega⟩ : Fin (N + 5)),
      P.lowData.arithmetic.sourceSecond_eq]
  have horderTail : ordUnit K
      ((-1 : Kˣ) * A.tail.prefixProduct 3 * B.tail.prefixProduct 1) =
        A.tail.order ⟨0, by omega⟩ + A.tail.order ⟨1, by omega⟩ +
          A.tail.order ⟨2, by omega⟩ + B.tail.order ⟨0, by omega⟩ := by
    rw [ordUnit_mul, ordUnit_mul, hnegOne, zero_add,
      A.tail.ordUnit_prefixProduct_eq_orderSequence_prefixSum 3 (by omega),
      B.tail.ordUnit_prefixProduct_eq_orderSequence_prefixSum 1 (by omega),
      prefixSum_three_eq_orders A.tail, prefixSum_one_eq_order_zero B.tail]
  have hoddTail : Odd (ordUnit K
      ((-1 : Kˣ) * A.tail.prefixProduct 3 * B.tail.prefixProduct 1)) := by
    rw [horderTail, hATailZero, hATailOne, hATailTwo, hBTailZero]
    refine ⟨2 * a.order (⟨0, by omega⟩ : Fin (N + 5)) -
      2 * zOne - zTwo - zThree, ?_⟩
    omega
  constructor
  · exact truncatedPrefixDefect_eq_zero_of_odd_order_mixed
      (alphaV := targetLaws) (alphaW := sourceLaws)
      A B (-1) 4 2 hoddOriginal
  · exact truncatedPrefixDefect_eq_zero_of_odd_order_mixed
      (alphaV := targetLaws) (alphaW := sourceLaws)
      A.tail B.tail (-1) 3 1 hoddTail

/-- At paper boundary `i = 4`, the target cap is covered by the later part
of Lemma 9.2 and the source cap by its exceptional early clause. -/
theorem Beli2019Lemma93ExceptionalNormalizedPair.thirdCoreDefect_eq_tail
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 5)} {b : GoodBONG r M (N + 5)}
    (P : Beli2019Lemma93ExceptionalNormalizedPair a b) :
    P.normalized.targetTransform.transformed.truncatedPrefixDefect
        P.normalized.sourceTransform.transformed (-1) 5 3 =
      P.normalized.targetTransform.transformed.tail.truncatedPrefixDefect
        P.normalized.sourceTransform.transformed.tail (-1) 4 2 := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  have htargetLater : ∀ k : Fin (N + 3), 2 ≤ k.val →
      A.alphaValue k.succ = A.tail.alphaValue k := by
    intro k hk
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    exact P.normalized.targetTransform.transformed_laterAlpha_eq_tail k hk
  have hcapA : A.prefixAlphaCap 5 = A.tail.prefixAlphaCap 4 :=
    A.prefixAlphaCap_shift_eq_tail_of_laterAlphaValue_eq
      htargetLater 4 (by omega) (by omega)
  have hsourceEarly :
      B.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) =
        B.tail.alphaValue (⟨1, by omega⟩ : Fin (N + 3)) := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact P.normalized.sourceTransform.transformed_earlyAlpha_eq_tail
      P.sourceEarly
  have hcapB : B.prefixAlphaCap 3 = B.tail.prefixAlphaCap 2 := by
    rw [B.prefixAlphaCap_of_internal (by omega) (by omega),
      B.tail.prefixAlphaCap_of_internal (by omega) (by omega)]
    exact congrArg (fun z : ℚ => (z : WithTop ℚ)) hsourceEarly
  exact A.truncatedPrefixDefect_shift_eq_tail_of_caps_eq
    B P.normalized.headValue_eq (-1) 4 2 (by omega) (by omega) hcapA hcapB

/-- From paper boundary `i = 5` onward, both caps are in the unconditional
later range of Lemma 9.2. -/
theorem Beli2019Lemma93ExceptionalNormalizedPair.laterCoreDefect_eq_tail
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 5)} {b : GoodBONG r M (N + 5)}
    (P : Beli2019Lemma93ExceptionalNormalizedPair a b)
    (k : Nat) (hk : 4 ≤ k) (hklt : k < N + 4) :
    P.normalized.targetTransform.transformed.truncatedPrefixDefect
        P.normalized.sourceTransform.transformed (-1) (k + 2) k =
      P.normalized.targetTransform.transformed.tail.truncatedPrefixDefect
        P.normalized.sourceTransform.transformed.tail (-1) (k + 1) (k - 1) := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let i : RepresentationIndex (N + 4) (N + 4) :=
    { val := k
      pos := by omega
      lt_large := hklt
      le_small := by omega }
  have h := A.primaryCoreDefect_shift_eq_tail_of_laterAlphaValue_eq
    B P.normalized.headValue_eq
    (fun j hj ↦ by
      letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
      exact P.normalized.targetTransform.transformed_laterAlpha_eq_tail j hj)
    (fun j hj ↦ by
      letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
      exact P.normalized.sourceTransform.transformed_laterAlpha_eq_tail j hj)
    i hk
  simpa only [i] using h

/-- Uniform core-defect transport for every valid comparison boundary.  The
four cases correspond exactly to the four calculations in the final branch
of the printed proof. -/
theorem Beli2019Lemma93ExceptionalNormalizedPair.coreDefect_eq_tail
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 5)} {b : GoodBONG r M (N + 5)}
    (P : Beli2019Lemma93ExceptionalNormalizedPair a b)
    (k : Nat) (hkpos : 0 < k) (hklt : k < N + 4) :
    P.normalized.targetTransform.transformed.truncatedPrefixDefect
        P.normalized.sourceTransform.transformed (-1) (k + 2) k =
      P.normalized.targetTransform.transformed.tail.truncatedPrefixDefect
        P.normalized.sourceTransform.transformed.tail (-1) (k + 1) (k - 1) := by
  by_cases hone : k = 1
  · subst k
    simpa only [Nat.reduceAdd, Nat.reduceSub] using
      (P.firstCoreDefect_eq_tail
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        (classificationV := classificationV) (classificationW := classificationW))
  by_cases htwo : k = 2
  · subst k
    rcases P.secondCoreDefects_eq_zero
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV) (classificationW := classificationW)
        with ⟨horiginal, htail⟩
    simpa only [Nat.reduceAdd, Nat.reduceSub, horiginal, htail]
  by_cases hthree : k = 3
  · subst k
    simpa only [Nat.reduceAdd, Nat.reduceSub] using
      (P.thirdCoreDefect_eq_tail
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        (classificationV := classificationV) (classificationW := classificationW))
  · exact P.laterCoreDefect_eq_tail
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV) (classificationW := classificationW)
      k (by omega) hklt

private theorem representationIndex_eq_of_val_eq_exceptional
    {largeRank smallRank : Nat}
    (i j : RepresentationIndex largeRank smallRank)
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  simp_all

/-- The four explicit defect calculations give the complete low reverse
certificate.  At the last tail boundary the secondary candidate is absent,
so primary-core equality alone is sufficient. -/
theorem Beli2019Lemma93ExceptionalNormalizedPair.toLowReverseCertificate
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 5)} {b : GoodBONG r M (N + 5)}
    (P : Beli2019Lemma93ExceptionalNormalizedPair a b) :
    Beli2019Lemma93LowReverseCertificate a b P.normalized := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let firstTail : RepresentationIndex (N + 4) (N + 4) :=
    firstRepresentationIndex (N + 2) (N + 3)
  refine { reverseAtImportant := ?_ }
  intro i himportant _hlow
  by_cases hone : i.val = 1
  · have hi : i = firstTail := by
      apply representationIndex_eq_of_val_eq_exceptional
      simpa only [firstTail, firstRepresentationIndex] using hone
    have hshift : firstTail.tailShift =
        secondRepresentationIndex (N + 2) (N + 3) := by
      apply representationIndex_eq_of_val_eq_exceptional
      simp only [RepresentationIndex.tailShift_val, firstTail,
        firstRepresentationIndex, secondRepresentationIndex]
    have hfirstOrder : A.order (0 : Fin (N + 5)) =
        B.order (0 : Fin (N + 5)) := by
      unfold GoodBONG.order
      rw [A.toBONG.order_eq_ordUnit, B.toBONG.order_eq_ordUnit]
      exact congrArg (ordUnit K) (by
        apply Units.ext
        exact P.normalized.headValue_eq)
    have hdefect := P.firstCoreDefect_eq_tail
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV) (classificationW := classificationW)
    rw [hi, hshift]
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact (A.representationAlpha_tail_first_eq_originalSecond_of_defect_eq
      B hfirstOrder hdefect).le
  · have hi : 1 < i.val := by
      have := i.pos
      omega
    have hcore := P.coreDefect_eq_tail
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV) (classificationW := classificationW)
      i.val i.pos i.lt_large
    by_cases hinterior : i.val + 1 < N + 4
    · exact (A.representationAlpha_tail_eq_shift_of_core_eq_at_important
        (alphaV := targetLaws) (alphaW := sourceLaws)
        B P.normalized.headValue_eq i hi himportant hcore
        (fun _ ↦ by
          have hprevious := P.coreDefect_eq_tail
            (targetLaws := targetLaws) (sourceLaws := sourceLaws)
            (classificationV := classificationV)
            (classificationW := classificationW)
            (i.val - 1) (by omega) (by omega)
          simpa only [show i.val - 1 + 2 = i.val + 1 by omega,
            show i.val - 1 + 1 = i.val by omega,
            show i.val - 1 - 1 = i.val - 2 by omega] using hprevious)
        (fun _ ↦ by
          have hnext := P.coreDefect_eq_tail
            (targetLaws := targetLaws) (sourceLaws := sourceLaws)
            (classificationV := classificationV)
            (classificationW := classificationW)
            (i.val + 1) (by omega) hinterior
          simpa only [show i.val + 1 + 2 = i.val + 3 by omega,
            show i.val + 1 + 1 = i.val + 2 by omega,
            show i.val + 1 - 1 = i.val by omega] using hnext)).le
    · have hprimary :=
        A.representationPrimaryDefect_tail_eq_shift_of_core_eq B i hcore
      exact (A.representationAlpha_tail_eq_shift_of_primary_secondary_eq
        B i hi hprimary (fun h ↦ False.elim (hinterior h))).le

/-- The selected exceptional pair, together with the proved low certificate,
is an ordinary head-reduction input for the recursive Section 9 argument. -/
noncomputable def Beli2019Lemma93ExceptionalNormalizedPair.toLemma93Input
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 4)))
    (P : Beli2019Lemma93ExceptionalNormalizedPair a b) :
    Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl (N + 4))
        ambient conditions) :=
  P.normalized.toLemma93Input
    (classificationV := classificationV) (classificationW := classificationW)
    a b ambient conditions
    (P.toLowReverseCertificate
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV) (classificationW := classificationW))

set_option maxHeartbeats 2400000 in
/-- End-to-end realization of the extra final branch proved in the v2 text.
The negated Lemma 9.1 alternatives make explicit that this is the genuinely
new branch rather than one of the four already discharged order cases. -/
theorem exists_beli2019Lemma93Input_exceptional
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [targetParity : Beli2009AlphaParityLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [targetLocalization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [targetConstruction : BeliLemma43ConstructionLaws.{u, v} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [targetSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [targetBinaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [targetQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [targetLemma49 : BeliLemma49Laws.{u, v} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [targetLemma47 : BeliLemma47Laws.{u, v} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFiveW : Beli2019SectionFiveLaws.{u, w} K]
    [sectionFourW : Beli2019SectionFourLaws.{u, w} K]
    [sectionFourV : Beli2019SectionFourLaws.{u, v} K]
    [deepWW : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K]
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5))
    (hfirst : a.order (0 : Fin (N + 5)) = b.order (0 : Fin (N + 5)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 4)))
    (hexceptional : a.Beli2019Lemma93ExceptionalCondition b)
    (hnotLemma91 : ¬a.Lemma91Alternative b) :
    Nonempty (Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl (N + 4))
        ambient conditions)) := by
  have H := exceptionalArithmetic_of_not_lemma91
    a b hfirst hexceptional hnotLemma91
  have D := exceptionalLowData
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (targetParity := targetParity) (sourceParity := sourceParity)
    a b hfirst conditions H
  rcases exists_beli2019Lemma93ExceptionalNormalizedPair
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (targetParity := targetParity) (sourceParity := sourceParity)
      (targetLocalization := targetLocalization)
      (sourceLocalization := sourceLocalization)
      (targetConstruction := targetConstruction)
      (sourceConstruction := sourceConstruction)
      (targetSectionTwo := targetSectionTwo)
      (sourceSectionTwo := sourceSectionTwo)
      (classificationV := classificationV) (classificationW := classificationW)
      (targetBinaryScaling := targetBinaryScaling)
      (sourceBinaryScaling := sourceBinaryScaling)
      (targetQuaternaryScaling := targetQuaternaryScaling)
      (sourceQuaternaryScaling := sourceQuaternaryScaling)
      (targetLemma49 := targetLemma49) (sourceLemma49 := sourceLemma49)
      (targetLemma47 := targetLemma47) (sourceLemma47 := sourceLemma47)
      (structuralV := structuralV) (structuralW := structuralW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      (sectionFiveW := sectionFiveW) (sectionFourW := sectionFourW)
      (sectionFourV := sectionFourV) (deepWW := deepWW)
      a b hfirst ambient conditions D with ⟨P⟩
  exact ⟨P.toLemma93Input
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (classificationV := classificationV) (classificationW := classificationW)
    a b ambient conditions⟩

section CompleteLemma93

variable
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [targetParity : Beli2009AlphaParityLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [targetLocalization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [targetConstruction : BeliLemma43ConstructionLaws.{u, v} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [targetSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [targetBinaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [targetQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [targetLemma49 : BeliLemma49Laws.{u, v} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [targetLemma47 : BeliLemma47Laws.{u, v} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFiveW : Beli2019SectionFiveLaws.{u, w} K]
    [sectionFourW : Beli2019SectionFourLaws.{u, w} K]
    [sectionFourV : Beli2019SectionFourLaws.{u, v} K]
    [deepWW : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K]

/-- Beli (2019), Lemma 9.3, in its printed hypothesis: the five alternatives
are exactly `Lemma91Alternative`.  The proof dispatches the exhaustive
Case 1/Case 2 split and produces the concrete recursive head input. -/
theorem exists_beli2019Lemma93Input
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5))
    (hfirst : a.order (0 : Fin (N + 5)) = b.order (0 : Fin (N + 5)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 4)))
    (hlemma91 : a.Lemma91Alternative b) :
    Nonempty (Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl (N + 4))
        ambient conditions)) := by
  by_cases hcase : a.Beli2019Lemma93CaseOneCondition b
  · exact a.exists_beli2019Lemma93Input_caseOne
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (targetParity := targetParity) (sourceParity := sourceParity)
      (targetLocalization := targetLocalization)
      (sourceLocalization := sourceLocalization)
      (targetConstruction := targetConstruction)
      (sourceConstruction := sourceConstruction)
      (targetSectionTwo := targetSectionTwo)
      (sourceSectionTwo := sourceSectionTwo)
      (classificationV := classificationV) (classificationW := classificationW)
      (targetBinaryScaling := targetBinaryScaling)
      (sourceBinaryScaling := sourceBinaryScaling)
      (targetQuaternaryScaling := targetQuaternaryScaling)
      (sourceQuaternaryScaling := sourceQuaternaryScaling)
      (targetLemma49 := targetLemma49) (sourceLemma49 := sourceLemma49)
      (targetLemma47 := targetLemma47) (sourceLemma47 := sourceLemma47)
      (structuralV := structuralV) (structuralW := structuralW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      (sectionFiveW := sectionFiveW) (sectionFourW := sectionFourW)
      (sectionFourV := sectionFourV) (deepWW := deepWW)
      b hfirst ambient conditions hlemma91 hcase
  · have hcaseTwo : a.Beli2019Lemma93CaseTwoCondition b :=
      (a.beli2019Lemma93CaseTwoCondition_iff_not_caseOneCondition b).2 hcase
    exact exists_beli2019Lemma93Input_caseTwo
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (targetParity := targetParity) (sourceParity := sourceParity)
      (targetLocalization := targetLocalization)
      (sourceLocalization := sourceLocalization)
      (targetConstruction := targetConstruction)
      (sourceConstruction := sourceConstruction)
      (targetSectionTwo := targetSectionTwo)
      (sourceSectionTwo := sourceSectionTwo)
      (classificationV := classificationV) (classificationW := classificationW)
      (targetBinaryScaling := targetBinaryScaling)
      (sourceBinaryScaling := sourceBinaryScaling)
      (targetQuaternaryScaling := targetQuaternaryScaling)
      (sourceQuaternaryScaling := sourceQuaternaryScaling)
      (targetLemma49 := targetLemma49) (sourceLemma49 := sourceLemma49)
      (targetLemma47 := targetLemma47) (sourceLemma47 := sourceLemma47)
      (structuralV := structuralV) (structuralW := structuralW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      (sectionFiveW := sectionFiveW) (sectionFourW := sectionFourW)
      (sectionFourV := sectionFourV) (deepWW := deepWW)
      a b hfirst ambient conditions hlemma91 hcaseTwo

/-- The stronger disjunction actually established by all paragraphs of the
v2 proof: besides the printed five alternatives, it includes the final
`S₂ = R₂ + 1`, `R₁ = R₅` branch. -/
theorem exists_beli2019Lemma93Input_v2Strengthened
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5))
    (hfirst : a.order (0 : Fin (N + 5)) = b.order (0 : Fin (N + 5)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 4)))
    (halternative : a.Lemma91Alternative b ∨
      a.Beli2019Lemma93ExceptionalCondition b) :
    Nonempty (Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl (N + 4))
        ambient conditions)) := by
  rcases halternative with hlemma91 | hexceptional
  · exact exists_beli2019Lemma93Input
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (targetParity := targetParity) (sourceParity := sourceParity)
      (targetLocalization := targetLocalization)
      (sourceLocalization := sourceLocalization)
      (targetConstruction := targetConstruction)
      (sourceConstruction := sourceConstruction)
      (targetSectionTwo := targetSectionTwo) (sourceSectionTwo := sourceSectionTwo)
      (classificationV := classificationV) (classificationW := classificationW)
      (targetBinaryScaling := targetBinaryScaling)
      (sourceBinaryScaling := sourceBinaryScaling)
      (targetQuaternaryScaling := targetQuaternaryScaling)
      (sourceQuaternaryScaling := sourceQuaternaryScaling)
      (targetLemma49 := targetLemma49) (sourceLemma49 := sourceLemma49)
      (targetLemma47 := targetLemma47) (sourceLemma47 := sourceLemma47)
      (structuralV := structuralV) (structuralW := structuralW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      (sectionFiveW := sectionFiveW) (sectionFourW := sectionFourW)
      (sectionFourV := sectionFourV) (deepWW := deepWW)
      a b hfirst ambient conditions hlemma91
  · by_cases hlemma91 : a.Lemma91Alternative b
    · exact exists_beli2019Lemma93Input
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        (targetParity := targetParity) (sourceParity := sourceParity)
        (targetLocalization := targetLocalization)
        (sourceLocalization := sourceLocalization)
        (targetConstruction := targetConstruction)
        (sourceConstruction := sourceConstruction)
        (targetSectionTwo := targetSectionTwo)
        (sourceSectionTwo := sourceSectionTwo)
        (classificationV := classificationV) (classificationW := classificationW)
        (targetBinaryScaling := targetBinaryScaling)
        (sourceBinaryScaling := sourceBinaryScaling)
        (targetQuaternaryScaling := targetQuaternaryScaling)
        (sourceQuaternaryScaling := sourceQuaternaryScaling)
        (targetLemma49 := targetLemma49) (sourceLemma49 := sourceLemma49)
        (targetLemma47 := targetLemma47) (sourceLemma47 := sourceLemma47)
        (structuralV := structuralV) (structuralW := structuralW)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        (sectionFiveW := sectionFiveW) (sectionFourW := sectionFourW)
        (sectionFourV := sectionFourV) (deepWW := deepWW)
        a b hfirst ambient conditions hlemma91
    · exact exists_beli2019Lemma93Input_exceptional
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        (targetParity := targetParity) (sourceParity := sourceParity)
        (targetLocalization := targetLocalization)
        (sourceLocalization := sourceLocalization)
        (targetConstruction := targetConstruction)
        (sourceConstruction := sourceConstruction)
        (targetSectionTwo := targetSectionTwo)
        (sourceSectionTwo := sourceSectionTwo)
        (classificationV := classificationV) (classificationW := classificationW)
        (targetBinaryScaling := targetBinaryScaling)
        (sourceBinaryScaling := sourceBinaryScaling)
        (targetQuaternaryScaling := targetQuaternaryScaling)
        (sourceQuaternaryScaling := sourceQuaternaryScaling)
        (targetLemma49 := targetLemma49) (sourceLemma49 := sourceLemma49)
        (targetLemma47 := targetLemma47) (sourceLemma47 := sourceLemma47)
        (structuralV := structuralV) (structuralW := structuralW)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        (sectionFiveW := sectionFiveW) (sectionFourW := sectionFourW)
        (sectionFourV := sectionFourV) (deepWW := deepWW)
        a b hfirst ambient conditions hexceptional hlemma91

end CompleteLemma93

end BONG.GoodBONG

end Bong
