/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma91ExceptionB
import Bong.Bong.Beli2019CappedDefectSharp

/-!
# Beli (2019), Lemma 9.1: the exception-(c) branch

The last branch of Lemma 9.1 assumes the first two target and source orders
agree and excludes Lemma 8.14(c).  The proof first derives the source-adjacent
defect and the third representation-alpha estimates used in the paper.  It
then splits according to whether the first and third source orders are equal.

This file introduces no paper-specific local-field law.  Its geometric core
is the paper-independent fact that an anisotropic ternary complement cannot
also be represented by an isotropic ternary complement with the same head.
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
  {L : Lattice K V} {M : Lattice K W} {N S : Nat}

/-- In exception (c), Remark 8.7 and the two complementary half-gap
identities give `alpha_1 = R_2 - R_4 + alpha_3`. -/
theorem firstAlpha_eq_secondFourthShift_thirdAlpha_of_exceptionC
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (C : a.Beli2019Lemma814ExceptionC b) :
    a.alphaValue (0 : Fin (N + 2)) =
      (((a.order (1 : Fin (N + 3)) -
        a.order (3 : Fin (N + 3)) : Int) : ℚ) +
          a.alphaValue (2 : Fin (N + 2))) := by
  have htwoOrder : (⟨2, by omega⟩ : Fin (N + 3)) =
      (2 : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have hthreeOrder : (⟨3, by have := C.rank_four; omega⟩ : Fin (N + 3)) =
      (3 : Fin (N + 3)) := by
    have hthreeLt : 3 < N + 3 := by
      have := C.rank_four
      omega
    apply Fin.ext
    change 3 = 3 % (N + 3)
    rw [Nat.mod_eq_of_lt hthreeLt]
  have htwoAlpha : (⟨2, by have := C.rank_four; omega⟩ : Fin (N + 2)) =
      (2 : Fin (N + 2)) := by
    have htwoLt : 2 < N + 2 := by
      have := C.rank_four
      omega
    apply Fin.ext
    change 2 = 2 % (N + 2)
    rw [Nat.mod_eq_of_lt htwoLt]
  have hremark :=
    (a.beli2019Remark87 (0 : Fin (N + 1))
      C.firstThirdOrders_eq).previousAlpha_eq
  have hfirstSecond : a.alphaValue (0 : Fin (N + 2)) =
      (((a.order (1 : Fin (N + 3)) -
        a.order (2 : Fin (N + 3)) : Int) : ℚ) +
          a.alphaValue (1 : Fin (N + 2))) := by
    change a.alphaValue (0 : Fin (N + 2)) =
      (((a.order (1 : Fin (N + 3)) -
        a.order (⟨2, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          a.alphaValue (1 : Fin (N + 2))) at hremark
    rw [htwoOrder] at hremark
    exact hremark
  have hsecond : a.alphaValue (1 : Fin (N + 2)) =
      (ramificationIndex K : ℚ) -
        ((a.order (3 : Fin (N + 3)) -
          a.order (2 : Fin (N + 3)) : Int) : ℚ) / 2 := by
    have h := C.secondAlpha_eq_complement
    change a.alphaValue (1 : Fin (N + 2)) =
      (ramificationIndex K : ℚ) -
        ((a.order (⟨3, by have := C.rank_four; omega⟩ : Fin (N + 3)) -
          a.order (⟨2, by omega⟩ : Fin (N + 3)) : Int) : ℚ) / 2 at h
    rw [hthreeOrder, htwoOrder] at h
    exact h
  have hthird : a.alphaValue (2 : Fin (N + 2)) =
      ((a.order (3 : Fin (N + 3)) -
        a.order (2 : Fin (N + 3)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) := by
    have h := C.thirdAlpha_eq_halfGap
    change a.alphaValue (⟨2, by have := C.rank_four; omega⟩ : Fin (N + 2)) =
      ((a.order (⟨3, by have := C.rank_four; omega⟩ : Fin (N + 3)) -
        a.order (⟨2, by omega⟩ : Fin (N + 3)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) at h
    rw [htwoAlpha, hthreeOrder, htwoOrder] at h
    exact h
  push_cast at hfirstSecond hsecond hthird ⊢
  linarith

/-- The strict second/fourth order inequality in exception (c) makes the
third target alpha strictly larger than the first. -/
theorem firstAlpha_lt_thirdAlpha_of_exceptionC
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (C : a.Beli2019Lemma814ExceptionC b) :
    a.alphaValue (0 : Fin (N + 2)) <
      a.alphaValue (2 : Fin (N + 2)) := by
  have hrelation :=
    a.firstAlpha_eq_secondFourthShift_thirdAlpha_of_exceptionC b C
  have horder : (a.order (1 : Fin (N + 3)) : ℚ) <
      (a.order (3 : Fin (N + 3)) : ℚ) := by
    have h := C.secondFourthOrders_lt
    have hthreeOrder :
        (⟨3, by have := C.rank_four; omega⟩ : Fin (N + 3)) =
        (3 : Fin (N + 3)) := by
      have hthreeLt : 3 < N + 3 := by
        have := C.rank_four
        omega
      apply Fin.ext
      change 3 = 3 % (N + 3)
      rw [Nat.mod_eq_of_lt hthreeLt]
    rw [hthreeOrder] at h
    exact_mod_cast h
  push_cast at hrelation
  linarith

set_option maxHeartbeats 600000 in
-- The proof selects the non-half-gap side of Remark 1.1 and then normalizes
-- the equal target/source orders.
/-- Before removing the source cap, the first source adjacent defect is
already exactly the target second alpha. -/
theorem sourceFirstCappedAdjacentDefect_eq_targetSecond_of_exceptionC
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (hsourceAlpha : c.alphaValue (0 : Fin (S + 1)) =
      a.alphaValue (0 : Fin (N + 2)))
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    c.truncatedPrefixDefect c (-1) 0 2 =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
  have hsourceStrict : c.alphaValue (0 : Fin (S + 1)) <
      c.halfGapValue (0 : Fin (S + 1)) := by
    unfold halfGapValue orderGap
    change c.alphaValue (0 : Fin (S + 1)) <
      (((c.order (1 : Fin (S + 2)) -
        c.order (0 : Fin (S + 2)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ))
    rw [hsourceAlpha, ← hfirst, ← hsecond]
    have htargetStrict := by
      letI : Beli2006AlphaLaws.{u, v} K := targetLaws
      exact a.firstAlpha_lt_halfGap_of_lemma814ExceptionC
        c.firstUnarySegment C
    simpa [halfGapValue, orderGap] using htargetStrict
  have hlocal := by
    letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
    exact c.alpha_eq_min_halfGap_add_cappedAdjacent
      (0 : Fin (S + 1))
  let right : WithTop ℚ :=
    ((((c.order (1 : Fin (S + 2)) -
      c.order (0 : Fin (S + 2)) : Int) : ℚ) : WithTop ℚ) +
        c.truncatedPrefixDefect c (-1) 0 2)
  change (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) =
    min (c.halfGapCandidate (0 : Fin (S + 1))) right at hlocal
  have hrightLe : right ≤ c.halfGapCandidate (0 : Fin (S + 1)) := by
    by_contra hnot
    have hhalfLe : c.halfGapCandidate (0 : Fin (S + 1)) ≤ right :=
      le_of_not_ge hnot
    have hhalfEq : (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) =
        c.halfGapCandidate (0 : Fin (S + 1)) := by
      simpa only [min_eq_left hhalfLe] using hlocal
    have hstrictTop :
        (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) <
          c.halfGapCandidate (0 : Fin (S + 1)) := by
      rw [← c.coe_halfGapValue]
      exact_mod_cast hsourceStrict
    exact (ne_of_lt hstrictTop) hhalfEq
  have hright : (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) =
      right := by
    simpa only [min_eq_right hrightLe] using hlocal
  have hremark := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact (a.beli2019Remark87 (0 : Fin (N + 1))
      C.firstThirdOrders_eq).currentAlpha_eq
  change a.alphaValue (1 : Fin (N + 2)) =
    (((a.order (0 : Fin (N + 3)) -
      a.order (1 : Fin (N + 3)) : Int) : ℚ) +
        a.alphaValue (0 : Fin (N + 2))) at hremark
  have htargetRelation :
      ((c.orderGap (0 : Fin (S + 1)) : ℚ) : WithTop ℚ) +
          (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) =
        (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) := by
    apply WithTop.coe_eq_coe.mpr
    unfold orderGap
    change (((c.order (1 : Fin (S + 2)) -
        c.order (0 : Fin (S + 2)) : Int) : ℚ) +
          a.alphaValue (1 : Fin (N + 2)) =
        c.alphaValue (0 : Fin (S + 1)))
    rw [hsourceAlpha, ← hfirst, ← hsecond]
    push_cast at hremark ⊢
    linarith
  apply WithTop.add_left_cancel WithTop.coe_ne_top
  calc
    ((c.orderGap (0 : Fin (S + 1)) : ℚ) : WithTop ℚ) +
          c.truncatedPrefixDefect c (-1) 0 2 = right := by
      change right = right
      rfl
    _ = (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) := hright.symm
    _ = ((c.orderGap (0 : Fin (S + 1)) : ℚ) : WithTop ℚ) +
          (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) :=
      htargetRelation.symm

/-- Exception (c)'s two exact capped defects dominate the mixed determinant
`d[-a_(1,4)c_(1,2)]`.  This is the first inequality in the paper's estimate
of the third representation alpha. -/
theorem targetSecondAlpha_le_firstFour_sourceFirstTwoCappedDefect_of_exceptionC
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (hsourceAlpha : c.alphaValue (0 : Fin (S + 1)) =
      a.alphaValue (0 : Fin (N + 2)))
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) ≤
      a.truncatedPrefixDefect c (-1) 4 2 := by
  have hfirstFour : a.truncatedPrefixDefect a (1 : Kˣ) 4 0 =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
    simpa only [lemma814FirstFourCappedDefect] using
      C.firstFourDefect_eq_secondAlpha
  have hsource :=
    a.sourceFirstCappedAdjacentDefect_eq_targetSecond_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hfirst hsecond hsourceAlpha C
  have hsourceMixed : a.truncatedPrefixDefect c (-1 : Kˣ) 0 2 =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
    rw [a.truncatedPrefixDefect_zero_left_eq_self c]
    exact hsource
  have hdomination :=
    a.truncatedPrefixDefect_domination a c (1 : Kˣ) (-1 : Kˣ) 4 0 2
  rw [hfirstFour, hsourceMixed, min_self] at hdomination
  simpa only [one_mul] using hdomination

set_option maxHeartbeats 1000000 in
-- The optional previous candidate is present precisely from target rank five.
/-- In exception (c), the third representation alpha has the lower bound
`R₃ - S₃ + α₃` displayed in the proof of Lemma 9.1. -/
theorem thirdRepresentationAlpha_lower_of_exceptionC
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    (((c.order (0 : Fin (S + 2)) : ℚ) -
          (c.order (2 : Fin (S + 2)) : ℚ) +
            a.alphaValue (2 : Fin (N + 2)) : ℚ) : WithTop ℚ) ≤
      a.representationAlpha c
        (lemma91ThirdRepresentationIndex
          (by have := C.rank_four; omega) hthree) := by
  let i := lemma91ThirdRepresentationIndex
    (by have := C.rank_four; omega : 3 < N + 3) hthree
  let firstAlpha : Fin (N + 2) := ⟨0, by omega⟩
  let secondAlpha : Fin (N + 2) := ⟨1, by omega⟩
  let thirdAlpha : Fin (N + 2) := ⟨2, by
    have := C.rank_four
    omega⟩
  let firstOrder : Fin (N + 3) := ⟨0, by omega⟩
  let secondOrder : Fin (N + 3) := ⟨1, by omega⟩
  let thirdOrder : Fin (N + 3) := ⟨2, by omega⟩
  let fourthOrder : Fin (N + 3) := ⟨3, by
    have := C.rank_four
    omega⟩
  let sourceFirst : Fin (S + 2) := ⟨0, by omega⟩
  let sourceSecond : Fin (S + 2) := ⟨1, by omega⟩
  let sourceThird : Fin (S + 2) := ⟨2, by omega⟩
  have hFirstAlpha : firstAlpha = (0 : Fin (N + 2)) := by
    apply Fin.ext
    rfl
  have hSecondAlpha : secondAlpha = (1 : Fin (N + 2)) := by
    have hlt : 1 < N + 2 := by
      have := C.rank_four
      omega
    apply Fin.ext
    simp [secondAlpha, Nat.mod_eq_of_lt hlt]
  have hSecondOrder : secondOrder = (1 : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have hThirdAlpha : thirdAlpha = (2 : Fin (N + 2)) := by
    have hlt : 2 < N + 2 := by
      have := C.rank_four
      omega
    apply Fin.ext
    simp [thirdAlpha, Nat.mod_eq_of_lt hlt]
  have hFourthOrder : fourthOrder = (3 : Fin (N + 3)) := by
    have hlt : 3 < N + 3 := by
      have := C.rank_four
      omega
    apply Fin.ext
    simp [fourthOrder, Nat.mod_eq_of_lt hlt]
  have hSourceFirst : sourceFirst = (0 : Fin (S + 2)) := by
    apply Fin.ext
    rfl
  have hSourceSecond : sourceSecond = (1 : Fin (S + 2)) := by
    apply Fin.ext
    simp [sourceSecond, Nat.mod_eq_of_lt (by omega : 1 < S + 2)]
  have hSourceThird : sourceThird = (2 : Fin (S + 2)) := by
    apply Fin.ext
    simp [sourceThird, Nat.mod_eq_of_lt (by omega : 2 < S + 2)]
  have hrigidity := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.secondOrderRigidity_of_exceptionBC
      c hRank hfirst hsecond conditions (Or.inr C)
  have hfull := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.fullFirstThirdDefect_eq_sourceFirstAlpha_of_exceptionBC
      c hRank hfirst hsecond conditions (Or.inr C)
  have hthirdFormula : a.alphaValue thirdAlpha =
      ((a.order fourthOrder - a.order thirdOrder : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) := by
    simpa [thirdAlpha, fourthOrder, thirdOrder, halfGapValue, orderGap]
      using C.thirdAlpha_eq_halfGap
  have hsecondFormula : a.alphaValue secondAlpha =
      (ramificationIndex K : ℚ) -
        ((a.order fourthOrder - a.order thirdOrder : Int) : ℚ) / 2 := by
    simpa [secondAlpha, fourthOrder, thirdOrder,
      lemma814ThirdComplementaryDefect, orderGap]
        using C.secondAlpha_eq_complement
  have hsourceOrders : c.order sourceFirst ≤ c.order sourceThird := by
    have hgood := c.good sourceFirst (by
      simp only [sourceFirst]
      omega)
    change c.order sourceFirst ≤ c.order sourceThird at hgood
    exact hgood
  let threshold : ℚ :=
    (c.order sourceFirst : ℚ) - (c.order sourceThird : ℚ) +
      a.alphaValue thirdAlpha
  suffices hthreshold : (threshold : WithTop ℚ) ≤
      a.representationAlpha c i by
    dsimp only [threshold] at hthreshold
    rw [hSourceFirst, hSourceThird, hThirdAlpha] at hthreshold
    simpa only [i] using hthreshold
  have hhalfQ : threshold ≤
      ((a.order fourthOrder - c.order sourceThird : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) := by
    have houter := C.firstThirdOrders_eq
    change a.order firstOrder = a.order thirdOrder at houter
    have hfirst' : a.order firstOrder = c.order sourceFirst := hfirst
    have houterQ : (a.order firstOrder : ℚ) =
        (a.order thirdOrder : ℚ) := by exact_mod_cast houter
    have hfirstQ : (a.order firstOrder : ℚ) =
        (c.order sourceFirst : ℚ) := by exact_mod_cast hfirst'
    have hsourceOrdersQ : (c.order sourceFirst : ℚ) ≤
        (c.order sourceThird : ℚ) := by exact_mod_cast hsourceOrders
    dsimp only [threshold]
    push_cast at hthirdFormula ⊢
    linarith
  have hhalf : (threshold : WithTop ℚ) ≤
      a.representationHalfGap c i := by
    unfold representationHalfGap
    simpa only [i, lemma91ThirdRepresentationIndex,
      sourceThird, fourthOrder] using
        (show
          (threshold : WithTop ℚ) ≤
            ((((a.order fourthOrder - c.order sourceThird : Int) : ℚ) /
              2 + (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) by
          exact_mod_cast hhalfQ)
  have hmixed :=
    a.targetSecondAlpha_le_firstFour_sourceFirstTwoCappedDefect_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hfirst hsecond hrigidity.2 C
  have hprimaryEquality : threshold =
      ((a.order fourthOrder - c.order sourceThird : Int) : ℚ) +
        a.alphaValue secondAlpha := by
    have houter := C.firstThirdOrders_eq
    change a.order firstOrder = a.order thirdOrder at houter
    have hfirst' : a.order firstOrder = c.order sourceFirst := hfirst
    have houterQ : (a.order firstOrder : ℚ) =
        (a.order thirdOrder : ℚ) := by exact_mod_cast houter
    have hfirstQ : (a.order firstOrder : ℚ) =
        (c.order sourceFirst : ℚ) := by exact_mod_cast hfirst'
    dsimp only [threshold]
    push_cast at hthirdFormula hsecondFormula ⊢
    linarith
  have hprimary : (threshold : WithTop ℚ) ≤
      a.representationPrimaryDefect c i := by
    unfold representationPrimaryDefect
    change (threshold : WithTop ℚ) ≤
      (((a.order fourthOrder - c.order sourceThird : Int) : ℚ) :
          WithTop ℚ) + a.truncatedPrefixDefect c (-1) 4 2
    calc
      (threshold : WithTop ℚ) =
          (((a.order fourthOrder - c.order sourceThird : Int) : ℚ) :
              WithTop ℚ) + (a.alphaValue secondAlpha : WithTop ℚ) := by
        exact_mod_cast hprimaryEquality
      _ ≤ (((a.order fourthOrder - c.order sourceThird : Int) : ℚ) :
              WithTop ℚ) + a.truncatedPrefixDefect c (-1) 4 2 := by
        apply add_le_add_right
        rw [hSecondAlpha]
        exact hmixed
  have hcross : c.order sourceSecond ≤ a.order fourthOrder := by
    have hstrict := C.secondFourthOrders_lt
    change a.order secondOrder < a.order fourthOrder at hstrict
    have hsecond' : a.order secondOrder = c.order sourceSecond := hsecond
    exact hsecond'.symm.trans_le hstrict.le
  by_cases hinterior : 4 < N + 3
  · have htargetSkip : a.order thirdOrder ≤
        a.order (⟨4, hinterior⟩ : Fin (N + 3)) := by
      have hgood := a.good thirdOrder (by omega)
      change a.order thirdOrder ≤
        a.order (⟨thirdOrder.1 + 2, by omega⟩ : Fin (N + 3)) at hgood
      convert hgood using 1
    have hpreviousQ : threshold ≤
        ((a.order fourthOrder +
          a.order (⟨4, hinterior⟩ : Fin (N + 3)) -
          c.order sourceSecond - c.order sourceThird : Int) : ℚ) +
            a.alphaValue firstAlpha := by
      have hrelation :=
        by
          letI : Beli2006AlphaLaws.{u, v} K := targetLaws
          exact a.firstAlpha_eq_secondFourthShift_thirdAlpha_of_exceptionC
            c.firstUnarySegment C
      have houter := C.firstThirdOrders_eq
      change a.order firstOrder = a.order thirdOrder at houter
      have hfirst' : a.order firstOrder = c.order sourceFirst := hfirst
      have hsecond' : a.order secondOrder = c.order sourceSecond := hsecond
      have houterQ : (a.order firstOrder : ℚ) =
          (a.order thirdOrder : ℚ) := by exact_mod_cast houter
      have hfirstQ : (a.order firstOrder : ℚ) =
          (c.order sourceFirst : ℚ) := by exact_mod_cast hfirst'
      have hsecondQ : (a.order secondOrder : ℚ) =
          (c.order sourceSecond : ℚ) := by exact_mod_cast hsecond'
      have htargetSkipQ : (a.order thirdOrder : ℚ) ≤
          (a.order (⟨4, hinterior⟩ : Fin (N + 3)) : ℚ) := by
        exact_mod_cast htargetSkip
      dsimp only [threshold]
      rw [← hFirstAlpha, ← hSecondOrder, ← hFourthOrder,
        ← hThirdAlpha] at hrelation
      push_cast at hrelation ⊢
      linarith
    have hprevious : (threshold : WithTop ℚ) ≤
        a.representationSecondaryPreviousDefect c i
          (by simp only [i, lemma91ThirdRepresentationIndex]; omega) := by
      unfold representationSecondaryPreviousDefect
      change (threshold : WithTop ℚ) ≤
        ((((a.order fourthOrder +
          a.order (⟨4, hinterior⟩ : Fin (N + 3)) -
          c.order sourceSecond - c.order sourceThird : Int) : ℚ) :
            WithTop ℚ) + a.truncatedPrefixDefect c (-1) 3 1)
      rw [hfull, hrigidity.2]
      exact_mod_cast hpreviousQ
    have hprime := by
      letI : Beli2006AlphaLaws.{u, v} K := targetLaws
      exact a.representationAlphaPrime_eq_min_primary_previous c i
        (by simp only [i, lemma91ThirdRepresentationIndex]; omega) hcross
    rw [a.representationAlpha_eq_min_halfGap_prime c i, hprime]
    exact le_min hhalf (le_min hprimary hprevious)
  · have hN : N = 1 := by
      have := C.rank_four
      omega
    subst N
    rw [a.representationAlpha_eq_min_halfGap_prime c i,
      a.representationAlphaPrime_eq_primary_of_not_interior c i
        (by simp only [i, lemma91ThirdRepresentationIndex]; omega)]
    exact le_min hhalf hprimary

/-- Condition (ii), together with `α₁ < α₃`, turns the preceding lower bound
into strict bounds for both the raw equal-prefix determinant defect and the
source prefix cap. -/
theorem thirdRawDefect_and_sourceCap_strict_of_exceptionC
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    ((((c.order (0 : Fin (S + 2)) : ℚ) -
          (c.order (2 : Fin (S + 2)) : ℚ) +
            a.alphaValue (0 : Fin (N + 2)) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
          ((1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 3)) ∧
      ((((c.order (0 : Fin (S + 2)) : ℚ) -
          (c.order (2 : Fin (S + 2)) : ℚ) +
            a.alphaValue (0 : Fin (N + 2)) : ℚ) : WithTop ℚ) <
        c.prefixAlphaCap 3) := by
  let i := lemma91ThirdRepresentationIndex
    (by have := C.rank_four; omega : 3 < N + 3) hthree
  have hlower :=
    a.thirdRepresentationAlpha_lower_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree C
  have halpha := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.firstAlpha_lt_thirdAlpha_of_exceptionC
      c.firstUnarySegment C
  have hthreshold :
      (((c.order (0 : Fin (S + 2)) : ℚ) -
          (c.order (2 : Fin (S + 2)) : ℚ) +
            a.alphaValue (0 : Fin (N + 2)) : ℚ) : WithTop ℚ) <
        (((c.order (0 : Fin (S + 2)) : ℚ) -
          (c.order (2 : Fin (S + 2)) : ℚ) +
            a.alphaValue (2 : Fin (N + 2)) : ℚ) : WithTop ℚ) := by
    exact_mod_cast (by linarith)
  have hstrict :
      (((c.order (0 : Fin (S + 2)) : ℚ) -
          (c.order (2 : Fin (S + 2)) : ℚ) +
            a.alphaValue (0 : Fin (N + 2)) : ℚ) : WithTop ℚ) <
        a.representationAlpha c i := by
    simpa only [i] using hthreshold.trans_le hlower
  have hcondition := conditions.defectCondition i
  rw [a.coe_representationAlphaValue c i] at hcondition
  have htruncated := hstrict.trans_le hcondition
  constructor
  · have hraw := a.truncatedPrefixDefect_le_defect c (1 : Kˣ)
      i.val i.val
    simpa only [i, lemma91ThirdRepresentationIndex_val] using
      htruncated.trans_le hraw
  · have hcap := a.truncatedPrefixDefect_le_rightCap c (1 : Kˣ)
      i.val i.val
    simpa only [i, lemma91ThirdRepresentationIndex_val] using
      htruncated.trans_le hcap

/-- In the branch `S₁ = S₃`, condition (ii) squeezes both `A₃` and
`d[a₁,₃b₁,₃]` to the common value `α₃`. -/
theorem thirdRepresentationAlpha_and_cappedDefect_eq_thirdAlpha_of_exceptionC
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (hsourceOuter : c.order (0 : Fin (S + 2)) =
      c.order (2 : Fin (S + 2)))
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    a.representationAlpha c
          (lemma91ThirdRepresentationIndex
            (by have := C.rank_four; omega) hthree) =
        (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) ∧
      a.truncatedPrefixDefect c (1 : Kˣ) 3 3 =
        (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) := by
  let i := lemma91ThirdRepresentationIndex
    (by have := C.rank_four; omega : 3 < N + 3) hthree
  have hlower :=
    a.thirdRepresentationAlpha_lower_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree C
  have hlower' :
      (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) ≤
        a.representationAlpha c i := by
    have hthreshold :
        (((c.order (0 : Fin (S + 2)) : ℚ) -
            (c.order (2 : Fin (S + 2)) : ℚ) +
              a.alphaValue (2 : Fin (N + 2)) : ℚ) : WithTop ℚ) =
          (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) := by
      rw [hsourceOuter]
      simp
    rw [hthreshold] at hlower
    simpa only [i] using hlower
  have hcondition := conditions.defectCondition i
  rw [a.coe_representationAlphaValue c i] at hcondition
  have hcap := a.truncatedPrefixDefect_le_leftCap c (1 : Kˣ)
    i.val i.val
  have hcap' : a.truncatedPrefixDefect c (1 : Kˣ) 3 3 ≤
      (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) := by
    change a.truncatedPrefixDefect c (1 : Kˣ) 3 3 ≤
      a.prefixAlphaCap 3 at hcap
    rw [a.prefixAlphaCap_of_internal (i := 3) (by omega) (by
      have := C.rank_four
      omega)] at hcap
    have htargetIndex :
        (⟨3 - 1, by have := C.rank_four; omega⟩ : Fin (N + 2)) =
          (2 : Fin (N + 2)) := by
      have hlt : 2 < N + 2 := by
        have := C.rank_four
        omega
      apply Fin.ext
      simp [Nat.mod_eq_of_lt hlt]
    rw [htargetIndex] at hcap
    exact hcap
  have hcondition' : a.representationAlpha c i ≤
      a.truncatedPrefixDefect c (1 : Kˣ) 3 3 := by
    simpa only [i, lemma91ThirdRepresentationIndex_val] using hcondition
  constructor
  · exact le_antisymm (hcondition'.trans hcap') hlower'
  · exact le_antisymm hcap' (hlower'.trans hcondition')

set_option maxHeartbeats 800000 in
-- The two determinant defects share the target ternary prefix; multiplying
-- them cancels it and leaves the second source adjacent product up to a square.
/-- When `S₁ = S₃`, the second source adjacent defect is at least
`α₃`, as in the second subcase of Lemma 9.1. -/
theorem thirdAlpha_le_sourceSecondAdjacentDefect_of_exceptionC
    [QuadraticDefectLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (hsourceOuter : c.order (0 : Fin (S + 2)) =
      c.order (2 : Fin (S + 2)))
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) ≤
      c.adjacentDefect (⟨1, hthree⟩ : Fin (S + 1)) := by
  let x : Kˣ := (-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1
  let y : Kˣ := (1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 3
  let second : Fin (S + 1) := ⟨1, hthree⟩
  have heq :=
    a.thirdRepresentationAlpha_and_cappedDefect_eq_thirdAlpha_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree hsourceOuter C
  have hyRaw := a.truncatedPrefixDefect_le_defect c (1 : Kˣ) 3 3
  have hy : (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) ≤
      defectOrder (K := K) y := by
    rw [heq.2] at hyRaw
    simpa only [y] using hyRaw
  have hxRaw := a.truncatedPrefixDefect_le_defect
    c.firstUnarySegment (-1 : Kˣ) 3 1
  have hx : (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) ≤
      defectOrder (K := K) x := by
    have hCapped := C.firstThirdDefect_eq_alpha
    have hindex :
        (⟨2, by have := C.rank_four; omega⟩ : Fin (N + 2)) =
          (2 : Fin (N + 2)) := by
      have hlt : 2 < N + 2 := by
        have := C.rank_four
        omega
      apply Fin.ext
      change 2 = 2 % (N + 2)
      rw [Nat.mod_eq_of_lt hlt]
    rw [hindex] at hCapped
    change a.lemma814FirstThirdCappedDefect c.firstUnarySegment ≤
      defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct 3 *
          c.firstUnarySegment.prefixProduct 1) at hxRaw
    rw [hCapped] at hxRaw
    rw [c.firstUnarySegment_prefixProduct_one] at hxRaw
    simpa only [x] using hxRaw
  have hproduct : (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) ≤
      defectOrder (K := K) (x * y) :=
    (le_min hx hy).trans (defectOrder_mul_ge_min x y)
  have hproductIdentity : x * y =
      c.adjacentProduct second *
        (a.prefixProduct 3 * c.prefixProduct 1) ^ 2 := by
    have hprefixTwo := c.toBONG.prefixProduct_succ 1 (by omega)
    have hprefixThree := c.toBONG.prefixProduct_succ 2 (by omega)
    change c.prefixProduct 2 = c.prefixProduct 1 *
      c.valueUnit (⟨1, by omega⟩ : Fin (S + 2)) at hprefixTwo
    change c.prefixProduct 3 = c.prefixProduct 2 *
      c.valueUnit (⟨2, by omega⟩ : Fin (S + 2)) at hprefixThree
    have hcast : second.castSucc =
        (⟨1, by omega⟩ : Fin (S + 2)) := by
      apply Fin.ext
      rfl
    have hsucc : second.succ =
        (⟨2, by omega⟩ : Fin (S + 2)) := by
      apply Fin.ext
      rfl
    dsimp only [x, y]
    unfold adjacentProduct
    rw [hcast, hsucc, hprefixThree, hprefixTwo]
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_one, one_mul,
      pow_two]
    ring
  rw [hproductIdentity, defectOrder_mul_square] at hproduct
  simpa only [second, adjacentDefect] using hproduct

set_option maxHeartbeats 800000 in
-- Capped-defect domination combines `d[a₁,₃b₁,₃] = α₃` with
-- the adjacent target defect `d[-a₄a₅]`.
/-- In the equal source-order branch and target rank at least five,
`d[-a₁,₅b₁,₃] > R₄ - R₅ + α₂`. -/
theorem fourthFifthShift_secondAlpha_lt_firstFive_sourceFirstThreeCappedDefect
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (hsourceOuter : c.order (0 : Fin (S + 2)) =
      c.order (2 : Fin (S + 2)))
    (hfive : 4 < N + 3)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    ((((a.order (3 : Fin (N + 3)) : ℚ) -
        (a.order ⟨4, hfive⟩ : ℚ) +
          a.alphaValue (1 : Fin (N + 2)) : ℚ) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 5 3) := by
  let thirdAlpha : Fin (N + 2) := ⟨2, by omega⟩
  let fourthAlpha : Fin (N + 2) := ⟨3, by omega⟩
  have hthirdIndex : thirdAlpha = (2 : Fin (N + 2)) := by
    have hlt : 2 < N + 2 := by omega
    apply Fin.ext
    simp [thirdAlpha, Nat.mod_eq_of_lt hlt]
  have hfourthIndex : fourthAlpha = (3 : Fin (N + 2)) := by
    have hlt : 3 < N + 2 := by omega
    apply Fin.ext
    simp [fourthAlpha, Nat.mod_eq_of_lt hlt]
  have hfourthVal : fourthAlpha.val = 3 := by
    rfl
  have hfourthCast : fourthAlpha.castSucc =
      (3 : Fin (N + 3)) := by
    have hlt : 3 < N + 3 := by omega
    apply Fin.ext
    change 3 = 3 % (N + 3)
    rw [Nat.mod_eq_of_lt hlt]
  have hfourthSucc : fourthAlpha.succ = ⟨4, hfive⟩ := by
    apply Fin.ext
    rfl
  have hthirdSucc : thirdAlpha.succ =
      (3 : Fin (N + 3)) := by
    have hlt : 3 < N + 3 := by omega
    apply Fin.ext
    change 3 = 3 % (N + 3)
    rw [Nat.mod_eq_of_lt hlt]
  have hp1 := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact (a.alpha_p1 thirdAlpha (by
      dsimp only [thirdAlpha]
      omega)).2
  have hnext :
      (⟨thirdAlpha.1 + 1, by
        dsimp only [thirdAlpha]
        omega⟩ : Fin (N + 2)) = fourthAlpha := by
    apply Fin.ext
    rfl
  rw [hnext] at hp1
  have hthirdGe :
      (((a.order (3 : Fin (N + 3)) : ℚ) -
          (a.order ⟨4, hfive⟩ : ℚ) +
            a.alphaValue (3 : Fin (N + 2)) : ℚ) : WithTop ℚ) ≤
        (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) := by
    unfold alphaRightEndpoint at hp1
    rw [hfourthSucc, hthirdSucc] at hp1
    rw [hfourthIndex, hthirdIndex] at hp1
    apply WithTop.coe_le_coe.mpr
    push_cast
    linarith
  have heq :=
    a.thirdRepresentationAlpha_and_cappedDefect_eq_thirdAlpha_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree hsourceOuter C
  have hequalPrefix :
      (((a.order (3 : Fin (N + 3)) : ℚ) -
          (a.order ⟨4, hfive⟩ : ℚ) +
            a.alphaValue (3 : Fin (N + 2)) : ℚ) : WithTop ℚ) ≤
        a.truncatedPrefixDefect c (1 : Kˣ) 3 3 := by
    rw [heq.2]
    exact hthirdGe
  have hlocal := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.order_sub_add_alpha_le_cappedAdjacent fourthAlpha
  have hlocal' :
      (((a.order (3 : Fin (N + 3)) : ℚ) -
          (a.order ⟨4, hfive⟩ : ℚ) +
            a.alphaValue (3 : Fin (N + 2)) : ℚ) : WithTop ℚ) ≤
        a.truncatedPrefixDefect a (-1) 5 3 := by
    rw [a.truncatedPrefixDefect_comm a (-1) 5 3]
    rw [hfourthCast, hfourthSucc] at hlocal
    rw [hfourthVal, hfourthIndex] at hlocal
    norm_num at hlocal
    push_cast at hlocal ⊢
    rw [← a.coe_alphaValue (3 : Fin (N + 2))] at hlocal
    exact hlocal
  have hdomination :=
    a.truncatedPrefixDefect_domination a c (-1) 1 5 3 3
  have hfourthLower :
      (((a.order (3 : Fin (N + 3)) : ℚ) -
          (a.order ⟨4, hfive⟩ : ℚ) +
            a.alphaValue (3 : Fin (N + 2)) : ℚ) : WithTop ℚ) ≤
        a.truncatedPrefixDefect c (-1) 5 3 :=
    (le_min hlocal' hequalPrefix).trans (by
      simpa only [mul_one] using hdomination)
  have hlater := C.laterAlpha_strict (by omega : 5 ≤ N + 3)
  have hsecondComplement := C.secondAlpha_eq_complement
  have hlater' : a.alphaValue (1 : Fin (N + 2)) <
      a.alphaValue (3 : Fin (N + 2)) := by
    rw [hsecondComplement]
    convert hlater using 1
    congr 1
    apply Fin.ext
    have hlt : 3 < N + 2 := by omega
    change 3 % (N + 2) = 3
    rw [Nat.mod_eq_of_lt hlt]
  have hstrict :
      (((a.order (3 : Fin (N + 3)) : ℚ) -
          (a.order ⟨4, hfive⟩ : ℚ) +
            a.alphaValue (1 : Fin (N + 2)) : ℚ) : WithTop ℚ) <
        (((a.order (3 : Fin (N + 3)) : ℚ) -
          (a.order ⟨4, hfive⟩ : ℚ) +
            a.alphaValue (3 : Fin (N + 2)) : ℚ) : WithTop ℚ) := by
    exact_mod_cast (by linarith)
  exact hstrict.trans_le hfourthLower

/-- Exception (c) forces `R₃ < R₅` whenever the fifth target value
exists.  Equality would contradict P6 using `α₂ + α₃ = 2e` and
`α₄ > α₂`. -/
theorem thirdFifthOrders_lt_of_exceptionC
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfive : 4 < N + 3)
    (C : a.Beli2019Lemma814ExceptionC b) :
    a.order (2 : Fin (N + 3)) < a.order ⟨4, hfive⟩ := by
  let thirdOrder : Fin (N + 3) := ⟨2, by omega⟩
  have htwoStep := a.good thirdOrder (by
    dsimp only [thirdOrder]
    omega)
  have htargetIndex : thirdOrder = (2 : Fin (N + 3)) := by
    have hlt : 2 < N + 3 := by omega
    apply Fin.ext
    simp [thirdOrder, Nat.mod_eq_of_lt hlt]
  have hfifthIndex :
      (⟨thirdOrder.1 + 2, by
        dsimp only [thirdOrder]
        omega⟩ : Fin (N + 3)) = ⟨4, hfive⟩ := by
    apply Fin.ext
    rfl
  have htwoStep' : a.order (2 : Fin (N + 3)) ≤
      a.order ⟨4, hfive⟩ := by
    convert htwoStep using 1
    · exact congrArg a.order htargetIndex.symm
    · exact congrArg a.order hfifthIndex.symm
  refine lt_of_le_of_ne htwoStep' ?_
  intro heq
  let thirdAlpha : Fin (N + 2) := ⟨2, by omega⟩
  let fourthAlpha : Fin (N + 2) := ⟨3, by omega⟩
  have hp6 := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.alpha_p6 thirdAlpha (by
      dsimp only [thirdAlpha]
      omega)
  have hthirdCast : thirdAlpha.castSucc =
      (2 : Fin (N + 3)) := by
    have hlt : 2 < N + 3 := by omega
    apply Fin.ext
    change 2 = 2 % (N + 3)
    rw [Nat.mod_eq_of_lt hlt]
  have hfourthSucc : fourthAlpha.succ = ⟨4, hfive⟩ := by
    apply Fin.ext
    rfl
  have heq' : a.order thirdAlpha.castSucc =
      a.order fourthAlpha.succ := by
    rw [hthirdCast, hfourthSucc]
    exact heq
  have hbound := hp6 heq'
  have hsum :=
    a.secondAlpha_add_thirdAlpha_eq_twoE_of_lemma814ExceptionC
      b C (by have := C.rank_four; omega)
  have hsumThirdIndex :
      (⟨2, by have := C.rank_four; omega⟩ : Fin (N + 2)) =
        (2 : Fin (N + 2)) := by
    have hlt : 2 < N + 2 := by omega
    apply Fin.ext
    change 2 = 2 % (N + 2)
    rw [Nat.mod_eq_of_lt hlt]
  rw [hsumThirdIndex] at hsum
  have hlater := C.laterAlpha_strict (by omega : 5 ≤ N + 3)
  have hsecondComplement := C.secondAlpha_eq_complement
  have hlater' : a.alphaValue (1 : Fin (N + 2)) <
      a.alphaValue (3 : Fin (N + 2)) := by
    rw [hsecondComplement]
    convert hlater using 1
    congr 1
    apply Fin.ext
    have hlt : 3 < N + 2 := by omega
    change 3 % (N + 2) = 3
    rw [Nat.mod_eq_of_lt hlt]
  have hnextAlpha :
      (⟨thirdAlpha.1 + 1, by
        dsimp only [thirdAlpha]
        omega⟩ : Fin (N + 2)) = fourthAlpha := by
    apply Fin.ext
    rfl
  have hboundNamed : a.alphaValue thirdAlpha +
      a.alphaValue fourthAlpha ≤
        2 * (ramificationIndex K : ℚ) := by
    calc
      a.alphaValue thirdAlpha + a.alphaValue fourthAlpha =
          a.alphaValue thirdAlpha +
            a.alphaValue ⟨thirdAlpha.1 + 1, by
              dsimp only [thirdAlpha]
              omega⟩ :=
        congrArg (fun z => a.alphaValue thirdAlpha + a.alphaValue z)
          hnextAlpha.symm
      _ ≤ 2 * (ramificationIndex K : ℚ) := hbound
  have hbound' : a.alphaValue (2 : Fin (N + 2)) +
      a.alphaValue (3 : Fin (N + 2)) ≤
        2 * (ramificationIndex K : ℚ) := by
    have hthirdIndex : thirdAlpha = (2 : Fin (N + 2)) := by
      apply Fin.ext
      exact_mod_cast (Nat.mod_eq_of_lt (by omega : 2 < N + 2)).symm
    have hfourthIndex : fourthAlpha = (3 : Fin (N + 2)) := by
      apply Fin.ext
      exact_mod_cast (Nat.mod_eq_of_lt (by omega : 3 < N + 2)).symm
    calc
      a.alphaValue (2 : Fin (N + 2)) +
          a.alphaValue (3 : Fin (N + 2)) =
        a.alphaValue thirdAlpha + a.alphaValue fourthAlpha :=
          congrArg₂ (fun x y => x + y)
            (congrArg a.alphaValue hthirdIndex.symm)
            (congrArg a.alphaValue hfourthIndex.symm)
      _ ≤ 2 * (ramificationIndex K : ℚ) := hboundNamed
  linarith

/-- The condition-(iii′) index `i = 4` used in the equal source-order
subcase of Lemma 9.1. -/
def lemma91QuaternaryCentralIndex
    (hfive : 4 < N + 3) (hthree : 1 < S + 1) :
    CentralRepresentationIndex (N + 3) (S + 2) where
  val := 4
  one_lt := by omega
  lt_large := hfive
  le_small_succ := by omega

@[simp]
theorem lemma91QuaternaryCentralIndex_val
    (hfive : 4 < N + 3) (hthree : 1 < S + 1) :
    (lemma91QuaternaryCentralIndex hfive hthree).val = 4 :=
  rfl

/-- The ordinary representation index `4` used when the source has a fourth
value. -/
def lemma91FourthRepresentationIndex
    (hfive : 4 < N + 3) (hsourceFour : 4 ≤ S + 2) :
    RepresentationIndex (N + 3) (S + 2) where
  val := 4
  pos := by omega
  lt_large := hfive
  le_small := hsourceFour

@[simp]
theorem lemma91FourthRepresentationIndex_val
    (hfive : 4 < N + 3) (hsourceFour : 4 ≤ S + 2) :
    (lemma91FourthRepresentationIndex hfive hsourceFour).val = 4 :=
  rfl

set_option maxHeartbeats 1000000 in
-- In the interior case Lemma 2.7(i) replaces the secondary candidate by the
-- preceding mixed defect; at target rank five only the primary candidate
-- remains.
/-- Under `S₁ = S₃`, the prime fourth representation alpha satisfies
`A₄' > R₄ - S₄ + α₂`. -/
theorem fourthRepresentationAlphaPrime_lower_of_exceptionC
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hsourceOuter : c.order (0 : Fin (S + 2)) =
      c.order (2 : Fin (S + 2)))
    (hfive : 4 < N + 3) (hsourceFour : 4 ≤ S + 2)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    ((((a.order (⟨3, by omega⟩ : Fin (N + 3)) : ℚ) -
        (c.order (⟨3, by omega⟩ : Fin (S + 2)) : ℚ) +
          a.alphaValue (1 : Fin (N + 2)) : ℚ) : WithTop ℚ) <
      a.representationAlphaPrime c
        (lemma91FourthRepresentationIndex hfive hsourceFour)) := by
  let i := lemma91FourthRepresentationIndex hfive hsourceFour
  let targetFourth : Fin (N + 3) := ⟨3, by omega⟩
  let targetFifth : Fin (N + 3) := ⟨4, hfive⟩
  let sourceThird : Fin (S + 2) := ⟨2, by omega⟩
  let sourceFourth : Fin (S + 2) := ⟨3, by omega⟩
  let threshold : ℚ :=
    (a.order targetFourth : ℚ) - (c.order sourceFourth : ℚ) +
      a.alphaValue (1 : Fin (N + 2))
  have hrigidity := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.secondOrderRigidity_of_exceptionBC
      c hRank hfirst hsecond conditions (Or.inr C)
  have hmixed :=
    a.targetSecondAlpha_le_firstFour_sourceFirstTwoCappedDefect_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hfirst hsecond hrigidity.2 C
  have htail :=
    a.fourthFifthShift_secondAlpha_lt_firstFive_sourceFirstThreeCappedDefect
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions (by omega) hsourceOuter hfive C
  have hsourceTarget : c.order sourceThird < a.order targetFifth := by
    have hsourceThirdIndex : sourceThird =
        (2 : Fin (S + 2)) := by
      have hlt : 2 < S + 2 := by omega
      apply Fin.ext
      simp [sourceThird, Nat.mod_eq_of_lt hlt]
    calc
      c.order sourceThird = c.order (2 : Fin (S + 2)) :=
        congrArg c.order hsourceThirdIndex
      _ = c.order (0 : Fin (S + 2)) := hsourceOuter.symm
      _ = a.order (0 : Fin (N + 3)) := hfirst.symm
      _ = a.order (2 : Fin (N + 3)) := C.firstThirdOrders_eq
      _ < a.order targetFifth := by
        simpa only [targetFifth] using
          a.thirdFifthOrders_lt_of_exceptionC
            (targetLaws := targetLaws) c.firstUnarySegment hfive C
  let primaryShift : ℚ :=
    ((a.order targetFifth - c.order sourceFourth : Int) : ℚ)
  let tailCut : ℚ :=
    (a.order targetFourth : ℚ) - (a.order targetFifth : ℚ) +
      a.alphaValue (1 : Fin (N + 2))
  have htail' : (tailCut : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 5 3 := by
    have htargetFourthIndex : targetFourth =
        (3 : Fin (N + 3)) := by
      have hlt : 3 < N + 3 := by omega
      apply Fin.ext
      simp [targetFourth, Nat.mod_eq_of_lt hlt]
    dsimp only [tailCut]
    rw [htargetFourthIndex]
    simpa only [targetFifth] using htail
  have hthresholdPrimary : threshold = primaryShift + tailCut := by
    dsimp only [threshold, primaryShift, tailCut]
    push_cast
    ring
  have hprimary : (threshold : WithTop ℚ) <
      a.representationPrimaryDefect c i := by
    unfold representationPrimaryDefect
    change (threshold : WithTop ℚ) <
      (primaryShift : WithTop ℚ) +
        a.truncatedPrefixDefect c (-1) 5 3
    rw [hthresholdPrimary]
    exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mpr htail'
  by_cases hsix : 5 < N + 3
  · let targetSixth : Fin (N + 3) := ⟨5, hsix⟩
    let secondaryShift : ℚ :=
      ((a.order targetFifth + a.order targetSixth -
        c.order sourceThird - c.order sourceFourth : Int) : ℚ)
    have htargetTwoStep : a.order targetFourth ≤
        a.order targetSixth := by
      have hgood := a.good targetFourth (by
        dsimp only [targetFourth]
        omega)
      have hindex :
          (⟨targetFourth.1 + 2, by
            dsimp only [targetFourth]
            omega⟩ : Fin (N + 3)) = targetSixth := by
        apply Fin.ext
        rfl
      exact hgood.trans_eq (congrArg a.order hindex)
    have hsecondaryQ : threshold < secondaryShift +
        a.alphaValue (1 : Fin (N + 2)) := by
      dsimp only [threshold, secondaryShift]
      push_cast
      have hsourceTargetQ : (c.order sourceThird : ℚ) <
          (a.order targetFifth : ℚ) := by
        exact_mod_cast hsourceTarget
      have htargetTwoStepQ : (a.order targetFourth : ℚ) ≤
          (a.order targetSixth : ℚ) := by
        exact_mod_cast htargetTwoStep
      linarith
    have hinterior : 1 < i.val ∧ i.val + 1 < N + 3 := by
      dsimp only [i, lemma91FourthRepresentationIndex]
      omega
    have hsecondary : (threshold : WithTop ℚ) <
        a.representationSecondaryPreviousDefect c i hinterior := by
      unfold representationSecondaryPreviousDefect
      change (threshold : WithTop ℚ) <
        (secondaryShift : WithTop ℚ) +
          a.truncatedPrefixDefect c (-1) 4 2
      calc
        (threshold : WithTop ℚ) <
            (secondaryShift : WithTop ℚ) +
              (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
          exact_mod_cast hsecondaryQ
        _ ≤ (secondaryShift : WithTop ℚ) +
              a.truncatedPrefixDefect c (-1) 4 2 :=
          add_le_add_right hmixed (secondaryShift : WithTop ℚ)
    have hcross : c.order ⟨i.val - 2, by
        have := i.le_small
        omega⟩ ≤ a.order ⟨i.val, i.lt_large⟩ := by
      simpa only [i, lemma91FourthRepresentationIndex,
        sourceThird, targetFifth] using hsourceTarget.le
    have hnormal := by
      letI : Beli2006AlphaLaws.{u, v} K := targetLaws
      exact a.representationAlphaPrime_eq_min_primary_previous c i
        hinterior hcross
    rw [hnormal]
    exact lt_min hprimary hsecondary
  · have hendpoint := a.representationAlphaPrime_eq_primary_of_not_interior
        c i (by
          dsimp only [i, lemma91FourthRepresentationIndex]
          omega)
    rw [hendpoint]
    exact hprimary

set_option maxHeartbeats 1000000 in
-- Lemma 2.14 disposes of the mismatch `A₄ ≠ A₄'`; in the equality
-- branch the preceding candidate bounds give the original condition-(iii)
-- trigger directly.
/-- The condition-(iii) trigger at `i = 4` in the ordinary-source branch
`S₁ = S₃`. -/
theorem quaternaryCentralAlphaTrigger_of_exceptionC_of_sourceFirstThird_eq
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hsourceOuter : c.order (0 : Fin (S + 2)) =
      c.order (2 : Fin (S + 2)))
    (hfive : 4 < N + 3) (hsourceFour : 4 ≤ S + 2)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    a.centralAlphaTrigger c
      (lemma91QuaternaryCentralIndex hfive (by omega)) := by
  let central := lemma91QuaternaryCentralIndex hfive (by omega : 1 < S + 1)
  let current := central.current hsourceFour
  change a.centralAlphaTrigger c central
  have hsourceTarget :
      c.order (2 : Fin (S + 2)) < a.order ⟨4, hfive⟩ := by
    calc
      c.order (2 : Fin (S + 2)) = c.order (0 : Fin (S + 2)) :=
        hsourceOuter.symm
      _ = a.order (0 : Fin (N + 3)) := hfirst.symm
      _ = a.order (2 : Fin (N + 3)) := C.firstThirdOrders_eq
      _ < a.order ⟨4, hfive⟩ :=
        a.thirdFifthOrders_lt_of_exceptionC
          (targetLaws := targetLaws) c.firstUnarySegment hfive C
  by_cases heq : a.representationAlpha c current =
      a.representationAlphaPrime c current
  · have hthree : 1 < S + 1 := by omega
    have hthird :=
      a.thirdRepresentationAlpha_and_cappedDefect_eq_thirdAlpha_of_exceptionC
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          c hRank hfirst hsecond conditions hthree hsourceOuter C
    have hfourthPrime :=
      a.fourthRepresentationAlphaPrime_lower_of_exceptionC
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          c hRank hfirst hsecond conditions hsourceOuter hfive
            hsourceFour C
    have hcurrentIndex : current =
        lemma91FourthRepresentationIndex hfive hsourceFour := by
      rfl
    rw [← hcurrentIndex, ← heq] at hfourthPrime
    have hpreviousIndex : central.previous =
        lemma91ThirdRepresentationIndex (by omega) hthree := by
      rfl
    have hsum :=
      a.secondAlpha_add_thirdAlpha_eq_twoE_of_lemma814ExceptionC
        c.firstUnarySegment C (by have := C.rank_four; omega)
    have hthirdIndex :
        (⟨2, by have := C.rank_four; omega⟩ : Fin (N + 2)) =
          (2 : Fin (N + 2)) := by
      have hlt : 2 < N + 2 := by omega
      apply Fin.ext
      change 2 = 2 % (N + 2)
      rw [Nat.mod_eq_of_lt hlt]
    rw [hthirdIndex] at hsum
    let targetFourth : Fin (N + 3) := ⟨3, by omega⟩
    let sourceFourth : Fin (S + 2) := ⟨3, by omega⟩
    let cut : ℚ :=
      (a.order targetFourth : ℚ) - (c.order sourceFourth : ℚ) +
        a.alphaValue (1 : Fin (N + 2))
    have hfourth : (cut : WithTop ℚ) <
        a.representationAlpha c current := by
      simpa only [cut, targetFourth, sourceFourth] using hfourthPrime
    have hsourceShift :
        ((c.order sourceFourth : ℚ) : WithTop ℚ) +
            (cut : WithTop ℚ) <
          ((c.order sourceFourth : ℚ) : WithTop ℚ) +
            a.representationAlpha c current :=
      (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mpr hfourth
    have htotal :
        (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) +
            (((c.order sourceFourth : ℚ) : WithTop ℚ) +
              (cut : WithTop ℚ)) <
          (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) +
            (((c.order sourceFourth : ℚ) : WithTop ℚ) +
              a.representationAlpha c current) :=
      (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mpr hsourceShift
    have hleft :
        (((2 * (ramificationIndex K : ℚ) +
          (a.order targetFourth : ℚ) : ℚ)) : WithTop ℚ) =
          (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) +
            (((c.order sourceFourth : ℚ) : WithTop ℚ) +
              (cut : WithTop ℚ)) := by
      apply WithTop.coe_eq_coe.mpr
      dsimp only [cut]
      push_cast at hsum ⊢
      linarith
    unfold centralAlphaTrigger
    refine ⟨?_, ?_⟩
    · have hsourceIndex :
          (⟨central.val - 2, by
            have := central.one_lt
            have := central.le_small_succ
            omega⟩ : Fin (S + 2)) = (2 : Fin (S + 2)) := by
        have hlt : 2 < S + 2 := by omega
        apply Fin.ext
        simp [central, lemma91QuaternaryCentralIndex,
          Nat.mod_eq_of_lt hlt]
      have htargetIndex :
          (⟨central.val, by have := central.lt_large; omega⟩ :
            Fin (N + 3)) = ⟨4, hfive⟩ := by
        apply Fin.ext
        rfl
      rw [hsourceIndex, htargetIndex]
      exact hsourceTarget
    · unfold centralAdjustedAlpha
      have hi : central.val ≤ S + 1 + 1 := by
        dsimp only [central, lemma91QuaternaryCentralIndex]
        omega
      rw [dif_pos hi]
      rw [a.coe_representationAlphaValue c central.previous,
        a.coe_representationAlphaValue c (central.current hi)]
      have hcurrentHi : central.current hi = current := by
        rfl
      rw [hcurrentHi]
      rw [hpreviousIndex, hthird.1]
      rw [← hleft] at htotal
      simpa only [central, current, lemma91QuaternaryCentralIndex,
        targetFourth, sourceFourth] using htotal
  · letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
    exact a.centralAlphaTrigger_of_current_alpha_ne_prime
      c hRank conditions.orderCondition conditions.defectCondition
        central hsourceFour heq

/-- In the ordinary-source case, the condition-(iii) trigger at `i = 4`
supplies representation of the source ternary prefix by the target
quaternary prefix. -/
theorem ternaryPrefixRepresentation_of_exceptionC_of_sourceFirstThird_eq_ordinary
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hsourceOuter : c.order (0 : Fin (S + 2)) =
      c.order (2 : Fin (S + 2)))
    (hfive : 4 < N + 3) (hsourceFour : 4 ≤ S + 2)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    DiagonalRepresents
      (c.prefixValues 3 (by omega))
      (a.prefixValues 4 (by omega)) := by
  let central := lemma91QuaternaryCentralIndex hfive (by omega : 1 < S + 1)
  have htrigger : a.centralAlphaTrigger c central := by
    simpa only [central] using
      a.quaternaryCentralAlphaTrigger_of_exceptionC_of_sourceFirstThird_eq
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          c hRank hfirst hsecond conditions hsourceOuter hfive hsourceFour C
  have hrepresentation := conditions.centralRepresentations central htrigger
  simpa only [central, lemma91QuaternaryCentralIndex] using hrepresentation

set_option maxHeartbeats 1000000 in
/-- For a ternary source, Definition 4's terminal value at `i = 4` is
strictly larger than `R₄ + α₂` in the equal-outer-order branch. -/
theorem terminalAdjustedAlpha_lower_of_exceptionC_of_sourceRankThree
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M 3)
    (hRank : 2 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) = c.order (0 : Fin 3))
    (hsecond : a.order (1 : Fin (N + 3)) = c.order (1 : Fin 3))
    (conditions : RepresentationConditions a c hRank)
    (hsourceOuter : c.order (0 : Fin 3) = c.order (2 : Fin 3))
    (hfive : 4 < N + 3)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    ((((a.order (3 : Fin (N + 3)) : ℚ) +
        a.alphaValue (1 : Fin (N + 2)) : ℚ)) : WithTop ℚ) <
      a.terminalAdjustedAlpha c hfive := by
  let targetFourth : Fin (N + 3) := ⟨3, by omega⟩
  let targetFifth : Fin (N + 3) := ⟨4, hfive⟩
  let sourceThird : Fin 3 := ⟨2, by omega⟩
  let threshold : ℚ :=
    (a.order targetFourth : ℚ) + a.alphaValue (1 : Fin (N + 2))
  let primaryCut : ℚ :=
    (a.order targetFourth : ℚ) - (a.order targetFifth : ℚ) +
      a.alphaValue (1 : Fin (N + 2))
  have htargetFourthIndex : targetFourth = (3 : Fin (N + 3)) := by
    have hlt : 3 < N + 3 := by omega
    apply Fin.ext
    change 3 = 3 % (N + 3)
    rw [Nat.mod_eq_of_lt hlt]
  rw [← htargetFourthIndex]
  change (threshold : WithTop ℚ) < a.terminalAdjustedAlpha c hfive
  have htail :=
    a.fourthFifthShift_secondAlpha_lt_firstFive_sourceFirstThreeCappedDefect
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions (by omega) hsourceOuter hfive C
  have htail' : (primaryCut : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 5 3 := by
    rw [← htargetFourthIndex] at htail
    simpa only [primaryCut, targetFifth] using htail
  have hthresholdPrimary : threshold =
      (a.order targetFifth : ℚ) + primaryCut := by
    dsimp only [threshold, primaryCut]
    ring
  have hprimary : (threshold : WithTop ℚ) <
      a.terminalAdjustedPrimary c hfive := by
    unfold terminalAdjustedPrimary
    change (threshold : WithTop ℚ) <
      ((a.order targetFifth : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect c (-1) 5 3
    rw [hthresholdPrimary]
    exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mpr htail'
  have hsourceTarget : c.order sourceThird < a.order targetFifth := by
    calc
      c.order sourceThird = c.order (2 : Fin 3) := by
        congr 1
      _ = c.order (0 : Fin 3) := hsourceOuter.symm
      _ = a.order (0 : Fin (N + 3)) := hfirst.symm
      _ = a.order (2 : Fin (N + 3)) := C.firstThirdOrders_eq
      _ < a.order targetFifth := by
        simpa only [targetFifth] using
          a.thirdFifthOrders_lt_of_exceptionC
            (targetLaws := targetLaws) c.firstUnarySegment hfive C
  by_cases hsix : 5 < N + 3
  · let targetSixth : Fin (N + 3) := ⟨5, hsix⟩
    let secondaryShift : ℚ :=
      ((a.order targetFifth + a.order targetSixth -
        c.order sourceThird : Int) : ℚ)
    have htargetTwoStep : a.order targetFourth ≤ a.order targetSixth := by
      have hgood := a.good targetFourth (by
        dsimp only [targetFourth]
        omega)
      have hindex :
          (⟨targetFourth.val + 2, by
            dsimp only [targetFourth]
            omega⟩ : Fin (N + 3)) = targetSixth := by
        apply Fin.ext
        rfl
      exact hgood.trans_eq (congrArg a.order hindex)
    have hshift : (a.order targetFourth : ℚ) < secondaryShift := by
      dsimp only [secondaryShift]
      have hsourceTargetQ : (c.order sourceThird : ℚ) <
          (a.order targetFifth : ℚ) := by
        exact_mod_cast hsourceTarget
      have htargetTwoStepQ : (a.order targetFourth : ℚ) ≤
          (a.order targetSixth : ℚ) := by
        exact_mod_cast htargetTwoStep
      push_cast
      linarith
    have hrigidity := by
      letI : Beli2006AlphaLaws.{u, v} K := targetLaws
      exact a.secondOrderRigidity_of_exceptionBC
        c hRank hfirst hsecond conditions (Or.inr C)
    have hmixed :=
      a.targetSecondAlpha_le_firstFour_sourceFirstTwoCappedDefect_of_exceptionC
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          c hfirst hsecond hrigidity.2 C
    have hsecondary : (threshold : WithTop ℚ) <
        a.terminalAdjustedSecondaryPrevious c hsix := by
      unfold terminalAdjustedSecondaryPrevious
      change (threshold : WithTop ℚ) <
        (secondaryShift : WithTop ℚ) +
          a.truncatedPrefixDefect c (-1) 4 2
      change ((a.order targetFourth : ℚ) : WithTop ℚ) +
          (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
        (secondaryShift : WithTop ℚ) +
          a.truncatedPrefixDefect c (-1) 4 2
      have hshiftTop : ((a.order targetFourth : ℚ) : WithTop ℚ) <
          (secondaryShift : WithTop ℚ) :=
        WithTop.coe_lt_coe.mpr hshift
      exact WithTop.add_lt_add_of_lt_of_le WithTop.coe_ne_top
        hshiftTop hmixed
    have hnormal := by
      letI : Beli2006AlphaLaws.{u, v} K := targetLaws
      exact a.terminalAdjustedAlpha_eq_min_primary_previous
        c hfive hsix hsourceTarget.le
    rw [hnormal]
    exact lt_min hprimary hsecondary
  · rw [a.terminalAdjustedAlpha_eq_primary_of_not_inner c hfive hsix]
    exact hprimary

/-- At the terminal central index for a ternary source, the preceding
representation alpha and Definition 4's terminal value satisfy the original
condition-(iii) trigger. -/
theorem quaternaryCentralAlphaTrigger_of_exceptionC_of_sourceRankThree
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M 3)
    (hRank : 2 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) = c.order (0 : Fin 3))
    (hsecond : a.order (1 : Fin (N + 3)) = c.order (1 : Fin 3))
    (conditions : RepresentationConditions a c hRank)
    (hsourceOuter : c.order (0 : Fin 3) = c.order (2 : Fin 3))
    (hfive : 4 < N + 3)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    a.centralAlphaTrigger c
      (lemma91QuaternaryCentralIndex (S := 1) hfive (by omega)) := by
  let central := lemma91QuaternaryCentralIndex (S := 1) hfive
    (by omega : 1 < 1 + 1)
  change a.centralAlphaTrigger c central
  have hthird :=
    a.thirdRepresentationAlpha_and_cappedDefect_eq_thirdAlpha_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions (by omega) hsourceOuter C
  have hterminal :=
    a.terminalAdjustedAlpha_lower_of_exceptionC_of_sourceRankThree
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hsourceOuter hfive C
  have hsum :=
    a.secondAlpha_add_thirdAlpha_eq_twoE_of_lemma814ExceptionC
      c.firstUnarySegment C (by have := C.rank_four; omega)
  have hthirdIndex :
      (⟨2, by have := C.rank_four; omega⟩ : Fin (N + 2)) =
        (2 : Fin (N + 2)) := by
    have hlt : 2 < N + 2 := by omega
    apply Fin.ext
    change 2 = 2 % (N + 2)
    rw [Nat.mod_eq_of_lt hlt]
  rw [hthirdIndex] at hsum
  unfold centralAlphaTrigger
  constructor
  · have hsourceIndex :
        (⟨central.val - 2, by
          have := central.one_lt
          have := central.le_small_succ
          omega⟩ : Fin 3) = (2 : Fin 3) := by
      apply Fin.ext
      rfl
    have htargetIndex :
        (⟨central.val, by have := central.lt_large; omega⟩ :
          Fin (N + 3)) = ⟨4, hfive⟩ := by
      apply Fin.ext
      rfl
    rw [hsourceIndex, htargetIndex]
    calc
      c.order (2 : Fin 3) = c.order (0 : Fin 3) := hsourceOuter.symm
      _ = a.order (0 : Fin (N + 3)) := hfirst.symm
      _ = a.order (2 : Fin (N + 3)) := C.firstThirdOrders_eq
      _ < a.order ⟨4, hfive⟩ :=
        a.thirdFifthOrders_lt_of_exceptionC
          (targetLaws := targetLaws) c.firstUnarySegment hfive C
  · unfold centralAdjustedAlpha
    have hnotOrdinary : ¬central.val ≤ 3 := by
      dsimp only [central, lemma91QuaternaryCentralIndex]
      omega
    rw [dif_neg hnotOrdinary]
    rw [a.coe_representationAlphaValue c central.previous]
    have hpreviousIndex : central.previous =
        lemma91ThirdRepresentationIndex (by omega) (by omega) := by
      rfl
    rw [hpreviousIndex, hthird.1]
    have htargetFourth :
        (⟨central.val - 1, by
          have := central.one_lt
          have := central.lt_large
          omega⟩ : Fin (N + 3)) = (3 : Fin (N + 3)) := by
      apply Fin.ext
      simp [central, lemma91QuaternaryCentralIndex,
        Nat.mod_eq_of_lt (by omega : 3 < N + 3)]
    rw [htargetFourth]
    have hleft :
        (((2 * (ramificationIndex K : ℚ) +
          (a.order (3 : Fin (N + 3)) : ℚ) : ℚ)) : WithTop ℚ) =
          (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) +
            (((a.order (3 : Fin (N + 3)) : ℚ) +
              a.alphaValue (1 : Fin (N + 2)) : ℚ) : WithTop ℚ) := by
      apply WithTop.coe_eq_coe.mpr
      push_cast at hsum ⊢
      linarith
    rw [hleft]
    exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mpr hterminal

/-- Condition (iii) therefore represents the full ternary source prefix at
the terminal boundary. -/
theorem ternaryPrefixRepresentation_of_exceptionC_of_sourceRankThree
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M 3)
    (hRank : 2 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) = c.order (0 : Fin 3))
    (hsecond : a.order (1 : Fin (N + 3)) = c.order (1 : Fin 3))
    (conditions : RepresentationConditions a c hRank)
    (hsourceOuter : c.order (0 : Fin 3) = c.order (2 : Fin 3))
    (hfive : 4 < N + 3)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    DiagonalRepresents
      (c.prefixValues 3 (Nat.le_refl _))
      (a.prefixValues 4 (by omega)) := by
  let central := lemma91QuaternaryCentralIndex (S := 1) hfive
    (by omega : 1 < 1 + 1)
  have htrigger : a.centralAlphaTrigger c central := by
    simpa only [central] using
      a.quaternaryCentralAlphaTrigger_of_exceptionC_of_sourceRankThree
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          c hRank hfirst hsecond conditions hsourceOuter hfive C
  have hrepresentation := conditions.centralRepresentations central htrigger
  simpa only [central, lemma91QuaternaryCentralIndex] using hrepresentation

set_option maxHeartbeats 800000 in
-- Multiplication cancels the target ternary prefix and the first source
-- coefficient, leaving the second source adjacent product up to a square.
/-- The strict full-prefix determinant bound forces the second source
adjacent defect above `S₁ - S₃ + α₁` in exception (c). -/
theorem sourceSecondAdjacentDefect_strict_of_fullRaw_exceptionC
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hthree : 1 < S + 1)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment)
    (hfullRaw :
      ((((c.order (0 : Fin (S + 2)) : ℚ) -
          (c.order (2 : Fin (S + 2)) : ℚ) +
            a.alphaValue (0 : Fin (N + 2)) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
          ((1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 3))) :
    ((((c.order (0 : Fin (S + 2)) : ℚ) -
        (c.order (2 : Fin (S + 2)) : ℚ) +
          a.alphaValue (0 : Fin (N + 2)) : ℚ) : WithTop ℚ) <
      c.adjacentDefect (⟨1, hthree⟩ : Fin (S + 1))) := by
  let threshold : WithTop ℚ :=
    (((c.order (0 : Fin (S + 2)) : ℚ) -
      (c.order (2 : Fin (S + 2)) : ℚ) +
        a.alphaValue (0 : Fin (N + 2)) : ℚ) : WithTop ℚ)
  let x : Kˣ := (-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1
  let y : Kˣ := (1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 3
  let second : Fin (S + 1) := ⟨1, hthree⟩
  have hy : threshold < defectOrder (K := K) y := by
    simpa only [threshold, y] using hfullRaw
  have hsourceOrders :
      c.order (0 : Fin (S + 2)) ≤ c.order (2 : Fin (S + 2)) := by
    let sourceFirst : Fin (S + 2) := ⟨0, by omega⟩
    let sourceThird : Fin (S + 2) := ⟨2, by omega⟩
    have hgood := c.good sourceFirst (by
      simp only [sourceFirst]
      omega)
    change c.order sourceFirst ≤ c.order sourceThird at hgood
    have hSourceFirst : sourceFirst = (0 : Fin (S + 2)) := by
      apply Fin.ext
      rfl
    have hSourceThird : sourceThird = (2 : Fin (S + 2)) := by
      apply Fin.ext
      simp [sourceThird, Nat.mod_eq_of_lt (by omega : 2 < S + 2)]
    rw [hSourceFirst, hSourceThird] at hgood
    exact hgood
  have hthresholdLe : threshold ≤
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
    dsimp only [threshold]
    apply WithTop.coe_le_coe.mpr
    have hsourceOrdersQ :
        (c.order (0 : Fin (S + 2)) : ℚ) ≤
          (c.order (2 : Fin (S + 2)) : ℚ) := by
      exact_mod_cast hsourceOrders
    linarith
  have halpha := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.firstAlpha_lt_thirdAlpha_of_exceptionC
      c.firstUnarySegment C
  have hcappedRaw := a.truncatedPrefixDefect_le_defect
    c.firstUnarySegment (-1 : Kˣ) 3 1
  have hx : threshold < defectOrder (K := K) x := by
    calc
      threshold ≤ (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) :=
        hthresholdLe
      _ < (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) := by
        exact_mod_cast halpha
      _ = a.lemma814FirstThirdCappedDefect c.firstUnarySegment := by
        have h := C.firstThirdDefect_eq_alpha
        have hindex : (⟨2, by have := C.rank_four; omega⟩ : Fin (N + 2)) =
            (2 : Fin (N + 2)) := by
          have hlt : 2 < N + 2 := by
            have := C.rank_four
            omega
          apply Fin.ext
          change 2 = 2 % (N + 2)
          rw [Nat.mod_eq_of_lt hlt]
        rw [hindex] at h
        exact h.symm
      _ ≤ defectOrder (K := K)
          ((-1 : Kˣ) * a.prefixProduct 3 *
            c.firstUnarySegment.prefixProduct 1) := hcappedRaw
      _ = defectOrder (K := K) x := by
        rw [c.firstUnarySegment_prefixProduct_one]
  have hproduct : threshold < defectOrder (K := K) (x * y) :=
    (lt_min hx hy).trans_le (defectOrder_mul_ge_min x y)
  have hproductIdentity : x * y =
      c.adjacentProduct second *
        (a.prefixProduct 3 * c.prefixProduct 1) ^ 2 := by
    have hprefixTwo := c.toBONG.prefixProduct_succ 1 (by omega)
    have hprefixThree := c.toBONG.prefixProduct_succ 2 (by omega)
    change c.prefixProduct 2 = c.prefixProduct 1 *
      c.valueUnit (⟨1, by omega⟩ : Fin (S + 2)) at hprefixTwo
    change c.prefixProduct 3 = c.prefixProduct 2 *
      c.valueUnit (⟨2, by omega⟩ : Fin (S + 2)) at hprefixThree
    have hcast : second.castSucc =
        (⟨1, by omega⟩ : Fin (S + 2)) := by
      apply Fin.ext
      rfl
    have hsucc : second.succ =
        (⟨2, by omega⟩ : Fin (S + 2)) := by
      apply Fin.ext
      rfl
    dsimp only [x, y]
    unfold adjacentProduct
    rw [hcast, hsucc, hprefixThree, hprefixTwo]
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_one, one_mul,
      pow_two]
    ring
  rw [hproductIdentity, defectOrder_mul_square] at hproduct
  simpa only [threshold, second, adjacentDefect] using hproduct

/-- Condition (ii) supplies the full-prefix premise of the preceding
determinant calculation. -/
theorem sourceSecondAdjacentDefect_strict_of_exceptionC
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    ((((c.order (0 : Fin (S + 2)) : ℚ) -
        (c.order (2 : Fin (S + 2)) : ℚ) +
          a.alphaValue (0 : Fin (N + 2)) : ℚ) : WithTop ℚ) <
      c.adjacentDefect (⟨1, hthree⟩ : Fin (S + 1))) := by
  have hbounds :=
    a.thirdRawDefect_and_sourceCap_strict_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree C
  exact a.sourceSecondAdjacentDefect_strict_of_fullRaw_exceptionC
    (targetLaws := targetLaws) c hthree C hbounds.1

/-- Rewriting the second adjacent-defect estimate by the source order shift
gives the second right-defect candidate bound for the first source alpha. -/
theorem targetFirstAlpha_lt_sourceSecondRightDefect_of_exceptionC
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) <
      c.rightDefectCandidate (0 : Fin (S + 1))
        (⟨1, hthree⟩ : Fin (S + 1)) := by
  have hadjacent :=
    a.sourceSecondAdjacentDefect_strict_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree C
  exact a.targetFirstAlpha_lt_sourceSecondRightDefect_of_adjacent
    c hthree hadjacent

/-- In source rank at least four, the source-cap half of condition (ii) is
the strict third left-endpoint bound required by property P1. -/
theorem sourceThirdLeftEndpoint_strict_of_exceptionC
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hsourceFour : 2 < S + 1)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    (c.order (0 : Fin (S + 2)) : ℚ) +
        a.alphaValue (0 : Fin (N + 2)) <
      c.alphaLeftEndpoint (⟨2, hsourceFour⟩ : Fin (S + 1)) := by
  have hbounds :=
    a.thirdRawDefect_and_sourceCap_strict_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions (by omega) C
  have hcap := hbounds.2
  rw [c.prefixAlphaCap_of_internal (i := 3) (by omega) (by omega)] at hcap
  let third : Fin (S + 1) := ⟨2, hsourceFour⟩
  have hcapIndex : (⟨3 - 1, by omega⟩ : Fin (S + 1)) = third := by
    apply Fin.ext
    rfl
  rw [hcapIndex] at hcap
  have hcapQ :
      (c.order (0 : Fin (S + 2)) : ℚ) -
          (c.order (2 : Fin (S + 2)) : ℚ) +
            a.alphaValue (0 : Fin (N + 2)) <
        c.alphaValue third := by
    exact WithTop.coe_lt_coe.mp hcap
  have hthirdCast : third.castSucc = (2 : Fin (S + 2)) := by
    apply Fin.ext
    simp [third, Nat.mod_eq_of_lt (by omega : 2 < S + 2)]
  unfold alphaLeftEndpoint
  rw [hthirdCast]
  linarith

/-- The `A₃` estimate and property P1 force the first source alpha to be
attained on its first binary segment. -/
theorem firstBinaryAlpha_eq_sourceFirstAlpha_of_exceptionC
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    c.firstBinaryAlpha =
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) := by
  have hrigidity := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.secondOrderRigidity_of_exceptionBC
      c hRank hfirst hsecond conditions (Or.inr C)
  have hsecondBound :=
    a.targetFirstAlpha_lt_sourceSecondRightDefect_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree C
  rw [← hrigidity.2] at hsecondBound
  have hthirdBound : ∀ h : 2 < S + 1,
      (c.order (0 : Fin (S + 2)) : ℚ) +
          c.alphaValue (0 : Fin (S + 1)) <
        c.alphaLeftEndpoint (⟨2, h⟩ : Fin (S + 1)) := by
    intro h
    have hbound :=
      a.sourceThirdLeftEndpoint_strict_of_exceptionC
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          c hRank hfirst hsecond conditions h C
    rw [← hrigidity.2] at hbound
    exact hbound
  have hlater := by
    letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
    exact c.laterRightDefects_strict_of_second_and_third
      hthree hsecondBound hthirdBound
  exact c.firstBinaryAlpha_eq_alpha_of_laterRightDefects hlater

/-- Once the first source alpha is attained on the first binary segment,
Remark 8.7 identifies the raw source adjacent defect with `α₂`. -/
theorem sourceFirstAdjacentDefect_eq_targetSecond_of_firstBinary_exceptionC
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (hsourceAlpha : c.alphaValue (0 : Fin (S + 1)) =
      a.alphaValue (0 : Fin (N + 2)))
    (hbinary : c.firstBinaryAlpha =
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ))
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    c.adjacentDefect (0 : Fin (S + 1)) =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
  have hsourceStrict : c.alphaValue (0 : Fin (S + 1)) <
      c.halfGapValue (0 : Fin (S + 1)) := by
    unfold halfGapValue orderGap
    change c.alphaValue (0 : Fin (S + 1)) <
      (((c.order (1 : Fin (S + 2)) -
        c.order (0 : Fin (S + 2)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ))
    rw [hsourceAlpha, ← hfirst, ← hsecond]
    simpa [halfGapValue, orderGap] using
      (a.firstAlpha_lt_halfGap_of_lemma814ExceptionC
        c.firstUnarySegment C)
  have hstrictTop :
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) <
        c.halfGapCandidate (0 : Fin (S + 1)) := by
    rw [← c.coe_halfGapValue]
    exact_mod_cast hsourceStrict
  have hleftLt :
      c.leftDefectCandidate (0 : Fin (S + 1)) (0 : Fin (S + 1)) <
        c.halfGapCandidate (0 : Fin (S + 1)) := by
    by_contra hnot
    have hhalfLe : c.halfGapCandidate (0 : Fin (S + 1)) ≤
        c.leftDefectCandidate (0 : Fin (S + 1))
          (0 : Fin (S + 1)) := le_of_not_gt hnot
    have hmin := hbinary
    unfold firstBinaryAlpha at hmin
    rw [min_eq_left hhalfLe] at hmin
    exact (ne_of_lt hstrictTop) hmin.symm
  have hleft :
      c.leftDefectCandidate (0 : Fin (S + 1)) (0 : Fin (S + 1)) =
        (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) := by
    have hmin := hbinary
    unfold firstBinaryAlpha at hmin
    rw [min_eq_right hleftLt.le] at hmin
    exact hmin
  have hremark :=
    (a.beli2019Remark87 (0 : Fin (N + 1))
      C.firstThirdOrders_eq).currentAlpha_eq
  have hcurrent :
      a.alphaValue (1 : Fin (N + 2)) =
        ((a.order (0 : Fin (N + 3)) -
          a.order (1 : Fin (N + 3)) : Int) : ℚ) +
            a.alphaValue (0 : Fin (N + 2)) := by
    simpa [remark87CurrentAlpha, remark87PreviousAlpha,
      remark87PreviousValue, remark87MiddleValue] using hremark
  have hgap :
      (c.orderGap (0 : Fin (S + 1)) : ℚ) +
          a.alphaValue (1 : Fin (N + 2)) =
        c.alphaValue (0 : Fin (S + 1)) := by
    unfold orderGap
    change ((c.order (1 : Fin (S + 2)) -
        c.order (0 : Fin (S + 2)) : Int) : ℚ) +
          a.alphaValue (1 : Fin (N + 2)) =
        c.alphaValue (0 : Fin (S + 1))
    rw [← hfirst, ← hsecond, hsourceAlpha]
    push_cast at hcurrent ⊢
    linarith
  have hgapTop :
      ((c.orderGap (0 : Fin (S + 1)) : ℚ) : WithTop ℚ) +
          (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) =
        (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) := by
    exact_mod_cast hgap
  apply WithTop.add_left_cancel WithTop.coe_ne_top
  calc
    ((c.orderGap (0 : Fin (S + 1)) : ℚ) : WithTop ℚ) +
          c.adjacentDefect (0 : Fin (S + 1)) =
        (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) := by
      simpa only [leftDefectCandidate, orderGap] using hleft
    _ = ((c.orderGap (0 : Fin (S + 1)) : ℚ) : WithTop ℚ) +
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := hgapTop.symm

/-- Under the equal first two orders and representation conditions, the raw
first source adjacent defect is exactly the target second alpha. -/
theorem sourceFirstAdjacentDefect_eq_targetSecond_of_exceptionC
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    c.adjacentDefect (0 : Fin (S + 1)) =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
  have hrigidity := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.secondOrderRigidity_of_exceptionBC
      c hRank hfirst hsecond conditions (Or.inr C)
  have hbinary :=
    a.firstBinaryAlpha_eq_sourceFirstAlpha_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree C
  exact a.sourceFirstAdjacentDefect_eq_targetSecond_of_firstBinary_exceptionC
    (targetLaws := targetLaws) c hfirst hsecond hrigidity.2 hbinary C

set_option maxHeartbeats 1000000 in
/-- In the branch `S₁ < S₃`, every candidate defining the second source
alpha is strictly larger than the target `α₂`. -/
theorem targetSecondAlpha_lt_sourceSecondAlpha_of_exceptionC
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (hsourceOuter : c.order (0 : Fin (S + 2)) <
      c.order (2 : Fin (S + 2)))
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
      (c.alphaValue (1 : Fin (S + 1)) : WithTop ℚ) := by
  let sourceFirstAlpha : Fin (S + 1) := ⟨0, by omega⟩
  let sourceSecondAlpha : Fin (S + 1) := ⟨1, hthree⟩
  let sourceFirst : Fin (S + 2) := ⟨0, by omega⟩
  let sourceSecond : Fin (S + 2) := ⟨1, by omega⟩
  let sourceThird : Fin (S + 2) := ⟨2, by omega⟩
  have hSourceFirstAlpha : sourceFirstAlpha = (0 : Fin (S + 1)) := by
    apply Fin.ext
    rfl
  have hSourceSecondAlpha : sourceSecondAlpha =
      (1 : Fin (S + 1)) := by
    apply Fin.ext
    simp [sourceSecondAlpha, Nat.mod_eq_of_lt hthree]
  have hSourceFirst : sourceFirst = (0 : Fin (S + 2)) := by
    apply Fin.ext
    rfl
  have hSourceSecond : sourceSecond = (1 : Fin (S + 2)) := by
    apply Fin.ext
    simp [sourceSecond, Nat.mod_eq_of_lt (by omega : 1 < S + 2)]
  have hSourceThird : sourceThird = (2 : Fin (S + 2)) := by
    apply Fin.ext
    simp [sourceThird, Nat.mod_eq_of_lt (by omega : 2 < S + 2)]
  have hfirstCast : sourceFirstAlpha.castSucc = sourceFirst := by
    apply Fin.ext
    rfl
  have hsecondCast : sourceSecondAlpha.castSucc = sourceSecond := by
    apply Fin.ext
    rfl
  have hsecondSucc : sourceSecondAlpha.succ = sourceThird := by
    apply Fin.ext
    rfl
  have hrigidity := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.secondOrderRigidity_of_exceptionBC
      c hRank hfirst hsecond conditions (Or.inr C)
  have hremark := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact (a.beli2019Remark87 (0 : Fin (N + 1))
      C.firstThirdOrders_eq).currentAlpha_eq
  have hbase : a.alphaValue (1 : Fin (N + 2)) =
      ((c.order sourceFirst - c.order sourceSecond : Int) : ℚ) +
        c.alphaValue sourceFirstAlpha := by
    change a.alphaValue (1 : Fin (N + 2)) =
      (((a.order (0 : Fin (N + 3)) -
        a.order (1 : Fin (N + 3)) : Int) : ℚ) +
          a.alphaValue (0 : Fin (N + 2))) at hremark
    rw [hSourceFirst, hSourceSecond, hSourceFirstAlpha]
    rw [← hfirst, ← hsecond, hrigidity.2]
    exact hremark
  have htargetHalf := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.secondAlpha_lt_halfGap_of_lemma814ExceptionC
      c.firstUnarySegment C
  have hhalfQ : a.alphaValue (1 : Fin (N + 2)) <
      ((c.order sourceThird - c.order sourceSecond : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) := by
    have houter := C.firstThirdOrders_eq
    have hsourceOuter' : c.order sourceFirst < c.order sourceThird := by
      simpa only [hSourceFirst, hSourceThird] using hsourceOuter
    have hsourceOuterQ : (c.order sourceFirst : ℚ) <
        (c.order sourceThird : ℚ) := by exact_mod_cast hsourceOuter'
    have htargetThird : a.order (2 : Fin (N + 3)) =
        c.order sourceFirst := by
      rw [hSourceFirst, ← hfirst]
      exact houter.symm
    unfold halfGapValue orderGap at htargetHalf
    change a.alphaValue (1 : Fin (N + 2)) <
      (((a.order (2 : Fin (N + 3)) -
        a.order (1 : Fin (N + 3)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ)) at htargetHalf
    rw [hsecond, ← hSourceSecond, htargetThird] at htargetHalf
    push_cast at htargetHalf ⊢
    linarith
  have hhalf : (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
      c.halfGapCandidate sourceSecondAlpha := by
    unfold halfGapCandidate
    rw [hsecondCast, hsecondSucc]
    exact_mod_cast hhalfQ
  have hadjacentZero :=
    a.sourceFirstAdjacentDefect_eq_targetSecond_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree C
  have hleftZero :
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
        c.leftDefectCandidate sourceSecondAlpha sourceFirstAlpha := by
    unfold leftDefectCandidate
    rw [← hSourceFirstAlpha] at hadjacentZero
    rw [hsecondSucc, hfirstCast, hadjacentZero]
    apply WithTop.coe_lt_coe.mpr
    have hsourceOuterQ : (c.order sourceFirst : ℚ) <
        (c.order sourceThird : ℚ) := by
      exact_mod_cast (show c.order sourceFirst < c.order sourceThird by
        simpa only [hSourceFirst, hSourceThird] using hsourceOuter)
    push_cast
    linarith
  have hadjacentOne :=
    a.sourceSecondAdjacentDefect_strict_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree C
  have hleftOne :
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
        c.leftDefectCandidate sourceSecondAlpha sourceSecondAlpha := by
    unfold leftDefectCandidate
    rw [hsecondSucc, hsecondCast]
    rw [← hrigidity.2, ← hSourceFirstAlpha, ← hSourceFirst,
      ← hSourceThird] at hadjacentOne
    change
      (((c.order sourceFirst : ℚ) - (c.order sourceThird : ℚ) +
        c.alphaValue sourceFirstAlpha : ℚ) : WithTop ℚ) <
          c.adjacentDefect sourceSecondAlpha at hadjacentOne
    have hshifted :=
      (WithTop.add_lt_add_iff_left
        (show (((c.order sourceThird - c.order sourceSecond : Int) : ℚ) :
          WithTop ℚ) ≠ ⊤ from WithTop.coe_ne_top)).mpr hadjacentOne
    have hleftEquality :
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) =
          (((c.order sourceThird - c.order sourceSecond : Int) : ℚ) :
              WithTop ℚ) +
            (((c.order sourceFirst : ℚ) - (c.order sourceThird : ℚ) +
              c.alphaValue sourceFirstAlpha : ℚ) : WithTop ℚ) := by
      apply WithTop.coe_eq_coe.mpr
      push_cast at hbase ⊢
      linarith
    rw [hleftEquality]
    exact hshifted
  have hsecondBound :=
    a.targetFirstAlpha_lt_sourceSecondRightDefect_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree C
  rw [← hrigidity.2] at hsecondBound
  have hthirdBound : ∀ h : 2 < S + 1,
      (c.order (0 : Fin (S + 2)) : ℚ) +
          c.alphaValue (0 : Fin (S + 1)) <
        c.alphaLeftEndpoint (⟨2, h⟩ : Fin (S + 1)) := by
    intro h
    have hbound :=
      a.sourceThirdLeftEndpoint_strict_of_exceptionC
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          c hRank hfirst hsecond conditions h C
    rw [← hrigidity.2] at hbound
    exact hbound
  have hlater := by
    letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
    exact c.laterRightDefects_strict_of_second_and_third
      hthree hsecondBound hthirdBound
  have hright : ∀ j : Fin (S + 1), sourceSecondAlpha ≤ j →
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
        c.rightDefectCandidate sourceSecondAlpha j := by
    intro j hj
    have hjpos : 0 < j.1 := by
      have hjone : 1 ≤ j.1 := by
        change 1 ≤ j.1 at hj
        exact hj
      omega
    have hfirstRight := hlater j hjpos
    rw [← hSourceFirstAlpha] at hfirstRight
    let shift : ℚ :=
      ((c.order sourceFirst - c.order sourceSecond : Int) : ℚ)
    have hbaseTop :
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) =
          (shift : WithTop ℚ) +
            (c.alphaValue sourceFirstAlpha : WithTop ℚ) := by
      exact_mod_cast hbase
    have hshifted :
        (shift : WithTop ℚ) +
            (c.alphaValue sourceFirstAlpha : WithTop ℚ) <
          (shift : WithTop ℚ) +
            c.rightDefectCandidate sourceFirstAlpha j :=
      (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mpr hfirstRight
    rw [hbaseTop]
    calc
      (shift : WithTop ℚ) +
          (c.alphaValue sourceFirstAlpha : WithTop ℚ) <
        (shift : WithTop ℚ) +
          c.rightDefectCandidate sourceFirstAlpha j := hshifted
      _ = c.rightDefectCandidate sourceSecondAlpha j := by
        unfold rightDefectCandidate
        rw [hfirstCast, hsecondCast]
        have hordersQ : shift +
            ((c.order j.succ - c.order sourceFirst : Int) : ℚ) =
          ((c.order j.succ - c.order sourceSecond : Int) : ℚ) := by
          dsimp only [shift]
          push_cast
          ring
        let before : WithTop ℚ :=
          (((c.order j.succ - c.order sourceFirst : Int) : ℚ) : WithTop ℚ)
        let after : WithTop ℚ :=
          (((c.order j.succ - c.order sourceSecond : Int) : ℚ) : WithTop ℚ)
        have hordersTop : (shift : WithTop ℚ) + before = after := by
          dsimp only [before, after]
          exact_mod_cast hordersQ
        change (shift : WithTop ℚ) + (before + c.adjacentDefect j) =
          after + c.adjacentDefect j
        exact (add_assoc _ _ _).symm.trans
          (congrArg (fun t => t + c.adjacentDefect j) hordersTop)
  have hmem : (c.alphaValue sourceSecondAlpha : WithTop ℚ) ∈
      c.alphaCandidates sourceSecondAlpha := by
    rw [c.coe_alphaValue]
    exact Finset.min'_mem _ _
  simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union] at hmem
  have hresult : (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
      (c.alphaValue sourceSecondAlpha : WithTop ℚ) := by
    rcases hmem with hhalfEq | hleft | hrightMem
    · exact hhalf.trans_eq hhalfEq.symm
    · rcases Finset.mem_image.mp hleft with ⟨j, hj, hcandidateEq⟩
      have hjle : j ≤ sourceSecondAlpha :=
        (Finset.mem_filter.mp hj).2
      by_cases hjzero : j.1 = 0
      · have hjEq : j = sourceFirstAlpha := by
          apply Fin.ext
          exact hjzero
        rw [hjEq] at hcandidateEq
        exact hleftZero.trans_eq hcandidateEq
      · have hjone : j.1 = 1 := by
          change j.1 ≤ 1 at hjle
          omega
        have hjEq : j = sourceSecondAlpha := by
          apply Fin.ext
          exact hjone
        rw [hjEq] at hcandidateEq
        exact hleftOne.trans_eq hcandidateEq
    · rcases Finset.mem_image.mp hrightMem with ⟨j, hj, hcandidateEq⟩
      have hjge : sourceSecondAlpha ≤ j :=
        (Finset.mem_filter.mp hj).2
      exact (hright j hjge).trans_eq hcandidateEq
  rw [hSourceSecondAlpha] at hresult
  exact hresult

/-- Lemma 8.1(ii) applied to the source first adjacent product and the target
quaternary determinant removes the remaining cap strictly:
`d(-a_(1,4)c_(1,2)) > α₂`. -/
theorem targetSecondAlpha_lt_firstFour_sourceFirstTwoRawDefect_of_exceptionC
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
      defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct 4 * c.prefixProduct 2) := by
  let x := c.adjacentProduct (0 : Fin (S + 1))
  let z := a.prefixProduct 4
  have hx : defectOrder (K := K) x =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
    change c.adjacentDefect (0 : Fin (S + 1)) = _
    exact a.sourceFirstAdjacentDefect_eq_targetSecond_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree C
  have hz : defectOrder (K := K) z =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) :=
    a.lemma814FirstFourRawDefect_eq_secondAlpha_of_exceptionC
      c.firstUnarySegment C
  have hdefectEq : quadraticDefect K x = quadraticDefect K z :=
    quadraticDefect_eq_of_defectOrder_eq x z (hx.trans hz.symm)
  have hxFinite : quadraticDefect K x ≠ ⊤ :=
    quadraticDefect_ne_top_of_defectOrder_eq_coe x
      (a.alphaValue (1 : Fin (N + 2))) hx
  have hstrict := beli2019Lemma81_ii_strict
    C.residueTwo x z hdefectEq hxFinite
  have hstrictOrder :=
    defectOrder_lt_of_quadraticDefect_lt x (x * z) hstrict
  have hproduct : x * z =
      (-1 : Kˣ) * a.prefixProduct 4 * c.prefixProduct 2 := by
    unfold x z
    rw [c.prefixProduct_add_two 0 (by omega),
      show c.prefixProduct 0 = 1 by exact c.toBONG.prefixProduct_zero]
    unfold adjacentProduct
    have hcast : (0 : Fin (S + 1)).castSucc =
        (⟨0, by omega⟩ : Fin (S + 2)) := by
      apply Fin.ext
      rfl
    have hsucc : (0 : Fin (S + 1)).succ =
        (⟨1, by omega⟩ : Fin (S + 2)) := by
      apply Fin.ext
      rfl
    rw [hcast, hsucc]
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_one, one_mul]
    ring
  rw [hproduct, hx] at hstrictOrder
  exact hstrictOrder

/-- In the branch `S₁ < S₃`, neither endpoint alpha cap cuts down the strict
raw mixed defect, so the bracketed defect is also strictly above `α₂`. -/
theorem targetSecondAlpha_lt_firstFour_sourceFirstTwoCappedDefect_of_exceptionC
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (hsourceOuter : c.order (0 : Fin (S + 2)) <
      c.order (2 : Fin (S + 2)))
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 4 2 := by
  have hraw :=
    a.targetSecondAlpha_lt_firstFour_sourceFirstTwoRawDefect_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree C
  have htargetCap :
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
        a.prefixAlphaCap 4 := by
    by_cases hfive : 5 ≤ N + 3
    · rw [a.prefixAlphaCap_of_internal (i := 4) (by omega) (by omega)]
      let fourthAlpha : Fin (N + 2) := ⟨3, by omega⟩
      have hindex : (⟨4 - 1, by omega⟩ : Fin (N + 2)) =
          fourthAlpha := by
        apply Fin.ext
        rfl
      rw [hindex]
      have hlater := C.laterAlpha_strict hfive
      have hsecondComplement := C.secondAlpha_eq_complement
      exact_mod_cast hsecondComplement.symm ▸ hlater
    · have hlast : 4 = N + 3 := by
        have := C.rank_four
        omega
      rw [hlast, a.prefixAlphaCap_last]
      apply WithTop.lt_top_iff_ne_top.mpr
      exact WithTop.coe_ne_top
  have hsourceAlpha :=
    a.targetSecondAlpha_lt_sourceSecondAlpha_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree hsourceOuter C
  have hsourceCap :
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
        c.prefixAlphaCap 2 := by
    rw [c.prefixAlphaCap_of_internal (i := 2) (by omega) (by omega)]
    have hindex : (⟨2 - 1, by omega⟩ : Fin (S + 1)) =
        (1 : Fin (S + 1)) := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt hthree]
    rw [hindex]
    exact hsourceAlpha
  unfold truncatedPrefixDefect
  exact lt_min hraw (lt_min htargetCap hsourceCap)

/-- The strict capped mixed defect verifies the condition-(iii′) determinant
inequality at `i = 3` in the branch `S₁ < S₃`. -/
theorem lemma91BinaryCentralDefectInequality_of_exceptionC
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (hsourceOuter : c.order (0 : Fin (S + 2)) <
      c.order (2 : Fin (S + 2)))
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    a.lemma91BinaryCentralDefectInequality c
      (by have := C.rank_four; omega) := by
  have hrigidity := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.secondOrderRigidity_of_exceptionBC
      c hRank hfirst hsecond conditions (Or.inr C)
  have hfull := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.fullFirstThirdDefect_eq_sourceFirstAlpha_of_exceptionBC
      c hRank hfirst hsecond conditions (Or.inr C)
  have hmixed :=
    a.targetSecondAlpha_lt_firstFour_sourceFirstTwoCappedDefect_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree hsourceOuter C
  have hrelation := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.firstAlpha_eq_secondFourthShift_thirdAlpha_of_exceptionC
      c.firstUnarySegment C
  have hsum :=
    a.secondAlpha_add_thirdAlpha_eq_twoE_of_lemma814ExceptionC
      c.firstUnarySegment C (by have := C.rank_four; omega)
  have hthirdIndex :
      (⟨2, by have := C.rank_four; omega⟩ : Fin (N + 2)) =
        (2 : Fin (N + 2)) := by
    have hlt : 2 < N + 2 := by
      have := C.rank_four
      omega
    apply Fin.ext
    change 2 = 2 % (N + 2)
    rw [Nat.mod_eq_of_lt hlt]
  rw [hthirdIndex] at hsum
  have hconstantQ :
      2 * (ramificationIndex K : ℚ) +
          (c.order (1 : Fin (S + 2)) : ℚ) -
            (a.order (3 : Fin (N + 3)) : ℚ) =
        a.alphaValue (0 : Fin (N + 2)) +
          a.alphaValue (1 : Fin (N + 2)) := by
    rw [← hsecond]
    push_cast at hrelation
    linarith
  have hconstantTop :
      (((2 * (ramificationIndex K : ℚ) +
        (c.order (1 : Fin (S + 2)) : ℚ) -
          (a.order (3 : Fin (N + 3)) : ℚ) : ℚ)) : WithTop ℚ) =
        (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) +
          (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
    exact_mod_cast hconstantQ
  unfold lemma91BinaryCentralDefectInequality
  have hfourthIndex :
      (⟨3, by have := C.rank_four; omega⟩ : Fin (N + 3)) =
        (3 : Fin (N + 3)) := by
    have hlt : 3 < N + 3 := by
      have := C.rank_four
      omega
    apply Fin.ext
    change 3 = 3 % (N + 3)
    rw [Nat.mod_eq_of_lt hlt]
  rw [hfourthIndex]
  rw [hfull, hrigidity.2, hconstantTop]
  exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mpr hmixed

/-- Condition (iii′) therefore gives the binary source prefix represented by
the target ternary prefix in the strict source-order branch. -/
theorem binaryPrefixRepresentation_of_exceptionC_of_firstThird_lt
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (hsourceOuter : c.order (0 : Fin (S + 2)) <
      c.order (2 : Fin (S + 2)))
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    DiagonalRepresents
      (c.prefixValues 2 (by omega))
      (a.prefixValues 3 (by omega)) := by
  have hfour : 3 < N + 3 := by
    have := C.rank_four
    omega
  have hdefect :=
    a.lemma91BinaryCentralDefectInequality_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree hsourceOuter C
  have horder : c.order (1 : Fin (S + 2)) < a.order ⟨3, hfour⟩ := by
    rw [← hsecond]
    have hstrict := C.secondFourthOrders_lt
    convert hstrict using 1
  exact a.binaryPrefixRepresentation_of_centralDefectInequality
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      c hRank conditions hfour horder hdefect

/-- An isotropic ternary complement with the prescribed first value rules out
exception (c).  This is the common geometric endpoint of both source-order
subcases in the proof of Lemma 9.1. -/
theorem not_lemma814ExceptionC_of_isotropicUnitComplement
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfour : 4 ≤ N + 3) (candidate : Fin 3 → Kˣ)
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.cons (b.valueUnit (0 : Fin 1)) candidate))
      (a.prefixValues 4 hfour))
    (hisotropic : DiagonalIsotropic
      (diagonalUnitCoefficients candidate)) :
    ¬a.Beli2019Lemma814ExceptionC b := by
  intro C
  rcases C.firstFourComplement_anisotropic with
    ⟨complement, hcomplement, hanisotropic⟩
  have hcandidate : DiagonalRepresents
      (Fin.cons (b.value (0 : Fin 1))
        (diagonalUnitCoefficients candidate))
      (a.prefixValues 4 C.rank_four) := by
    simpa only [diagonalUnitCoefficients_cons, GoodBONG.coe_valueUnit]
      using hrep
  have hboth : DiagonalRepresents
      (Fin.cons (b.value (0 : Fin 1))
        (diagonalUnitCoefficients candidate))
      (Fin.cons (b.value (0 : Fin 1)) complement) :=
    hcandidate.trans hcomplement.symm_of_sameRank
  have htail : DiagonalRepresents
      (diagonalUnitCoefficients candidate) complement := by
    apply DiagonalRepresents.cancel_common_head
      (b.value (0 : Fin 1))
      (diagonalUnitCoefficients candidate) complement
    · exact b.toBONG.value_ne_zero _
    · intro i
      exact Units.ne_zero (candidate i)
    · intro i
      exact diagonalAnisotropic_coefficient_ne_zero
        complement hanisotropic i
    · exact hboth
  have hcandidateAnisotropic : DiagonalAnisotropic
      (diagonalUnitCoefficients candidate) :=
    htail.anisotropic_of hanisotropic
  rcases hisotropic with ⟨x, hx, hzero⟩
  exact hx (hcandidateAnisotropic x hzero)

set_option maxHeartbeats 1000000 in
-- Complete the represented binary prefix by its determinant line and then
-- append the fourth target coefficient.  The tail after the common first
-- coefficient is the ternary complement used in the paper.
/-- The binary-prefix representation and strict mixed raw defect contradict
the anisotropic ternary complement in exception (c). -/
theorem false_of_exceptionC_of_binaryPrefix_of_mixedRaw
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hbinary : DiagonalRepresents
      (c.prefixValues 2 (by omega))
      (a.prefixValues 3 (by omega)))
    (hmixed : (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
      defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct 4 * c.prefixProduct 2))
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) : False := by
  let base := a.prefixValueUnits 3 (by omega)
  let head := c.prefixValueUnits 2 (by omega)
  let d := diagonalUnitDeterminant base * diagonalUnitDeterminant head
  let completed : Fin 3 → Kˣ := Fin.snoc head d
  let fourth := a.valueUnit (⟨3, by
    have := C.rank_four
    omega⟩ : Fin (N + 3))
  let full : Fin 4 → Kˣ := Fin.snoc completed fourth
  let tail : Fin 3 → Kˣ := fun j => full j.succ
  have hheadRep : DiagonalRepresents
      (diagonalUnitCoefficients head)
      (diagonalUnitCoefficients base) := by
    simpa only [head, base,
      c.diagonalUnitCoefficients_prefixValueUnits,
      a.diagonalUnitCoefficients_prefixValueUnits] using hbinary
  have hcompletedRep : DiagonalRepresents
      (diagonalUnitCoefficients completed)
      (diagonalUnitCoefficients base) := by
    simpa only [completed, d] using
      determinantCompletion_represents_base base head hheadRep
  have hfullRep : DiagonalRepresents
      (diagonalUnitCoefficients full)
      (diagonalUnitCoefficients
        (a.prefixValueUnits 4 C.rank_four)) := by
    have hs := diagonalRepresents_snoc hcompletedRep (fourth : K)
    have htarget : a.prefixValueUnits 4 C.rank_four =
        Fin.snoc base fourth := by
      simpa only [base, fourth] using
        a.prefixValueUnits_succ_eq_snoc 3 C.rank_four
    rw [htarget]
    simpa only [full, diagonalUnitCoefficients_snoc] using hs
  have hcompletedZero : completed (0 : Fin 3) = head (0 : Fin 2) := by
    simp [completed]
  have hcompletedOne : completed (1 : Fin 3) = head (1 : Fin 2) := by
    change (Fin.snoc head d : Fin 3 → Kˣ) 1 = head 1
    rw [show (1 : Fin 3) = (1 : Fin 2).castSucc by rfl,
      Fin.snoc_castSucc]
  have hcompletedTwo : completed (2 : Fin 3) = d := by
    change (Fin.snoc head d : Fin 3 → Kˣ) 2 = d
    rw [show (2 : Fin 3) = Fin.last 2 by rfl, Fin.snoc_last]
  have hfullZero : full (0 : Fin 4) = completed (0 : Fin 3) := by
    change (Fin.snoc completed fourth : Fin 4 → Kˣ) 0 = completed 0
    rw [show (0 : Fin 4) = (0 : Fin 3).castSucc by rfl,
      Fin.snoc_castSucc]
  have hfullOne : full (1 : Fin 4) = completed (1 : Fin 3) := by
    change (Fin.snoc completed fourth : Fin 4 → Kˣ) 1 = completed 1
    rw [show (1 : Fin 4) = (1 : Fin 3).castSucc by rfl,
      Fin.snoc_castSucc]
  have hfullTwo : full (2 : Fin 4) = completed (2 : Fin 3) := by
    change (Fin.snoc completed fourth : Fin 4 → Kˣ) 2 = completed 2
    rw [show (2 : Fin 4) = (2 : Fin 3).castSucc by rfl,
      Fin.snoc_castSucc]
  have hfullThree : full (3 : Fin 4) = fourth := by
    change (Fin.snoc completed fourth : Fin 4 → Kˣ) 3 = fourth
    rw [show (3 : Fin 4) = Fin.last 3 by rfl, Fin.snoc_last]
  have htailZero : tail (0 : Fin 3) = head (1 : Fin 2) := by
    change full (1 : Fin 4) = head (1 : Fin 2)
    rw [hfullOne, hcompletedOne]
  have htailOne : tail (1 : Fin 3) = d := by
    change full (2 : Fin 4) = d
    rw [hfullTwo, hcompletedTwo]
  have htailTwo : tail (2 : Fin 3) = fourth := by
    change full (3 : Fin 4) = fourth
    exact hfullThree
  have hfullCons : full =
      Fin.cons (c.valueUnit (0 : Fin (S + 2))) tail := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · change full (0 : Fin 4) = c.valueUnit (0 : Fin (S + 2))
      rw [hfullZero, hcompletedZero]
      rfl
    · rfl
  have htailRep : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.cons (c.valueUnit (0 : Fin (S + 2))) tail))
      (a.prefixValues 4 C.rank_four) := by
    rw [← hfullCons]
    simpa only [a.diagonalUnitCoefficients_prefixValueUnits] using hfullRep
  have hfirstArgument : -(tail 0 * tail 1) =
      ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1) *
        (c.valueUnit (1 : Fin (S + 2))) ^ 2 := by
    rw [htailZero, htailOne]
    have hheadOne : head (1 : Fin 2) =
        c.valueUnit (1 : Fin (S + 2)) := by
      rfl
    rw [hheadOne]
    dsimp only [d]
    rw [a.diagonalUnitDeterminant_prefixValueUnits 3 (by omega),
      c.diagonalUnitDeterminant_prefixValueUnits 2 (by omega)]
    have hprefix := c.toBONG.prefixProduct_succ 1 (by omega)
    change c.prefixProduct 2 = c.prefixProduct 1 *
      c.valueUnit (1 : Fin (S + 2)) at hprefix
    rw [hprefix]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_one, pow_two]
    ring
  have hsecondArgument : -(tail 1 * tail 2) =
      (-1 : Kˣ) * a.prefixProduct 4 * c.prefixProduct 2 := by
    rw [htailOne, htailTwo]
    dsimp only [d, fourth]
    rw [a.diagonalUnitDeterminant_prefixValueUnits 3 (by omega),
      c.diagonalUnitDeterminant_prefixValueUnits 2 (by omega)]
    have hprefix := a.toBONG.prefixProduct_succ 3 (by
      have := C.rank_four
      omega)
    change a.prefixProduct 4 = a.prefixProduct 3 *
      a.valueUnit (⟨3, by have := C.rank_four; omega⟩ : Fin (N + 3))
        at hprefix
    rw [hprefix]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_one]
    ring
  have hfirstRaw := a.truncatedPrefixDefect_le_defect
    c.firstUnarySegment (-1 : Kˣ) 3 1
  change a.lemma814FirstThirdCappedDefect c.firstUnarySegment ≤
    defectOrder (K := K)
      ((-1 : Kˣ) * a.prefixProduct 3 *
        c.firstUnarySegment.prefixProduct 1) at hfirstRaw
  rw [c.firstUnarySegment_prefixProduct_one] at hfirstRaw
  have hthirdIndex :
      (⟨2, by have := C.rank_four; omega⟩ : Fin (N + 2)) =
        (2 : Fin (N + 2)) := by
    have hlt : 2 < N + 2 := by
      have := C.rank_four
      omega
    apply Fin.ext
    change 2 = 2 % (N + 2)
    rw [Nat.mod_eq_of_lt hlt]
  have hfirstDefect :
      (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) ≤
        defectOrder (K := K) (-(tail 0 * tail 1)) := by
    rw [hfirstArgument, defectOrder_mul_square]
    have hCapped := C.firstThirdDefect_eq_alpha
    rw [hthirdIndex] at hCapped
    exact hCapped.symm.trans_le hfirstRaw
  have hsecondDefect :
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
        defectOrder (K := K) (-(tail 1 * tail 2)) := by
    rw [hsecondArgument]
    exact hmixed
  have hsum :=
    a.secondAlpha_add_thirdAlpha_eq_twoE_of_lemma814ExceptionC
      c.firstUnarySegment C (by have := C.rank_four; omega)
  rw [hthirdIndex] at hsum
  have hdefectSum :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        defectOrder (K := K) (-(tail 0 * tail 1)) +
          defectOrder (K := K) (-(tail 1 * tail 2)) := by
    have hsumTop :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) =
          (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) +
            (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
      exact_mod_cast hsum.symm.trans (add_comm _ _)
    rw [hsumTop]
    exact WithTop.add_lt_add_of_le_of_lt WithTop.coe_ne_top
      hfirstDefect hsecondDefect
  have hhilbert :
      hilbertSymbol K (-(tail 0 * tail 1)) (-(tail 1 * tail 2)) = 1 :=
    hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e hdefectSum
  have htailIsotropic :
      DiagonalIsotropic (diagonalUnitCoefficients tail) :=
    (diagonalUnitTernary_isotropic_iff_adjacentHilbertOne tail).mpr hhilbert
  exact (a.not_lemma814ExceptionC_of_isotropicUnitComplement
    c.firstUnarySegment C.rank_four tail (by
      simpa only [c.firstUnarySegment_valueUnit_zero] using htailRep)
        htailIsotropic) C

set_option maxHeartbeats 1000000 in
-- Complete the represented ternary prefix by its determinant line.  Removing
-- the common first coefficient leaves exactly the ternary complement in the
-- equal source-order subcase of the paper.
/-- A represented source ternary prefix, the lower bound
`d(-b₂b₃) ≥ α₃`, and the strict mixed defect contradict exception (c). -/
theorem false_of_exceptionC_of_ternaryPrefix_of_adjacent_of_mixedRaw
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hthree : 1 < S + 1)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment)
    (hternary : DiagonalRepresents
      (c.prefixValues 3 (by omega))
      (a.prefixValues 4 (by have := C.rank_four; omega)))
    (hadjacent : (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) ≤
      c.adjacentDefect (⟨1, hthree⟩ : Fin (S + 1)))
    (hmixed : (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
      defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct 4 * c.prefixProduct 2)) : False := by
  let base := a.prefixValueUnits 4 C.rank_four
  let head := c.prefixValueUnits 3 (by omega)
  let d := diagonalUnitDeterminant base * diagonalUnitDeterminant head
  let completed : Fin 4 → Kˣ := Fin.snoc head d
  let tail : Fin 3 → Kˣ := fun j => completed j.succ
  let second : Fin (S + 1) := ⟨1, hthree⟩
  have hheadRep : DiagonalRepresents
      (diagonalUnitCoefficients head)
      (diagonalUnitCoefficients base) := by
    simpa only [head, base,
      c.diagonalUnitCoefficients_prefixValueUnits,
      a.diagonalUnitCoefficients_prefixValueUnits] using hternary
  have hcompletedRep : DiagonalRepresents
      (diagonalUnitCoefficients completed)
      (diagonalUnitCoefficients base) := by
    simpa only [completed, d] using
      determinantCompletion_represents_base_general base head hheadRep
  have hcompletedZero : completed (0 : Fin 4) = head (0 : Fin 3) := by
    simp [completed]
  have hcompletedOne : completed (1 : Fin 4) = head (1 : Fin 3) := by
    change (Fin.snoc head d : Fin 4 → Kˣ) 1 = head 1
    rw [show (1 : Fin 4) = (1 : Fin 3).castSucc by rfl,
      Fin.snoc_castSucc]
  have hcompletedTwo : completed (2 : Fin 4) = head (2 : Fin 3) := by
    change (Fin.snoc head d : Fin 4 → Kˣ) 2 = head 2
    rw [show (2 : Fin 4) = (2 : Fin 3).castSucc by rfl,
      Fin.snoc_castSucc]
  have hcompletedThree : completed (3 : Fin 4) = d := by
    change (Fin.snoc head d : Fin 4 → Kˣ) 3 = d
    rw [show (3 : Fin 4) = Fin.last 3 by rfl, Fin.snoc_last]
  have htailZero : tail (0 : Fin 3) = head (1 : Fin 3) := by
    change completed (1 : Fin 4) = head (1 : Fin 3)
    exact hcompletedOne
  have htailOne : tail (1 : Fin 3) = head (2 : Fin 3) := by
    change completed (2 : Fin 4) = head (2 : Fin 3)
    exact hcompletedTwo
  have htailTwo : tail (2 : Fin 3) = d := by
    change completed (3 : Fin 4) = d
    exact hcompletedThree
  have hcompletedCons : completed =
      Fin.cons (c.valueUnit (0 : Fin (S + 2))) tail := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · change completed (0 : Fin 4) = c.valueUnit (0 : Fin (S + 2))
      rw [hcompletedZero]
      rfl
    · rfl
  have htailRep : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.cons (c.valueUnit (0 : Fin (S + 2))) tail))
      (a.prefixValues 4 C.rank_four) := by
    rw [← hcompletedCons]
    simpa only [base,
      a.diagonalUnitCoefficients_prefixValueUnits] using hcompletedRep
  have hheadOne : head (1 : Fin 3) =
      c.valueUnit (1 : Fin (S + 2)) := by
    rfl
  have hheadTwo : head (2 : Fin 3) =
      c.valueUnit (2 : Fin (S + 2)) := by
    dsimp only [head, prefixValueUnits]
    congr 1
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < S + 2)]
  have hfirstArgument : -(tail 0 * tail 1) =
      c.adjacentProduct second := by
    rw [htailZero, htailOne, hheadOne, hheadTwo]
    unfold adjacentProduct
    have hcast : second.castSucc =
        (1 : Fin (S + 2)) := by
      apply Fin.ext
      rfl
    have hsucc : second.succ =
        (2 : Fin (S + 2)) := by
      have hlt : 2 < S + 2 := by omega
      apply Fin.ext
      change 2 = 2 % (S + 2)
      rw [Nat.mod_eq_of_lt hlt]
    rw [hcast, hsucc]
  have hsecondArgument : -(tail 1 * tail 2) =
      ((-1 : Kˣ) * a.prefixProduct 4 * c.prefixProduct 2) *
        (c.valueUnit (2 : Fin (S + 2))) ^ 2 := by
    rw [htailOne, htailTwo, hheadTwo]
    dsimp only [d]
    rw [a.diagonalUnitDeterminant_prefixValueUnits 4 C.rank_four,
      c.diagonalUnitDeterminant_prefixValueUnits 3 (by omega)]
    have hprefix : c.prefixProduct 3 = c.prefixProduct 2 *
        c.valueUnit (2 : Fin (S + 2)) := by
      have h := c.toBONG.prefixProduct_succ 2 (by omega)
      have hindex : (⟨2, by omega⟩ : Fin (S + 2)) =
          (2 : Fin (S + 2)) := by
        have hlt : 2 < S + 2 := by omega
        apply Fin.ext
        change 2 = 2 % (S + 2)
        rw [Nat.mod_eq_of_lt hlt]
      rw [hindex] at h
      norm_num at h ⊢
      exact h
    rw [hprefix]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_one, pow_two]
    ring
  have hfirstDefect :
      (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) ≤
        defectOrder (K := K) (-(tail 0 * tail 1)) := by
    rw [hfirstArgument]
    simpa only [adjacentDefect, second] using hadjacent
  have hsecondDefect :
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
        defectOrder (K := K) (-(tail 1 * tail 2)) := by
    rw [hsecondArgument, defectOrder_mul_square]
    exact hmixed
  have hsum :=
    a.secondAlpha_add_thirdAlpha_eq_twoE_of_lemma814ExceptionC
      c.firstUnarySegment C (by have := C.rank_four; omega)
  have hthirdIndex :
      (⟨2, by have := C.rank_four; omega⟩ : Fin (N + 2)) =
        (2 : Fin (N + 2)) := by
    have hlt : 2 < N + 2 := by
      have := C.rank_four
      omega
    apply Fin.ext
    change 2 = 2 % (N + 2)
    rw [Nat.mod_eq_of_lt hlt]
  rw [hthirdIndex] at hsum
  have hdefectSum :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        defectOrder (K := K) (-(tail 0 * tail 1)) +
          defectOrder (K := K) (-(tail 1 * tail 2)) := by
    have hsumTop :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) =
          (a.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) +
            (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
      exact_mod_cast hsum.symm.trans (add_comm _ _)
    rw [hsumTop]
    exact WithTop.add_lt_add_of_le_of_lt WithTop.coe_ne_top
      hfirstDefect hsecondDefect
  have hhilbert :
      hilbertSymbol K (-(tail 0 * tail 1)) (-(tail 1 * tail 2)) = 1 :=
    hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e hdefectSum
  have htailIsotropic :
      DiagonalIsotropic (diagonalUnitCoefficients tail) :=
    (diagonalUnitTernary_isotropic_iff_adjacentHilbertOne tail).mpr hhilbert
  exact (a.not_lemma814ExceptionC_of_isotropicUnitComplement
    c.firstUnarySegment C.rank_four tail (by
      simpa only [c.firstUnarySegment_valueUnit_zero] using htailRep)
        htailIsotropic) C

/-- The strict source-order branch `S₁ < S₃` of Lemma 9.1 excludes
exception (c): condition (iii′) gives the binary prefix representation and
Lemma 8.1(ii) makes the second adjacent Hilbert defect strict. -/
theorem not_lemma814ExceptionC_of_equalSecondOrder_of_sourceFirstThird_lt
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (hsourceOuter : c.order (0 : Fin (S + 2)) <
      c.order (2 : Fin (S + 2))) :
    ¬a.Beli2019Lemma814ExceptionC c.firstUnarySegment := by
  intro C
  have hbinary :=
    a.binaryPrefixRepresentation_of_exceptionC_of_firstThird_lt
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree hsourceOuter C
  have hmixed :=
    a.targetSecondAlpha_lt_firstFour_sourceFirstTwoRawDefect_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree C
  exact a.false_of_exceptionC_of_binaryPrefix_of_mixedRaw
    c hbinary hmixed C

/-- The revised condition-(iii′) inequality at `i = 4`. -/
noncomputable def lemma91TernaryCentralDefectInequality
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hfive : 4 < N + 3) : Prop :=
  (((2 * (ramificationIndex K : ℚ) +
      (c.order (2 : Fin (S + 2)) : ℚ) -
        (a.order ⟨4, hfive⟩ : ℚ)) : ℚ) : WithTop ℚ) <
    a.truncatedPrefixDefect c (-1) 4 2 +
      a.truncatedPrefixDefect c (-1) 5 3

/-- Condition (iii′) at `i = 4` converts the displayed strict defect
inequality into representation of the source ternary prefix by the target
quaternary prefix. -/
theorem ternaryPrefixRepresentation_of_quaternaryCentralDefectInequality
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (conditions : RepresentationConditions a c hRank)
    (hfive : 4 < N + 3) (hthree : 1 < S + 1)
    (horder : c.order (2 : Fin (S + 2)) < a.order ⟨4, hfive⟩)
    (hdefect : a.lemma91TernaryCentralDefectInequality c hfive) :
    DiagonalRepresents
      (c.prefixValues 3 (by omega))
      (a.prefixValues 4 (by omega)) := by
  let i := lemma91QuaternaryCentralIndex hfive hthree
  have htriggers : a.CentralTriggerEquivalence c :=
    a.beli2019Lemma216 (sourceLaws := targetLaws)
      (targetLaws := sourceLaws) c hRank conditions.orderCondition
        conditions.defectCondition
  have hprime : a.CentralRepresentationConditionsPrime c :=
    (a.centralRepresentationConditions_iff_prime c htriggers).mp
      conditions.centralRepresentations
  have hsourceThird :
      (⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : Fin (S + 2)) = (2 : Fin (S + 2)) := by
    have hlt : 2 < S + 2 := by omega
    apply Fin.ext
    simp [i, lemma91QuaternaryCentralIndex,
      Nat.mod_eq_of_lt hlt]
  have htargetFifth :
      (⟨i.val, by have := i.lt_large; omega⟩ : Fin (N + 3)) =
        ⟨4, hfive⟩ := by
    apply Fin.ext
    rfl
  have htrigger : a.centralDefectTrigger c i := by
    constructor
    · rw [hsourceThird, htargetFifth]
      exact horder
    · rw [hsourceThird, htargetFifth]
      simpa [i, lemma91QuaternaryCentralIndex,
        centralPreviousDefect, centralCurrentDefect,
        lemma91TernaryCentralDefectInequality] using hdefect
  simpa [i, lemma91QuaternaryCentralIndex] using hprime i htrigger

/-- If the target has rank four, ambient representation directly supplies
the source ternary-prefix representation used in the paper. -/
theorem ternaryPrefixRepresentation_of_ambient_rankFour
    (a : GoodBONG q L 4) (c : GoodBONG r M (S + 2))
    (hthree : 1 < S + 1) (ambient : q.Represents r) :
    DiagonalRepresents
      (c.prefixValues 3 (by omega))
      (a.prefixValues 4 (Nat.le_refl _)) := by
  let w := c.toBONG.segmentWitness 0 3 (by omega)
  let inclusion : QuadraticSpace.Representation
      (r.restrict w.carrier w.nondegenerate) r :=
    { toLinearMap := Submodule.subtype w.carrier
      injective := Subtype.val_injective
      map_bilin _ _ := rfl }
  have hsegment : q.Represents (r.restrict w.carrier w.nondegenerate) :=
    ambient.trans ⟨inclusion⟩
  have hdiagonal :=
    a.toBONG.diagonalRepresents_of_ambient w.bong hsegment
  convert hdiagonal using 1
  · funext i
    unfold prefixValues
    rw [w.value_eq]
    apply congrArg c.toBONG.value
    apply Fin.ext
    simp [BONG.SegmentWitness.sourceIndex]
  · funext i
    rfl

/-- When both the target fifth coefficient and the source fourth coefficient
exist, the equal-outer-order branch of exception (c) is impossible. -/
theorem not_lemma814ExceptionC_of_equalSecondOrder_of_sourceFirstThird_eq_ordinary
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hsourceOuter : c.order (0 : Fin (S + 2)) =
      c.order (2 : Fin (S + 2)))
    (hfive : 4 < N + 3) (hsourceFour : 4 ≤ S + 2) :
    ¬a.Beli2019Lemma814ExceptionC c.firstUnarySegment := by
  intro C
  have hthree : 1 < S + 1 := by omega
  have hternary :=
    a.ternaryPrefixRepresentation_of_exceptionC_of_sourceFirstThird_eq_ordinary
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hsourceOuter hfive hsourceFour C
  have hadjacent :=
    a.thirdAlpha_le_sourceSecondAdjacentDefect_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree hsourceOuter C
  have hmixed :=
    a.targetSecondAlpha_lt_firstFour_sourceFirstTwoRawDefect_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree C
  exact a.false_of_exceptionC_of_ternaryPrefix_of_adjacent_of_mixedRaw
    c hthree C hternary hadjacent hmixed

/-- In target rank four, ambient representation replaces condition (iii) and
directly supplies the ternary-prefix representation needed to exclude
exception (c). -/
theorem not_lemma814ExceptionC_of_equalSecondOrder_rankFour
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L 4) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ 3)
    (hfirst : a.order (0 : Fin 4) = c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin 4) = c.order (1 : Fin (S + 2)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (hsourceOuter : c.order (0 : Fin (S + 2)) =
      c.order (2 : Fin (S + 2))) :
    ¬a.Beli2019Lemma814ExceptionC c.firstUnarySegment := by
  intro C
  have hternary :=
    a.ternaryPrefixRepresentation_of_ambient_rankFour c hthree ambient
  have hadjacent :=
    a.thirdAlpha_le_sourceSecondAdjacentDefect_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree hsourceOuter C
  have hmixed :=
    a.targetSecondAlpha_lt_firstFour_sourceFirstTwoRawDefect_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hthree C
  exact a.false_of_exceptionC_of_ternaryPrefix_of_adjacent_of_mixedRaw
    c hthree C hternary hadjacent hmixed

/-- For a ternary source and target rank at least five, the terminal
condition-(iii) representation gives the same geometric contradiction. -/
theorem not_lemma814ExceptionC_of_equalSecondOrder_sourceRankThree
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M 3)
    (hRank : 2 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) = c.order (0 : Fin 3))
    (hsecond : a.order (1 : Fin (N + 3)) = c.order (1 : Fin 3))
    (conditions : RepresentationConditions a c hRank)
    (hsourceOuter : c.order (0 : Fin 3) = c.order (2 : Fin 3))
    (hfive : 4 < N + 3) :
    ¬a.Beli2019Lemma814ExceptionC c.firstUnarySegment := by
  intro C
  have hternary :=
    a.ternaryPrefixRepresentation_of_exceptionC_of_sourceRankThree
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hsourceOuter hfive C
  have hadjacent :=
    a.thirdAlpha_le_sourceSecondAdjacentDefect_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions (by omega) hsourceOuter C
  have hmixed :=
    a.targetSecondAlpha_lt_firstFour_sourceFirstTwoRawDefect_of_exceptionC
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions (by omega) C
  exact a.false_of_exceptionC_of_ternaryPrefix_of_adjacent_of_mixedRaw
    c (by omega) C hternary hadjacent hmixed

/-- For a binary source, its only binary alpha is the source first alpha, so
the equal-order rigidity identifies the raw first adjacent defect with the
target second alpha. -/
theorem sourceFirstAdjacentDefect_eq_targetSecond_of_exceptionC_sourceRankTwo
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M 2)
    (hRank : 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) = c.order (0 : Fin 2))
    (hsecond : a.order (1 : Fin (N + 3)) = c.order (1 : Fin 2))
    (conditions : RepresentationConditions a c hRank)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    c.adjacentDefect (0 : Fin 1) =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
  have hrigidity := a.secondOrderRigidity_of_exceptionBC
    c hRank hfirst hsecond conditions (Or.inr C)
  have hbinary : c.firstBinaryAlpha =
      (c.alphaValue (0 : Fin 1) : WithTop ℚ) := by
    unfold firstBinaryAlpha
    exact c.binary_alpha_eq_min_candidates.symm
  exact a.sourceFirstAdjacentDefect_eq_targetSecond_of_firstBinary_exceptionC
    (targetLaws := targetLaws) c hfirst hsecond hrigidity.2 hbinary C

/-- Lemma 8.1(ii) removes the raw mixed-defect cap for a binary source. -/
theorem targetSecondAlpha_lt_firstFour_sourceRankTwoRawDefect_of_exceptionC
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M 2)
    (hRank : 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) = c.order (0 : Fin 2))
    (hsecond : a.order (1 : Fin (N + 3)) = c.order (1 : Fin 2))
    (conditions : RepresentationConditions a c hRank)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
      defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct 4 * c.prefixProduct 2) := by
  let x := c.adjacentProduct (0 : Fin 1)
  let z := a.prefixProduct 4
  have hx : defectOrder (K := K) x =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
    change c.adjacentDefect (0 : Fin 1) = _
    exact
      a.sourceFirstAdjacentDefect_eq_targetSecond_of_exceptionC_sourceRankTwo
        (targetLaws := targetLaws) c hRank hfirst hsecond conditions C
  have hz : defectOrder (K := K) z =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) :=
    a.lemma814FirstFourRawDefect_eq_secondAlpha_of_exceptionC
      c.firstUnarySegment C
  have hdefectEq : quadraticDefect K x = quadraticDefect K z :=
    quadraticDefect_eq_of_defectOrder_eq x z (hx.trans hz.symm)
  have hxFinite : quadraticDefect K x ≠ ⊤ :=
    quadraticDefect_ne_top_of_defectOrder_eq_coe x
      (a.alphaValue (1 : Fin (N + 2))) hx
  have hstrict := beli2019Lemma81_ii_strict
    C.residueTwo x z hdefectEq hxFinite
  have hstrictOrder :=
    defectOrder_lt_of_quadraticDefect_lt x (x * z) hstrict
  have hproduct : x * z =
      (-1 : Kˣ) * a.prefixProduct 4 * c.prefixProduct 2 := by
    unfold x z
    rw [c.prefixProduct_add_two 0 (by omega),
      show c.prefixProduct 0 = 1 by exact c.toBONG.prefixProduct_zero]
    unfold adjacentProduct
    have hcast : (0 : Fin 1).castSucc = (0 : Fin 2) := by
      apply Fin.ext
      rfl
    have hsucc : (0 : Fin 1).succ = (1 : Fin 2) := by
      apply Fin.ext
      rfl
    rw [hcast, hsucc]
    have hzero : (⟨0, by omega⟩ : Fin 2) = (0 : Fin 2) := by
      apply Fin.ext
      rfl
    have hone : (⟨1, by omega⟩ : Fin 2) = (1 : Fin 2) := by
      apply Fin.ext
      rfl
    rw [hzero, hone]
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_one, one_mul]
    ring
  rw [hproduct, hx] at hstrictOrder
  exact hstrictOrder

/-- Since the source prefix is the whole binary source, its endpoint cap is
`⊤`; the strict raw estimate therefore gives the capped mixed estimate. -/
theorem targetSecondAlpha_lt_firstFour_sourceRankTwoCappedDefect_of_exceptionC
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M 2)
    (hRank : 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) = c.order (0 : Fin 2))
    (hsecond : a.order (1 : Fin (N + 3)) = c.order (1 : Fin 2))
    (conditions : RepresentationConditions a c hRank)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 4 2 := by
  have hraw :=
    a.targetSecondAlpha_lt_firstFour_sourceRankTwoRawDefect_of_exceptionC
      (targetLaws := targetLaws)
        c hRank hfirst hsecond conditions C
  have htargetCap :
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
        a.prefixAlphaCap 4 := by
    by_cases hfive : 5 ≤ N + 3
    · rw [a.prefixAlphaCap_of_internal (i := 4) (by omega) (by omega)]
      have hlater := C.laterAlpha_strict hfive
      have hsecondComplement := C.secondAlpha_eq_complement
      exact_mod_cast hsecondComplement.symm ▸ hlater
    · have hlast : 4 = N + 3 := by
        have := C.rank_four
        omega
      rw [hlast, a.prefixAlphaCap_last]
      exact WithTop.coe_lt_top _
  unfold truncatedPrefixDefect
  rw [c.prefixAlphaCap_last, min_top_right]
  exact lt_min hraw htargetCap

/-- In source rank two, the strict capped mixed defect verifies the revised
condition-(iii′) determinant inequality at `i = 3`. -/
theorem lemma91BinaryCentralDefectInequality_of_exceptionC_sourceRankTwo
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M 2)
    (hRank : 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) = c.order (0 : Fin 2))
    (hsecond : a.order (1 : Fin (N + 3)) = c.order (1 : Fin 2))
    (conditions : RepresentationConditions a c hRank)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    a.lemma91BinaryCentralDefectInequality c
      (by have := C.rank_four; omega) := by
  have hrigidity := a.secondOrderRigidity_of_exceptionBC
    c hRank hfirst hsecond conditions (Or.inr C)
  have hfull := a.fullFirstThirdDefect_eq_sourceFirstAlpha_of_exceptionBC
    c hRank hfirst hsecond conditions (Or.inr C)
  have hmixed :=
    a.targetSecondAlpha_lt_firstFour_sourceRankTwoCappedDefect_of_exceptionC
      (targetLaws := targetLaws)
        c hRank hfirst hsecond conditions C
  have hrelation :=
    a.firstAlpha_eq_secondFourthShift_thirdAlpha_of_exceptionC
      c.firstUnarySegment C
  have hsum :=
    a.secondAlpha_add_thirdAlpha_eq_twoE_of_lemma814ExceptionC
      c.firstUnarySegment C (by have := C.rank_four; omega)
  have hthirdIndex :
      (⟨2, by have := C.rank_four; omega⟩ : Fin (N + 2)) =
        (2 : Fin (N + 2)) := by
    have hlt : 2 < N + 2 := by
      have := C.rank_four
      omega
    apply Fin.ext
    change 2 = 2 % (N + 2)
    rw [Nat.mod_eq_of_lt hlt]
  rw [hthirdIndex] at hsum
  have hconstantQ :
      2 * (ramificationIndex K : ℚ) +
          (c.order (1 : Fin 2) : ℚ) -
            (a.order (3 : Fin (N + 3)) : ℚ) =
        a.alphaValue (0 : Fin (N + 2)) +
          a.alphaValue (1 : Fin (N + 2)) := by
    rw [← hsecond]
    push_cast at hrelation
    linarith
  have hconstantTop :
      (((2 * (ramificationIndex K : ℚ) +
        (c.order (1 : Fin 2) : ℚ) -
          (a.order (3 : Fin (N + 3)) : ℚ) : ℚ)) : WithTop ℚ) =
        (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) +
          (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
    exact_mod_cast hconstantQ
  unfold lemma91BinaryCentralDefectInequality
  have hfourthIndex :
      (⟨3, by have := C.rank_four; omega⟩ : Fin (N + 3)) =
        (3 : Fin (N + 3)) := by
    have hlt : 3 < N + 3 := by
      have := C.rank_four
      omega
    apply Fin.ext
    change 3 = 3 % (N + 3)
    rw [Nat.mod_eq_of_lt hlt]
  rw [hfourthIndex, hfull, hrigidity.2, hconstantTop]
  exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mpr hmixed

/-- The revised condition-(iii′) implication gives the binary-prefix
representation for a binary source. -/
theorem binaryPrefixRepresentation_of_exceptionC_sourceRankTwo
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M 2)
    (hRank : 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) = c.order (0 : Fin 2))
    (hsecond : a.order (1 : Fin (N + 3)) = c.order (1 : Fin 2))
    (conditions : RepresentationConditions a c hRank)
    (C : a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    DiagonalRepresents
      (c.prefixValues 2 (Nat.le_refl _))
      (a.prefixValues 3 (by omega)) := by
  have hfour : 3 < N + 3 := by
    have := C.rank_four
    omega
  have hdefect :=
    a.lemma91BinaryCentralDefectInequality_of_exceptionC_sourceRankTwo
      (targetLaws := targetLaws)
        c hRank hfirst hsecond conditions C
  have horder : c.order (1 : Fin 2) < a.order ⟨3, hfour⟩ := by
    rw [← hsecond]
    convert C.secondFourthOrders_lt using 1
  exact a.binaryPrefixRepresentation_of_centralDefectInequality
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      c hRank conditions hfour horder hdefect

/-- Complete exception-(c) exclusion for a binary source. -/
theorem not_lemma814ExceptionC_of_equalSecondOrder_sourceRankTwo
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M 2)
    (hRank : 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) = c.order (0 : Fin 2))
    (hsecond : a.order (1 : Fin (N + 3)) = c.order (1 : Fin 2))
    (conditions : RepresentationConditions a c hRank) :
    ¬a.Beli2019Lemma814ExceptionC c.firstUnarySegment := by
  intro C
  have hbinary :=
    a.binaryPrefixRepresentation_of_exceptionC_sourceRankTwo
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions C
  have hmixed :=
    a.targetSecondAlpha_lt_firstFour_sourceRankTwoRawDefect_of_exceptionC
      (targetLaws := targetLaws)
        c hRank hfirst hsecond conditions C
  exact a.false_of_exceptionC_of_binaryPrefix_of_mixedRaw
    c hbinary hmixed C

/-- The equal source-outer-order branch is excluded for every source of rank
at least three: target rank four uses ambient representation, source rank
three uses Definition 4, and the remaining ranks use the ordinary `A₄`. -/
theorem not_lemma814ExceptionC_of_equalSecondOrder_of_sourceFirstThird_eq
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1)
    (hsourceOuter : c.order (0 : Fin (S + 2)) =
      c.order (2 : Fin (S + 2))) :
    ¬a.Beli2019Lemma814ExceptionC c.firstUnarySegment := by
  intro C
  by_cases hfive : 4 < N + 3
  · by_cases hsourceFour : 4 ≤ S + 2
    · exact
        (a.not_lemma814ExceptionC_of_equalSecondOrder_of_sourceFirstThird_eq_ordinary
          (targetLaws := targetLaws) (sourceLaws := sourceLaws)
            c hRank hfirst hsecond conditions hsourceOuter hfive hsourceFour) C
    · have hS : S = 1 := by omega
      subst S
      exact
        (a.not_lemma814ExceptionC_of_equalSecondOrder_sourceRankThree
          (targetLaws := targetLaws) (sourceLaws := sourceLaws)
            c hRank hfirst hsecond conditions hsourceOuter hfive) C
  · have hN : N = 1 := by
      have := C.rank_four
      omega
    subst N
    exact
      (a.not_lemma814ExceptionC_of_equalSecondOrder_rankFour
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          c hRank hfirst hsecond ambient conditions hthree hsourceOuter) C

/-- Exception (c) is excluded for every source of rank at least three.  The
good-BONG inequality `S₁ ≤ S₃` divides the proof into the strict binary-prefix
branch and the equal ternary-prefix branch. -/
theorem not_lemma814ExceptionC_of_equalSecondOrder_sourceRankAtLeastThree
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c hRank)
    (hthree : 1 < S + 1) :
    ¬a.Beli2019Lemma814ExceptionC c.firstUnarySegment := by
  have hsourceLe : c.order (0 : Fin (S + 2)) ≤
      c.order (2 : Fin (S + 2)) := by
    let sourceFirst : Fin (S + 2) := ⟨0, by omega⟩
    let sourceThird : Fin (S + 2) := ⟨2, by omega⟩
    have hgood := c.good sourceFirst (by
      dsimp only [sourceFirst]
      omega)
    change c.order sourceFirst ≤ c.order sourceThird at hgood
    have hsourceFirst : sourceFirst = (0 : Fin (S + 2)) := by
      apply Fin.ext
      rfl
    have hsourceThird : sourceThird = (2 : Fin (S + 2)) := by
      have hlt : 2 < S + 2 := by omega
      apply Fin.ext
      simp [sourceThird, Nat.mod_eq_of_lt hlt]
    rw [hsourceFirst, hsourceThird] at hgood
    exact hgood
  rcases lt_or_eq_of_le hsourceLe with hstrict | hequal
  · exact
      a.not_lemma814ExceptionC_of_equalSecondOrder_of_sourceFirstThird_lt
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          c hRank hfirst hsecond conditions hthree hstrict
  · exact
      a.not_lemma814ExceptionC_of_equalSecondOrder_of_sourceFirstThird_eq
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          c hRank hfirst hsecond ambient conditions hthree hequal

/-- Complete exception-(c) exclusion in the equal-first/equal-second-order
branch, uniformly in the source and target ranks. -/
theorem not_lemma814ExceptionC_of_equalSecondOrder
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c hRank) :
    ¬a.Beli2019Lemma814ExceptionC c.firstUnarySegment := by
  by_cases hthree : 1 < S + 1
  · exact
      a.not_lemma814ExceptionC_of_equalSecondOrder_sourceRankAtLeastThree
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          c hRank hfirst hsecond ambient conditions hthree
  · have hS : S = 0 := by omega
    subst S
    exact a.not_lemma814ExceptionC_of_equalSecondOrder_sourceRankTwo
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions

end BONG.GoodBONG

end Bong
