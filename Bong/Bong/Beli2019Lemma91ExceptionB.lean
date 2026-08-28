/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma91ExceptionA

/-!
# Beli (2019), Lemma 9.1: the exception-(b) branch

Exception (b) shares the source-cap rigidity of exception (c).  In target
rank at least four its strict `alpha_2 + alpha_3` inequality, condition (ii),
P1, and capped-defect domination verify condition (iii') at `i = 3`.  Thus
the same binary-prefix representation used in exception (a) is available.
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

set_option maxHeartbeats 800000 in
-- The proof normalizes the first three alpha/order indices and then reuses
-- the source-cap arithmetic already isolated for exception (a).
/-- In target rank at least four, exception (b) forces the strict revised-v2
condition-(iii') defect inequality. -/
theorem lemma91BinaryCentralDefectInequality_of_exceptionB
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hfour : 3 < N + 3)
    (B : a.Beli2019Lemma814ExceptionB c.firstUnarySegment) :
    a.lemma91BinaryCentralDefectInequality c hfour := by
  let firstAlpha : Fin (N + 2) := ⟨0, by omega⟩
  let secondAlpha : Fin (N + 2) := ⟨1, by omega⟩
  let thirdAlpha : Fin (N + 2) := ⟨2, by omega⟩
  let secondOrder : Fin (N + 3) := ⟨1, by omega⟩
  let thirdOrder : Fin (N + 3) := ⟨2, by omega⟩
  let fourthOrder : Fin (N + 3) := ⟨3, hfour⟩
  have hfirstAlpha : (0 : Fin (N + 2)) = firstAlpha := by
    apply Fin.ext
    rfl
  have hsecondAlpha : (1 : Fin (N + 2)) = secondAlpha := by
    apply Fin.ext
    simp [secondAlpha, Nat.mod_eq_of_lt (by omega : 1 < N + 2)]
  have hthirdAlpha : (2 : Fin (N + 2)) = thirdAlpha := by
    apply Fin.ext
    simp [thirdAlpha, Nat.mod_eq_of_lt (by omega : 2 < N + 2)]
  have hsecondOrder : (1 : Fin (N + 3)) = secondOrder := by
    apply Fin.ext
    simp [secondOrder, Nat.mod_eq_of_lt (by omega : 1 < N + 3)]
  have hthirdOrder : (2 : Fin (N + 3)) = thirdOrder := by
    apply Fin.ext
    simp [thirdOrder, Nat.mod_eq_of_lt (by omega : 2 < N + 3)]
  have hfull :=
    a.fullFirstThirdDefect_eq_sourceFirstAlpha_of_exceptionBC
      c hRank hfirst hsecond conditions (Or.inl B)
  have hrigidity :=
    a.secondRepresentationAlpha_eq_targetSecond_and_sourceFirst_eq_targetFirst
      c hRank hfirst B.firstThirdOrders_eq hsecond conditions hfull
  have hsourceTargetAlpha : c.alphaValue (0 : Fin (S + 1)) =
      a.alphaValue firstAlpha := by
    simpa only [hfirstAlpha] using hrigidity.2
  have hfullTarget : a.truncatedPrefixDefect c (-1) 3 1 =
      (a.alphaValue firstAlpha : WithTop ℚ) := by
    rw [hfull, hsourceTargetAlpha]
  have hfirstRelation : a.alphaValue firstAlpha =
      (a.order secondOrder : ℚ) - (a.order thirdOrder : ℚ) +
        a.alphaValue secondAlpha := by
    have hremark :=
      (a.beli2019Remark87 (0 : Fin (N + 1))
        B.firstThirdOrders_eq).previousAlpha_eq
    dsimp only [remark87PreviousAlpha, remark87CurrentAlpha,
      remark87MiddleValue, remark87NextValue] at hremark
    change a.alphaValue firstAlpha =
      (((a.order secondOrder - a.order thirdOrder : Int) : ℚ) +
        a.alphaValue secondAlpha) at hremark
    push_cast at hremark
    exact hremark
  have hnext : secondAlpha.val + 1 < N + 2 := by
    change 1 + 1 < N + 2
    omega
  have hrightQ : -(a.order fourthOrder : ℚ) +
      a.alphaValue thirdAlpha ≤
        -(a.order thirdOrder : ℚ) + a.alphaValue secondAlpha := by
    have hp1 := (a.alpha_p1 secondAlpha hnext).2
    change -(a.order fourthOrder : ℚ) + a.alphaValue thirdAlpha ≤
      -(a.order thirdOrder : ℚ) + a.alphaValue secondAlpha at hp1
    exact hp1
  have halphaSum : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue secondAlpha + a.alphaValue thirdAlpha := by
    have h := B.laterAlphaSum_strict (by omega : 4 ≤ N + 3)
    simpa only [hsecondAlpha, hthirdAlpha] using h
  obtain ⟨hprefixQ, hadjacentQ⟩ :=
    lemma91ExceptionASourceCapArithmetic halphaSum le_rfl
      hfirstRelation hrightQ
  have hprefixLower : (a.alphaValue secondAlpha : WithTop ℚ) ≤
      a.truncatedPrefixDefect c 1 2 2 := by
    let second := secondRepresentationIndex N S
    have hcondition := conditions.defectCondition second
    rw [a.coe_representationAlphaValue c second,
      show second = secondRepresentationIndex N S by rfl,
      hrigidity.1, hsecondAlpha] at hcondition
    exact hcondition
  have hadjacentLower :
      (((((a.order thirdOrder - a.order fourthOrder : Int) : ℚ) +
        a.alphaValue thirdAlpha : ℚ)) : WithTop ℚ) ≤
          a.truncatedPrefixDefect a (-1) 2 4 := by
    have hlocal := a.order_sub_add_alpha_le_cappedAdjacent thirdAlpha
    change (((((a.order thirdOrder - a.order fourthOrder : Int) : ℚ) +
      a.alphaValue thirdAlpha : ℚ)) : WithTop ℚ) ≤
        a.truncatedPrefixDefect a (-1) 2 4 at hlocal
    exact hlocal
  have hprefixStrict :
      (((2 * (ramificationIndex K : ℚ) +
        (a.order secondOrder : ℚ) -
          (a.order fourthOrder : ℚ) : ℚ)) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1 +
          a.truncatedPrefixDefect c 1 2 2 := by
    have hlowerStrict :
        (((2 * (ramificationIndex K : ℚ) +
          (a.order secondOrder : ℚ) -
            (a.order fourthOrder : ℚ) : ℚ)) : WithTop ℚ) <
          a.truncatedPrefixDefect c (-1) 3 1 +
            (a.alphaValue secondAlpha : WithTop ℚ) := by
      rw [hfullTarget]
      exact_mod_cast hprefixQ
    exact hlowerStrict.trans_le (add_le_add le_rfl hprefixLower)
  have hadjacentStrict :
      (((2 * (ramificationIndex K : ℚ) +
        (a.order secondOrder : ℚ) -
          (a.order fourthOrder : ℚ) : ℚ)) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1 +
          a.truncatedPrefixDefect a (-1) 2 4 := by
    have hlowerStrict :
        (((2 * (ramificationIndex K : ℚ) +
          (a.order secondOrder : ℚ) -
            (a.order fourthOrder : ℚ) : ℚ)) : WithTop ℚ) <
          a.truncatedPrefixDefect c (-1) 3 1 +
            (((((a.order thirdOrder - a.order fourthOrder : Int) : ℚ) +
              a.alphaValue thirdAlpha : ℚ)) : WithTop ℚ) := by
      rw [hfullTarget]
      exact_mod_cast hadjacentQ
    exact hlowerStrict.trans_le (add_le_add le_rfl hadjacentLower)
  have hminimumStrict :
      (((2 * (ramificationIndex K : ℚ) +
        (a.order secondOrder : ℚ) -
          (a.order fourthOrder : ℚ) : ℚ)) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1 +
          min (a.truncatedPrefixDefect a (-1) 2 4)
            (a.truncatedPrefixDefect c 1 2 2) := by
    rw [add_min]
    exact lt_min hadjacentStrict hprefixStrict
  have hdomination :=
    a.min_thirdAdjacent_secondPrefix_le_firstFourthDefect c
  have hfinal := hminimumStrict.trans_le (add_le_add le_rfl hdomination)
  unfold lemma91BinaryCentralDefectInequality
  rw [← hsecond, hsecondOrder]
  exact hfinal

/-- The ordinary representation-alpha index `i = 3`, available when both
the target has a fourth coefficient and the source has a third one. -/
def lemma91ThirdRepresentationIndex
    (hfour : 3 < N + 3) (hthree : 1 < S + 1) :
    RepresentationIndex (N + 3) (S + 2) where
  val := 3
  pos := by omega
  lt_large := hfour
  le_small := by omega

@[simp]
theorem lemma91ThirdRepresentationIndex_val
    (hfour : 3 < N + 3) (hthree : 1 < S + 1) :
    (lemma91ThirdRepresentationIndex hfour hthree).val = 3 :=
  rfl

set_option maxHeartbeats 1000000 in
-- The proof uses the Lemma 2.7 previous-defect normal form for the optional
-- secondary candidate of A₃.  This is the paper's displayed A₃ estimate.
/-- In exception (b), the third representation alpha lies strictly above
`S₁ - S₃ + α₁`.  This lower bound will force both the source third alpha
and the determinant defect `d(a₁,₃b₁,₃)` above the same threshold. -/
theorem thirdRepresentationAlpha_strict_of_exceptionB
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hfour : 3 < N + 3)
    (hthree : 1 < S + 1)
    (hsecondFourth : a.order (1 : Fin (N + 3)) <
      a.order ⟨3, hfour⟩)
    (B : a.Beli2019Lemma814ExceptionB c.firstUnarySegment) :
    (((c.order (0 : Fin (S + 2)) : ℚ) -
        (c.order (2 : Fin (S + 2)) : ℚ) +
          a.alphaValue (0 : Fin (N + 2)) : ℚ) : WithTop ℚ) <
      a.representationAlpha c
        (lemma91ThirdRepresentationIndex hfour hthree) := by
  let i := lemma91ThirdRepresentationIndex hfour hthree
  let firstAlpha : Fin (N + 2) := ⟨0, by omega⟩
  let secondAlpha : Fin (N + 2) := ⟨1, by omega⟩
  let thirdAlpha : Fin (N + 2) := ⟨2, by omega⟩
  let firstOrder : Fin (N + 3) := ⟨0, by omega⟩
  let secondOrder : Fin (N + 3) := ⟨1, by omega⟩
  let thirdOrder : Fin (N + 3) := ⟨2, by omega⟩
  let fourthOrder : Fin (N + 3) := ⟨3, hfour⟩
  let sourceFirst : Fin (S + 2) := ⟨0, by omega⟩
  let sourceSecond : Fin (S + 2) := ⟨1, by omega⟩
  let sourceThird : Fin (S + 2) := ⟨2, by omega⟩
  have hFirstAlpha : firstAlpha = (0 : Fin (N + 2)) := by
    apply Fin.ext
    rfl
  have hSourceFirst : sourceFirst = (0 : Fin (S + 2)) := by
    apply Fin.ext
    rfl
  have hSourceSecond : sourceSecond = (1 : Fin (S + 2)) := by
    apply Fin.ext
    simp [sourceSecond, Nat.mod_eq_of_lt (by omega : 1 < S + 2)]
  have hSourceThird : sourceThird = (2 : Fin (S + 2)) := by
    apply Fin.ext
    simp [sourceThird, Nat.mod_eq_of_lt (by omega : 2 < S + 2)]
  have hFourthOrder : fourthOrder = (⟨3, hfour⟩ : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have hfull :=
    a.fullFirstThirdDefect_eq_sourceFirstAlpha_of_exceptionBC
      c hRank hfirst hsecond conditions (Or.inl B)
  have hrigidity :=
    a.secondRepresentationAlpha_eq_targetSecond_and_sourceFirst_eq_targetFirst
      c hRank hfirst B.firstThirdOrders_eq hsecond conditions hfull
  have hsourceLeUnary :
      (a.alphaValue firstAlpha : WithTop ℚ) ≤
        a.lemma814FirstThirdCappedDefect c.firstUnarySegment := by
    calc
      (a.alphaValue firstAlpha : WithTop ℚ) =
          (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) := by
        exact_mod_cast hrigidity.2.symm
      _ = a.truncatedPrefixDefect c (-1) 3 1 := hfull.symm
      _ = min (a.lemma814FirstThirdCappedDefect c.firstUnarySegment)
          (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) :=
        a.fullFirstThirdDefect_eq_min_unary_sourceFirstAlpha c
      _ ≤ a.lemma814FirstThirdCappedDefect c.firstUnarySegment :=
        min_le_left _ _
  have hlater := B.laterAlphaSum_strict (by omega : 4 ≤ N + 3)
  have hlaterTop :
      ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) <
        (a.alphaValue secondAlpha : WithTop ℚ) +
          (a.alphaValue thirdAlpha : WithTop ℚ) := by
    exact_mod_cast hlater
  have hdefectSum := B.defectSum_eq
  have hunaryLtThird :
      a.lemma814FirstThirdCappedDefect c.firstUnarySegment <
        (a.alphaValue thirdAlpha : WithTop ℚ) := by
    have hsumLt :
        (a.alphaValue secondAlpha : WithTop ℚ) +
            a.lemma814FirstThirdCappedDefect c.firstUnarySegment <
          (a.alphaValue secondAlpha : WithTop ℚ) +
            (a.alphaValue thirdAlpha : WithTop ℚ) := by
      exact hdefectSum.trans_lt hlaterTop
    exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hsumLt
  have hfirstLtThird : a.alphaValue firstAlpha <
      a.alphaValue thirdAlpha := by
    exact_mod_cast hsourceLeUnary.trans_lt hunaryLtThird
  have htargetThirdHalf := a.alphaValue_le_halfGapValue thirdAlpha
  have htargetThirdHalfQ : a.alphaValue thirdAlpha ≤
      (((a.order fourthOrder - a.order thirdOrder : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ)) := by
    unfold halfGapValue orderGap at htargetThirdHalf
    have hcast : thirdAlpha.castSucc = thirdOrder := by
      apply Fin.ext
      rfl
    have hsucc : thirdAlpha.succ = fourthOrder := by
      apply Fin.ext
      rfl
    rw [hcast, hsucc] at htargetThirdHalf
    exact htargetThirdHalf
  have hsourceThirdOrder : a.order thirdOrder ≤ c.order sourceThird := by
    have hsourceSkip := c.good sourceFirst (by
      simp only [sourceFirst]
      omega)
    change c.order sourceFirst ≤ c.order sourceThird at hsourceSkip
    have houter := B.firstThirdOrders_eq
    change a.order firstOrder = a.order thirdOrder at houter
    calc
      a.order thirdOrder = a.order firstOrder := houter.symm
      _ = c.order sourceFirst := hfirst
      _ ≤ c.order sourceThird := hsourceSkip
  have hhalfQ :
      (c.order sourceFirst : ℚ) - (c.order sourceThird : ℚ) +
          a.alphaValue firstAlpha <
        ((a.order fourthOrder - c.order sourceThird : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) := by
    have houter := B.firstThirdOrders_eq
    change a.order firstOrder = a.order thirdOrder at houter
    have hfirst' : a.order firstOrder = c.order sourceFirst := hfirst
    have houterQ : (a.order firstOrder : ℚ) =
        (a.order thirdOrder : ℚ) := by exact_mod_cast houter
    have hfirstQ : (a.order firstOrder : ℚ) =
        (c.order sourceFirst : ℚ) := by exact_mod_cast hfirst'
    have hsourceThirdOrderQ : (a.order thirdOrder : ℚ) ≤
        (c.order sourceThird : ℚ) := by exact_mod_cast hsourceThirdOrder
    push_cast at htargetThirdHalfQ ⊢
    linarith
  have hhalf :
      (((c.order sourceFirst : ℚ) - (c.order sourceThird : ℚ) +
          a.alphaValue firstAlpha : ℚ) : WithTop ℚ) <
        a.representationHalfGap c i := by
    unfold representationHalfGap
    simpa only [i, lemma91ThirdRepresentationIndex,
      sourceThird, fourthOrder] using
        (show
          (((c.order sourceFirst : ℚ) - (c.order sourceThird : ℚ) +
            a.alphaValue firstAlpha : ℚ) : WithTop ℚ) <
              ((((a.order fourthOrder - c.order sourceThird : Int) : ℚ) /
                2 + (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) by
            exact_mod_cast hhalfQ)
  have hcentral :=
    a.lemma91BinaryCentralDefectInequality_of_exceptionB
      (targetLaws := targetLaws) c hRank hfirst hsecond conditions hfour B
  have hsumLeTop :
      (a.alphaValue secondAlpha : WithTop ℚ) +
          (a.alphaValue firstAlpha : WithTop ℚ) ≤
        ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    calc
      (a.alphaValue secondAlpha : WithTop ℚ) +
          (a.alphaValue firstAlpha : WithTop ℚ) ≤
        (a.alphaValue secondAlpha : WithTop ℚ) +
          a.lemma814FirstThirdCappedDefect c.firstUnarySegment :=
        add_le_add_right hsourceLeUnary _
      _ = ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) :=
        hdefectSum
  have hsumLeQ : a.alphaValue secondAlpha +
      a.alphaValue firstAlpha ≤ 2 * (ramificationIndex K : ℚ) := by
    exact_mod_cast hsumLeTop
  have hremark :=
    (a.beli2019Remark87 (0 : Fin (N + 1))
      B.firstThirdOrders_eq).currentAlpha_eq
  have hcurrent : a.alphaValue secondAlpha =
      ((a.order firstOrder - a.order secondOrder : Int) : ℚ) +
        a.alphaValue firstAlpha := by
    simpa [firstAlpha, secondAlpha, firstOrder, secondOrder,
      remark87CurrentAlpha, remark87PreviousAlpha,
      remark87PreviousValue, remark87MiddleValue] using hremark
  let threshold : ℚ :=
    (c.order sourceFirst : ℚ) - (c.order sourceThird : ℚ) +
      a.alphaValue firstAlpha
  let primaryShift : ℚ :=
    ((a.order fourthOrder - c.order sourceThird : Int) : ℚ)
  let centralBound : ℚ :=
    2 * (ramificationIndex K : ℚ) +
      (c.order sourceSecond : ℚ) - (a.order fourthOrder : ℚ)
  suffices hthreshold :
      (threshold : WithTop ℚ) < a.representationAlpha c i by
    dsimp only [threshold] at hthreshold
    rw [hSourceFirst, hSourceThird, hFirstAlpha] at hthreshold
    simpa only [i] using hthreshold
  have hconstant :
      a.alphaValue firstAlpha + (threshold - primaryShift) ≤
        centralBound := by
    dsimp only [threshold, primaryShift, centralBound]
    have houter := B.firstThirdOrders_eq
    change a.order firstOrder = a.order thirdOrder at houter
    have hfirst' : a.order firstOrder = c.order sourceFirst := hfirst
    have hsecond' : a.order secondOrder = c.order sourceSecond := hsecond
    have houterQ : (a.order firstOrder : ℚ) =
        (a.order thirdOrder : ℚ) := by exact_mod_cast houter
    have hfirstQ : (a.order firstOrder : ℚ) =
        (c.order sourceFirst : ℚ) := by exact_mod_cast hfirst'
    have hsecondQ : (a.order secondOrder : ℚ) =
        (c.order sourceSecond : ℚ) := by exact_mod_cast hsecond'
    push_cast at hcurrent ⊢
    linarith
  have hcentral' : (centralBound : WithTop ℚ) <
      (a.alphaValue firstAlpha : WithTop ℚ) +
        a.truncatedPrefixDefect c (-1) 4 2 := by
    unfold lemma91BinaryCentralDefectInequality at hcentral
    dsimp only [centralBound]
    rw [hSourceSecond, hFourthOrder, hFirstAlpha]
    simpa only [hfull, hrigidity.2] using hcentral
  have hprimaryTail : ((threshold - primaryShift : ℚ) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 4 2 := by
    have hlower :
        ((a.alphaValue firstAlpha + (threshold - primaryShift) : ℚ) :
            WithTop ℚ) <
          (a.alphaValue firstAlpha : WithTop ℚ) +
            a.truncatedPrefixDefect c (-1) 4 2 :=
      (WithTop.coe_le_coe.mpr hconstant).trans_lt hcentral'
    rw [WithTop.coe_add] at hlower
    exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hlower
  have hprimary : (threshold : WithTop ℚ) <
      a.representationPrimaryDefect c i := by
    unfold representationPrimaryDefect
    change (threshold : WithTop ℚ) <
      (primaryShift : WithTop ℚ) +
        a.truncatedPrefixDefect c (-1) 4 2
    calc
      (threshold : WithTop ℚ) =
          (primaryShift : WithTop ℚ) +
            ((threshold - primaryShift : ℚ) : WithTop ℚ) := by
        exact_mod_cast (by ring : threshold = primaryShift +
          (threshold - primaryShift))
      _ < (primaryShift : WithTop ℚ) +
          a.truncatedPrefixDefect c (-1) 4 2 :=
        (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mpr hprimaryTail
  have hcross : c.order sourceSecond ≤ a.order fourthOrder := by
    rw [hSourceSecond, hFourthOrder]
    exact hsecond.symm.trans_le hsecondFourth.le
  by_cases hinterior : 4 < N + 3
  · have htargetSkip : a.order thirdOrder ≤
        a.order (⟨4, hinterior⟩ : Fin (N + 3)) := by
      have hgood := a.good thirdOrder (by omega)
      change a.order thirdOrder ≤
        a.order (⟨thirdOrder.1 + 2, by omega⟩ : Fin (N + 3)) at hgood
      convert hgood using 1
    have hpreviousQ : threshold <
        ((a.order fourthOrder + a.order (⟨4, hinterior⟩ : Fin (N + 3)) -
          c.order sourceSecond - c.order sourceThird : Int) : ℚ) +
            a.alphaValue firstAlpha := by
      dsimp only [threshold]
      have houter := B.firstThirdOrders_eq
      change a.order firstOrder = a.order thirdOrder at houter
      have hfirst' : a.order firstOrder = c.order sourceFirst := hfirst
      have hsecond' : a.order secondOrder = c.order sourceSecond := hsecond
      have houterQ : (a.order firstOrder : ℚ) =
          (a.order thirdOrder : ℚ) := by exact_mod_cast houter
      have hfirstQ : (a.order firstOrder : ℚ) =
          (c.order sourceFirst : ℚ) := by exact_mod_cast hfirst'
      have hsecondQ : (a.order secondOrder : ℚ) =
          (c.order sourceSecond : ℚ) := by exact_mod_cast hsecond'
      have hsecondFourthQ : (a.order secondOrder : ℚ) <
          (a.order fourthOrder : ℚ) := by
        exact_mod_cast hsecondFourth
      have htargetSkipQ : (a.order thirdOrder : ℚ) ≤
          (a.order (⟨4, hinterior⟩ : Fin (N + 3)) : ℚ) := by
        exact_mod_cast htargetSkip
      push_cast
      linarith
    have hprevious : (threshold : WithTop ℚ) <
        a.representationSecondaryPreviousDefect c i
          (by simp only [i, lemma91ThirdRepresentationIndex]; omega) := by
      unfold representationSecondaryPreviousDefect
      change (threshold : WithTop ℚ) <
        ((((a.order fourthOrder +
          a.order (⟨4, hinterior⟩ : Fin (N + 3)) -
          c.order sourceSecond - c.order sourceThird : Int) : ℚ) :
            WithTop ℚ) + a.truncatedPrefixDefect c (-1) 3 1)
      rw [hfull, hrigidity.2]
      have hpreviousTop : (threshold : WithTop ℚ) <
          ((((a.order fourthOrder +
            a.order (⟨4, hinterior⟩ : Fin (N + 3)) -
            c.order sourceSecond - c.order sourceThird : Int) : ℚ) :
              WithTop ℚ) +
            (a.alphaValue firstAlpha : WithTop ℚ)) := by
        exact_mod_cast hpreviousQ
      rw [hFirstAlpha] at hpreviousTop
      exact hpreviousTop
    rw [a.representationAlpha_eq_min_halfGap_prime c i,
      a.representationAlphaPrime_eq_min_primary_previous c i
        (by simp only [i, lemma91ThirdRepresentationIndex]; omega) hcross]
    exact lt_min hhalf (lt_min hprimary hprevious)
  · have hN : N = 1 := by omega
    subst N
    rw [a.representationAlpha_eq_min_halfGap_prime c i,
      a.representationAlphaPrime_eq_primary_of_not_interior c i
        (by simp only [i, lemma91ThirdRepresentationIndex]; omega)]
    exact lt_min hhalf hprimary

/-- Condition (ii) turns the strict `A₃` estimate into simultaneous strict
lower bounds for the raw equal-prefix defect and the source-side prefix cap.
Keeping both consequences together mirrors the single use of condition (ii)
in Beli's proof. -/
theorem thirdRawDefect_and_sourceCap_strict_of_exceptionB
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hfour : 3 < N + 3) (hthree : 1 < S + 1)
    (hsecondFourth : a.order (1 : Fin (N + 3)) <
      a.order ⟨3, hfour⟩)
    (B : a.Beli2019Lemma814ExceptionB c.firstUnarySegment) :
    ((((c.order (0 : Fin (S + 2)) : ℚ) -
          (c.order (2 : Fin (S + 2)) : ℚ) +
            a.alphaValue (0 : Fin (N + 2)) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
          ((1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 3)) ∧
      ((((c.order (0 : Fin (S + 2)) : ℚ) -
          (c.order (2 : Fin (S + 2)) : ℚ) +
            a.alphaValue (0 : Fin (N + 2)) : ℚ) : WithTop ℚ) <
        c.prefixAlphaCap 3) := by
  let i := lemma91ThirdRepresentationIndex hfour hthree
  have hstrict := a.thirdRepresentationAlpha_strict_of_exceptionB
    (targetLaws := targetLaws) c hRank hfirst hsecond conditions hfour
      hthree hsecondFourth B
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

/-- For a source of rank at least four, the source-cap half of the preceding
estimate is exactly the strict lower bound for the third source left
endpoint needed by P1. -/
theorem sourceThirdLeftEndpoint_strict_of_exceptionB
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hfour : 3 < N + 3) (hsourceFour : 2 < S + 1)
    (hsecondFourth : a.order (1 : Fin (N + 3)) <
      a.order ⟨3, hfour⟩)
    (B : a.Beli2019Lemma814ExceptionB c.firstUnarySegment) :
    (c.order (0 : Fin (S + 2)) : ℚ) +
        a.alphaValue (0 : Fin (N + 2)) <
      c.alphaLeftEndpoint (⟨2, hsourceFour⟩ : Fin (S + 1)) := by
  have hbounds := a.thirdRawDefect_and_sourceCap_strict_of_exceptionB
    (targetLaws := targetLaws) c hRank hfirst hsecond conditions hfour
      (by omega) hsecondFourth B
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

/-- The high-rank binary prefix required in exception (b), obtained directly
from condition (iii') rather than assumed. -/
theorem binaryPrefixRepresentation_of_exceptionB
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hfour : 3 < N + 3)
    (hsecondFourth : a.order (1 : Fin (N + 3)) < a.order ⟨3, hfour⟩)
    (B : a.Beli2019Lemma814ExceptionB c.firstUnarySegment) :
    DiagonalRepresents
      (c.prefixValues 2 (by omega))
      (a.prefixValues 3 (by omega)) := by
  have hdefect := a.lemma91BinaryCentralDefectInequality_of_exceptionB
    (targetLaws := targetLaws) c hRank hfirst hsecond conditions hfour B
  have horder : c.order (1 : Fin (S + 2)) < a.order ⟨3, hfour⟩ := by
    rw [← hsecond]
    exact hsecondFourth
  exact a.binaryPrefixRepresentation_of_centralDefectInequality
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      c hRank conditions hfour horder hdefect

/-- In exception (b), the unary first-three defect is not cut down by the
third target alpha.  In rank three both prefix caps are endpoints; in higher
rank this follows from `α₂ + α₃ > 2e = α₂ + d[-a₁,₃b₁]`. -/
theorem lemma91ExceptionBOtherRawDefect_eq_capped
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (B : a.Beli2019Lemma814ExceptionB c.firstUnarySegment) :
    defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1) =
      a.lemma814FirstThirdCappedDefect c.firstUnarySegment := by
  by_cases hfour : 4 ≤ N + 3
  · let secondAlpha : Fin (N + 2) := ⟨1, by omega⟩
    let thirdAlpha : Fin (N + 2) := ⟨2, by omega⟩
    have hsecondAlpha : (1 : Fin (N + 2)) = secondAlpha := by
      apply Fin.ext
      simp [secondAlpha, Nat.mod_eq_of_lt (by omega : 1 < N + 2)]
    have hthirdAlpha : (⟨2, by omega⟩ : Fin (N + 2)) =
        thirdAlpha := by
      apply Fin.ext
      rfl
    have hlater := B.laterAlphaSum_strict hfour
    rw [hsecondAlpha, hthirdAlpha] at hlater
    have hlaterTop :
        ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) <
          (a.alphaValue secondAlpha : WithTop ℚ) +
            (a.alphaValue thirdAlpha : WithTop ℚ) := by
      rw [← WithTop.coe_add]
      apply WithTop.coe_lt_coe.mpr
      simpa only [secondAlpha, thirdAlpha] using hlater
    have hsumLt :
        (a.alphaValue secondAlpha : WithTop ℚ) +
            a.lemma814FirstThirdCappedDefect c.firstUnarySegment <
          (a.alphaValue secondAlpha : WithTop ℚ) +
            (a.alphaValue thirdAlpha : WithTop ℚ) := by
      have heq := B.defectSum_eq
      rw [hsecondAlpha] at heq
      exact heq.trans_lt hlaterTop
    have hcapLt :
        a.lemma814FirstThirdCappedDefect c.firstUnarySegment <
          (a.alphaValue thirdAlpha : WithTop ℚ) :=
      (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hsumLt
    have hminimum :
        a.lemma814FirstThirdCappedDefect c.firstUnarySegment =
          min
            (defectOrder (K := K)
              ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1))
            (a.alphaValue thirdAlpha : WithTop ℚ) := by
      unfold lemma814FirstThirdCappedDefect truncatedPrefixDefect
      rw [c.firstUnarySegment_prefixProduct_one,
        a.prefixAlphaCap_of_internal (by omega) (by omega),
        c.firstUnarySegment.prefixAlphaCap_last]
      have hindex : (⟨3 - 1, by omega⟩ : Fin (N + 2)) =
          thirdAlpha := by
        apply Fin.ext
        rfl
      rw [hindex]
      simp
    exact (eq_left_of_eq_min_lt_right hminimum hcapLt).symm
  · have hN : N = 0 := by omega
    subst N
    unfold lemma814FirstThirdCappedDefect truncatedPrefixDefect
    rw [c.firstUnarySegment_prefixProduct_one,
      a.prefixAlphaCap_last, c.firstUnarySegment.prefixAlphaCap_last]
    simp

/-- In exception (b), the uncapped unary first-three defect is strictly
larger than the first target alpha.  Equality would force
`alpha_1 + alpha_2 = 2e`; Remark 8.7 would then make `alpha_1` attain its
half-gap, contradicting the strict clause of exception (b). -/
theorem firstAlpha_lt_lemma814FirstThirdCappedDefect_of_exceptionB
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (B : a.Beli2019Lemma814ExceptionB b) :
    (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) <
      a.lemma814FirstThirdCappedDefect b := by
  have R := a.beli2019Remark87 (0 : Fin (N + 1))
    B.firstThirdOrders_eq
  have hsumNe :
      a.alphaValue (0 : Fin (N + 2)) +
          a.alphaValue (1 : Fin (N + 2)) ≠
        2 * (ramificationIndex K : ℚ) := by
    intro hsum
    have hhalf := R.alphaSum_eq_twoE_iff.mp hsum
    change a.alphaValue (0 : Fin (N + 2)) =
      a.halfGapValue (0 : Fin (N + 2)) at hhalf
    exact (ne_of_lt B.firstAlpha_strict) hhalf
  have hsumLt :
      a.alphaValue (1 : Fin (N + 2)) +
          a.alphaValue (0 : Fin (N + 2)) <
        2 * (ramificationIndex K : ℚ) := by
    have hsumLt' := lt_of_le_of_ne R.alphaSum_le_twoE hsumNe
    have hprevious : remark87PreviousAlpha (0 : Fin (N + 1)) =
        (0 : Fin (N + 2)) := by
      apply Fin.ext
      rfl
    have hcurrent : remark87CurrentAlpha (0 : Fin (N + 1)) =
        (1 : Fin (N + 2)) := by
      apply Fin.ext
      simp [remark87CurrentAlpha, Nat.mod_eq_of_lt (by omega : 1 < N + 2)]
    rw [hprevious, hcurrent] at hsumLt'
    simpa only [add_comm] using hsumLt'
  have hsumLtTop :
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) +
          (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) <
        ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    exact_mod_cast hsumLt
  have hcancel :
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) +
          (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) <
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) +
          a.lemma814FirstThirdCappedDefect b :=
    hsumLtTop.trans_eq B.defectSum_eq.symm
  exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hcancel

set_option maxHeartbeats 800000 in
-- Multiplying the two determinant defects cancels the target ternary prefix
-- and leaves the second source adjacent product, up to a square.
/-- A strict full-prefix determinant defect forces the second source
adjacent defect above `S₁ - S₃ + alpha₁`.  The other factor is strictly
above this threshold because exception (b)'s unary defect is strictly above
`alpha₁` and goodness gives `S₁ ≤ S₃`. -/
theorem sourceSecondAdjacentDefect_strict_of_fullRaw
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hthree : 1 < S + 1)
    (B : a.Beli2019Lemma814ExceptionB c.firstUnarySegment)
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
  have hunaryStrict :=
    a.firstAlpha_lt_lemma814FirstThirdCappedDefect_of_exceptionB
      c.firstUnarySegment B
  have hotherRaw := a.lemma91ExceptionBOtherRawDefect_eq_capped c B
  have hx : threshold < defectOrder (K := K) x := by
    calc
      threshold ≤ (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) :=
        hthresholdLe
      _ < a.lemma814FirstThirdCappedDefect c.firstUnarySegment :=
        hunaryStrict
      _ = defectOrder (K := K) x := by
        simpa only [x] using hotherRaw.symm
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
    have hcast : second.castSucc = (⟨1, by omega⟩ : Fin (S + 2)) := by
      apply Fin.ext
      rfl
    have hsucc : second.succ = (⟨2, by omega⟩ : Fin (S + 2)) := by
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
determinant argument in every target rank at least four. -/
theorem sourceSecondAdjacentDefect_strict_of_exceptionB
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hfour : 3 < N + 3) (hthree : 1 < S + 1)
    (hsecondFourth : a.order (1 : Fin (N + 3)) <
      a.order ⟨3, hfour⟩)
    (B : a.Beli2019Lemma814ExceptionB c.firstUnarySegment) :
    ((((c.order (0 : Fin (S + 2)) : ℚ) -
        (c.order (2 : Fin (S + 2)) : ℚ) +
          a.alphaValue (0 : Fin (N + 2)) : ℚ) : WithTop ℚ) <
      c.adjacentDefect (⟨1, hthree⟩ : Fin (S + 1))) := by
  have hbounds := a.thirdRawDefect_and_sourceCap_strict_of_exceptionB
    (targetLaws := targetLaws) c hRank hfirst hsecond conditions hfour
      hthree hsecondFourth B
  exact a.sourceSecondAdjacentDefect_strict_of_fullRaw
    (targetLaws := targetLaws) c hthree B hbounds.1

/-- Rewriting the preceding adjacent-defect estimate by the order shift
`S₃ - S₁` gives precisely the second right-defect candidate bound used
in the definition of the first source alpha. -/
theorem targetFirstAlpha_lt_sourceSecondRightDefect_of_adjacent
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hthree : 1 < S + 1)
    (hadjacent :
      ((((c.order (0 : Fin (S + 2)) : ℚ) -
          (c.order (2 : Fin (S + 2)) : ℚ) +
            a.alphaValue (0 : Fin (N + 2)) : ℚ) : WithTop ℚ) <
        c.adjacentDefect (⟨1, hthree⟩ : Fin (S + 1)))) :
    (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) <
      c.rightDefectCandidate (0 : Fin (S + 1))
        (⟨1, hthree⟩ : Fin (S + 1)) := by
  let first : Fin (S + 1) := ⟨0, by omega⟩
  let second : Fin (S + 1) := ⟨1, hthree⟩
  have hfirst : first = (0 : Fin (S + 1)) := by
    apply Fin.ext
    rfl
  have hsecond : second = (⟨1, hthree⟩ : Fin (S + 1)) := by
    rfl
  have hfirstCast : first.castSucc = (0 : Fin (S + 2)) := by
    apply Fin.ext
    rfl
  have hsecondSucc : second.succ = (2 : Fin (S + 2)) := by
    apply Fin.ext
    simp [second, Nat.mod_eq_of_lt (by omega : 2 < S + 2)]
  have hsplit :
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) =
        ((((c.order (2 : Fin (S + 2)) -
          c.order (0 : Fin (S + 2)) : Int) : ℚ) : WithTop ℚ) +
          (((c.order (0 : Fin (S + 2)) : ℚ) -
            (c.order (2 : Fin (S + 2)) : ℚ) +
              a.alphaValue (0 : Fin (N + 2)) : ℚ) : WithTop ℚ)) := by
    apply WithTop.coe_eq_coe.mpr
    push_cast
    ring
  rw [← hfirst, ← hsecond]
  unfold rightDefectCandidate
  rw [hfirstCast, hsecondSucc]
  calc
    (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) =
        ((((c.order (2 : Fin (S + 2)) -
          c.order (0 : Fin (S + 2)) : Int) : ℚ) : WithTop ℚ) +
          (((c.order (0 : Fin (S + 2)) : ℚ) -
            (c.order (2 : Fin (S + 2)) : ℚ) +
              a.alphaValue (0 : Fin (N + 2)) : ℚ) : WithTop ℚ)) := hsplit
    _ < ((((c.order (2 : Fin (S + 2)) -
          c.order (0 : Fin (S + 2)) : Int) : ℚ) : WithTop ℚ) +
        c.adjacentDefect second) :=
      (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mpr (by
        simpa only [second] using hadjacent)

/-- In target rank at least four, condition (ii) supplies the adjacent
defect premise of the preceding order-shift calculation. -/
theorem targetFirstAlpha_lt_sourceSecondRightDefect_of_exceptionB
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hfour : 3 < N + 3) (hthree : 1 < S + 1)
    (hsecondFourth : a.order (1 : Fin (N + 3)) <
      a.order ⟨3, hfour⟩)
    (B : a.Beli2019Lemma814ExceptionB c.firstUnarySegment) :
    (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) <
      c.rightDefectCandidate (0 : Fin (S + 1))
        (⟨1, hthree⟩ : Fin (S + 1)) := by
  have hadjacent := a.sourceSecondAdjacentDefect_strict_of_exceptionB
    (targetLaws := targetLaws) c hRank hfirst hsecond conditions hfour
      hthree hsecondFourth B
  exact a.targetFirstAlpha_lt_sourceSecondRightDefect_of_adjacent
    c hthree hadjacent

/-- If the source first alpha is attained on its first binary segment, the
equal-order rigidity of Lemma 9.1 identifies the raw source adjacent defect
with the target second alpha.  This is the source analogue of the local
calculation in the necessity proof of Lemma 8.14(b). -/
theorem sourceFirstAdjacentDefect_eq_targetSecond_of_firstBinary
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
    (B : a.Beli2019Lemma814ExceptionB c.firstUnarySegment) :
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
    simpa [halfGapValue, orderGap] using B.firstAlpha_strict
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
      B.firstThirdOrders_eq).currentAlpha_eq
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

/-- Candidate-level criterion for the first source alpha to be attained on
the first binary segment.  It is enough to rule out every genuinely later
right-defect candidate; the minimum is then either the first half-gap or the
first adjacent-defect candidate. -/
theorem firstBinaryAlpha_eq_alpha_of_laterRightDefects
    (c : GoodBONG r M (S + 2))
    (hlater : ∀ j : Fin (S + 1), 0 < j.1 →
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) <
        c.rightDefectCandidate (0 : Fin (S + 1)) j) :
    c.firstBinaryAlpha =
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) := by
  have halphaLe :
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) ≤
        c.firstBinaryAlpha := by
    unfold firstBinaryAlpha
    rw [c.coe_alphaValue]
    exact le_min (c.alpha_le_halfGapCandidate 0)
      (c.alpha_le_leftDefectCandidate (i := 0) (j := 0) le_rfl)
  have hmem : c.alpha (0 : Fin (S + 1)) ∈
      c.alphaCandidates (0 : Fin (S + 1)) :=
    Finset.min'_mem _ _
  have hfirstLe : c.firstBinaryAlpha ≤
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) := by
    unfold alphaCandidates at hmem
    rcases Finset.mem_insert.mp hmem with hhalf | hunion
    · rw [c.coe_alphaValue]
      rw [hhalf]
      exact min_le_left _ _
    · rcases Finset.mem_union.mp hunion with hleft | hright
      · rcases Finset.mem_image.mp hleft with ⟨j, hj, hvalue⟩
        have hjle : j ≤ (0 : Fin (S + 1)) :=
          (Finset.mem_filter.mp hj).2
        have hjzero : j = (0 : Fin (S + 1)) :=
          le_antisymm hjle (Fin.zero_le _)
        subst j
        rw [c.coe_alphaValue]
        rw [← hvalue]
        exact min_le_right _ _
      · rcases Finset.mem_image.mp hright with ⟨j, hj, hvalue⟩
        have hjge : (0 : Fin (S + 1)) ≤ j :=
          (Finset.mem_filter.mp hj).2
        by_cases hjzero : j = (0 : Fin (S + 1))
        · subst j
          rw [c.coe_alphaValue]
          rw [← hvalue]
          unfold firstBinaryAlpha leftDefectCandidate rightDefectCandidate
          exact min_le_right _ _
        · have hjpos : 0 < j.1 := by
            by_contra hnot
            have : j.1 = 0 := by omega
            exact hjzero (Fin.ext this)
          have hstrict := hlater j hjpos
          rw [c.coe_alphaValue, ← hvalue] at hstrict
          exact (lt_irrefl _ hstrict).elim
  exact le_antisymm hfirstLe halphaLe

/-- It suffices to control the second right-defect candidate and the third
left alpha endpoint.  Property P1 propagates the latter to every later
alpha, while the defining candidate inequality converts each propagated
endpoint bound into a right-defect bound for the first alpha. -/
theorem laterRightDefects_strict_of_second_and_third
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (c : GoodBONG r M (S + 2))
    (hthree : 1 < S + 1)
    (hsecond :
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) <
        c.rightDefectCandidate (0 : Fin (S + 1)) ⟨1, hthree⟩)
    (hthird : ∀ h : 2 < S + 1,
      (c.order (0 : Fin (S + 2)) : ℚ) +
          c.alphaValue (0 : Fin (S + 1)) <
        c.alphaLeftEndpoint (⟨2, h⟩ : Fin (S + 1))) :
    ∀ j : Fin (S + 1), 0 < j.1 →
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) <
        c.rightDefectCandidate (0 : Fin (S + 1)) j := by
  intro j hjpos
  by_cases hjone : j.1 = 1
  · have hj : j = (⟨1, hthree⟩ : Fin (S + 1)) := by
      apply Fin.ext
      exact hjone
    simpa only [hj] using hsecond
  · have hjtwo : 2 ≤ j.1 := by omega
    have hthirdIndex : 2 < S + 1 := lt_of_le_of_lt hjtwo j.isLt
    let third : Fin (S + 1) := ⟨2, hthirdIndex⟩
    have hthirdJ : third ≤ j := by
      change 2 ≤ j.1
      exact hjtwo
    have hendpoint :
        (c.order (0 : Fin (S + 2)) : ℚ) +
            c.alphaValue (0 : Fin (S + 1)) <
          c.alphaLeftEndpoint j :=
      (hthird hthirdIndex).trans_le
        (c.alphaLeftEndpoint_monotone hthirdJ)
    have hshiftQ : c.alphaValue (0 : Fin (S + 1)) <
        ((c.order j.castSucc - c.order (0 : Fin (S + 2)) : Int) : ℚ) +
          c.alphaValue j := by
      unfold alphaLeftEndpoint at hendpoint
      push_cast at hendpoint ⊢
      linarith
    have hshiftTop :
        (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) <
          (((c.order j.castSucc -
            c.order (0 : Fin (S + 2)) : Int) : ℚ) : WithTop ℚ) +
            (c.alphaValue j : WithTop ℚ) := by
      exact_mod_cast hshiftQ
    have halphaLe : (c.alphaValue j : WithTop ℚ) ≤
        c.leftDefectCandidate j j := by
      rw [c.coe_alphaValue]
      exact c.alpha_le_leftDefectCandidate le_rfl
    have hbound := hshiftTop.trans_le
      (add_le_add_right halphaLe
        (((c.order j.castSucc -
          c.order (0 : Fin (S + 2)) : Int) : ℚ) : WithTop ℚ))
    unfold leftDefectCandidate at hbound
    have hzero : (0 : Fin (S + 1)).castSucc =
        (0 : Fin (S + 2)) := by
      apply Fin.ext
      rfl
    unfold rightDefectCandidate
    rw [hzero]
    have hordersQ :
        ((c.order j.castSucc - c.order (0 : Fin (S + 2)) : Int) : ℚ) +
            ((c.order j.succ - c.order j.castSucc : Int) : ℚ) =
          ((c.order j.succ - c.order (0 : Fin (S + 2)) : Int) : ℚ) := by
      push_cast
      ring
    have hordersTop :
        (((c.order j.castSucc -
            c.order (0 : Fin (S + 2)) : Int) : ℚ) : WithTop ℚ) +
          (((c.order j.succ -
            c.order j.castSucc : Int) : ℚ) : WithTop ℚ) =
        (((c.order j.succ -
            c.order (0 : Fin (S + 2)) : Int) : ℚ) : WithTop ℚ) := by
      exact_mod_cast hordersQ
    calc
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) <
          (((c.order j.castSucc -
              c.order (0 : Fin (S + 2)) : Int) : ℚ) : WithTop ℚ) +
            ((((c.order j.succ -
                c.order j.castSucc : Int) : ℚ) : WithTop ℚ) +
              c.adjacentDefect j) := hbound
      _ = ((((c.order j.castSucc -
              c.order (0 : Fin (S + 2)) : Int) : ℚ) : WithTop ℚ) +
            (((c.order j.succ -
              c.order j.castSucc : Int) : ℚ) : WithTop ℚ)) +
              c.adjacentDefect j := by rw [add_assoc]
      _ = (((c.order j.succ -
              c.order (0 : Fin (S + 2)) : Int) : ℚ) : WithTop ℚ) +
            c.adjacentDefect j := by rw [hordersTop]

/-- In every source rank at least three, exception (b)'s `A₃` estimate and
P1 force the first source alpha to be attained on its first binary segment.
For source rank three the third-endpoint premise is vacuous; for larger rank
it is supplied by the source-cap half of condition (ii). -/
theorem firstBinaryAlpha_eq_sourceFirstAlpha_of_exceptionB
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hfour : 3 < N + 3) (hthree : 1 < S + 1)
    (hsecondFourth : a.order (1 : Fin (N + 3)) <
      a.order ⟨3, hfour⟩)
    (B : a.Beli2019Lemma814ExceptionB c.firstUnarySegment) :
    c.firstBinaryAlpha =
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) := by
  have hrigidity := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.secondOrderRigidity_of_exceptionBC
      c hRank hfirst hsecond conditions (Or.inl B)
  have hsecondBound :=
    a.targetFirstAlpha_lt_sourceSecondRightDefect_of_exceptionB
      (targetLaws := targetLaws) c hRank hfirst hsecond conditions hfour
        hthree hsecondFourth B
  rw [← hrigidity.2] at hsecondBound
  have hthirdBound : ∀ h : 2 < S + 1,
      (c.order (0 : Fin (S + 2)) : ℚ) +
          c.alphaValue (0 : Fin (S + 1)) <
        c.alphaLeftEndpoint (⟨2, h⟩ : Fin (S + 1)) := by
    intro h
    have hbound := a.sourceThirdLeftEndpoint_strict_of_exceptionB
      (targetLaws := targetLaws) c hRank hfirst hsecond conditions hfour h
        hsecondFourth B
    rw [← hrigidity.2] at hbound
    exact hbound
  have hlater := by
    letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
    exact c.laterRightDefects_strict_of_second_and_third
      hthree hsecondBound hthirdBound
  exact c.firstBinaryAlpha_eq_alpha_of_laterRightDefects hlater

set_option maxHeartbeats 800000 in
-- The determinant completion has the two adjacent products occurring in
-- the paper, up to a square in the second argument.
/-- The geometric core of exception (b).  Once the source first adjacent
defect is exactly `α₂`, determinant completion of the represented source
binary prefix is isotropic by exception (b), but the residue-two boundary
criterion makes its adjacent Hilbert symbol non-one. -/
theorem not_lemma814ExceptionB_of_binaryPrefix_of_sourceAdjacentDefect
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hbinary : DiagonalRepresents
      (c.prefixValues 2 (by omega))
      (a.prefixValues 3 (by omega)))
    (hsourceAdjacent :
      c.adjacentDefect (0 : Fin (S + 1)) =
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ)) :
    ¬a.Beli2019Lemma814ExceptionB c.firstUnarySegment := by
  intro B
  let base := a.prefixValueUnits 3 (by omega)
  let head := c.prefixValueUnits 2 (by omega)
  let d := diagonalUnitDeterminant base * diagonalUnitDeterminant head
  let candidate : Fin 3 → Kˣ := Fin.snoc head d
  have hheadRep : DiagonalRepresents
      (diagonalUnitCoefficients head)
      (diagonalUnitCoefficients base) := by
    simpa only [head, base,
      c.diagonalUnitCoefficients_prefixValueUnits,
      a.diagonalUnitCoefficients_prefixValueUnits] using hbinary
  have hcandidateRep : DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients base) := by
    simpa only [candidate, d] using
      determinantCompletion_represents_base base head hheadRep
  have hcandidateZero : candidate (0 : Fin 3) = head (0 : Fin 2) := by
    simp [candidate]
  have hcandidateOne : candidate (1 : Fin 3) = head (1 : Fin 2) := by
    change (Fin.snoc head d : Fin 3 → Kˣ) 1 = head 1
    rw [show (1 : Fin 3) = (1 : Fin 2).castSucc by rfl,
      Fin.snoc_castSucc]
  have hcandidateTwo : candidate (2 : Fin 3) = d := by
    change (Fin.snoc head d : Fin 3 → Kˣ) 2 = d
    rw [show (2 : Fin 3) = Fin.last 2 by rfl, Fin.snoc_last]
  have hheadOne : head (1 : Fin 2) =
      c.valueUnit (1 : Fin (S + 2)) := by
    rfl
  have hfirstArgument : -(candidate 0 * candidate 1) =
      c.adjacentProduct (0 : Fin (S + 1)) := by
    rw [hcandidateZero, hcandidateOne]
    simp [head, prefixValueUnits, adjacentProduct]
  have hsecondArgument : -(candidate 1 * candidate 2) =
      ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1) *
        (c.valueUnit (1 : Fin (S + 2))) ^ 2 := by
    rw [hcandidateOne, hcandidateTwo, hheadOne]
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
  have hcandidateIsotropic :
      DiagonalIsotropic (diagonalUnitCoefficients candidate) := by
    have hbaseIsotropic :
        DiagonalIsotropic (diagonalUnitCoefficients base) := by
      exact B.firstThree_isotropic
    exact hcandidateRep.symm_of_sameRank.isotropic_of hbaseIsotropic
  have hone :
      hilbertSymbol K (-(candidate 0 * candidate 1))
          (-(candidate 1 * candidate 2)) = 1 :=
    (diagonalUnitTernary_isotropic_iff_adjacentHilbertOne candidate).mp
      hcandidateIsotropic
  have hotherRaw := a.lemma91ExceptionBOtherRawDefect_eq_capped c B
  have hsum' :
      c.adjacentDefect (0 : Fin (S + 1)) +
          defectOrder (K := K)
            ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1) =
        ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    rw [hsourceAdjacent, hotherRaw]
    exact B.defectSum_eq
  have hsum :
      defectOrder (K := K)
          (c.adjacentProduct (0 : Fin (S + 1))) +
        defectOrder (K := K)
          ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1) =
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    simpa only [adjacentDefect, Nat.cast_mul, Nat.cast_ofNat] using hsum'
  have hneBase :
      hilbertSymbol K (c.adjacentProduct (0 : Fin (S + 1)))
          ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1) ≠ 1 :=
    hilbertSymbol_ne_one_of_residue_two_of_defectOrder_add_eq_twoE
      B.residueTwo _ _ hsum
  have hne :
      hilbertSymbol K (-(candidate 0 * candidate 1))
          (-(candidate 1 * candidate 2)) ≠ 1 := by
    rw [hfirstArgument, hsecondArgument, hilbertSymbol_mul_square_right]
    exact hneBase
  exact hne hone

/-- Exception (b) is excluded for every represented source of rank at least
three.  The arithmetic estimates force the first source binary alpha, the
equal-order calculation identifies its adjacent defect with `alpha₂`, and
the determinant-completion theorem supplies the final contradiction. -/
theorem not_lemma814ExceptionB_of_equalSecondOrder_sourceRankAtLeastThree
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
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
    (hfour : 3 < N + 3) (hthree : 1 < S + 1)
    (hsecondFourth : a.order (1 : Fin (N + 3)) <
      a.order ⟨3, hfour⟩) :
    ¬a.Beli2019Lemma814ExceptionB c.firstUnarySegment := by
  intro B
  have hrigidity := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.secondOrderRigidity_of_exceptionBC
      c hRank hfirst hsecond conditions (Or.inl B)
  have hsourceBinary :=
    a.firstBinaryAlpha_eq_sourceFirstAlpha_of_exceptionB
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond conditions hfour hthree hsecondFourth B
  have hsourceAdjacent :=
    a.sourceFirstAdjacentDefect_eq_targetSecond_of_firstBinary
      (targetLaws := targetLaws) c hfirst hsecond hrigidity.2
        hsourceBinary B
  have hbinary := a.binaryPrefixRepresentation_of_exceptionB
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      c hRank hfirst hsecond conditions hfour hsecondFourth B
  exact (a.not_lemma814ExceptionB_of_binaryPrefix_of_sourceAdjacentDefect
    c hbinary hsourceAdjacent) B

/-- Exception (b) is completely excluded when the represented source has
rank two.  Here the source first alpha is definitionally the alpha of its
only binary segment, so no tail estimate is needed. -/
theorem not_lemma814ExceptionB_of_equalSecondOrder_sourceRankTwo
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M 2)
    (hRank : 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) = c.order (0 : Fin 2))
    (hsecond : a.order (1 : Fin (N + 3)) = c.order (1 : Fin 2))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c hRank)
    (hsecondFourth : ∀ hfour : 3 < N + 3,
      a.order (1 : Fin (N + 3)) < a.order ⟨3, hfour⟩) :
    ¬a.Beli2019Lemma814ExceptionB c.firstUnarySegment := by
  intro B
  have hrigidity := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.secondOrderRigidity_of_exceptionBC
      c hRank hfirst hsecond conditions (Or.inl B)
  have hsourceBinary : c.firstBinaryAlpha =
      (c.alphaValue (0 : Fin 1) : WithTop ℚ) := by
    unfold firstBinaryAlpha
    exact c.binary_alpha_eq_min_candidates.symm
  have hsourceAdjacent :=
    a.sourceFirstAdjacentDefect_eq_targetSecond_of_firstBinary
      (targetLaws := targetLaws) c hfirst hsecond hrigidity.2
        hsourceBinary B
  have hbinary : DiagonalRepresents
      (c.prefixValues 2 (Nat.le_refl _))
      (a.prefixValues 3 (by omega)) := by
    cases N with
    | zero =>
        exact a.binaryPrefixRepresentation_of_ambient_rankThree c ambient
    | succ N =>
        have hfour : 3 < N.succ + 3 := by omega
        exact a.binaryPrefixRepresentation_of_exceptionB
          (targetLaws := targetLaws) (sourceLaws := sourceLaws)
            c hRank hfirst hsecond conditions hfour
              (hsecondFourth hfour) B
  exact (a.not_lemma814ExceptionB_of_binaryPrefix_of_sourceAdjacentDefect
    c hbinary hsourceAdjacent) B

set_option maxHeartbeats 800000 in
-- In the equal-rank ternary boundary the paper replaces the unavailable
-- A₃ estimate by the fact that the full determinant ratio is a square.
/-- Complete exception-(b) exclusion when the target has rank three.  A
binary source is the preceding base case.  A ternary source has square full
determinant ratio by equal-rank ambient representation, which supplies the
same raw-defect input used by the high-rank proof. -/
theorem not_lemma814ExceptionB_of_equalSecondOrder_rankThree
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [DiagonalIsometryInvariantLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L 3) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ 2)
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin 3) = c.order (1 : Fin (S + 2)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c hRank) :
    ¬a.Beli2019Lemma814ExceptionB c.firstUnarySegment := by
  by_cases hthree : 1 < S + 1
  · have hS : S = 1 := by omega
    subst S
    intro B
    let targetUnits := a.prefixValueUnits 3 (Nat.le_refl _)
    let sourceUnits := c.prefixValueUnits 3 (Nat.le_refl _)
    have hfullRepresentation : DiagonalRepresents
        (c.prefixValues 3 (Nat.le_refl _))
        (a.prefixValues 3 (Nat.le_refl _)) := by
      have hambient :=
        a.toBONG.diagonalRepresents_of_ambient c.toBONG ambient
      convert hambient using 1 <;> funext i <;> rfl
    have hunitRepresentation : DiagonalRepresents
        (diagonalUnitCoefficients sourceUnits)
        (diagonalUnitCoefficients targetUnits) := by
      simpa only [sourceUnits, targetUnits,
        c.diagonalUnitCoefficients_prefixValueUnits,
        a.diagonalUnitCoefficients_prefixValueUnits] using
          hfullRepresentation
    have hsquareDeterminant :=
      DiagonalIsometryInvariantLaws.determinant_square
        sourceUnits targetUnits hunitRepresentation
    have hsourceDeterminant : diagonalUnitDeterminant sourceUnits =
        c.prefixProduct 3 := by
      simpa only [sourceUnits] using
        c.diagonalUnitDeterminant_prefixValueUnits 3 (Nat.le_refl _)
    have htargetDeterminant : diagonalUnitDeterminant targetUnits =
        a.prefixProduct 3 := by
      simpa only [targetUnits] using
        a.diagonalUnitDeterminant_prefixValueUnits 3 (Nat.le_refl _)
    have hsquare : IsSquare
        ((1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 3) := by
      rw [hsourceDeterminant, htargetDeterminant] at hsquareDeterminant
      simpa only [one_mul, mul_comm] using hsquareDeterminant
    have hfullRaw :
        ((((c.order (0 : Fin 3) : ℚ) -
            (c.order (2 : Fin 3) : ℚ) +
              a.alphaValue (0 : Fin 2) : ℚ) : WithTop ℚ) <
          defectOrder (K := K)
            ((1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 3)) := by
      rw [defectOrder_eq_top_of_isSquare hsquare]
      exact WithTop.coe_lt_top _
    have hadjacent := a.sourceSecondAdjacentDefect_strict_of_fullRaw
      (targetLaws := targetLaws) c (by omega) B hfullRaw
    have hsecondBound :=
      a.targetFirstAlpha_lt_sourceSecondRightDefect_of_adjacent
        c (by omega) hadjacent
    have hrigidity := by
      letI : Beli2006AlphaLaws.{u, v} K := targetLaws
      exact a.secondOrderRigidity_of_exceptionBC
        c hRank hfirst hsecond conditions (Or.inl B)
    rw [← hrigidity.2] at hsecondBound
    have hthirdBound : ∀ h : 2 < 2,
        (c.order (0 : Fin 3) : ℚ) + c.alphaValue (0 : Fin 2) <
          c.alphaLeftEndpoint (⟨2, h⟩ : Fin 2) := by
      intro h
      omega
    have hlater := by
      letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
      exact c.laterRightDefects_strict_of_second_and_third
        (by omega) hsecondBound hthirdBound
    have hsourceBinary :=
      c.firstBinaryAlpha_eq_alpha_of_laterRightDefects hlater
    have hsourceAdjacent :=
      a.sourceFirstAdjacentDefect_eq_targetSecond_of_firstBinary
        (targetLaws := targetLaws) c hfirst hsecond hrigidity.2
          hsourceBinary B
    have hbinary :=
      a.binaryPrefixRepresentation_of_ambient_rankThree c ambient
    exact (a.not_lemma814ExceptionB_of_binaryPrefix_of_sourceAdjacentDefect
      c hbinary hsourceAdjacent) B
  · have hS : S = 0 := by omega
    subst S
    exact a.not_lemma814ExceptionB_of_equalSecondOrder_sourceRankTwo
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        c hRank hfirst hsecond ambient conditions (by
          intro hfour
          omega)

/-- Complete exception-(b) exclusion in the equal-first/equal-second order
branch.  Source rank two is handled by the ambient rank-three base case or
condition (iii'); all larger source ranks are handled by the `A₃`/P1
argument above. -/
theorem not_lemma814ExceptionB_of_equalSecondOrder
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [DiagonalIsometryInvariantLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c hRank)
    (hsecondFourth : ∀ hfour : 3 < N + 3,
      a.order (1 : Fin (N + 3)) < a.order ⟨3, hfour⟩) :
    ¬a.Beli2019Lemma814ExceptionB c.firstUnarySegment := by
  cases N with
  | zero =>
      exact a.not_lemma814ExceptionB_of_equalSecondOrder_rankThree
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          c hRank hfirst hsecond ambient conditions
  | succ N =>
      have hfour : 3 < N.succ + 3 := by omega
      by_cases hthree : 1 < S + 1
      · exact
          a.not_lemma814ExceptionB_of_equalSecondOrder_sourceRankAtLeastThree
            (targetLaws := targetLaws) (sourceLaws := sourceLaws)
              c hRank hfirst hsecond conditions hfour hthree
                (hsecondFourth hfour)
      · have hS : S = 0 := by omega
        subst S
        exact a.not_lemma814ExceptionB_of_equalSecondOrder_sourceRankTwo
          (targetLaws := targetLaws) (sourceLaws := sourceLaws)
            c hRank hfirst hsecond ambient conditions hsecondFourth

end BONG.GoodBONG

end Bong
