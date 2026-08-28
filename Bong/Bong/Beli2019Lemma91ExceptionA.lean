/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma91SecondOrder
import Bong.Bong.Beli2019Lemma216Complete

/-!
# Beli (2019), Lemma 9.1: the exception-(a) prefix representation

In target rank at least four, the binary prefix representation used in the
exception-(a) contradiction is exactly condition (iii') of the revised paper
at `i = 3`.  Lemma 2.16 converts the original condition (iii), already stored
in `RepresentationConditions`, to this revised form.

This file isolates that conversion.  The remaining arithmetic task is the
strict capped-defect inequality displayed in the proof of Lemma 9.1.
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

/-- The condition-(iii') index `i = 3` in the rank-at-least-four branch of
Lemma 9.1. -/
def lemma91CentralIndex (hfour : 3 < N + 3) :
    CentralRepresentationIndex (N + 3) (S + 2) where
  val := 3
  one_lt := by omega
  lt_large := hfour
  le_small_succ := by omega

@[simp]
theorem lemma91CentralIndex_val (hfour : 3 < N + 3) :
    (lemma91CentralIndex (S := S) hfour).val = 3 :=
  rfl

/-- The strict defect inequality in condition (iii') at `i = 3`:
`d[-a_{1,3}b_1] + d[-a_{1,4}b_{1,2}] > 2e + S_2 - R_4`. -/
noncomputable def lemma91BinaryCentralDefectInequality
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hfour : 3 < N + 3) : Prop :=
  (((2 * (ramificationIndex K : ℚ) +
      (c.order (1 : Fin (S + 2)) : ℚ) -
        (a.order ⟨3, hfour⟩ : ℚ)) : ℚ) : WithTop ℚ) <
    a.truncatedPrefixDefect c (-1) 3 1 +
      a.truncatedPrefixDefect c (-1) 4 2

/-- Internal extraction of the `i = 3` revised central representation. -/
private theorem binaryPrefixRepresentation_of_centralDefectInequalityCore
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (conditions : RepresentationConditions a c hRank)
    (hfour : 3 < N + 3)
    (horder : c.order (1 : Fin (S + 2)) < a.order ⟨3, hfour⟩)
    (hdefect : a.lemma91BinaryCentralDefectInequality c hfour) :
    DiagonalRepresents
      (c.prefixValues 2 (by omega))
      (a.prefixValues 3 (by omega)) := by
  let i := lemma91CentralIndex (S := S) hfour
  have htriggers : a.CentralTriggerEquivalence c :=
    a.beli2019Lemma216 (sourceLaws := targetLaws)
      (targetLaws := sourceLaws) c hRank conditions.orderCondition
        conditions.defectCondition
  have hprime : a.CentralRepresentationConditionsPrime c :=
    (a.centralRepresentationConditions_iff_prime c htriggers).mp
      conditions.centralRepresentations
  have hsourceSecond :
      (⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : Fin (S + 2)) = (1 : Fin (S + 2)) := by
    apply Fin.ext
    simp [i, lemma91CentralIndex]
  have htargetFourth :
      (⟨i.val, by
        have := i.lt_large
        omega⟩ : Fin (N + 3)) = ⟨3, hfour⟩ := by
    apply Fin.ext
    rfl
  have htrigger : a.centralDefectTrigger c i := by
    constructor
    · rw [hsourceSecond, htargetFourth]
      exact horder
    · rw [hsourceSecond, htargetFourth]
      simpa [i, lemma91CentralIndex, centralPreviousDefect,
        centralCurrentDefect, lemma91BinaryCentralDefectInequality] using
          hdefect
  simpa [i, lemma91CentralIndex] using hprime i htrigger

set_option maxHeartbeats 600000 in
-- The proof normalizes several dependent finite indices before rational
-- linear arithmetic can compare the two Lemma 8.12(ii) candidates.
/-- Under `R₁ = R₃`, `R₁ = S₁`, and `R₂ = S₂`, the first-three
defect is bounded by the source first alpha.  Hence the primary candidate
in Lemma 8.12(ii) is no larger than the half-gap candidate, so `A₂` is the
primary candidate. -/
theorem secondRepresentationAlpha_eq_primary_of_equalOrders
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (houter : a.order (0 : Fin (N + 3)) =
      a.order (2 : Fin (N + 3)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2))) :
    a.representationAlpha c (secondRepresentationIndex N S) =
      a.secondRepresentationPrimaryFormula c := by
  have hfullLe : a.truncatedPrefixDefect c (-1) 3 1 ≤
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) := by
    rw [a.fullFirstThirdDefect_eq_min_unary_sourceFirstAlpha c]
    exact min_le_right _ _
  have hsourceCastZero : (0 : Fin (S + 1)).castSucc =
      (0 : Fin (S + 2)) := by
    apply Fin.ext
    rfl
  have hsourceSucc : (0 : Fin (S + 1)).succ =
      (1 : Fin (S + 2)) := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 1 < S + 2)]
  have hsourceHalf : c.alphaValue (0 : Fin (S + 1)) ≤
      (((c.order (1 : Fin (S + 2)) -
        c.order (0 : Fin (S + 2)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ)) := by
    have h := c.alphaValue_le_halfGapValue (0 : Fin (S + 1))
    unfold halfGapValue orderGap at h
    rw [hsourceCastZero, hsourceSucc] at h
    exact h
  rw [← hsecond, ← hfirst] at hsourceHalf
  have hprimaryLe : a.secondRepresentationPrimaryFormula c ≤
      a.secondRepresentationHalfGapFormula c := by
    unfold secondRepresentationPrimaryFormula
      secondRepresentationHalfGapFormula
    calc
      (((a.order (2 : Fin (N + 3)) -
          c.order (1 : Fin (S + 2)) : Int) : ℚ) : WithTop ℚ) +
            a.truncatedPrefixDefect c (-1) 3 1 ≤
        (((a.order (2 : Fin (N + 3)) -
          c.order (1 : Fin (S + 2)) : Int) : ℚ) : WithTop ℚ) +
            (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) :=
        by
          simpa only [add_comm] using add_le_add_left hfullLe
            ((((a.order (2 : Fin (N + 3)) -
              c.order (1 : Fin (S + 2)) : Int) : ℚ) : WithTop ℚ))
      _ ≤ (((((a.order (2 : Fin (N + 3)) -
          c.order (1 : Fin (S + 2)) : Int) : ℚ) / 2 +
            (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) := by
        apply WithTop.coe_le_coe.mpr
        rw [← houter, ← hsecond]
        push_cast at hsourceHalf ⊢
        linarith
  letI : Beli2006AlphaLaws.{u, v} K := targetLaws
  rw [a.beli2019Lemma812_ii c hfirst, min_eq_right hprimaryLe]

/-- Condition 2.1(ii) at the second boundary therefore bounds the binary
prefix defect below by the explicit primary candidate. -/
theorem secondPrefixDefect_ge_primary_of_equalOrders
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (houter : a.order (0 : Fin (N + 3)) =
      a.order (2 : Fin (N + 3)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank) :
    a.secondRepresentationPrimaryFormula c ≤
      a.truncatedPrefixDefect c 1 2 2 := by
  let second := secondRepresentationIndex N S
  have hcondition := conditions.defectCondition second
  rw [a.coe_representationAlphaValue c second,
    show second = secondRepresentationIndex N S by rfl,
    a.secondRepresentationAlpha_eq_primary_of_equalOrders
      (targetLaws := targetLaws) c hfirst houter hsecond] at hcondition
  exact hcondition

/-- The domination principle expresses the second defect in condition
(iii') as being at least the minimum of the target adjacent defect
`d[-a₃a₄]` and the condition-(ii) defect `d[a₁a₂b₁b₂]`. -/
theorem min_thirdAdjacent_secondPrefix_le_firstFourthDefect
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2)) :
    min (a.truncatedPrefixDefect a (-1) 2 4)
        (a.truncatedPrefixDefect c 1 2 2) ≤
      a.truncatedPrefixDefect c (-1) 4 2 := by
  have hdomination :=
    a.truncatedPrefixDefect_domination a c (-1) 1 4 2 2
  rw [a.truncatedPrefixDefect_comm a (-1) 4 2] at hdomination
  simpa using hdomination

/-- The rational arithmetic in the unary-defect subcase of exception (a).
The two conclusions correspond to the two inputs of the domination minimum. -/
theorem lemma91ExceptionAUnaryArithmetic
    {e r₂ r₃ r₄ α₂ α₃ d : ℚ}
    (hstrict : 2 * e < α₂ + d)
    (hhalf : α₂ ≤ (r₃ - r₂) / 2 + e)
    (horder : r₂ < r₄)
    (hleft : r₂ + α₂ ≤ r₃ + α₃) :
    2 * e + r₂ - r₄ < d + (r₃ - r₂ + d) ∧
      2 * e + r₂ - r₄ < d + (r₃ - r₄ + α₃) := by
  constructor <;> linarith

/-- The rational arithmetic in the source-alpha-cap subcase of exception
(a).  Property P1 supplies `hright`, while Remark 8.7 supplies `hfirst`. -/
theorem lemma91ExceptionASourceCapArithmetic
    {e r₂ r₃ r₄ α₁ α₂ α₃ d : ℚ}
    (hstrict : 2 * e < α₂ + d)
    (hcap : d ≤ α₃)
    (hfirst : α₁ = r₂ - r₃ + α₂)
    (hright : -r₄ + α₃ ≤ -r₃ + α₂) :
    2 * e + r₂ - r₄ < α₁ + α₂ ∧
      2 * e + r₂ - r₄ < α₁ + (r₃ - r₄ + α₃) := by
  constructor <;> linarith

set_option maxHeartbeats 800000 in
-- This is the first of the two minimum branches in the paper's long
-- exception-(a) estimate.  Dependent finite indices are normalized once,
-- after which the strict part is rational linear arithmetic.
/-- If the full first-three defect selects the unary defect, exception (a)
forces the strict condition-(iii') inequality at `i = 3`. -/
theorem lemma91BinaryCentralDefectInequality_of_exceptionA_unary
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hfour : 3 < N + 3)
    (hsecondFourth : a.order (1 : Fin (N + 3)) < a.order ⟨3, hfour⟩)
    (A : a.Beli2019Lemma814ExceptionA c.firstUnarySegment)
    (hfull : a.truncatedPrefixDefect c (-1) 3 1 =
      a.lemma814FirstThirdCappedDefect c.firstUnarySegment) :
    a.lemma91BinaryCentralDefectInequality c hfour := by
  let secondAlpha : Fin (N + 2) := ⟨1, by omega⟩
  let thirdAlpha : Fin (N + 2) := ⟨2, by omega⟩
  let secondOrder : Fin (N + 3) := ⟨1, by omega⟩
  let thirdOrder : Fin (N + 3) := ⟨2, by omega⟩
  let fourthOrder : Fin (N + 3) := ⟨3, hfour⟩
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
  have hfourthOrder : (⟨3, hfour⟩ : Fin (N + 3)) = fourthOrder := rfl
  have hunaryCap :
      a.lemma814FirstThirdCappedDefect c.firstUnarySegment ≤
        (a.alphaValue thirdAlpha : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_leftCap
      c.firstUnarySegment (-1) 3 1
    rw [a.prefixAlphaCap_of_internal (by omega) hfour] at hcap
    change a.lemma814FirstThirdCappedDefect c.firstUnarySegment ≤
      (a.alphaValue thirdAlpha : WithTop ℚ) at hcap
    exact hcap
  have hunaryFinite :
      a.lemma814FirstThirdCappedDefect c.firstUnarySegment ≠ ⊤ := by
    intro htop
    rw [htop] at hunaryCap
    exact (not_le_of_gt (WithTop.coe_lt_top _)) hunaryCap
  let d : ℚ :=
    (a.lemma814FirstThirdCappedDefect c.firstUnarySegment).untop
      hunaryFinite
  have hdCoe : (d : WithTop ℚ) =
      a.lemma814FirstThirdCappedDefect c.firstUnarySegment :=
    WithTop.coe_untop _ _
  have hstrictQ : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue secondAlpha + d := by
    have hstrict := A.defectSum_strict
    rw [hsecondAlpha, ← hdCoe] at hstrict
    exact WithTop.coe_lt_coe.mp (by
      simpa only [WithTop.coe_add] using hstrict)
  have hhalfQ : a.alphaValue secondAlpha ≤
      (((a.order thirdOrder - a.order secondOrder : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ)) := by
    have hhalf := a.alphaValue_le_halfGapValue secondAlpha
    change a.alphaValue secondAlpha ≤
      (((a.order thirdOrder - a.order secondOrder : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ)) at hhalf
    exact hhalf
  have horderQ : (a.order secondOrder : ℚ) <
      (a.order fourthOrder : ℚ) := by
    exact_mod_cast (by
      simpa only [hsecondOrder, hfourthOrder] using hsecondFourth)
  have hleftQ : (a.order secondOrder : ℚ) +
      a.alphaValue secondAlpha ≤
        (a.order thirdOrder : ℚ) + a.alphaValue thirdAlpha := by
    have hnext : secondAlpha.val + 1 < N + 2 := by
      change 1 + 1 < N + 2
      omega
    have hp1 := (a.alpha_p1 secondAlpha hnext).1
    change (a.order secondOrder : ℚ) + a.alphaValue secondAlpha ≤
      (a.order thirdOrder : ℚ) + a.alphaValue thirdAlpha at hp1
    exact hp1
  push_cast at hhalfQ
  obtain ⟨hprefixQ, hadjacentQ⟩ :=
    lemma91ExceptionAUnaryArithmetic hstrictQ hhalfQ horderQ hleftQ
  have hprefixLower :=
    a.secondPrefixDefect_ge_primary_of_equalOrders
      (targetLaws := targetLaws) c hRank hfirst A.firstThirdOrders_eq
        hsecond conditions
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
    have hprimaryStrict :
        (((2 * (ramificationIndex K : ℚ) +
          (a.order secondOrder : ℚ) -
            (a.order fourthOrder : ℚ) : ℚ)) : WithTop ℚ) <
          a.truncatedPrefixDefect c (-1) 3 1 +
            a.secondRepresentationPrimaryFormula c := by
      unfold secondRepresentationPrimaryFormula
      rw [hfull, ← hdCoe, ← hsecond, hsecondOrder, hthirdOrder]
      exact_mod_cast hprefixQ
    exact hprimaryStrict.trans_le (add_le_add le_rfl hprefixLower)
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
      rw [hfull, ← hdCoe]
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

set_option maxHeartbeats 800000 in
-- In the source-cap subcase, the earlier second-order rigidity theorem
-- identifies both the source cap and the second representation alpha.
/-- If the full first-three defect selects the source first alpha, exception
(a) again forces the strict condition-(iii') inequality at `i = 3`. -/
theorem lemma91BinaryCentralDefectInequality_of_exceptionA_sourceCap
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hfour : 3 < N + 3)
    (A : a.Beli2019Lemma814ExceptionA c.firstUnarySegment)
    (hfull : a.truncatedPrefixDefect c (-1) 3 1 =
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ)) :
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
  have hunaryCap :
      a.lemma814FirstThirdCappedDefect c.firstUnarySegment ≤
        (a.alphaValue thirdAlpha : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_leftCap
      c.firstUnarySegment (-1) 3 1
    rw [a.prefixAlphaCap_of_internal (by omega) hfour] at hcap
    change a.lemma814FirstThirdCappedDefect c.firstUnarySegment ≤
      (a.alphaValue thirdAlpha : WithTop ℚ) at hcap
    exact hcap
  have hunaryFinite :
      a.lemma814FirstThirdCappedDefect c.firstUnarySegment ≠ ⊤ := by
    intro htop
    rw [htop] at hunaryCap
    exact (not_le_of_gt (WithTop.coe_lt_top _)) hunaryCap
  let d : ℚ :=
    (a.lemma814FirstThirdCappedDefect c.firstUnarySegment).untop
      hunaryFinite
  have hdCoe : (d : WithTop ℚ) =
      a.lemma814FirstThirdCappedDefect c.firstUnarySegment :=
    WithTop.coe_untop _ _
  have hstrictQ : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue secondAlpha + d := by
    have hstrict := A.defectSum_strict
    rw [hsecondAlpha, ← hdCoe] at hstrict
    exact WithTop.coe_lt_coe.mp (by
      simpa only [WithTop.coe_add] using hstrict)
  have hcapQ : d ≤ a.alphaValue thirdAlpha := by
    exact WithTop.coe_le_coe.mp (by
      rw [hdCoe]
      exact hunaryCap)
  have hrigidity :=
    a.secondRepresentationAlpha_eq_targetSecond_and_sourceFirst_eq_targetFirst
      c hRank hfirst A.firstThirdOrders_eq hsecond conditions hfull
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
        A.firstThirdOrders_eq).previousAlpha_eq
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
  obtain ⟨hprefixQ, hadjacentQ⟩ :=
    lemma91ExceptionASourceCapArithmetic hstrictQ hcapQ
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

/-- The unary-defect/source-cap split is exhaustive because the full-source
first-three defect is their minimum. -/
theorem lemma91BinaryCentralDefectInequality_of_exceptionA
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hfour : 3 < N + 3)
    (hsecondFourth : a.order (1 : Fin (N + 3)) < a.order ⟨3, hfour⟩)
    (A : a.Beli2019Lemma814ExceptionA c.firstUnarySegment) :
    a.lemma91BinaryCentralDefectInequality c hfour := by
  have hminimum := a.fullFirstThirdDefect_eq_min_unary_sourceFirstAlpha c
  by_cases hle : a.lemma814FirstThirdCappedDefect c.firstUnarySegment ≤
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ)
  · have hfull : a.truncatedPrefixDefect c (-1) 3 1 =
        a.lemma814FirstThirdCappedDefect c.firstUnarySegment := by
      rw [hminimum, min_eq_left hle]
    exact a.lemma91BinaryCentralDefectInequality_of_exceptionA_unary
      (targetLaws := targetLaws) c hRank hfirst hsecond conditions hfour
        hsecondFourth A hfull
  · have hfull : a.truncatedPrefixDefect c (-1) 3 1 =
        (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) := by
      rw [hminimum, min_eq_right (le_of_not_ge hle)]
    exact a.lemma91BinaryCentralDefectInequality_of_exceptionA_sourceCap
      (targetLaws := targetLaws) c hRank hfirst hsecond conditions hfour A
        hfull

/-- In target rank at least four, exception (a) itself supplies the revised
condition-(iii') inequality; the order trigger is `R₄ > S₂`. -/
theorem binaryPrefixRepresentation_of_exceptionA
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
    (A : a.Beli2019Lemma814ExceptionA c.firstUnarySegment) :
    DiagonalRepresents
      (c.prefixValues 2 (by omega))
      (a.prefixValues 3 (by omega)) := by
  have hdefect :=
    a.lemma91BinaryCentralDefectInequality_of_exceptionA
      (targetLaws := targetLaws) c hRank hfirst hsecond conditions hfour
        hsecondFourth A
  have horder : c.order (1 : Fin (S + 2)) < a.order ⟨3, hfour⟩ := by
    rw [← hsecond]
    exact hsecondFourth
  exact binaryPrefixRepresentation_of_centralDefectInequalityCore
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      a c hRank conditions hfour horder hdefect

/-- The high-rank `R₂ = S₂ < R₄` part of Lemma 9.1 now excludes exception
(a) without taking a binary-prefix representation as an extra hypothesis. -/
theorem not_lemma814ExceptionA_of_equalSecondOrder
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
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
    (hfour : 3 < N + 3)
    (hsecondFourth : a.order (1 : Fin (N + 3)) < a.order ⟨3, hfour⟩) :
    ¬a.Beli2019Lemma814ExceptionA c.firstUnarySegment := by
  intro A
  have hbinary := a.binaryPrefixRepresentation_of_exceptionA
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      c hRank hfirst hsecond conditions hfour hsecondFourth A
  exact a.not_lemma814ExceptionA_of_binaryPrefixRepresentation
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      c hRank hfirst hsecond conditions hbinary A

/-- In target rank three, the target's complete diagonal space represents
the first binary segment of the source directly from the ambient hypothesis.
This is the paper's "obvious if `n = 3`" clause. -/
theorem binaryPrefixRepresentation_of_ambient_rankThree
    (a : GoodBONG q L 3) (c : GoodBONG r M (S + 2))
    (ambient : q.Represents r) :
    DiagonalRepresents
      (c.prefixValues 2 (by omega))
      (a.prefixValues 3 (Nat.le_refl _)) := by
  let w := c.toBONG.segmentWitness 0 2 (by omega)
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

/-- Exception (a) is also impossible in target rank three, where no fourth
order and no condition-(iii') estimate are needed. -/
theorem not_lemma814ExceptionA_of_equalSecondOrder_rankThree
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L 3) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ 2)
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin 3) = c.order (1 : Fin (S + 2)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c hRank) :
    ¬a.Beli2019Lemma814ExceptionA c.firstUnarySegment := by
  have hbinary := a.binaryPrefixRepresentation_of_ambient_rankThree c ambient
  exact a.not_lemma814ExceptionA_of_binaryPrefixRepresentation
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      c hRank hfirst hsecond conditions hbinary

/-- Rank three and ranks at least four combine into the complete
exception-(a) exclusion used by the `R₂ = S₂` branch.  The final hypothesis
is vacuous in rank three and records `R₂ < R₄` in every higher rank. -/
theorem not_lemma814ExceptionA_of_equalSecondOrder_allRanks
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
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
    (hsecondFourth : ∀ hfour : 3 < N + 3,
      a.order (1 : Fin (N + 3)) < a.order ⟨3, hfour⟩) :
    ¬a.Beli2019Lemma814ExceptionA c.firstUnarySegment := by
  cases N with
  | zero =>
      exact a.not_lemma814ExceptionA_of_equalSecondOrder_rankThree
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          c hRank hfirst hsecond ambient conditions
  | succ N =>
      have hfour : 3 < N.succ + 3 := by omega
      exact a.not_lemma814ExceptionA_of_equalSecondOrder
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          c hRank hfirst hsecond conditions hfour
            (hsecondFourth hfour)

/-- Condition (iii') at `i = 3` gives the binary-prefix representation used
in the exception-(a) branch.  The conversion from condition (iii) is the
already proved revised-v2 Lemma 2.16. -/
theorem binaryPrefixRepresentation_of_centralDefectInequality
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (conditions : RepresentationConditions a c hRank)
    (hfour : 3 < N + 3)
    (horder : c.order (1 : Fin (S + 2)) <
      a.order ⟨3, hfour⟩)
    (hdefect : a.lemma91BinaryCentralDefectInequality c hfour) :
    DiagonalRepresents
      (c.prefixValues 2 (by omega))
      (a.prefixValues 3 (by omega)) :=
  binaryPrefixRepresentation_of_centralDefectInequalityCore
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      a c hRank conditions hfour horder hdefect

end BONG.GoodBONG

end Bong
