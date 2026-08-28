/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93CaseTwoSubcaseA
import Bong.Bong.Beli2019Lemma29ComparisonReduction

/-!
# Beli (2019), Lemma 9.3: ordinary Case 2(b)

This file follows lines 9348--9376 of the v2 source.  The strict failure at
`β₃` first forces the source order pattern `S₁ = S₃`, `S₂ < S₄`.  It then
selects the second target order alternative and applies the double-crossing
branch of Lemma 2.9 at `A₃`.
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

private theorem representationIndex_eq_of_val_eq_caseTwo
    {largeRank smallRank : Nat}
    (i j : RepresentationIndex largeRank smallRank)
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  simp_all

/-- If the first of two nested capped minima is below both possible final
caps, changing that final cap does not change the minimum. -/
theorem min_nested_eq_of_lt_caps (x y c d : WithTop ℚ)
    (hc : min x (min y c) < c) (hd : min x (min y c) < d) :
    min x (min y c) = min x (min y d) := by
  have hxyc : min x y < c := by
    have h : min (min x y) c < c := by
      simpa only [min_assoc] using hc
    exact (min_lt_iff.mp h).resolve_right (lt_irrefl c)
  have horiginal : min x (min y c) = min x y := by
    rw [← min_assoc, min_eq_left hxyc.le]
  have hxyd : min x y < d := by
    rw [horiginal] at hd
    exact hd
  rw [horiginal, ← min_assoc, min_eq_left hxyd.le]

set_option maxHeartbeats 800000 in
-- Several dependent finite indices must be normalized after substituting `i.val = 3`.
/-- The strict `β₃ < β₃*` failure rules out every early alternative of the
source Lemma 9.2 transform.  Goodness then turns the first two negations into
`S₁ = S₃` and `S₂ < S₄`. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.sourceOrderPattern_of_thirdPrimaryStrict
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : i.val = 3)
    (hstrict :
      P.normalized.targetTransform.transformed.representationPrimaryDefect
          P.normalized.sourceTransform.transformed i.tailShift <
        P.normalized.targetTransform.transformed.tail.representationPrimaryDefect
          P.normalized.sourceTransform.transformed.tail i) :
    P.normalized.sourceTransform.transformed.order (0 : Fin (N + 4)) =
        P.normalized.sourceTransform.transformed.order (2 : Fin (N + 4)) ∧
      P.normalized.sourceTransform.transformed.order (1 : Fin (N + 4)) <
        P.normalized.sourceTransform.transformed.order (3 : Fin (N + 4)) := by
  let B := P.normalized.sourceTransform.transformed
  have hfailure := P.primaryStrict_sourceAlphaFailure
    (classificationV := classificationV) i (by omega) hstrict
  have hfailureThree :
      (B.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) <
        (B.tail.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
    have h := hfailure.2
    have hleft : (⟨i.val - 1, by have := i.lt_large; omega⟩ :
        Fin (N + 3)) = (2 : Fin (N + 3)) := by
      apply Fin.ext
      change i.val - 1 = 2 % (N + 3)
      rw [hi, Nat.mod_eq_of_lt (by omega)]
    have hright : (⟨i.val - 2, by have := i.lt_large; omega⟩ :
        Fin (N + 2)) = (1 : Fin (N + 2)) := by
      apply Fin.ext
      change i.val - 2 = 1 % (N + 2)
      rw [hi, Nat.mod_eq_of_lt (by omega)]
    simpa only [B, hleft, hright] using h
  have hnotBefore :
      ¬P.normalized.sourceBeforeLemma92.Lemma92EarlyAlternative := by
    intro hearly
    have heq := by
      letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
      exact P.normalized.sourceTransform.transformed_earlyAlpha_eq_tail hearly
    exact (ne_of_lt hfailureThree)
      (congrArg (fun x : ℚ => (x : WithTop ℚ)) heq)
  have hnotB : ¬B.Lemma92EarlyAlternative := by
    intro hearly
    apply hnotBefore
    exact (P.normalized.sourceBeforeLemma92.lemma92EarlyAlternative_iff
      (classification := classificationW) B).mpr hearly
  have hnotFirst : ¬B.order (0 : Fin (N + 4)) <
      B.order (2 : Fin (N + 4)) := by
    intro h
    exact hnotB (Or.inl h)
  have hnotSecond : ¬B.order (1 : Fin (N + 4)) =
      B.order (3 : Fin (N + 4)) := by
    intro h
    exact hnotB (Or.inr (Or.inl h))
  have hsourceFirstThird : B.order (0 : Fin (N + 4)) =
      B.order (2 : Fin (N + 4)) :=
    le_antisymm B.order_zero_le_two (le_of_not_gt hnotFirst)
  have htail := B.tail.order_zero_le_two
  have hsourceSecondFourthLe : B.order (1 : Fin (N + 4)) ≤
      B.order (3 : Fin (N + 4)) := by
    have hzeroSucc : (⟨0, by omega⟩ : Fin (N + 3)).succ =
        (1 : Fin (N + 4)) := by
      apply Fin.ext
      simp
    have htwoSucc : (⟨2, by omega⟩ : Fin (N + 3)).succ =
        (3 : Fin (N + 4)) := by
      apply Fin.ext
      change 2 + 1 = 3 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [B.order_goodTail, B.order_goodTail, hzeroSucc, htwoSucc] at htail
    exact htail
  exact ⟨hsourceFirstThird,
    lt_of_le_of_ne hsourceSecondFourthLe hnotSecond⟩

set_option maxHeartbeats 800000 in
-- The proof combines the source order pattern with the selected Case-2 order dichotomy.
/-- In Case 2(b), the first target order alternative is impossible.  Hence
`R₂ = S₂ < R₄`, exactly as in lines 9351--9352. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.secondSelectedOrder_of_thirdPrimaryStrict
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : i.val = 3)
    (hstrict :
      P.normalized.targetTransform.transformed.representationPrimaryDefect
          P.normalized.sourceTransform.transformed i.tailShift <
        P.normalized.targetTransform.transformed.tail.representationPrimaryDefect
          P.normalized.sourceTransform.transformed.tail i)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed)
    (horder :
      P.normalized.targetTransform.transformed.order (0 : Fin (N + 4)) <
          P.normalized.targetTransform.transformed.order (2 : Fin (N + 4)) ∨
        (P.normalized.targetTransform.transformed.order (1 : Fin (N + 4)) =
            P.normalized.sourceTransform.transformed.order (1 : Fin (N + 4)) ∧
          P.normalized.targetTransform.transformed.order (1 : Fin (N + 4)) <
            P.normalized.targetTransform.transformed.order (3 : Fin (N + 4)))) :
    P.normalized.targetTransform.transformed.order (1 : Fin (N + 4)) =
        P.normalized.sourceTransform.transformed.order (1 : Fin (N + 4)) ∧
      P.normalized.targetTransform.transformed.order (1 : Fin (N + 4)) <
        P.normalized.targetTransform.transformed.order (3 : Fin (N + 4)) := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  have hsourcePattern := P.sourceOrderPattern_of_thirdPrimaryStrict
    (classificationV := classificationV) (classificationW := classificationW)
    i hi hstrict
  rcases horder with hfirst | hsecond
  · have hthirdTarget :=
      P.thirdTargetOrder_le_thirdSourceOrder_of_primaryStrict
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        (classificationV := classificationV) i (Or.inr hi) hstrict hcase
    have hhead : A.order (0 : Fin (N + 4)) =
        B.order (0 : Fin (N + 4)) := by
      unfold GoodBONG.order
      rw [A.toBONG.order_eq_ordUnit, B.toBONG.order_eq_ordUnit]
      exact congrArg (ordUnit K) (by
        apply Units.ext
        exact P.normalized.headValue_eq)
    have : A.order (0 : Fin (N + 4)) <
        A.order (0 : Fin (N + 4)) := by
      calc
        A.order (0 : Fin (N + 4)) < A.order (2 : Fin (N + 4)) := hfirst
        _ ≤ B.order (2 : Fin (N + 4)) := hthirdTarget
        _ = B.order (0 : Fin (N + 4)) := hsourcePattern.1.symm
        _ = A.order (0 : Fin (N + 4)) := hhead.symm
    exact (lt_irrefl _ this).elim
  · exact hsecond

set_option maxHeartbeats 1200000 in
-- This proof normalizes four finite indices and three nested `WithTop ℚ` minima.
/-- Lemma 2.9 at the third boundary in Case 2(b).  The selected order pattern
gives both crossing inequalities and a positive secondary shift.  The
half-gap candidate is strictly above `β₁ ≥ A₃`, so the primary candidate
must realize `A₃`. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.thirdRepresentationAlpha_eq_primary_of_thirdPrimaryStrict
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : i.val = 3)
    (hstrict :
      P.normalized.targetTransform.transformed.representationPrimaryDefect
          P.normalized.sourceTransform.transformed i.tailShift <
        P.normalized.targetTransform.transformed.tail.representationPrimaryDefect
          P.normalized.sourceTransform.transformed.tail i)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed)
    (horder :
      P.normalized.targetTransform.transformed.order (0 : Fin (N + 4)) <
          P.normalized.targetTransform.transformed.order (2 : Fin (N + 4)) ∨
        (P.normalized.targetTransform.transformed.order (1 : Fin (N + 4)) =
            P.normalized.sourceTransform.transformed.order (1 : Fin (N + 4)) ∧
          P.normalized.targetTransform.transformed.order (1 : Fin (N + 4)) <
            P.normalized.targetTransform.transformed.order (3 : Fin (N + 4)))) :
    P.normalized.targetTransform.transformed.representationAlpha
        P.normalized.sourceTransform.transformed
          (lemma93ThirdRepresentationIndex N) =
      P.normalized.targetTransform.transformed.representationPrimaryDefect
        P.normalized.sourceTransform.transformed
          (lemma93ThirdRepresentationIndex N) := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let third := lemma93ThirdRepresentationIndex N
  let fifth : Fin (N + 4) := ⟨4, by have := i.lt_large; omega⟩
  have hN : 0 < N := by
    have := i.lt_large
    omega
  have hone : (⟨3 - 2, by omega⟩ : Fin (N + 4)) =
      (1 : Fin (N + 4)) := by
    apply Fin.ext
    change 3 - 2 = 1 % (N + 4)
    rw [Nat.mod_eq_of_lt (by omega)]
  have htwo : (⟨3 - 1, by omega⟩ : Fin (N + 4)) =
      (2 : Fin (N + 4)) := by
    apply Fin.ext
    change 3 - 1 = 2 % (N + 4)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hthree : (⟨3, by omega⟩ : Fin (N + 4)) =
      (3 : Fin (N + 4)) := by
    apply Fin.ext
    change 3 = 3 % (N + 4)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hfour : (⟨3 + 1, by omega⟩ : Fin (N + 4)) = fifth := by
    apply Fin.ext
    rfl
  have hsourcePattern := P.sourceOrderPattern_of_thirdPrimaryStrict
    (classificationV := classificationV) (classificationW := classificationW)
    i hi hstrict
  have hselected := P.secondSelectedOrder_of_thirdPrimaryStrict
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (classificationV := classificationV) (classificationW := classificationW)
    i hi hstrict hcase horder
  have hhead : A.order (0 : Fin (N + 4)) =
      B.order (0 : Fin (N + 4)) := by
    unfold GoodBONG.order
    rw [A.toBONG.order_eq_ordUnit, B.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) (by
      apply Units.ext
      exact P.normalized.headValue_eq)
  have htargetZeroLeFour : A.order (0 : Fin (N + 4)) ≤
      A.order fifth := by
    have hzeroTwo := A.order_zero_le_two
    have htwoFour : A.order (2 : Fin (N + 4)) ≤ A.order fifth := by
      let two : Fin (N + 4) := ⟨2, by omega⟩
      let four : Fin (N + 4) := ⟨4, by omega⟩
      have hraw := A.good two (by simp only [two]; omega)
      have h : A.order two ≤ A.order four := by
        unfold GoodBONG.order
        convert hraw using 1 <;> apply Fin.ext <;> rfl
      have htwoIndex : two = (2 : Fin (N + 4)) := by
        apply Fin.ext
        change 2 = 2 % (N + 4)
        rw [Nat.mod_eq_of_lt (by omega)]
      have hend : four = fifth := by
        apply Fin.ext
        rfl
      calc
        A.order (2 : Fin (N + 4)) = A.order two :=
          congrArg A.order htwoIndex.symm
        _ ≤ A.order four := h
        _ = A.order fifth := congrArg A.order hend
    exact hzeroTwo.trans htwoFour
  have hleft : B.order (1 : Fin (N + 4)) ≤
      A.order (3 : Fin (N + 4)) := by
    rw [← hselected.1]
    exact hselected.2.le
  have hright : B.order (2 : Fin (N + 4)) ≤ A.order fifth := by
    rw [← hsourcePattern.1, ← hhead]
    exact htargetZeroLeFour
  have hshift : 0 <
      A.order (3 : Fin (N + 4)) + A.order fifth -
        B.order (1 : Fin (N + 4)) - B.order (2 : Fin (N + 4)) := by
    have hfourth : B.order (1 : Fin (N + 4)) <
        A.order (3 : Fin (N + 4)) := by
      rw [← hselected.1]
      exact hselected.2
    omega
  have hcomparison : A.representationAlpha B third ≤
      A.truncatedPrefixDefect B 1 3 3 := by
    have h := P.normalized.selectedConditions.defectCondition third
    rw [A.coe_representationAlphaValue B third] at h
    simpa only [third, lemma93ThirdRepresentationIndex] using h
  have hnormal := A.representationAlpha_eq_min_halfGap_primary_of_comparison
    (alphaV := targetLaws) (alphaW := sourceLaws) B third (by
      simp only [third, lemma93ThirdRepresentationIndex]
      exact ⟨by omega, by omega⟩) (by
        simpa only [third, lemma93ThirdRepresentationIndex, hone, hthree]
          using hleft)
      (by
        simpa only [third, lemma93ThirdRepresentationIndex, htwo, hfour]
          using hright)
      (by
        simpa only [third, lemma93ThirdRepresentationIndex, hone, htwo,
          hthree, hfour] using hshift)
      hcomparison
  have hbetaThreshold :
      (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) <
        ((((B.order (1 : Fin (N + 4)) -
          A.order (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
            (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    rw [← hcase.1]
    exact hcase.2.1
  have hthresholdHalf :
      ((((B.order (1 : Fin (N + 4)) -
        A.order (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) <
        A.representationHalfGap B third := by
    unfold representationHalfGap
    simp only [third, lemma93ThirdRepresentationIndex, htwo, hthree]
    apply WithTop.coe_lt_coe.mpr
    have htargetZeroTwo := A.order_zero_le_two
    have hfourth : B.order (1 : Fin (N + 4)) <
        A.order (3 : Fin (N + 4)) := by
      rw [← hselected.1]
      exact hselected.2
    have hsourceThirdTargetThird : B.order (2 : Fin (N + 4)) ≤
        A.order (2 : Fin (N + 4)) := by
      rw [← hsourcePattern.1, ← hhead]
      exact htargetZeroTwo
    have hfourthQ : (B.order (1 : Fin (N + 4)) : ℚ) <
        (A.order (3 : Fin (N + 4)) : ℚ) := by
      exact_mod_cast hfourth
    have hsourceThirdTargetThirdQ :
        (B.order (2 : Fin (N + 4)) : ℚ) ≤
          (A.order (2 : Fin (N + 4)) : ℚ) := by
      exact_mod_cast hsourceThirdTargetThird
    push_cast
    linarith
  have hbetaHalf : (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) <
      A.representationHalfGap B third :=
    hbetaThreshold.trans hthresholdHalf
  have hthirdLeBeta :=
    P.thirdRepresentationAlpha_le_firstSourceAlpha_of_primaryStrict
      (sourceLaws := sourceLaws) (classificationV := classificationV)
      i (Or.inr hi) hstrict
  have hthirdLtHalf : A.representationAlpha B third <
      A.representationHalfGap B third :=
    hthirdLeBeta.trans_lt hbetaHalf
  have hprimaryLeHalf : A.representationPrimaryDefect B third ≤
      A.representationHalfGap B third := by
    by_contra hnot
    have hhalfLe : A.representationHalfGap B third ≤
        A.representationPrimaryDefect B third := le_of_not_ge hnot
    have heq : A.representationAlpha B third =
        A.representationHalfGap B third :=
      hnormal.trans (min_eq_left hhalfLe)
    exact (ne_of_lt hthirdLtHalf) heq
  exact hnormal.trans (min_eq_right hprimaryLeHalf)

set_option maxHeartbeats 1000000 in
-- Coercion cancellation is performed only after the capped defect is shown finite.
/-- The next inequality in Case 2(b):
`d[-a_(1,4)b_(1,2)] < β₂`. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.fourthSecondDefect_lt_sourceSecondAlpha
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : i.val = 3)
    (hstrict :
      P.normalized.targetTransform.transformed.representationPrimaryDefect
          P.normalized.sourceTransform.transformed i.tailShift <
        P.normalized.targetTransform.transformed.tail.representationPrimaryDefect
          P.normalized.sourceTransform.transformed.tail i)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed)
    (horder :
      P.normalized.targetTransform.transformed.order (0 : Fin (N + 4)) <
          P.normalized.targetTransform.transformed.order (2 : Fin (N + 4)) ∨
        (P.normalized.targetTransform.transformed.order (1 : Fin (N + 4)) =
            P.normalized.sourceTransform.transformed.order (1 : Fin (N + 4)) ∧
          P.normalized.targetTransform.transformed.order (1 : Fin (N + 4)) <
            P.normalized.targetTransform.transformed.order (3 : Fin (N + 4)))) :
    P.normalized.targetTransform.transformed.truncatedPrefixDefect
        P.normalized.sourceTransform.transformed (-1) 4 2 <
      (P.normalized.sourceTransform.transformed.alphaValue
        (1 : Fin (N + 3)) : WithTop ℚ) := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let third := lemma93ThirdRepresentationIndex N
  let D := A.truncatedPrefixDefect B (-1) 4 2
  have hselected := P.secondSelectedOrder_of_thirdPrimaryStrict
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (classificationV := classificationV) (classificationW := classificationW)
    i hi hstrict hcase horder
  have hthirdEq := P.thirdRepresentationAlpha_eq_primary_of_thirdPrimaryStrict
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (classificationV := classificationV) (classificationW := classificationW)
    i hi hstrict hcase horder
  have hthirdLeBeta :=
    P.thirdRepresentationAlpha_le_firstSourceAlpha_of_primaryStrict
      (sourceLaws := sourceLaws) (classificationV := classificationV)
      i (Or.inr hi) hstrict
  have hprimaryLeBeta : A.representationPrimaryDefect B third ≤
      (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := by
    rw [← hthirdEq]
    exact hthirdLeBeta
  have hDne : D ≠ ⊤ := by
    intro htop
    have h := hprimaryLeBeta
    unfold representationPrimaryDefect at h
    simp only [third, lemma93ThirdRepresentationIndex] at h
    change (((A.order (3 : Fin (N + 4)) -
      B.order (2 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) + D ≤
        (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) at h
    rw [htop, add_top] at h
    exact WithTop.coe_ne_top (top_unique h)
  let d : ℚ := D.untop hDne
  have hd : (d : WithTop ℚ) = D := WithTop.coe_untop D hDne
  have hprimaryLeBetaQ :
      ((A.order (3 : Fin (N + 4)) -
        B.order (2 : Fin (N + 4)) : Int) : ℚ) + d ≤
          B.alphaValue (0 : Fin (N + 3)) := by
    have h := hprimaryLeBeta
    unfold representationPrimaryDefect at h
    simp only [third, lemma93ThirdRepresentationIndex] at h
    change (((A.order (3 : Fin (N + 4)) -
      B.order (2 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) + D ≤
        (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) at h
    rw [← hd, ← WithTop.coe_add] at h
    exact WithTop.coe_le_coe.mp h
  have hsourceFormula := P.sourceSecondAlphaFormula_of_primaryStrict
    (sourceLaws := sourceLaws) (classificationV := classificationV)
    i (Or.inr hi) hstrict
  have hfourth : B.order (1 : Fin (N + 4)) <
      A.order (3 : Fin (N + 4)) := by
    rw [← hselected.1]
    exact hselected.2
  have hfourthQ : (B.order (1 : Fin (N + 4)) : ℚ) <
      (A.order (3 : Fin (N + 4)) : ℚ) := by
    exact_mod_cast hfourth
  have hdlt : d < B.alphaValue (1 : Fin (N + 3)) := by
    push_cast at hprimaryLeBetaQ hsourceFormula ⊢
    linarith
  change D < (B.alphaValue (1 : Fin (N + 3)) : WithTop ℚ)
  rw [← hd]
  exact WithTop.coe_lt_coe.mpr hdlt

set_option maxHeartbeats 1000000 in
-- The proof unfolds both capped minima after transporting their raw defect and target cap.
/-- The equality concluded on line 9358:
`d[-a_(1,4)b_(1,2)] = d[-a_(2,4)b_2]`.  In zero-based tail notation the
right side is the corresponding `3`-by-`1` capped defect. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.fourthSecondDefect_eq_tail
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : i.val = 3)
    (hstrict :
      P.normalized.targetTransform.transformed.representationPrimaryDefect
          P.normalized.sourceTransform.transformed i.tailShift <
        P.normalized.targetTransform.transformed.tail.representationPrimaryDefect
          P.normalized.sourceTransform.transformed.tail i)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed)
    (horder :
      P.normalized.targetTransform.transformed.order (0 : Fin (N + 4)) <
          P.normalized.targetTransform.transformed.order (2 : Fin (N + 4)) ∨
        (P.normalized.targetTransform.transformed.order (1 : Fin (N + 4)) =
            P.normalized.sourceTransform.transformed.order (1 : Fin (N + 4)) ∧
          P.normalized.targetTransform.transformed.order (1 : Fin (N + 4)) <
            P.normalized.targetTransform.transformed.order (3 : Fin (N + 4)))) :
    P.normalized.targetTransform.transformed.truncatedPrefixDefect
        P.normalized.sourceTransform.transformed (-1) 4 2 =
      P.normalized.targetTransform.transformed.tail.truncatedPrefixDefect
        P.normalized.sourceTransform.transformed.tail (-1) 3 1 := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let D := A.truncatedPrefixDefect B (-1) 4 2
  let E := A.tail.truncatedPrefixDefect B.tail (-1) 3 1
  let raw := defectOrder (K := K)
    ((-1) * A.tail.prefixProduct 3 * B.tail.prefixProduct 1)
  let left := A.tail.prefixAlphaCap 3
  let right := B.prefixAlphaCap 2
  let rightTail := B.tail.prefixAlphaCap 1
  have hN : 0 < N := by
    have := i.lt_large
    omega
  have hdefectLt := P.fourthSecondDefect_lt_sourceSecondAlpha
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (classificationV := classificationV) (classificationW := classificationW)
    i hi hstrict hcase horder
  have hraw := A.defectOrder_shiftedPrefixes_eq_tail B
    P.normalized.headValue_eq (-1) 3 1 (by omega) (by omega)
  have hcapA := by
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    exact A.prefixAlphaCap_shift_eq_tail_of_laterAlphaValue_eq
      (fun k hk ↦
        P.normalized.targetTransform.transformed_laterAlpha_eq_tail k hk)
      3 (by omega) (by omega)
  have hDdecomp : D = min raw (min left right) := by
    unfold D raw left right truncatedPrefixDefect
    rw [hraw, hcapA]
  have hEdecomp : E = min raw (min left rightTail) := by
    rfl
  have hright : right =
      (B.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) := by
    unfold right
    rw [B.prefixAlphaCap_of_internal (by omega) (by omega)]
    congr 1
  have hrightTail : rightTail =
      (B.tail.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
    unfold rightTail
    rw [B.tail.prefixAlphaCap_of_internal (by omega) (by omega)]
    congr 1
  have hshiftAlpha :
      (B.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) ≤
        (B.tail.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
    have h := B.alphaValue_shift_le_tail (0 : Fin (N + 2))
    simpa using h
  have hDltRight : D < right := by
    rw [hright]
    exact hdefectLt
  have hDltRightTail : D < rightTail := by
    rw [hrightTail]
    exact hdefectLt.trans_le hshiftAlpha
  have hnested := min_nested_eq_of_lt_caps raw left right rightTail
    (by rw [← hDdecomp]; exact hDltRight)
    (by rw [← hDdecomp]; exact hDltRightTail)
  change D = E
  exact hDdecomp.trans (hnested.trans hEdecomp.symm)

set_option maxHeartbeats 800000 in
-- The direct primary-candidate calculation contains dependent tail indices.
/-- Exact transport at the second tail boundary in Case 2(b).  The primary
candidate equality follows from `fourthSecondDefect_eq_tail`; ordinary tail
monotonicity supplies the opposite inequality needed to obtain equality of
the full representation invariants. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.secondTailRepresentationAlpha_eq
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : i.val = 3)
    (hstrict :
      P.normalized.targetTransform.transformed.representationPrimaryDefect
          P.normalized.sourceTransform.transformed i.tailShift <
        P.normalized.targetTransform.transformed.tail.representationPrimaryDefect
          P.normalized.sourceTransform.transformed.tail i)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed)
    (horder :
      P.normalized.targetTransform.transformed.order (0 : Fin (N + 4)) <
          P.normalized.targetTransform.transformed.order (2 : Fin (N + 4)) ∨
        (P.normalized.targetTransform.transformed.order (1 : Fin (N + 4)) =
            P.normalized.sourceTransform.transformed.order (1 : Fin (N + 4)) ∧
          P.normalized.targetTransform.transformed.order (1 : Fin (N + 4)) <
            P.normalized.targetTransform.transformed.order (3 : Fin (N + 4)))) :
    P.normalized.targetTransform.transformed.tail.representationAlpha
        P.normalized.sourceTransform.transformed.tail
          (lemma93SecondTailRepresentationIndex N) =
      P.normalized.targetTransform.transformed.representationAlpha
        P.normalized.sourceTransform.transformed
          (lemma93ThirdRepresentationIndex N) := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let secondTail := lemma93SecondTailRepresentationIndex N
  let third := lemma93ThirdRepresentationIndex N
  have hdefect := P.fourthSecondDefect_eq_tail
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (classificationV := classificationV) (classificationW := classificationW)
    i hi hstrict hcase horder
  have hprimary : A.tail.representationPrimaryDefect B.tail secondTail =
      A.representationPrimaryDefect B third := by
    unfold representationPrimaryDefect
    simp only [secondTail, third, lemma93SecondTailRepresentationIndex,
      lemma93ThirdRepresentationIndex]
    rw [A.order_goodTail, B.order_goodTail]
    have htarget : (⟨2, by omega⟩ : Fin (N + 3)).succ =
        (3 : Fin (N + 4)) := by
      apply Fin.ext
      change 2 + 1 = 3 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega)]
    have hsource : (⟨2 - 1, by omega⟩ : Fin (N + 3)).succ =
        (2 : Fin (N + 4)) := by
      apply Fin.ext
      change (2 - 1) + 1 = 2 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega)]
    have hthreeOriginal : (⟨3, by omega⟩ : Fin (N + 4)) =
        (3 : Fin (N + 4)) := by
      apply Fin.ext
      change 3 = 3 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega)]
    have htwoOriginal : (⟨3 - 1, by omega⟩ : Fin (N + 4)) =
        (2 : Fin (N + 4)) := by
      apply Fin.ext
      change 3 - 1 = 2 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [htarget, hsource]
    rw [hthreeOriginal, htwoOriginal]
    change _ + A.tail.truncatedPrefixDefect B.tail (-1) 3 1 =
      _ + A.truncatedPrefixDefect B (-1) 4 2
    rw [hdefect]
  have hthirdEq := P.thirdRepresentationAlpha_eq_primary_of_thirdPrimaryStrict
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (classificationV := classificationV) (classificationW := classificationW)
    i hi hstrict hcase horder
  have htailLe : A.tail.representationAlpha B.tail secondTail ≤
      A.representationAlpha B third := by
    calc
      A.tail.representationAlpha B.tail secondTail ≤
          A.tail.representationPrimaryDefect B.tail secondTail :=
        A.tail.representationAlpha_le_primary B.tail secondTail
      _ = A.representationPrimaryDefect B third := hprimary
      _ = A.representationAlpha B third := hthirdEq.symm
  have horiginalLe : A.representationAlpha B third ≤
      A.tail.representationAlpha B.tail secondTail := by
    have h := A.representationAlpha_shift_le_tail B
      P.normalized.headValue_eq secondTail
    have hindex : secondTail.tailShift = third := by
      rfl
    rw [hindex] at h
    exact h
  exact le_antisymm htailLe horiginalLe

set_option maxHeartbeats 1600000 in
-- The final contradiction uses capped-defect domination once, followed by rational arithmetic.
/-- The last contradiction in Case 2(b), lines 9371--9376.  The fourth
representation invariant cannot be its primary candidate.  The paper writes
the intermediate capped defect as `d[-b_(3,4)]`; the proof only needs the
weaker inequality from that adjacent source defect to the mixed defect, and
this is exactly what capped-defect domination supplies. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.fourthRepresentationAlpha_lt_primary_of_thirdPrimaryStrict
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 5)} {b : GoodBONG r M (N + 5)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair (N := N + 1) a b)
    (i : RepresentationIndex (N + 4) (N + 4)) (hi : i.val = 3)
    (hstrict :
      P.normalized.targetTransform.transformed.representationPrimaryDefect
          P.normalized.sourceTransform.transformed i.tailShift <
        P.normalized.targetTransform.transformed.tail.representationPrimaryDefect
          P.normalized.sourceTransform.transformed.tail i)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed)
    (horder :
      P.normalized.targetTransform.transformed.order (0 : Fin (N + 5)) <
          P.normalized.targetTransform.transformed.order (2 : Fin (N + 5)) ∨
        (P.normalized.targetTransform.transformed.order (1 : Fin (N + 5)) =
            P.normalized.sourceTransform.transformed.order (1 : Fin (N + 5)) ∧
          P.normalized.targetTransform.transformed.order (1 : Fin (N + 5)) <
            P.normalized.targetTransform.transformed.order (3 : Fin (N + 5)))) :
    P.normalized.targetTransform.transformed.representationAlpha
        P.normalized.sourceTransform.transformed
          (lemma93FourthRepresentationIndex N) <
      P.normalized.targetTransform.transformed.representationPrimaryDefect
        P.normalized.sourceTransform.transformed
          (lemma93FourthRepresentationIndex N) := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let third := lemma93ThirdRepresentationIndex (N + 1)
  let fourth := lemma93FourthRepresentationIndex N
  let failureIndex : RepresentationIndex (N + 4) (N + 4) :=
    { val := 3
      pos := by omega
      lt_large := by omega
      le_small := by omega }
  have hiIndex : i = failureIndex := by
    cases i with
    | mk val pos lt_large le_small =>
      simp only at hi
      subst val
      rfl
  let D42 := A.truncatedPrefixDefect B (-1) 4 2
  let C44 := A.truncatedPrefixDefect B 1 4 4
  have hstrictFailure :
      A.representationPrimaryDefect B failureIndex.tailShift <
        A.tail.representationPrimaryDefect B.tail failureIndex := by
    simpa only [A, B, hiIndex] using hstrict
  have hfailure := P.primaryStrict_sourceAlphaFailure
    (classificationV := classificationV) failureIndex (by
      simp only [failureIndex]
      omega) hstrictFailure
  have hbetaThreeStrict :
      (B.alphaValue (2 : Fin (N + 4)) : WithTop ℚ) <
        (B.tail.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) := by
    have hleft : (⟨3 - 1, by omega⟩ : Fin (N + 4)) =
        (2 : Fin (N + 4)) := by
      apply Fin.ext
      change 3 - 1 = 2 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega)]
    have hright : (⟨3 - 2, by omega⟩ : Fin (N + 3)) =
        (1 : Fin (N + 3)) := by
      apply Fin.ext
      change 3 - 2 = 1 % (N + 3)
      rw [Nat.mod_eq_of_lt (by omega)]
    simpa only [B, failureIndex, hleft, hright] using hfailure.2
  have hbetaThree := by
    letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
    exact B.thirdAlpha_eq_fourth_sub_second_add_first_of_lt_tail
      hbetaThreeStrict
  have hD53 : A.truncatedPrefixDefect B (-1) 5 3 =
      (B.alphaValue (2 : Fin (N + 4)) : WithTop ℚ) := by
    have hindex : (⟨3 - 1, by omega⟩ : Fin (N + 4)) =
        (2 : Fin (N + 4)) := by
      apply Fin.ext
      change 3 - 1 = 2 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega)]
    simpa only [A, B, failureIndex, Nat.reduceAdd, hindex] using hfailure.1
  have hsourcePattern := P.sourceOrderPattern_of_thirdPrimaryStrict
    (classificationV := classificationV) (classificationW := classificationW)
    i hi hstrict
  have hselected := P.secondSelectedOrder_of_thirdPrimaryStrict
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (classificationV := classificationV) (classificationW := classificationW)
    i hi hstrict hcase horder
  have hhead : A.order (0 : Fin (N + 5)) =
      B.order (0 : Fin (N + 5)) := by
    unfold GoodBONG.order
    rw [A.toBONG.order_eq_ordUnit, B.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) (by
      apply Units.ext
      exact P.normalized.headValue_eq)
  have htwoFourRaw := A.good
    (⟨2, by omega⟩ : Fin (N + 1 + 4)) (by
      change 2 + 2 < N + 1 + 4
      omega)
  have htwoFour : A.order (2 : Fin (N + 5)) ≤
      A.order (4 : Fin (N + 5)) := by
    unfold GoodBONG.order
    convert htwoFourRaw using 1 <;> congr 1 <;> apply Fin.ext <;> simp
  have hsourceThirdLeTargetFifth : B.order (2 : Fin (N + 5)) ≤
      A.order (4 : Fin (N + 5)) := by
    calc
      B.order (2 : Fin (N + 5)) = B.order (0 : Fin (N + 5)) :=
        hsourcePattern.1.symm
      _ = A.order (0 : Fin (N + 5)) := hhead.symm
      _ ≤ A.order (2 : Fin (N + 5)) := A.order_zero_le_two
      _ ≤ A.order (4 : Fin (N + 5)) := htwoFour
  have hfourthLe := A.representationAlpha_le_primary B fourth
  by_contra hnotStrict
  have hfourthEq : A.representationAlpha B fourth =
      A.representationPrimaryDefect B fourth :=
    le_antisymm hfourthLe (le_of_not_gt hnotStrict)
  have hcomparison := P.normalized.selectedConditions.defectCondition fourth
  rw [A.coe_representationAlphaValue B fourth] at hcomparison
  have hprimaryLeComparison : A.representationPrimaryDefect B fourth ≤ C44 := by
    rw [← hfourthEq]
    exact hcomparison
  have hprimaryFormula : A.representationPrimaryDefect B fourth =
      (((((A.order (4 : Fin (N + 5)) -
          B.order (3 : Fin (N + 5)) : Int) : ℚ) +
        B.alphaValue (2 : Fin (N + 4)) : ℚ)) : WithTop ℚ) := by
    unfold representationPrimaryDefect
    simp only [fourth, lemma93FourthRepresentationIndex]
    have hfour : (⟨4, by omega⟩ : Fin (N + 5)) =
        (4 : Fin (N + 5)) := by
      apply Fin.ext
      change 4 = 4 % (N + 5)
      rw [Nat.mod_eq_of_lt (by omega)]
    have hthree : (⟨4 - 1, by omega⟩ : Fin (N + 5)) =
        (3 : Fin (N + 5)) := by
      apply Fin.ext
      change 4 - 1 = 3 % (N + 5)
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hfour, hthree]
    rw [hD53, ← WithTop.coe_add]
  have hprimaryGtQ :
      ((B.order (2 : Fin (N + 5)) -
        A.order (3 : Fin (N + 5)) : Int) : ℚ) +
          B.alphaValue (0 : Fin (N + 4)) <
        ((A.order (4 : Fin (N + 5)) -
          B.order (3 : Fin (N + 5)) : Int) : ℚ) +
            B.alphaValue (2 : Fin (N + 4)) := by
    have hsourceThirdLeTargetFifthQ :
        (B.order (2 : Fin (N + 5)) : ℚ) ≤
          (A.order (4 : Fin (N + 5)) : ℚ) := by
      exact_mod_cast hsourceThirdLeTargetFifth
    have hselectedQ : (B.order (1 : Fin (N + 5)) : ℚ) <
        (A.order (3 : Fin (N + 5)) : ℚ) := by
      rw [← hselected.1]
      exact_mod_cast hselected.2
    push_cast at hbetaThree ⊢
    linarith
  have hthresholdLtComparison :
      (((((B.order (2 : Fin (N + 5)) -
          A.order (3 : Fin (N + 5)) : Int) : ℚ) +
        B.alphaValue (0 : Fin (N + 4)) : ℚ)) : WithTop ℚ) < C44 := by
    have hthresholdLtPrimary :
        (((((B.order (2 : Fin (N + 5)) -
            A.order (3 : Fin (N + 5)) : Int) : ℚ) +
          B.alphaValue (0 : Fin (N + 4)) : ℚ)) : WithTop ℚ) <
            A.representationPrimaryDefect B fourth := by
      rw [hprimaryFormula]
      exact WithTop.coe_lt_coe.mpr hprimaryGtQ
    exact hthresholdLtPrimary.trans_le hprimaryLeComparison
  have hthirdEq := P.thirdRepresentationAlpha_eq_primary_of_thirdPrimaryStrict
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (classificationV := classificationV) (classificationW := classificationW)
    i hi hstrict hcase horder
  have hthirdLeBeta :=
    P.thirdRepresentationAlpha_le_firstSourceAlpha_of_primaryStrict
      (sourceLaws := sourceLaws) (classificationV := classificationV)
      i (Or.inr hi) hstrict
  have hprimaryThirdLeBeta : A.representationPrimaryDefect B third ≤
      (B.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) := by
    rw [← hthirdEq]
    exact hthirdLeBeta
  have hD42lt := P.fourthSecondDefect_lt_sourceSecondAlpha
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (classificationV := classificationV) (classificationW := classificationW)
    i hi hstrict hcase horder
  have hD42ne : D42 ≠ ⊤ := ne_top_of_lt hD42lt
  let d42 : ℚ := D42.untop hD42ne
  have hd42 : (d42 : WithTop ℚ) = D42 := WithTop.coe_untop D42 hD42ne
  have hprimaryThirdLeBetaQ :
      ((A.order (3 : Fin (N + 5)) -
        B.order (2 : Fin (N + 5)) : Int) : ℚ) + d42 ≤
          B.alphaValue (0 : Fin (N + 4)) := by
    have h := hprimaryThirdLeBeta
    unfold representationPrimaryDefect at h
    simp only [third, lemma93ThirdRepresentationIndex] at h
    change (((A.order (3 : Fin (N + 5)) -
      B.order (2 : Fin (N + 5)) : Int) : ℚ) : WithTop ℚ) + D42 ≤
        (B.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) at h
    rw [← hd42, ← WithTop.coe_add] at h
    exact WithTop.coe_le_coe.mp h
  have hd42ThresholdQ : d42 ≤
      ((B.order (2 : Fin (N + 5)) -
        A.order (3 : Fin (N + 5)) : Int) : ℚ) +
          B.alphaValue (0 : Fin (N + 4)) := by
    push_cast at hprimaryThirdLeBetaQ ⊢
    linarith
  have hD42leThreshold : D42 ≤
      (((((B.order (2 : Fin (N + 5)) -
          A.order (3 : Fin (N + 5)) : Int) : ℚ) +
        B.alphaValue (0 : Fin (N + 4)) : ℚ)) : WithTop ℚ) := by
    rw [← hd42]
    exact WithTop.coe_le_coe.mpr hd42ThresholdQ
  have hD42ltComparison : D42 < C44 :=
    hD42leThreshold.trans_lt hthresholdLtComparison
  have hdomination :=
    A.truncatedPrefixDefect_domination B B 1 (-1) 4 4 2
  have hdomination' :
      min C44 (B.truncatedPrefixDefect B (-1) 4 2) ≤ D42 := by
    simpa only [C44, D42, one_mul] using hdomination
  have hsourceAdjacentLeD42 :
      B.truncatedPrefixDefect B (-1) 4 2 ≤ D42 := by
    by_contra hnot
    have hD42ltAdjacent : D42 <
        B.truncatedPrefixDefect B (-1) 4 2 := lt_of_not_ge hnot
    have hD42ltMin : D42 <
        min C44 (B.truncatedPrefixDefect B (-1) 4 2) :=
      lt_min hD42ltComparison hD42ltAdjacent
    exact (not_lt_of_ge hdomination') hD42ltMin
  have hsourceAdjacentLeD42' :
      B.truncatedPrefixDefect B (-1) 2 4 ≤ D42 := by
    rw [B.truncatedPrefixDefect_comm B (-1) 2 4]
    exact hsourceAdjacentLeD42
  have hsourceLower := by
    letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
    exact B.order_sub_add_alpha_le_cappedAdjacent
      (2 : Fin (N + 4))
  have htwoCast : (2 : Fin (N + 4)).castSucc =
      (2 : Fin (N + 5)) := by
    apply Fin.ext
    change 2 % (N + 4) = 2 % (N + 5)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have htwoSucc : (2 : Fin (N + 4)).succ =
      (3 : Fin (N + 5)) := by
    apply Fin.ext
    change 2 % (N + 4) + 1 = 3 % (N + 5)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have htwoVal : (2 : Fin (N + 4)).val = 2 := by
    change 2 % (N + 4) = 2
    rw [Nat.mod_eq_of_lt (by omega)]
  have hsourceLower' :
      (((((B.order (2 : Fin (N + 5)) -
          B.order (3 : Fin (N + 5)) : Int) : ℚ) +
        B.alphaValue (2 : Fin (N + 4)) : ℚ)) : WithTop ℚ) ≤
          B.truncatedPrefixDefect B (-1) 2 4 := by
    rw [htwoCast, htwoSucc, htwoVal] at hsourceLower
    simpa using hsourceLower
  have hfinalTop := hsourceLower'.trans
    (hsourceAdjacentLeD42'.trans hD42leThreshold)
  have hfinalQ :
      ((B.order (2 : Fin (N + 5)) -
        B.order (3 : Fin (N + 5)) : Int) : ℚ) +
          B.alphaValue (2 : Fin (N + 4)) ≤
        ((B.order (2 : Fin (N + 5)) -
          A.order (3 : Fin (N + 5)) : Int) : ℚ) +
            B.alphaValue (0 : Fin (N + 4)) :=
    WithTop.coe_le_coe.mp hfinalTop
  have hselectedQ : (B.order (1 : Fin (N + 5)) : ℚ) <
      (A.order (3 : Fin (N + 5)) : ℚ) := by
    rw [← hselected.1]
    exact_mod_cast hselected.2
  push_cast at hbetaThree hfinalQ
  linarith

set_option maxHeartbeats 1200000 in
-- Both Lemma 2.7(i) normal forms contain dependent indices through rank six.
/-- Exact transport at the fourth paper boundary in Case 2(b).  Its primary
candidate grows strictly, but the actual invariant lies strictly below that
candidate; the half-gap and previous-form secondary candidates are unchanged.
Hence increasing the unused primary candidate leaves the defining minimum
unchanged. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.thirdTailRepresentationAlpha_eq_of_thirdPrimaryStrict
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 6)} {b : GoodBONG r M (N + 6)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair (N := N + 2) a b)
    (hstrict :
      P.normalized.targetTransform.transformed.representationPrimaryDefect
          P.normalized.sourceTransform.transformed
            (lemma93FourthRepresentationIndex (N + 1)) <
        P.normalized.targetTransform.transformed.tail.representationPrimaryDefect
          P.normalized.sourceTransform.transformed.tail
            (lemma93ThirdRepresentationIndex (N + 1)))
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed)
    (horder :
      P.normalized.targetTransform.transformed.order (0 : Fin (N + 6)) <
          P.normalized.targetTransform.transformed.order (2 : Fin (N + 6)) ∨
        (P.normalized.targetTransform.transformed.order (1 : Fin (N + 6)) =
            P.normalized.sourceTransform.transformed.order (1 : Fin (N + 6)) ∧
          P.normalized.targetTransform.transformed.order (1 : Fin (N + 6)) <
            P.normalized.targetTransform.transformed.order (3 : Fin (N + 6)))) :
    P.normalized.targetTransform.transformed.tail.representationAlpha
        P.normalized.sourceTransform.transformed.tail
          (lemma93ThirdRepresentationIndex (N + 1)) =
      P.normalized.targetTransform.transformed.representationAlpha
        P.normalized.sourceTransform.transformed
          (lemma93FourthRepresentationIndex (N + 1)) := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let thirdTail := lemma93ThirdRepresentationIndex (N + 1)
  let fourth := lemma93FourthRepresentationIndex (N + 1)
  have hshift : thirdTail.tailShift = fourth := by
    apply representationIndex_eq_of_val_eq_caseTwo
    simp only [RepresentationIndex.tailShift_val, thirdTail, fourth,
      lemma93ThirdRepresentationIndex, lemma93FourthRepresentationIndex]
  have hstrict' : A.representationPrimaryDefect B thirdTail.tailShift <
      A.tail.representationPrimaryDefect B.tail thirdTail := by
    simpa only [A, B, thirdTail, fourth, hshift] using hstrict
  have hsourcePattern := P.sourceOrderPattern_of_thirdPrimaryStrict
    (classificationV := classificationV) (classificationW := classificationW)
    thirdTail (by simp only [thirdTail, lemma93ThirdRepresentationIndex])
      hstrict'
  have hhead : A.order (0 : Fin (N + 6)) =
      B.order (0 : Fin (N + 6)) := by
    unfold GoodBONG.order
    rw [A.toBONG.order_eq_ordUnit, B.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) (by
      apply Units.ext
      exact P.normalized.headValue_eq)
  have htwoFourRaw := A.good
    (⟨2, by omega⟩ : Fin (N + 2 + 4)) (by
      change 2 + 2 < N + 2 + 4
      omega)
  have htwoFour : A.order (2 : Fin (N + 6)) ≤
      A.order (4 : Fin (N + 6)) := by
    unfold GoodBONG.order
    convert htwoFourRaw using 1 <;> congr 1 <;> apply Fin.ext <;> simp
  have hcross : B.order (2 : Fin (N + 6)) ≤
      A.order (4 : Fin (N + 6)) := by
    calc
      B.order (2 : Fin (N + 6)) = B.order (0 : Fin (N + 6)) :=
        hsourcePattern.1.symm
      _ = A.order (0 : Fin (N + 6)) := hhead.symm
      _ ≤ A.order (2 : Fin (N + 6)) := A.order_zero_le_two
      _ ≤ A.order (4 : Fin (N + 6)) := htwoFour
  have hcrossTail :
      B.tail.order ⟨thirdTail.val - 2, by
        simp only [thirdTail, lemma93ThirdRepresentationIndex]
        omega⟩ ≤
        A.tail.order ⟨thirdTail.val, thirdTail.lt_large⟩ := by
    rw [B.order_goodTail, A.order_goodTail]
    have hsourceIndex :
        (⟨3 - 2, by omega⟩ : Fin (N + 5)).succ =
          (2 : Fin (N + 6)) := by
      apply Fin.ext
      change (3 - 2) + 1 = 2 % (N + 6)
      rw [Nat.mod_eq_of_lt (by omega)]
    have htargetIndex :
        (⟨3, by omega⟩ : Fin (N + 5)).succ =
          (4 : Fin (N + 6)) := by
      apply Fin.ext
      change 3 + 1 = 4 % (N + 6)
      rw [Nat.mod_eq_of_lt (by omega)]
    simp only [thirdTail, lemma93ThirdRepresentationIndex]
    rw [hsourceIndex, htargetIndex]
    exact hcross
  have hcrossOriginal :
      B.order ⟨fourth.val - 2, by
        simp only [fourth, lemma93FourthRepresentationIndex]
        omega⟩ ≤
        A.order ⟨fourth.val, fourth.lt_large⟩ := by
    simp only [fourth, lemma93FourthRepresentationIndex]
    have hsourceIndex :
        (⟨4 - 2, by omega⟩ : Fin (N + 6)) =
          (2 : Fin (N + 6)) := by
      apply Fin.ext
      change 4 - 2 = 2 % (N + 6)
      rw [Nat.mod_eq_of_lt (by omega)]
    have htargetIndex :
        (⟨4, by omega⟩ : Fin (N + 6)) =
          (4 : Fin (N + 6)) := by
      apply Fin.ext
      change 4 = 4 % (N + 6)
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hsourceIndex, htargetIndex]
    exact hcross
  have hdefect := P.fourthSecondDefect_eq_tail
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (classificationV := classificationV) (classificationW := classificationW)
    thirdTail (by simp only [thirdTail, lemma93ThirdRepresentationIndex])
      hstrict' hcase horder
  have hprevious :
      A.tail.representationSecondaryPreviousDefect B.tail thirdTail (by
        simp only [thirdTail, lemma93ThirdRepresentationIndex]
        omega) =
        A.representationSecondaryPreviousDefect B fourth (by
          simp only [fourth, lemma93FourthRepresentationIndex]
          omega) := by
    unfold representationSecondaryPreviousDefect
    rw [A.order_goodTail, A.order_goodTail,
      B.order_goodTail, B.order_goodTail]
    simp only [thirdTail, fourth, lemma93ThirdRepresentationIndex,
      lemma93FourthRepresentationIndex]
    let coefficient : WithTop ℚ :=
      (((A.order (4 : Fin (N + 6)) + A.order (5 : Fin (N + 6)) -
        B.order (2 : Fin (N + 6)) - B.order (3 : Fin (N + 6)) : Int) : ℚ) :
          WithTop ℚ)
    change coefficient + A.tail.truncatedPrefixDefect B.tail (-1) 3 1 =
      coefficient + A.truncatedPrefixDefect B (-1) 4 2
    rw [hdefect]
  have hhalf := A.representationHalfGap_tail_eq_shift B thirdTail
  rw [hshift] at hhalf
  have htailPrime := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact A.tail.representationAlphaPrime_eq_min_primary_previous
      B.tail thirdTail (by
        simp only [thirdTail, lemma93ThirdRepresentationIndex]
        omega) hcrossTail
  have horiginalPrime := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact A.representationAlphaPrime_eq_min_primary_previous
      B fourth (by
        simp only [fourth, lemma93FourthRepresentationIndex]
        omega) hcrossOriginal
  have htailNormal : A.tail.representationAlpha B.tail thirdTail =
      min (A.tail.representationHalfGap B.tail thirdTail)
        (min (A.tail.representationPrimaryDefect B.tail thirdTail)
          (A.tail.representationSecondaryPreviousDefect B.tail thirdTail (by
            simp only [thirdTail, lemma93ThirdRepresentationIndex]
            omega))) := by
    rw [A.tail.representationAlpha_eq_min_halfGap_prime B.tail thirdTail,
      htailPrime]
  have horiginalNormal : A.representationAlpha B fourth =
      min (A.representationHalfGap B fourth)
        (min (A.representationPrimaryDefect B fourth)
          (A.representationSecondaryPreviousDefect B fourth (by
            simp only [fourth, lemma93FourthRepresentationIndex]
            omega))) := by
    rw [A.representationAlpha_eq_min_halfGap_prime B fourth,
      horiginalPrime]
  have hfourthStrict :=
    P.fourthRepresentationAlpha_lt_primary_of_thirdPrimaryStrict
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV) (classificationW := classificationW)
      thirdTail (by simp only [thirdTail, lemma93ThirdRepresentationIndex])
        hstrict' hcase horder
  rw [horiginalNormal] at hfourthStrict
  let half := A.representationHalfGap B fourth
  let previous := A.representationSecondaryPreviousDefect B fourth (by
    simp only [fourth, lemma93FourthRepresentationIndex]
    omega)
  let primary := A.representationPrimaryDefect B fourth
  let primaryTail := A.tail.representationPrimaryDefect B.tail thirdTail
  have hbelowPrimary : min half (min previous primary) < primary := by
    simpa only [half, previous, primary, min_comm primary previous]
      using hfourthStrict
  have hbelowTail : min half (min previous primary) < primaryTail :=
    hbelowPrimary.trans (by
      simpa only [primary, primaryTail, hshift] using hstrict')
  have hnested := min_nested_eq_of_lt_caps half previous primary primaryTail
    hbelowPrimary hbelowTail
  rw [htailNormal, horiginalNormal, hhalf, hprevious]
  change min half (min primaryTail previous) = min half (min primary previous)
  rw [min_comm primaryTail previous, min_comm primary previous]
  exact hnested.symm

set_option maxHeartbeats 800000 in
-- The two surviving outside equalities require dependent low-index dispatch.
/-- End-to-end low reverse certificate for the exceptional fifth-candidate
branch of Case 2(b).  Tail values `3,4` are discharged by the nonessential
triple; values `1,2` are the exact transports proved above. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.lowReverse_of_secondExceptionalBranch
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 7)} {b : GoodBONG r M (N + 7)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair (N := N + 3) a b)
    (i : RepresentationIndex (N + 6) (N + 6)) (hi : i.val = 3)
    (hstrict :
      P.normalized.targetTransform.transformed.representationPrimaryDefect
          P.normalized.sourceTransform.transformed i.tailShift <
        P.normalized.targetTransform.transformed.tail.representationPrimaryDefect
          P.normalized.sourceTransform.transformed.tail i)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed)
    (horder :
      P.normalized.targetTransform.transformed.order (0 : Fin (N + 7)) <
          P.normalized.targetTransform.transformed.order (2 : Fin (N + 7)) ∨
        (P.normalized.targetTransform.transformed.order (1 : Fin (N + 7)) =
            P.normalized.sourceTransform.transformed.order (1 : Fin (N + 7)) ∧
          P.normalized.targetTransform.transformed.order (1 : Fin (N + 7)) <
            P.normalized.targetTransform.transformed.order (3 : Fin (N + 7))))
    (hcross : P.normalized.sourceTransform.transformed.order
        (⟨3, by omega⟩ : Fin (N + 7)) <
      P.normalized.targetTransform.transformed.order
        (⟨5, by omega⟩ : Fin (N + 7)))
    (hfifthEq :
      P.normalized.targetTransform.transformed.representationAlpha
          P.normalized.sourceTransform.transformed
          (lemma93FifthRepresentationIndex (N + 1)) =
        P.normalized.targetTransform.transformed.representationSecondaryPreviousDefect
          P.normalized.sourceTransform.transformed
          (lemma93FifthRepresentationIndex (N + 1)) (by
            simp only [lemma93FifthRepresentationIndex]
            omega)) :
    Beli2019Lemma93LowReverseCertificate (N := N + 3) a b
      P.normalized := by
  have hfourthStrict :=
    P.fourthRepresentationAlpha_lt_primary_of_thirdPrimaryStrict
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV) (classificationW := classificationW)
      i hi hstrict hcase horder
  apply Beli2019Lemma93LowReverseCertificate.ofSecondCaseTwoBranch
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    P.normalized hcross hfourthStrict hfifthEq
  intro j hlow hthree hfour
  have hvalue : j.val = 1 ∨ j.val = 2 := by
    have := j.pos
    omega
  rcases hvalue with hone | htwo
  · let first := firstRepresentationIndex (N + 4) (N + 5)
    let second := secondRepresentationIndex (N + 4) (N + 5)
    have hj : j = first := by
      apply representationIndex_eq_of_val_eq_caseTwo
      simpa only [first, firstRepresentationIndex] using hone
    have hshift : first.tailShift = second := by
      apply representationIndex_eq_of_val_eq_caseTwo
      simp only [RepresentationIndex.tailShift_val, first, second,
        firstRepresentationIndex, secondRepresentationIndex]
    rw [hj, hshift]
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact P.firstRepresentationAlpha_eq hcase
  · let secondTail := lemma93SecondTailRepresentationIndex (N + 3)
    let third := lemma93ThirdRepresentationIndex (N + 3)
    have hj : j = secondTail := by
      apply representationIndex_eq_of_val_eq_caseTwo
      simpa only [secondTail, lemma93SecondTailRepresentationIndex] using htwo
    have hshift : secondTail.tailShift = third := by
      apply representationIndex_eq_of_val_eq_caseTwo
      simp only [RepresentationIndex.tailShift_val, secondTail, third,
        lemma93SecondTailRepresentationIndex, lemma93ThirdRepresentationIndex]
    rw [hj, hshift]
    exact P.secondTailRepresentationAlpha_eq
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV) (classificationW := classificationW)
      i hi hstrict hcase horder

end BONG.GoodBONG

end Bong
