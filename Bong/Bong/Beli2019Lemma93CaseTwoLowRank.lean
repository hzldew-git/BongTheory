/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93CaseTwoAssembly

/-!
# Beli (2019), Lemma 9.3: low-rank ordinary Case 2

The uniform Case-2 proof uses two three-boundary nonessentiality windows and
therefore starts in rank seven.  In ranks four, five, and six some of those
boundaries are endpoints or do not exist.  This file proves those cases
directly, without interpreting out-of-range numerals modulo a `Fin` rank.
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

private theorem representationIndex_eq_of_val_eq_caseTwoLowRank
    {largeRank smallRank : Nat}
    (i j : RepresentationIndex largeRank smallRank)
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  simp_all

set_option maxHeartbeats 1000000 in
/-- Ordinary Case 2 in rank four.  The second tail boundary is the endpoint,
so equality of its primary core is sufficient, while strict growth is
absorbed by the endpoint half-gap formula. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.toLowReverseCertificate_rankFour
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L 4} {b : GoodBONG r M 4}
    (P : Beli2019Lemma93CaseTwoNormalizedPair (N := 0) a b)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed)
    (horder :
      P.normalized.targetTransform.transformed.order (0 : Fin 4) <
          P.normalized.targetTransform.transformed.order (2 : Fin 4) ∨
        (P.normalized.targetTransform.transformed.order (1 : Fin 4) =
            P.normalized.sourceTransform.transformed.order (1 : Fin 4) ∧
          P.normalized.targetTransform.transformed.order (1 : Fin 4) <
            P.normalized.targetTransform.transformed.order (3 : Fin 4))) :
    Beli2019Lemma93LowReverseCertificate (N := 0) a b P.normalized := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let firstTail : RepresentationIndex 3 3 :=
    firstRepresentationIndex 1 2
  let secondTail : RepresentationIndex 3 3 :=
    lemma93SecondTailRepresentationIndex 0
  let thirdOriginal : RepresentationIndex 4 4 :=
    lemma93ThirdRepresentationIndex 0
  have hsecondShift : secondTail.tailShift = thirdOriginal := by
    apply representationIndex_eq_of_val_eq_caseTwoLowRank
    simp only [RepresentationIndex.tailShift_val, secondTail, thirdOriginal,
      lemma93SecondTailRepresentationIndex, lemma93ThirdRepresentationIndex]
  have htwoLeRaw := A.primaryCoreDefect_shift_le_tail
    B P.normalized.headValue_eq secondTail
  have htwoLe : A.truncatedPrefixDefect B (-1) 4 2 ≤
      A.tail.truncatedPrefixDefect B.tail (-1) 3 1 := by
    simpa only [secondTail, lemma93SecondTailRepresentationIndex,
      Nat.reduceAdd, Nat.reduceSub] using htwoLeRaw
  have hsecond : A.tail.representationAlpha B.tail secondTail =
      A.representationAlpha B secondTail.tailShift := by
    rcases lt_or_eq_of_le htwoLe with htwoStrict | htwoEq
    · have htwoPrimaryStrict :
          A.representationPrimaryDefect B secondTail.tailShift <
            A.tail.representationPrimaryDefect B.tail secondTail :=
        A.representationPrimaryDefect_shift_lt_tail_of_core_lt B secondTail (by
          simpa only [secondTail, lemma93SecondTailRepresentationIndex,
            Nat.reduceAdd, Nat.reduceSub] using htwoStrict)
      have hthirdAlphaLt :=
        P.thirdRepresentationAlpha_lt_primary_of_secondPrimaryStrict
          (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          (classificationV := classificationV)
          hcase horder htwoPrimaryStrict
      exact A.representationAlpha_tail_eq_shift_of_alpha_lt_primary_of_not_interior
        B P.normalized.headValue_eq secondTail (by
          simp only [secondTail, lemma93SecondTailRepresentationIndex]
          omega) (by
          simp only [secondTail, lemma93SecondTailRepresentationIndex]
          omega) (by
          simpa only [hsecondShift, thirdOriginal] using hthirdAlphaLt)
    · have hprimary :=
        A.representationPrimaryDefect_tail_eq_shift_of_core_eq B secondTail (by
          simpa only [secondTail, lemma93SecondTailRepresentationIndex,
            Nat.reduceAdd, Nat.reduceSub] using htwoEq)
      exact A.representationAlpha_tail_eq_shift_of_primary_secondary_eq
        B secondTail (by
          simp only [secondTail, lemma93SecondTailRepresentationIndex]
          omega) hprimary (fun hinterior ↦ by
            simp only [secondTail, lemma93SecondTailRepresentationIndex]
              at hinterior
            omega)
  refine { reverseAtImportant := ?_ }
  intro i _himportant _hlow
  have hvalue : i.val = 1 ∨ i.val = 2 := by
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  rcases hvalue with honeValue | htwoValue
  · have hi : i = firstTail := by
      apply representationIndex_eq_of_val_eq_caseTwoLowRank
      simpa only [firstTail, firstRepresentationIndex] using honeValue
    have hshift : firstTail.tailShift =
        secondRepresentationIndex 1 2 := by
      apply representationIndex_eq_of_val_eq_caseTwoLowRank
      simp only [RepresentationIndex.tailShift_val, firstTail,
        firstRepresentationIndex, secondRepresentationIndex]
    rw [hi, hshift]
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact (P.firstRepresentationAlpha_eq hcase).le
  · have hi : i = secondTail := by
      apply representationIndex_eq_of_val_eq_caseTwoLowRank
      simpa only [secondTail, lemma93SecondTailRepresentationIndex]
        using htwoValue
    rw [hi]
    exact hsecond.le

set_option maxHeartbeats 1600000 in
-- Rank five has one interior exceptional boundary and one endpoint boundary.
/-- Ordinary Case 2 in rank five.  The third tail boundary is the endpoint;
the strict-third-core branch is handled by the exact Case-2(b) transfer at
the preceding boundary and the endpoint half-gap formula at the last one. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.toLowReverseCertificate_rankFive
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L 5} {b : GoodBONG r M 5}
    (P : Beli2019Lemma93CaseTwoNormalizedPair (N := 1) a b)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed)
    (horder :
      P.normalized.targetTransform.transformed.order (0 : Fin 5) <
          P.normalized.targetTransform.transformed.order (2 : Fin 5) ∨
        (P.normalized.targetTransform.transformed.order (1 : Fin 5) =
            P.normalized.sourceTransform.transformed.order (1 : Fin 5) ∧
          P.normalized.targetTransform.transformed.order (1 : Fin 5) <
            P.normalized.targetTransform.transformed.order (3 : Fin 5))) :
    Beli2019Lemma93LowReverseCertificate (N := 1) a b P.normalized := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let firstTail : RepresentationIndex 4 4 :=
    firstRepresentationIndex 2 3
  let secondTail : RepresentationIndex 4 4 :=
    lemma93SecondTailRepresentationIndex 1
  let thirdTail : RepresentationIndex 4 4 :=
    lemma93ThirdRepresentationIndex 0
  let thirdOriginal : RepresentationIndex 5 5 :=
    lemma93ThirdRepresentationIndex 1
  let fourthOriginal : RepresentationIndex 5 5 :=
    lemma93FourthRepresentationIndex 0
  have hsecondShift : secondTail.tailShift = thirdOriginal := by
    apply representationIndex_eq_of_val_eq_caseTwoLowRank
    simp only [RepresentationIndex.tailShift_val, secondTail, thirdOriginal,
      lemma93SecondTailRepresentationIndex, lemma93ThirdRepresentationIndex]
  have hthirdShift : thirdTail.tailShift = fourthOriginal := by
    apply representationIndex_eq_of_val_eq_caseTwoLowRank
    simp only [RepresentationIndex.tailShift_val, thirdTail, fourthOriginal,
      lemma93ThirdRepresentationIndex, lemma93FourthRepresentationIndex]
  have hone : A.truncatedPrefixDefect B (-1) 3 1 =
      A.tail.truncatedPrefixDefect B.tail (-1) 2 0 :=
    P.firstThirdDefect_eq_tail hcase
  have htwoLeRaw := A.primaryCoreDefect_shift_le_tail
    B P.normalized.headValue_eq secondTail
  have hthreeLeRaw := A.primaryCoreDefect_shift_le_tail
    B P.normalized.headValue_eq thirdTail
  have htwoLe : A.truncatedPrefixDefect B (-1) 4 2 ≤
      A.tail.truncatedPrefixDefect B.tail (-1) 3 1 := by
    simpa only [secondTail, lemma93SecondTailRepresentationIndex,
      Nat.reduceAdd, Nat.reduceSub] using htwoLeRaw
  have hthreeLe : A.truncatedPrefixDefect B (-1) 5 3 ≤
      A.tail.truncatedPrefixDefect B.tail (-1) 4 2 := by
    simpa only [thirdTail, lemma93ThirdRepresentationIndex,
      Nat.reduceAdd, Nat.reduceSub] using hthreeLeRaw
  have hsecond
      (himportant : A.tail.IsCurrentEssential B.tail secondTail ∨
        A.tail.IsNextEssential B.tail secondTail) :
      A.tail.representationAlpha B.tail secondTail ≤
        A.representationAlpha B secondTail.tailShift := by
    rcases lt_or_eq_of_le hthreeLe with hthreeStrict | hthreeEq
    · have hthreePrimaryStrict :
          A.representationPrimaryDefect B thirdTail.tailShift <
            A.tail.representationPrimaryDefect B.tail thirdTail :=
        A.representationPrimaryDefect_shift_lt_tail_of_core_lt B thirdTail (by
          simpa only [thirdTail, lemma93ThirdRepresentationIndex,
            Nat.reduceAdd, Nat.reduceSub] using hthreeStrict)
      simpa only [hsecondShift, thirdOriginal] using
        (P.secondTailRepresentationAlpha_eq
          (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          (classificationV := classificationV)
          (classificationW := classificationW)
          thirdTail (by
            simp only [thirdTail, lemma93ThirdRepresentationIndex])
          hthreePrimaryStrict hcase horder).le
    · rcases lt_or_eq_of_le htwoLe with htwoStrict | htwoEq
      · have htwoPrimaryStrict :
            A.representationPrimaryDefect B secondTail.tailShift <
              A.tail.representationPrimaryDefect B.tail secondTail :=
          A.representationPrimaryDefect_shift_lt_tail_of_core_lt B secondTail (by
            simpa only [secondTail, lemma93SecondTailRepresentationIndex,
              Nat.reduceAdd, Nat.reduceSub] using htwoStrict)
        have hthirdAlphaLt :=
          P.thirdRepresentationAlpha_lt_primary_of_secondPrimaryStrict
            (targetLaws := targetLaws) (sourceLaws := sourceLaws)
            (classificationV := classificationV)
            hcase horder htwoPrimaryStrict
        exact (A.representationAlpha_tail_eq_shift_of_alpha_lt_primary_at_important
          (alphaV := targetLaws) (alphaW := sourceLaws)
          B P.normalized.headValue_eq secondTail (by
            simp only [secondTail, lemma93SecondTailRepresentationIndex]
            omega) (by
            simp only [secondTail, lemma93SecondTailRepresentationIndex]
            omega) himportant
          (by simpa only [hsecondShift, thirdOriginal] using hthirdAlphaLt)
          (fun _ ↦ by
            simpa only [secondTail, lemma93SecondTailRepresentationIndex]
              using hone)
          (fun _ ↦ by
            simpa only [secondTail, lemma93SecondTailRepresentationIndex]
              using hthreeEq)).le
      · exact (A.representationAlpha_tail_eq_shift_of_core_eq_at_important
          (alphaV := targetLaws) (alphaW := sourceLaws)
          B P.normalized.headValue_eq secondTail (by
            simp only [secondTail, lemma93SecondTailRepresentationIndex]
            omega) himportant
          (by simpa only [secondTail, lemma93SecondTailRepresentationIndex]
            using htwoEq)
          (fun _ ↦ by
            simpa only [secondTail, lemma93SecondTailRepresentationIndex]
              using hone)
          (fun _ ↦ by
            simpa only [secondTail, lemma93SecondTailRepresentationIndex]
              using hthreeEq)).le
  have hthird
      (_himportant : A.tail.IsCurrentEssential B.tail thirdTail ∨
        A.tail.IsNextEssential B.tail thirdTail) :
      A.tail.representationAlpha B.tail thirdTail ≤
        A.representationAlpha B thirdTail.tailShift := by
    rcases lt_or_eq_of_le hthreeLe with hthreeStrict | hthreeEq
    · have hthreePrimaryStrict :
          A.representationPrimaryDefect B thirdTail.tailShift <
            A.tail.representationPrimaryDefect B.tail thirdTail :=
        A.representationPrimaryDefect_shift_lt_tail_of_core_lt B thirdTail (by
          simpa only [thirdTail, lemma93ThirdRepresentationIndex,
            Nat.reduceAdd, Nat.reduceSub] using hthreeStrict)
      have hfourthAlphaLt :=
        P.fourthRepresentationAlpha_lt_primary_of_thirdPrimaryStrict
          (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          (classificationV := classificationV)
          (classificationW := classificationW)
          thirdTail (by
            simp only [thirdTail, lemma93ThirdRepresentationIndex])
          hthreePrimaryStrict hcase horder
      exact (A.representationAlpha_tail_eq_shift_of_alpha_lt_primary_of_not_interior
        B P.normalized.headValue_eq thirdTail (by
          simp only [thirdTail, lemma93ThirdRepresentationIndex]
          omega) (by
          simp only [thirdTail, lemma93ThirdRepresentationIndex]
          omega) (by
          simpa only [hthirdShift, fourthOriginal] using hfourthAlphaLt)).le
    · have hprimary :=
        A.representationPrimaryDefect_tail_eq_shift_of_core_eq B thirdTail (by
          simpa only [thirdTail, lemma93ThirdRepresentationIndex,
            Nat.reduceAdd, Nat.reduceSub] using hthreeEq)
      exact (A.representationAlpha_tail_eq_shift_of_primary_secondary_eq
        B thirdTail (by
          simp only [thirdTail, lemma93ThirdRepresentationIndex]
          omega) hprimary (fun hinterior ↦ by
            simp only [thirdTail, lemma93ThirdRepresentationIndex]
              at hinterior
            omega)).le
  refine { reverseAtImportant := ?_ }
  intro i himportant _hlow
  have hvalue : i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  rcases hvalue with honeValue | htwoValue | hthreeValue
  · have hi : i = firstTail := by
      apply representationIndex_eq_of_val_eq_caseTwoLowRank
      simpa only [firstTail, firstRepresentationIndex] using honeValue
    have hshift : firstTail.tailShift =
        secondRepresentationIndex 2 3 := by
      apply representationIndex_eq_of_val_eq_caseTwoLowRank
      simp only [RepresentationIndex.tailShift_val, firstTail,
        firstRepresentationIndex, secondRepresentationIndex]
    rw [hi, hshift]
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact (P.firstRepresentationAlpha_eq hcase).le
  · have hi : i = secondTail := by
      apply representationIndex_eq_of_val_eq_caseTwoLowRank
      simpa only [secondTail, lemma93SecondTailRepresentationIndex]
        using htwoValue
    rw [hi] at himportant ⊢
    exact hsecond himportant
  · have hi : i = thirdTail := by
      apply representationIndex_eq_of_val_eq_caseTwoLowRank
      simpa only [thirdTail, lemma93ThirdRepresentationIndex]
        using hthreeValue
    rw [hi] at himportant ⊢
    exact hthird himportant

set_option maxHeartbeats 2400000 in
-- Rank six retains the first nonessentiality triple; its fourth boundary is an endpoint.
/-- Ordinary Case 2 in rank six.  The first exceptional three-boundary
window is genuine and uses the paper's nonessentiality argument.  The next
window has reached the endpoint, where exact transport of the primary core
alone closes the comparison. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.toLowReverseCertificate_rankSix
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L 6} {b : GoodBONG r M 6}
    (P : Beli2019Lemma93CaseTwoNormalizedPair (N := 2) a b)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed)
    (horder :
      P.normalized.targetTransform.transformed.order (0 : Fin 6) <
          P.normalized.targetTransform.transformed.order (2 : Fin 6) ∨
        (P.normalized.targetTransform.transformed.order (1 : Fin 6) =
            P.normalized.sourceTransform.transformed.order (1 : Fin 6) ∧
          P.normalized.targetTransform.transformed.order (1 : Fin 6) <
            P.normalized.targetTransform.transformed.order (3 : Fin 6))) :
    Beli2019Lemma93LowReverseCertificate (N := 2) a b P.normalized := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let firstTail : RepresentationIndex 5 5 :=
    firstRepresentationIndex 3 4
  let secondTail : RepresentationIndex 5 5 :=
    lemma93SecondTailRepresentationIndex 2
  let thirdTail : RepresentationIndex 5 5 :=
    lemma93ThirdRepresentationIndex 1
  let fourthTail : RepresentationIndex 5 5 :=
    lemma93FourthRepresentationIndex 0
  let thirdOriginal : RepresentationIndex 6 6 :=
    lemma93ThirdRepresentationIndex 2
  let fourthOriginal : RepresentationIndex 6 6 :=
    lemma93FourthRepresentationIndex 1
  have hsecondShift : secondTail.tailShift = thirdOriginal := by
    apply representationIndex_eq_of_val_eq_caseTwoLowRank
    simp only [RepresentationIndex.tailShift_val, secondTail, thirdOriginal,
      lemma93SecondTailRepresentationIndex, lemma93ThirdRepresentationIndex]
  have hthirdShift : thirdTail.tailShift = fourthOriginal := by
    apply representationIndex_eq_of_val_eq_caseTwoLowRank
    simp only [RepresentationIndex.tailShift_val, thirdTail, fourthOriginal,
      lemma93ThirdRepresentationIndex, lemma93FourthRepresentationIndex]
  have hone : A.truncatedPrefixDefect B (-1) 3 1 =
      A.tail.truncatedPrefixDefect B.tail (-1) 2 0 :=
    P.firstThirdDefect_eq_tail hcase
  have htwoLeRaw := A.primaryCoreDefect_shift_le_tail
    B P.normalized.headValue_eq secondTail
  have hthreeLeRaw := A.primaryCoreDefect_shift_le_tail
    B P.normalized.headValue_eq thirdTail
  have htwoLe : A.truncatedPrefixDefect B (-1) 4 2 ≤
      A.tail.truncatedPrefixDefect B.tail (-1) 3 1 := by
    simpa only [secondTail, lemma93SecondTailRepresentationIndex,
      Nat.reduceAdd, Nat.reduceSub] using htwoLeRaw
  have hthreeLe : A.truncatedPrefixDefect B (-1) 5 3 ≤
      A.tail.truncatedPrefixDefect B.tail (-1) 4 2 := by
    simpa only [thirdTail, lemma93ThirdRepresentationIndex,
      Nat.reduceAdd, Nat.reduceSub] using hthreeLeRaw
  have hfourRaw := A.primaryCoreDefect_shift_eq_tail_of_laterAlphaValue_eq
    B P.normalized.headValue_eq
    (fun k hk ↦ by
      letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
      exact P.normalized.targetTransform.transformed_laterAlpha_eq_tail k hk)
    (fun k hk ↦ by
      letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
      exact P.normalized.sourceTransform.transformed_laterAlpha_eq_tail k hk)
    fourthTail (by
      simp only [fourthTail, lemma93FourthRepresentationIndex]
      omega)
  have hfour : A.truncatedPrefixDefect B (-1) 6 4 =
      A.tail.truncatedPrefixDefect B.tail (-1) 5 3 := by
    simpa only [fourthTail, lemma93FourthRepresentationIndex,
      Nat.reduceAdd, Nat.reduceSub] using hfourRaw
  have hsecond
      (himportant : A.tail.IsCurrentEssential B.tail secondTail ∨
        A.tail.IsNextEssential B.tail secondTail) :
      A.tail.representationAlpha B.tail secondTail ≤
        A.representationAlpha B secondTail.tailShift := by
    rcases lt_or_eq_of_le hthreeLe with hthreeStrict | hthreeEq
    · have hthreePrimaryStrict :
          A.representationPrimaryDefect B thirdTail.tailShift <
            A.tail.representationPrimaryDefect B.tail thirdTail :=
        A.representationPrimaryDefect_shift_lt_tail_of_core_lt B thirdTail (by
          simpa only [thirdTail, lemma93ThirdRepresentationIndex,
            Nat.reduceAdd, Nat.reduceSub] using hthreeStrict)
      simpa only [hsecondShift, thirdOriginal] using
        (P.secondTailRepresentationAlpha_eq
          (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          (classificationV := classificationV)
          (classificationW := classificationW)
          thirdTail (by
            simp only [thirdTail, lemma93ThirdRepresentationIndex])
          hthreePrimaryStrict hcase horder).le
    · rcases lt_or_eq_of_le htwoLe with htwoStrict | htwoEq
      · have htwoPrimaryStrict :
            A.representationPrimaryDefect B secondTail.tailShift <
              A.tail.representationPrimaryDefect B.tail secondTail :=
          A.representationPrimaryDefect_shift_lt_tail_of_core_lt B secondTail (by
            simpa only [secondTail, lemma93SecondTailRepresentationIndex,
              Nat.reduceAdd, Nat.reduceSub] using htwoStrict)
        have hthirdAlphaLt :=
          P.thirdRepresentationAlpha_lt_primary_of_secondPrimaryStrict
            (targetLaws := targetLaws) (sourceLaws := sourceLaws)
            (classificationV := classificationV)
            hcase horder htwoPrimaryStrict
        exact (A.representationAlpha_tail_eq_shift_of_alpha_lt_primary_at_important
          (alphaV := targetLaws) (alphaW := sourceLaws)
          B P.normalized.headValue_eq secondTail (by
            simp only [secondTail, lemma93SecondTailRepresentationIndex]
            omega) (by
            simp only [secondTail, lemma93SecondTailRepresentationIndex]
            omega) himportant
          (by simpa only [hsecondShift, thirdOriginal] using hthirdAlphaLt)
          (fun _ ↦ by
            simpa only [secondTail, lemma93SecondTailRepresentationIndex]
              using hone)
          (fun _ ↦ by
            simpa only [secondTail, lemma93SecondTailRepresentationIndex]
              using hthreeEq)).le
      · exact (A.representationAlpha_tail_eq_shift_of_core_eq_at_important
          (alphaV := targetLaws) (alphaW := sourceLaws)
          B P.normalized.headValue_eq secondTail (by
            simp only [secondTail, lemma93SecondTailRepresentationIndex]
            omega) himportant
          (by simpa only [secondTail, lemma93SecondTailRepresentationIndex]
            using htwoEq)
          (fun _ ↦ by
            simpa only [secondTail, lemma93SecondTailRepresentationIndex]
              using hone)
          (fun _ ↦ by
            simpa only [secondTail, lemma93SecondTailRepresentationIndex]
              using hthreeEq)).le
  have hthird
      (himportant : A.tail.IsCurrentEssential B.tail thirdTail ∨
        A.tail.IsNextEssential B.tail thirdTail) :
      A.tail.representationAlpha B.tail thirdTail ≤
        A.representationAlpha B thirdTail.tailShift := by
    rcases lt_or_eq_of_le hthreeLe with hthreeStrict | hthreeEq
    · have hthreePrimaryStrict :
          A.representationPrimaryDefect B thirdTail.tailShift <
            A.tail.representationPrimaryDefect B.tail thirdTail :=
        A.representationPrimaryDefect_shift_lt_tail_of_core_lt B thirdTail (by
          simpa only [thirdTail, lemma93ThirdRepresentationIndex,
            Nat.reduceAdd, Nat.reduceSub] using hthreeStrict)
      simpa only [hthirdShift, fourthOriginal] using
        (P.thirdTailRepresentationAlpha_eq_of_thirdPrimaryStrict
          (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          (classificationV := classificationV)
          (classificationW := classificationW)
          hthreePrimaryStrict hcase horder).le
    · rcases lt_or_eq_of_le htwoLe with htwoStrict | htwoEq
      · have htwoLe' : A.truncatedPrefixDefect B (-1) 4 2 ≤
            A.tail.truncatedPrefixDefect B.tail (-1) 3 1 := htwoStrict.le
        have htwoPrimaryStrict :
            A.representationPrimaryDefect B secondTail.tailShift <
              A.tail.representationPrimaryDefect B.tail secondTail :=
          A.representationPrimaryDefect_shift_lt_tail_of_core_lt B secondTail (by
            simpa only [secondTail, lemma93SecondTailRepresentationIndex,
              Nat.reduceAdd, Nat.reduceSub] using htwoStrict)
        have hthirdAlphaLt :=
          P.thirdRepresentationAlpha_lt_primary_of_secondPrimaryStrict
            (targetLaws := targetLaws) (sourceLaws := sourceLaws)
            (classificationV := classificationV)
            hcase horder htwoPrimaryStrict
        by_cases hcurrent : A.tail.IsCurrentEssential B.tail thirdTail
        · have hpreviousLe :=
            A.representationAlpha_shift_le_previous_of_currentEssential
              (alphaV := targetLaws) B thirdTail (by
                simp only [thirdTail, lemma93ThirdRepresentationIndex]
                omega) (by
                simp only [thirdTail, lemma93ThirdRepresentationIndex]
                omega) hcurrent
          by_cases heq : A.representationAlpha B thirdTail.tailShift =
              A.representationSecondaryPreviousDefect B thirdTail.tailShift (by
                simp only [RepresentationIndex.tailShift_val, thirdTail,
                  lemma93ThirdRepresentationIndex]
                omega)
          · have hcrossTail := order_previous_lt_current_of_currentEssential
                A.tail B.tail thirdTail (by
                  simp only [thirdTail, lemma93ThirdRepresentationIndex]
                  omega) (by
                  simp only [thirdTail, lemma93ThirdRepresentationIndex]
                  omega) hcurrent
            have hcross : B.order (2 : Fin 6) < A.order (4 : Fin 6) := by
              rw [B.order_goodTail, A.order_goodTail] at hcrossTail
              convert hcrossTail using 1 <;> congr 1 <;> apply Fin.ext <;>
                simp only [thirdTail, lemma93ThirdRepresentationIndex,
                  Fin.val_succ] <;> omega
            have hfourthEq : A.representationAlpha B fourthOriginal =
                A.representationSecondaryPreviousDefect B fourthOriginal (by
                  simp only [fourthOriginal, lemma93FourthRepresentationIndex]
                  omega) := by
              simpa only [hthirdShift] using heq
            have htriple :=
              tail_lowThree_not_essential_of_thirdPrimaryStrict_fourthPrevious
                (N := 0) (targetLaws := targetLaws)
                (sourceLaws := sourceLaws) A B hcross
                (by simpa only [thirdOriginal] using hthirdAlphaLt)
                (by simpa only [fourthOriginal] using hfourthEq)
            exfalso
            apply htriple.2.1
            unfold IsCurrentEssential at hcurrent
            have hindex : currentEssentialIndex thirdTail =
                (⟨2, by omega⟩ : Fin 5) := by
              apply Fin.ext
              simp only [currentEssentialIndex, thirdTail,
                lemma93ThirdRepresentationIndex]
            rwa [hindex] at hcurrent
          · exact (A.representationAlpha_tail_eq_shift_of_alpha_lt_previous_of_currentEssential
              (alphaV := targetLaws) B thirdTail (by
                simp only [thirdTail, lemma93ThirdRepresentationIndex]
                omega) (by
                simp only [thirdTail, lemma93ThirdRepresentationIndex]
                omega) hcurrent
              (by simpa only [thirdTail, lemma93ThirdRepresentationIndex]
                using hthreeEq)
              (by simpa only [thirdTail, lemma93ThirdRepresentationIndex]
                using htwoLe')
              (lt_of_le_of_ne hpreviousLe heq)).le
        · have hnext := himportant.resolve_left hcurrent
          exact (A.representationAlpha_tail_eq_shift_of_core_eq_at_important
            (alphaV := targetLaws) (alphaW := sourceLaws)
            B P.normalized.headValue_eq thirdTail (by
              simp only [thirdTail, lemma93ThirdRepresentationIndex]
              omega) (Or.inr hnext)
            (by simpa only [thirdTail, lemma93ThirdRepresentationIndex]
              using hthreeEq)
            (fun h ↦ False.elim (hcurrent h))
            (fun _ ↦ by
              simpa only [thirdTail, lemma93ThirdRepresentationIndex,
                Nat.reduceAdd] using hfour)).le
      · exact (A.representationAlpha_tail_eq_shift_of_core_eq_at_important
          (alphaV := targetLaws) (alphaW := sourceLaws)
          B P.normalized.headValue_eq thirdTail (by
            simp only [thirdTail, lemma93ThirdRepresentationIndex]
            omega) himportant
          (by simpa only [thirdTail, lemma93ThirdRepresentationIndex]
            using hthreeEq)
          (fun _ ↦ by
            simpa only [thirdTail, lemma93ThirdRepresentationIndex]
              using htwoEq)
          (fun _ ↦ by
            simpa only [thirdTail, lemma93ThirdRepresentationIndex,
              Nat.reduceAdd] using hfour)).le
  have hfourth
      (_himportant : A.tail.IsCurrentEssential B.tail fourthTail ∨
        A.tail.IsNextEssential B.tail fourthTail) :
      A.tail.representationAlpha B.tail fourthTail ≤
        A.representationAlpha B fourthTail.tailShift := by
    have hprimary :=
      A.representationPrimaryDefect_tail_eq_shift_of_core_eq B fourthTail (by
        simpa only [fourthTail, lemma93FourthRepresentationIndex,
          Nat.reduceAdd, Nat.reduceSub] using hfour)
    exact (A.representationAlpha_tail_eq_shift_of_primary_secondary_eq
      B fourthTail (by
        simp only [fourthTail, lemma93FourthRepresentationIndex]
        omega) hprimary (fun hinterior ↦ by
          simp only [fourthTail, lemma93FourthRepresentationIndex]
            at hinterior
          omega)).le
  refine { reverseAtImportant := ?_ }
  intro i himportant hlow
  have hvalue : i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by
    have hpos := i.pos
    omega
  rcases hvalue with honeValue | htwoValue | hthreeValue | hfourValue
  · have hi : i = firstTail := by
      apply representationIndex_eq_of_val_eq_caseTwoLowRank
      simpa only [firstTail, firstRepresentationIndex] using honeValue
    have hshift : firstTail.tailShift =
        secondRepresentationIndex 3 4 := by
      apply representationIndex_eq_of_val_eq_caseTwoLowRank
      simp only [RepresentationIndex.tailShift_val, firstTail,
        firstRepresentationIndex, secondRepresentationIndex]
    rw [hi, hshift]
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact (P.firstRepresentationAlpha_eq hcase).le
  · have hi : i = secondTail := by
      apply representationIndex_eq_of_val_eq_caseTwoLowRank
      simpa only [secondTail, lemma93SecondTailRepresentationIndex]
        using htwoValue
    rw [hi] at himportant ⊢
    exact hsecond himportant
  · have hi : i = thirdTail := by
      apply representationIndex_eq_of_val_eq_caseTwoLowRank
      simpa only [thirdTail, lemma93ThirdRepresentationIndex]
        using hthreeValue
    rw [hi] at himportant ⊢
    exact hthird himportant
  · have hi : i = fourthTail := by
      apply representationIndex_eq_of_val_eq_caseTwoLowRank
      simpa only [fourthTail, lemma93FourthRepresentationIndex]
        using hfourValue
    rw [hi] at himportant ⊢
    exact hfourth himportant

/-- Complete ordinary Case-2 low certificate in every rank covered by the
`N + 4` presentation.  Ranks four through six use the endpoint proofs above;
from rank seven onward the uniform two-window proof applies. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.toLowReverseCertificate
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed)
    (horder :
      P.normalized.targetTransform.transformed.order (0 : Fin (N + 4)) <
          P.normalized.targetTransform.transformed.order (2 : Fin (N + 4)) ∨
        (P.normalized.targetTransform.transformed.order (1 : Fin (N + 4)) =
            P.normalized.sourceTransform.transformed.order (1 : Fin (N + 4)) ∧
          P.normalized.targetTransform.transformed.order (1 : Fin (N + 4)) <
            P.normalized.targetTransform.transformed.order
              (3 : Fin (N + 4)))) :
    Beli2019Lemma93LowReverseCertificate a b P.normalized := by
  cases N with
  | zero =>
      exact P.toLowReverseCertificate_rankFour
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        (classificationV := classificationV)
        (classificationW := classificationW) hcase horder
  | succ N =>
      cases N with
      | zero =>
          exact P.toLowReverseCertificate_rankFive
            (targetLaws := targetLaws) (sourceLaws := sourceLaws)
            (classificationV := classificationV)
            (classificationW := classificationW) hcase horder
      | succ N =>
          cases N with
          | zero =>
              exact P.toLowReverseCertificate_rankSix
                (targetLaws := targetLaws) (sourceLaws := sourceLaws)
                (classificationV := classificationV)
                (classificationW := classificationW) hcase horder
          | succ N =>
              simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
                Nat.reduceAdd] using
                (P.toLowReverseCertificate_highRank
                  (N := N) (targetLaws := targetLaws)
                  (sourceLaws := sourceLaws)
                  (classificationV := classificationV)
                  (classificationW := classificationW) hcase horder)

/-- The original Lemma-9.1 and Case-2 hypotheses supply the uniform
all-rank low certificate after transporting them to the selected pair. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.toLowReverseCertificate_of_original
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (hlemma91 : a.Lemma91Alternative b)
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    Beli2019Lemma93LowReverseCertificate a b P.normalized :=
  P.toLowReverseCertificate
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (classificationV := classificationV) (classificationW := classificationW)
    (P.selectedCaseTwoCondition
      (classificationV := classificationV) (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW) hcase)
    (P.selectedEarlyOrderAlternative
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV) (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      hlemma91 hcase)

/-- A selected Case-2 pair in any rank `N + 4` constructs the concrete
recursive input required by Lemma 9.3. -/
noncomputable def Beli2019Lemma93CaseTwoNormalizedPair.toLemma93Input_caseTwo
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (hlemma91 : a.Lemma91Alternative b)
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl (N + 3))
        ambient conditions) :=
  P.normalized.toLemma93Input
    (classificationV := classificationV) (classificationW := classificationW)
    a b ambient conditions
    (P.toLowReverseCertificate_of_original
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV) (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      hlemma91 hcase)

/-- Full ordinary Case 2 of Lemma 9.3 in every rank `N + 4`, from the
original pair of good BONGs to the concrete recursive input. -/
theorem exists_beli2019Lemma93Input_caseTwo
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
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hfirst : a.order (0 : Fin (N + 4)) =
      b.order (0 : Fin (N + 4)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (hlemma91 : a.Lemma91Alternative b)
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    Nonempty (Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl (N + 3))
        ambient conditions)) := by
  rcases exists_beli2019Lemma93CaseTwoNormalizedPair
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
      a b hfirst ambient conditions hlemma91 hcase with ⟨P⟩
  exact ⟨P.toLemma93Input_caseTwo
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    a b ambient conditions hlemma91 hcase⟩

end BONG.GoodBONG

end Bong
