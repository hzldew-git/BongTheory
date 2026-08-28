/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93CoreTransport

/-!
# Beli (2019), Lemma 9.3: ordinary Case 2 assembly

This file assembles the local calculations from the two Case-2 subcases into
the low reverse certificate consumed by the ordinary Lemma 9.3 descent.  The
proof splits only on the two endpoint-sensitive core defects
`d[-a_(1,4)b_(1,2)]` and `d[-a_(1,5)b_(1,3)]`; every later core is transported
by Lemma 9.2.
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

private theorem representationIndex_eq_of_val_eq_caseTwoAssembly
    {largeRank smallRank : Nat}
    (i j : RepresentationIndex largeRank smallRank)
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  simp_all

set_option maxHeartbeats 1200000 in
-- Four dependent low indices and their shifted counterparts are normalized explicitly.
/-- If both exceptional core defects are unchanged, every low important
comparison invariant transports exactly. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.lowReverse_of_twoCoreEq
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 7)} {b : GoodBONG r M (N + 7)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair (N := N + 3) a b)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed)
    (htwo :
      P.normalized.targetTransform.transformed.truncatedPrefixDefect
          P.normalized.sourceTransform.transformed (-1) 4 2 =
        P.normalized.targetTransform.transformed.tail.truncatedPrefixDefect
          P.normalized.sourceTransform.transformed.tail (-1) 3 1)
    (hthree :
      P.normalized.targetTransform.transformed.truncatedPrefixDefect
          P.normalized.sourceTransform.transformed (-1) 5 3 =
        P.normalized.targetTransform.transformed.tail.truncatedPrefixDefect
          P.normalized.sourceTransform.transformed.tail (-1) 4 2) :
    Beli2019Lemma93LowReverseCertificate (N := N + 3) a b
      P.normalized := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let firstTail : RepresentationIndex (N + 6) (N + 6) :=
    firstRepresentationIndex (N + 4) (N + 5)
  let secondTail : RepresentationIndex (N + 6) (N + 6) :=
    lemma93SecondTailRepresentationIndex (N + 3)
  let thirdTail : RepresentationIndex (N + 6) (N + 6) :=
    lemma93ThirdRepresentationIndex (N + 2)
  let fourthTail : RepresentationIndex (N + 6) (N + 6) :=
    lemma93FourthRepresentationIndex (N + 1)
  let fifthTail : RepresentationIndex (N + 6) (N + 6) :=
    lemma93FifthRepresentationIndex N
  have hone : A.truncatedPrefixDefect B (-1) 3 1 =
      A.tail.truncatedPrefixDefect B.tail (-1) 2 0 :=
    P.firstThirdDefect_eq_tail hcase
  have hfour := A.primaryCoreDefect_shift_eq_tail_of_laterAlphaValue_eq
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
  have hfive := A.primaryCoreDefect_shift_eq_tail_of_laterAlphaValue_eq
    B P.normalized.headValue_eq
    (fun k hk ↦ by
      letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
      exact P.normalized.targetTransform.transformed_laterAlpha_eq_tail k hk)
    (fun k hk ↦ by
      letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
      exact P.normalized.sourceTransform.transformed_laterAlpha_eq_tail k hk)
    fifthTail (by
      simp only [fifthTail, lemma93FifthRepresentationIndex]
      omega)
  have hfourCore : A.truncatedPrefixDefect B (-1) 6 4 =
      A.tail.truncatedPrefixDefect B.tail (-1) 5 3 := by
    simpa only [fourthTail, lemma93FourthRepresentationIndex,
      Nat.reduceAdd, Nat.reduceSub] using hfour
  have hfiveCore : A.truncatedPrefixDefect B (-1) 7 5 =
      A.tail.truncatedPrefixDefect B.tail (-1) 6 4 := by
    simpa only [fifthTail, lemma93FifthRepresentationIndex,
      Nat.reduceAdd, Nat.reduceSub] using hfive
  refine { reverseAtImportant := ?_ }
  intro i himportant hlow
  have hvalue : i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by
    have := i.pos
    omega
  rcases hvalue with honeValue | htwoValue | hthreeValue | hfourValue
  · have hi : i = firstTail := by
      apply representationIndex_eq_of_val_eq_caseTwoAssembly
      simpa only [firstTail, firstRepresentationIndex] using honeValue
    have hshift : firstTail.tailShift =
        secondRepresentationIndex (N + 4) (N + 5) := by
      apply representationIndex_eq_of_val_eq_caseTwoAssembly
      simp only [RepresentationIndex.tailShift_val, firstTail,
        firstRepresentationIndex, secondRepresentationIndex]
    rw [hi, hshift]
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact (P.firstRepresentationAlpha_eq hcase).le
  · have hi : i = secondTail := by
      apply representationIndex_eq_of_val_eq_caseTwoAssembly
      simpa only [secondTail, lemma93SecondTailRepresentationIndex]
        using htwoValue
    rw [hi] at himportant ⊢
    exact (A.representationAlpha_tail_eq_shift_of_core_eq_at_important
      (alphaV := targetLaws) (alphaW := sourceLaws)
      B P.normalized.headValue_eq secondTail (by
        simp only [secondTail, lemma93SecondTailRepresentationIndex]
        omega) himportant
      (by simpa only [secondTail, lemma93SecondTailRepresentationIndex] using htwo)
      (fun _ ↦ by
        simpa only [secondTail, lemma93SecondTailRepresentationIndex] using hone)
      (fun _ ↦ by
        simpa only [secondTail, lemma93SecondTailRepresentationIndex]
          using hthree)).le
  · have hi : i = thirdTail := by
      apply representationIndex_eq_of_val_eq_caseTwoAssembly
      simpa only [thirdTail, lemma93ThirdRepresentationIndex]
        using hthreeValue
    rw [hi] at himportant ⊢
    exact (A.representationAlpha_tail_eq_shift_of_core_eq_at_important
      (alphaV := targetLaws) (alphaW := sourceLaws)
      B P.normalized.headValue_eq thirdTail (by
        simp only [thirdTail, lemma93ThirdRepresentationIndex]
        omega) himportant
      (by simpa only [thirdTail, lemma93ThirdRepresentationIndex] using hthree)
      (fun _ ↦ by
        simpa only [thirdTail, lemma93ThirdRepresentationIndex] using htwo)
      (fun _ ↦ by
        simpa only [thirdTail, lemma93ThirdRepresentationIndex,
          Nat.reduceAdd] using hfourCore)).le
  · have hi : i = fourthTail := by
      apply representationIndex_eq_of_val_eq_caseTwoAssembly
      simpa only [fourthTail, lemma93FourthRepresentationIndex]
        using hfourValue
    rw [hi] at himportant ⊢
    exact (A.representationAlpha_tail_eq_shift_of_core_eq_at_important
      (alphaV := targetLaws) (alphaW := sourceLaws)
      B P.normalized.headValue_eq fourthTail (by
        simp only [fourthTail, lemma93FourthRepresentationIndex]
        omega) himportant
      (by simpa only [fourthTail, lemma93FourthRepresentationIndex,
        Nat.reduceAdd] using hfourCore)
      (fun _ ↦ by
        simpa only [fourthTail, lemma93FourthRepresentationIndex] using hthree)
      (fun _ ↦ by
        simpa only [fourthTail, lemma93FourthRepresentationIndex,
          Nat.reduceAdd] using hfiveCore)).le

set_option maxHeartbeats 1800000 in
-- The current-essential third boundary carries the only dependent exceptional candidate.
/-- Subcase 2(a): the second core grows strictly and the third core is
unchanged.  The third original invariant lies below the growing primary
candidate.  At the following boundary, either the changing previous candidate
is unused or the first nonessential triple removes the obligation. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.lowReverse_of_secondCoreStrict
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 7)} {b : GoodBONG r M (N + 7)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair (N := N + 3) a b)
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
    (htwo :
      P.normalized.targetTransform.transformed.truncatedPrefixDefect
          P.normalized.sourceTransform.transformed (-1) 4 2 <
        P.normalized.targetTransform.transformed.tail.truncatedPrefixDefect
          P.normalized.sourceTransform.transformed.tail (-1) 3 1)
    (hthree :
      P.normalized.targetTransform.transformed.truncatedPrefixDefect
          P.normalized.sourceTransform.transformed (-1) 5 3 =
        P.normalized.targetTransform.transformed.tail.truncatedPrefixDefect
          P.normalized.sourceTransform.transformed.tail (-1) 4 2) :
    Beli2019Lemma93LowReverseCertificate (N := N + 3) a b
      P.normalized := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let firstTail : RepresentationIndex (N + 6) (N + 6) :=
    firstRepresentationIndex (N + 4) (N + 5)
  let secondTail : RepresentationIndex (N + 6) (N + 6) :=
    lemma93SecondTailRepresentationIndex (N + 3)
  let thirdTail : RepresentationIndex (N + 6) (N + 6) :=
    lemma93ThirdRepresentationIndex (N + 2)
  let fourthTail : RepresentationIndex (N + 6) (N + 6) :=
    lemma93FourthRepresentationIndex (N + 1)
  let fifthTail : RepresentationIndex (N + 6) (N + 6) :=
    lemma93FifthRepresentationIndex N
  let thirdOriginal : RepresentationIndex (N + 7) (N + 7) :=
    lemma93ThirdRepresentationIndex (N + 3)
  let fourthOriginal : RepresentationIndex (N + 7) (N + 7) :=
    lemma93FourthRepresentationIndex (N + 2)
  have hone : A.truncatedPrefixDefect B (-1) 3 1 =
      A.tail.truncatedPrefixDefect B.tail (-1) 2 0 :=
    P.firstThirdDefect_eq_tail hcase
  have htwoLe : A.truncatedPrefixDefect B (-1) 4 2 ≤
      A.tail.truncatedPrefixDefect B.tail (-1) 3 1 := htwo.le
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
  have hfiveRaw := A.primaryCoreDefect_shift_eq_tail_of_laterAlphaValue_eq
    B P.normalized.headValue_eq
    (fun k hk ↦ by
      letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
      exact P.normalized.targetTransform.transformed_laterAlpha_eq_tail k hk)
    (fun k hk ↦ by
      letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
      exact P.normalized.sourceTransform.transformed_laterAlpha_eq_tail k hk)
    fifthTail (by
      simp only [fifthTail, lemma93FifthRepresentationIndex]
      omega)
  have hfour : A.truncatedPrefixDefect B (-1) 6 4 =
      A.tail.truncatedPrefixDefect B.tail (-1) 5 3 := by
    simpa only [fourthTail, lemma93FourthRepresentationIndex,
      Nat.reduceAdd, Nat.reduceSub] using hfourRaw
  have hfive : A.truncatedPrefixDefect B (-1) 7 5 =
      A.tail.truncatedPrefixDefect B.tail (-1) 6 4 := by
    simpa only [fifthTail, lemma93FifthRepresentationIndex,
      Nat.reduceAdd, Nat.reduceSub] using hfiveRaw
  have htwoPrimaryStrict :
      A.representationPrimaryDefect B secondTail.tailShift <
        A.tail.representationPrimaryDefect B.tail secondTail :=
    A.representationPrimaryDefect_shift_lt_tail_of_core_lt B secondTail (by
      simpa only [secondTail, lemma93SecondTailRepresentationIndex,
        Nat.reduceAdd, Nat.reduceSub] using htwo)
  have hthirdAlphaLt :=
    P.thirdRepresentationAlpha_lt_primary_of_secondPrimaryStrict
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV) hcase horder htwoPrimaryStrict
  have hsecondShift : secondTail.tailShift = thirdOriginal := by
    apply representationIndex_eq_of_val_eq_caseTwoAssembly
    simp only [RepresentationIndex.tailShift_val, secondTail, thirdOriginal,
      lemma93SecondTailRepresentationIndex, lemma93ThirdRepresentationIndex]
  have hthirdShift : thirdTail.tailShift = fourthOriginal := by
    apply representationIndex_eq_of_val_eq_caseTwoAssembly
    simp only [RepresentationIndex.tailShift_val, thirdTail, fourthOriginal,
      lemma93ThirdRepresentationIndex, lemma93FourthRepresentationIndex]
  refine { reverseAtImportant := ?_ }
  intro i himportant hlow
  have hvalue : i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by
    have := i.pos
    omega
  rcases hvalue with honeValue | htwoValue | hthreeValue | hfourValue
  · have hi : i = firstTail := by
      apply representationIndex_eq_of_val_eq_caseTwoAssembly
      simpa only [firstTail, firstRepresentationIndex] using honeValue
    have hshift : firstTail.tailShift =
        secondRepresentationIndex (N + 4) (N + 5) := by
      apply representationIndex_eq_of_val_eq_caseTwoAssembly
      simp only [RepresentationIndex.tailShift_val, firstTail,
        firstRepresentationIndex, secondRepresentationIndex]
    rw [hi, hshift]
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact (P.firstRepresentationAlpha_eq hcase).le
  · have hi : i = secondTail := by
      apply representationIndex_eq_of_val_eq_caseTwoAssembly
      simpa only [secondTail, lemma93SecondTailRepresentationIndex]
        using htwoValue
    rw [hi] at himportant ⊢
    exact (A.representationAlpha_tail_eq_shift_of_alpha_lt_primary_at_important
      (alphaV := targetLaws) (alphaW := sourceLaws)
      B P.normalized.headValue_eq secondTail (by
        simp only [secondTail, lemma93SecondTailRepresentationIndex]
        omega) (by
        simp only [secondTail, lemma93SecondTailRepresentationIndex]
        omega) himportant
      (by simpa only [hsecondShift, thirdOriginal] using hthirdAlphaLt)
      (fun _ ↦ by
        simpa only [secondTail, lemma93SecondTailRepresentationIndex] using hone)
      (fun _ ↦ by
        simpa only [secondTail, lemma93SecondTailRepresentationIndex]
          using hthree)).le
  · have hi : i = thirdTail := by
      apply representationIndex_eq_of_val_eq_caseTwoAssembly
      simpa only [thirdTail, lemma93ThirdRepresentationIndex]
        using hthreeValue
    rw [hi] at himportant ⊢
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
        have hcross : B.order (2 : Fin (N + 7)) <
            A.order (4 : Fin (N + 7)) := by
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
            (N := N + 1) (targetLaws := targetLaws)
            (sourceLaws := sourceLaws) A B hcross
            (by simpa only [thirdOriginal] using hthirdAlphaLt)
            (by simpa only [fourthOriginal] using hfourthEq)
        exfalso
        apply htriple.2.1
        unfold IsCurrentEssential at hcurrent
        have hindex : currentEssentialIndex thirdTail =
            (⟨2, by omega⟩ : Fin (N + 6)) := by
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
            using hthree)
          (by simpa only [thirdTail, lemma93ThirdRepresentationIndex]
            using htwoLe)
          (lt_of_le_of_ne hpreviousLe heq)).le
    · have hnext := himportant.resolve_left hcurrent
      exact (A.representationAlpha_tail_eq_shift_of_core_eq_at_important
        (alphaV := targetLaws) (alphaW := sourceLaws)
        B P.normalized.headValue_eq thirdTail (by
          simp only [thirdTail, lemma93ThirdRepresentationIndex]
          omega) (Or.inr hnext)
        (by simpa only [thirdTail, lemma93ThirdRepresentationIndex]
          using hthree)
        (fun h ↦ False.elim (hcurrent h))
        (fun _ ↦ by
          simpa only [thirdTail, lemma93ThirdRepresentationIndex,
            Nat.reduceAdd] using hfour)).le
  · have hi : i = fourthTail := by
      apply representationIndex_eq_of_val_eq_caseTwoAssembly
      simpa only [fourthTail, lemma93FourthRepresentationIndex]
        using hfourValue
    rw [hi] at himportant ⊢
    exact (A.representationAlpha_tail_eq_shift_of_core_eq_at_important
      (alphaV := targetLaws) (alphaW := sourceLaws)
      B P.normalized.headValue_eq fourthTail (by
        simp only [fourthTail, lemma93FourthRepresentationIndex]
        omega) himportant
      (by simpa only [fourthTail, lemma93FourthRepresentationIndex,
        Nat.reduceAdd] using hfour)
      (fun _ ↦ by
        simpa only [fourthTail, lemma93FourthRepresentationIndex] using hthree)
      (fun _ ↦ by
        simpa only [fourthTail, lemma93FourthRepresentationIndex,
          Nat.reduceAdd] using hfive)).le

set_option maxHeartbeats 2000000 in
-- The shifted nonessentiality argument at the fourth low boundary is fully dependent.
/-- Subcase 2(b): the third core grows strictly.  The preceding second
boundary and the changing third boundary are transported by the two exact
subcase-(b) lemmas.  At the fourth boundary, either the moving previous
candidate is unused or the shifted nonessential triple removes the obligation. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.lowReverse_of_thirdCoreStrict
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 7)} {b : GoodBONG r M (N + 7)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair (N := N + 3) a b)
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
    (hthree :
      P.normalized.targetTransform.transformed.truncatedPrefixDefect
          P.normalized.sourceTransform.transformed (-1) 5 3 <
        P.normalized.targetTransform.transformed.tail.truncatedPrefixDefect
          P.normalized.sourceTransform.transformed.tail (-1) 4 2) :
    Beli2019Lemma93LowReverseCertificate (N := N + 3) a b
      P.normalized := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let firstTail : RepresentationIndex (N + 6) (N + 6) :=
    firstRepresentationIndex (N + 4) (N + 5)
  let secondTail : RepresentationIndex (N + 6) (N + 6) :=
    lemma93SecondTailRepresentationIndex (N + 3)
  let thirdTail : RepresentationIndex (N + 6) (N + 6) :=
    lemma93ThirdRepresentationIndex (N + 2)
  let fourthTail : RepresentationIndex (N + 6) (N + 6) :=
    lemma93FourthRepresentationIndex (N + 1)
  let fifthTail : RepresentationIndex (N + 6) (N + 6) :=
    lemma93FifthRepresentationIndex N
  let thirdOriginal : RepresentationIndex (N + 7) (N + 7) :=
    lemma93ThirdRepresentationIndex (N + 3)
  let fourthOriginal : RepresentationIndex (N + 7) (N + 7) :=
    lemma93FourthRepresentationIndex (N + 2)
  let fifthOriginal : RepresentationIndex (N + 7) (N + 7) :=
    lemma93FifthRepresentationIndex (N + 1)
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
  have hfiveRaw := A.primaryCoreDefect_shift_eq_tail_of_laterAlphaValue_eq
    B P.normalized.headValue_eq
    (fun k hk ↦ by
      letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
      exact P.normalized.targetTransform.transformed_laterAlpha_eq_tail k hk)
    (fun k hk ↦ by
      letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
      exact P.normalized.sourceTransform.transformed_laterAlpha_eq_tail k hk)
    fifthTail (by
      simp only [fifthTail, lemma93FifthRepresentationIndex]
      omega)
  have hfour : A.truncatedPrefixDefect B (-1) 6 4 =
      A.tail.truncatedPrefixDefect B.tail (-1) 5 3 := by
    simpa only [fourthTail, lemma93FourthRepresentationIndex,
      Nat.reduceAdd, Nat.reduceSub] using hfourRaw
  have hfive : A.truncatedPrefixDefect B (-1) 7 5 =
      A.tail.truncatedPrefixDefect B.tail (-1) 6 4 := by
    simpa only [fifthTail, lemma93FifthRepresentationIndex,
      Nat.reduceAdd, Nat.reduceSub] using hfiveRaw
  have hthreeLe : A.truncatedPrefixDefect B (-1) 5 3 ≤
      A.tail.truncatedPrefixDefect B.tail (-1) 4 2 := hthree.le
  have hthreePrimaryStrict :
      A.representationPrimaryDefect B thirdTail.tailShift <
        A.tail.representationPrimaryDefect B.tail thirdTail :=
    A.representationPrimaryDefect_shift_lt_tail_of_core_lt B thirdTail (by
      simpa only [thirdTail, lemma93ThirdRepresentationIndex,
        Nat.reduceAdd, Nat.reduceSub] using hthree)
  have hfourthAlphaLt :=
    P.fourthRepresentationAlpha_lt_primary_of_thirdPrimaryStrict
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV) (classificationW := classificationW)
      thirdTail (by
        simp only [thirdTail, lemma93ThirdRepresentationIndex])
      hthreePrimaryStrict hcase horder
  have hsecondShift : secondTail.tailShift = thirdOriginal := by
    apply representationIndex_eq_of_val_eq_caseTwoAssembly
    simp only [RepresentationIndex.tailShift_val, secondTail, thirdOriginal,
      lemma93SecondTailRepresentationIndex, lemma93ThirdRepresentationIndex]
  have hthirdShift : thirdTail.tailShift = fourthOriginal := by
    apply representationIndex_eq_of_val_eq_caseTwoAssembly
    simp only [RepresentationIndex.tailShift_val, thirdTail, fourthOriginal,
      lemma93ThirdRepresentationIndex, lemma93FourthRepresentationIndex]
  have hfourthShift : fourthTail.tailShift = fifthOriginal := by
    apply representationIndex_eq_of_val_eq_caseTwoAssembly
    simp only [RepresentationIndex.tailShift_val, fourthTail, fifthOriginal,
      lemma93FourthRepresentationIndex, lemma93FifthRepresentationIndex]
  refine { reverseAtImportant := ?_ }
  intro i himportant hlow
  have hvalue : i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by
    have := i.pos
    omega
  rcases hvalue with honeValue | htwoValue | hthreeValue | hfourValue
  · have hi : i = firstTail := by
      apply representationIndex_eq_of_val_eq_caseTwoAssembly
      simpa only [firstTail, firstRepresentationIndex] using honeValue
    have hshift : firstTail.tailShift =
        secondRepresentationIndex (N + 4) (N + 5) := by
      apply representationIndex_eq_of_val_eq_caseTwoAssembly
      simp only [RepresentationIndex.tailShift_val, firstTail,
        firstRepresentationIndex, secondRepresentationIndex]
    rw [hi, hshift]
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact (P.firstRepresentationAlpha_eq hcase).le
  · have hi : i = secondTail := by
      apply representationIndex_eq_of_val_eq_caseTwoAssembly
      simpa only [secondTail, lemma93SecondTailRepresentationIndex]
        using htwoValue
    rw [hi, hsecondShift]
    exact (P.secondTailRepresentationAlpha_eq
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV) (classificationW := classificationW)
      thirdTail (by
        simp only [thirdTail, lemma93ThirdRepresentationIndex])
      hthreePrimaryStrict hcase horder).le
  · have hi : i = thirdTail := by
      apply representationIndex_eq_of_val_eq_caseTwoAssembly
      simpa only [thirdTail, lemma93ThirdRepresentationIndex]
        using hthreeValue
    rw [hi, hthirdShift]
    exact (P.thirdTailRepresentationAlpha_eq_of_thirdPrimaryStrict
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV) (classificationW := classificationW)
      hthreePrimaryStrict hcase horder).le
  · have hi : i = fourthTail := by
      apply representationIndex_eq_of_val_eq_caseTwoAssembly
      simpa only [fourthTail, lemma93FourthRepresentationIndex]
        using hfourValue
    rw [hi] at himportant ⊢
    by_cases hcurrent : A.tail.IsCurrentEssential B.tail fourthTail
    · have hpreviousLe :=
        A.representationAlpha_shift_le_previous_of_currentEssential
          (alphaV := targetLaws) B fourthTail (by
            simp only [fourthTail, lemma93FourthRepresentationIndex]
            omega) (by
            simp only [fourthTail, lemma93FourthRepresentationIndex]
            omega) hcurrent
      by_cases heq : A.representationAlpha B fourthTail.tailShift =
          A.representationSecondaryPreviousDefect B fourthTail.tailShift (by
            simp only [RepresentationIndex.tailShift_val, fourthTail,
              lemma93FourthRepresentationIndex]
            omega)
      · have hcrossTail := order_previous_lt_current_of_currentEssential
          A.tail B.tail fourthTail (by
            simp only [fourthTail, lemma93FourthRepresentationIndex]
            omega) (by
            simp only [fourthTail, lemma93FourthRepresentationIndex]
            omega) hcurrent
        have hcross : B.order (3 : Fin (N + 7)) <
            A.order (5 : Fin (N + 7)) := by
          rw [B.order_goodTail, A.order_goodTail] at hcrossTail
          convert hcrossTail using 1 <;> congr 1 <;> apply Fin.ext <;>
            simp only [fourthTail, lemma93FourthRepresentationIndex,
              Fin.val_succ] <;> omega
        have hfifthEq : A.representationAlpha B fifthOriginal =
            A.representationSecondaryPreviousDefect B fifthOriginal (by
              simp only [fifthOriginal, lemma93FifthRepresentationIndex]
              omega) := by
          simpa only [hfourthShift] using heq
        have htriple :=
          tail_nextThree_not_essential_of_fourthPrimaryStrict_fifthPrevious
            (N := N) (targetLaws := targetLaws) (sourceLaws := sourceLaws)
            A B hcross
            (by simpa only [fourthOriginal] using hfourthAlphaLt)
            (by simpa only [fifthOriginal] using hfifthEq)
        exfalso
        apply htriple.2.1
        unfold IsCurrentEssential at hcurrent
        have hindex : currentEssentialIndex fourthTail =
            (⟨3, by omega⟩ : Fin (N + 6)) := by
          apply Fin.ext
          simp only [currentEssentialIndex, fourthTail,
            lemma93FourthRepresentationIndex]
        rwa [hindex] at hcurrent
      · exact (A.representationAlpha_tail_eq_shift_of_alpha_lt_previous_of_currentEssential
          (alphaV := targetLaws) B fourthTail (by
            simp only [fourthTail, lemma93FourthRepresentationIndex]
            omega) (by
            simp only [fourthTail, lemma93FourthRepresentationIndex]
            omega) hcurrent
          (by simpa only [fourthTail, lemma93FourthRepresentationIndex,
            Nat.reduceAdd] using hfour)
          (by simpa only [fourthTail, lemma93FourthRepresentationIndex]
            using hthreeLe)
          (lt_of_le_of_ne hpreviousLe heq)).le
    · have hnext := himportant.resolve_left hcurrent
      exact (A.representationAlpha_tail_eq_shift_of_core_eq_at_important
        (alphaV := targetLaws) (alphaW := sourceLaws)
        B P.normalized.headValue_eq fourthTail (by
          simp only [fourthTail, lemma93FourthRepresentationIndex]
          omega) (Or.inr hnext)
        (by simpa only [fourthTail, lemma93FourthRepresentationIndex,
          Nat.reduceAdd] using hfour)
        (fun h ↦ False.elim (hcurrent h))
        (fun _ ↦ by
          simpa only [fourthTail, lemma93FourthRepresentationIndex,
            Nat.reduceAdd] using hfive)).le

/-- Complete ordinary Case-2 low certificate in ranks at least seven.  Head
deletion can only raise the two exceptional cores, so linearity gives exactly
the three branches assembled above. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.toLowReverseCertificate_highRank
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 7)} {b : GoodBONG r M (N + 7)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair (N := N + 3) a b)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed)
    (horder :
      P.normalized.targetTransform.transformed.order (0 : Fin (N + 7)) <
          P.normalized.targetTransform.transformed.order (2 : Fin (N + 7)) ∨
        (P.normalized.targetTransform.transformed.order (1 : Fin (N + 7)) =
            P.normalized.sourceTransform.transformed.order (1 : Fin (N + 7)) ∧
          P.normalized.targetTransform.transformed.order (1 : Fin (N + 7)) <
            P.normalized.targetTransform.transformed.order (3 : Fin (N + 7)))) :
    Beli2019Lemma93LowReverseCertificate (N := N + 3) a b
      P.normalized := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let secondTail : RepresentationIndex (N + 6) (N + 6) :=
    lemma93SecondTailRepresentationIndex (N + 3)
  let thirdTail : RepresentationIndex (N + 6) (N + 6) :=
    lemma93ThirdRepresentationIndex (N + 2)
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
  rcases lt_or_eq_of_le hthreeLe with hthreeStrict | hthreeEq
  · exact P.lowReverse_of_thirdCoreStrict
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV) (classificationW := classificationW)
      hcase horder hthreeStrict
  · rcases lt_or_eq_of_le htwoLe with htwoStrict | htwoEq
    · exact P.lowReverse_of_secondCoreStrict
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        (classificationV := classificationV)
        (classificationW := classificationW)
        hcase horder htwoStrict hthreeEq
    · exact P.lowReverse_of_twoCoreEq
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        (classificationV := classificationV)
        (classificationW := classificationW)
        hcase htwoEq hthreeEq

/-- The original Case-2 and Lemma-9.1 hypotheses transport to the fully
selected pair and supply the two inputs of the preceding certificate. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.toLowReverseCertificate_highRank_of_original
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    {a : GoodBONG q L (N + 7)} {b : GoodBONG r M (N + 7)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair (N := N + 3) a b)
    (hlemma91 : a.Lemma91Alternative b)
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    Beli2019Lemma93LowReverseCertificate (N := N + 3) a b
      P.normalized :=
  P.toLowReverseCertificate_highRank
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

/-- A fully selected high-rank Case-2 pair now constructs the concrete
recursive input required by Lemma 9.3. -/
noncomputable def Beli2019Lemma93CaseTwoNormalizedPair.toLemma93Input_highRank
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    (a : GoodBONG q L (N + 7)) (b : GoodBONG r M (N + 7))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 6)))
    (P : Beli2019Lemma93CaseTwoNormalizedPair (N := N + 3) a b)
    (hlemma91 : a.Lemma91Alternative b)
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl (N + 6))
        ambient conditions) :=
  P.normalized.toLemma93Input
    (classificationV := classificationV) (classificationW := classificationW)
    a b ambient conditions
    (P.toLowReverseCertificate_highRank_of_original
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV) (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      hlemma91 hcase)

/-- Full ordinary Case 2 of Lemma 9.3 in ranks at least seven, from the
original pair of good BONGs to the concrete recursive input.  The rank is
written as `N + 7` because this is the first rank at which both exceptional
three-term windows used in the paper are interior windows. -/
theorem exists_beli2019Lemma93Input_caseTwo_highRank
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
    (a : GoodBONG q L (N + 7)) (b : GoodBONG r M (N + 7))
    (hfirst : a.order (0 : Fin (N + 7)) =
      b.order (0 : Fin (N + 7)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 6)))
    (hlemma91 : a.Lemma91Alternative b)
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    Nonempty (Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl (N + 6))
        ambient conditions)) := by
  rcases exists_beli2019Lemma93CaseTwoNormalizedPair
      (N := N + 3)
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
  exact ⟨P.toLemma93Input_highRank
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    a b ambient conditions hlemma91 hcase⟩

end BONG.GoodBONG

end Bong
