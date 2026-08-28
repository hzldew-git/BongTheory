/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93CaseTwoCertificates
import Bong.Bong.Beli2019CappedDefectSharp

/-!
# Beli (2019), Lemma 9.3: ordinary Case 2(a)

This file formalizes the contradiction at the end of subcase (a).  If the
second low primary defect grows after deleting the equal heads, then the
original third representation invariant cannot be its primary candidate.

The v2 source has a sign typo in this paragraph: from
`β₁ ≥ A₃ = R₄ - S₂ + β₁` one obtains `R₄ ≤ S₂`, not `R₄ > S₂`.
The following proof uses the former inequality, as does the very next
sentence of the paper.
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

/-- The tail boundary whose primary term contains
`d[-a₁,₄ b₁,₂]` in the paper's notation. -/
def lemma93SecondTailRepresentationIndex (N : Nat) :
    RepresentationIndex (N + 3) (N + 3) where
  val := 2
  pos := by omega
  lt_large := by omega
  le_small := by omega

set_option maxHeartbeats 1200000 in
/-- Case 2(a), terminal contradiction.  Under a strict second low primary
shift, `A₃` is strictly below its primary candidate.  This is the formal
version of lines 9337--9346 of the v2 source. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.thirdRepresentationAlpha_lt_primary_of_secondPrimaryStrict
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
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
              (3 : Fin (N + 4))))
    (hstrict :
      P.normalized.targetTransform.transformed.representationPrimaryDefect
          P.normalized.sourceTransform.transformed
            (lemma93SecondTailRepresentationIndex N).tailShift <
        P.normalized.targetTransform.transformed.tail.representationPrimaryDefect
          P.normalized.sourceTransform.transformed.tail
            (lemma93SecondTailRepresentationIndex N)) :
    P.normalized.targetTransform.transformed.representationAlpha
        P.normalized.sourceTransform.transformed
          (lemma93ThirdRepresentationIndex N) <
      P.normalized.targetTransform.transformed.representationPrimaryDefect
        P.normalized.sourceTransform.transformed
          (lemma93ThirdRepresentationIndex N) := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let tailSecond := lemma93SecondTailRepresentationIndex N
  let third := lemma93ThirdRepresentationIndex N
  have htailThird : tailSecond.tailShift = third := by
    rfl
  have hstrict' : A.representationPrimaryDefect B third <
      A.tail.representationPrimaryDefect B.tail tailSecond := by
    simpa only [A, B, tailSecond, third, htailThird] using hstrict
  have hthirdLePrimary : A.representationAlpha B third ≤
      A.representationPrimaryDefect B third :=
    A.representationAlpha_le_primary B third
  apply lt_of_le_of_ne hthirdLePrimary
  intro hthirdEq
  have hfailure := P.primaryStrict_sourceAlphaFailure
    (classificationV := classificationV) tailSecond (by
      simp only [tailSecond, lemma93SecondTailRepresentationIndex]
      omega) hstrict'
  have hsourceFormula := P.sourceSecondAlphaFormula_of_primaryStrict
    (sourceLaws := sourceLaws) (classificationV := classificationV)
    tailSecond (Or.inl (by
      simp only [tailSecond, lemma93SecondTailRepresentationIndex])) hstrict'
  have hsourceFormulaTop :
      (B.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) =
        (((B.order (2 : Fin (N + 4)) -
          B.order (1 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) +
          (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := by
    rw [← WithTop.coe_add]
    exact congrArg (fun z : ℚ => (z : WithTop ℚ)) hsourceFormula
  have hfailureDefect : A.truncatedPrefixDefect B (-1) 4 2 =
      (B.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) := by
    have h := hfailure.1
    change A.truncatedPrefixDefect B (-1) (2 + 2) 2 =
      (B.alphaValue ⟨2 - 1, by omega⟩ : WithTop ℚ) at h
    norm_num at h ⊢
    exact h
  have hprimaryFormula : A.representationPrimaryDefect B third =
      (((A.order (3 : Fin (N + 4)) -
        B.order (1 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) +
        (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := by
    unfold representationPrimaryDefect
    simp only [third, lemma93ThirdRepresentationIndex]
    have hthree : (⟨3, by omega⟩ : Fin (N + 4)) =
        (3 : Fin (N + 4)) := by
      apply Fin.ext
      change 3 = 3 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega)]
    have htwo : (⟨3 - 1, by omega⟩ : Fin (N + 4)) =
        (2 : Fin (N + 4)) := by
      apply Fin.ext
      change 2 = 2 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hthree, htwo, hfailureDefect, hsourceFormulaTop]
    norm_cast
    push_cast
    ring
  have hthirdFormula : A.representationAlpha B third =
      (((A.order (3 : Fin (N + 4)) -
        B.order (1 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) +
        (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) :=
    hthirdEq.trans hprimaryFormula
  have hthirdLeBeta :=
    P.thirdRepresentationAlpha_le_firstSourceAlpha_of_primaryStrict
      (sourceLaws := sourceLaws) (classificationV := classificationV)
      tailSecond (Or.inl (by
        simp only [tailSecond, lemma93SecondTailRepresentationIndex])) hstrict'
  have hfourthLeSecond : A.order (3 : Fin (N + 4)) ≤
      B.order (1 : Fin (N + 4)) := by
    have htop :
        (((A.order (3 : Fin (N + 4)) -
          B.order (1 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) +
            (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) ≤
          (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := by
      rw [← hthirdFormula]
      simpa only [A, B, third] using hthirdLeBeta
    rw [← WithTop.coe_add] at htop
    have hq := WithTop.coe_le_coe.mp htop
    push_cast at hq
    exact_mod_cast (show (A.order (3 : Fin (N + 4)) : ℚ) ≤
      (B.order (1 : Fin (N + 4)) : ℚ) by linarith)
  rcases horder with hfirstThird | hsecondFourth
  · have hfirst : A.order (0 : Fin (N + 4)) =
        B.order (0 : Fin (N + 4)) := by
      unfold GoodBONG.order
      rw [A.toBONG.order_eq_ordUnit, B.toBONG.order_eq_ordUnit]
      exact congrArg (ordUnit K) (by
        apply Units.ext
        exact P.normalized.headValue_eq)
    have hthirdSource :=
      P.thirdTargetOrder_le_thirdSourceOrder_of_primaryStrict
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        (classificationV := classificationV) tailSecond
        (Or.inl (by
          simp only [tailSecond, lemma93SecondTailRepresentationIndex]))
        hstrict' hcase
    have hsourceFirstThird : B.order (0 : Fin (N + 4)) <
        B.order (2 : Fin (N + 4)) := by
      rw [← hfirst]
      exact hfirstThird.trans_le hthirdSource
    have hbetaHalf := A.sourceFirstAlpha_lt_halfGap_of_caseTwo B hfirst hcase
    have hbetaHalfTop :
        (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) <
          B.halfGapCandidate (0 : Fin (N + 3)) := by
      rw [← B.coe_halfGapValue]
      exact_mod_cast hbetaHalf
    let sourceDefect : WithTop ℚ :=
      B.truncatedPrefixDefect B (-1) 0 2
    let sourceShift : ℚ :=
      ((B.order (1 : Fin (N + 4)) -
        B.order (0 : Fin (N + 4)) : Int) : ℚ)
    have hlocal := B.alpha_eq_min_halfGap_add_cappedAdjacent
      (0 : Fin (N + 3))
    change (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) =
      min (B.halfGapCandidate (0 : Fin (N + 3)))
        ((sourceShift : WithTop ℚ) + sourceDefect) at hlocal
    have hcandidateLe : (sourceShift : WithTop ℚ) + sourceDefect ≤
        B.halfGapCandidate (0 : Fin (N + 3)) := by
      by_contra hnot
      have hhalfLe : B.halfGapCandidate (0 : Fin (N + 3)) ≤
          (sourceShift : WithTop ℚ) + sourceDefect := le_of_not_ge hnot
      have heq : (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) =
          B.halfGapCandidate (0 : Fin (N + 3)) := by
        rw [hlocal]
        exact min_eq_left hhalfLe
      exact (ne_of_lt hbetaHalfTop) heq
    have hbetaCandidate :
        (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) =
          (sourceShift : WithTop ℚ) + sourceDefect := by
      rw [hlocal, min_eq_right hcandidateLe]
    have hsourceDefectNe : sourceDefect ≠ ⊤ := by
      intro htop
      rw [htop, add_top] at hbetaCandidate
      exact WithTop.coe_ne_top hbetaCandidate
    let d : ℚ := sourceDefect.untop hsourceDefectNe
    have hd : (d : WithTop ℚ) = sourceDefect :=
      WithTop.coe_untop sourceDefect hsourceDefectNe
    have hbetaCandidateQ : B.alphaValue (0 : Fin (N + 3)) =
        sourceShift + d := by
      rw [← hd, ← WithTop.coe_add] at hbetaCandidate
      exact WithTop.coe_eq_coe.mp hbetaCandidate
    let second := secondRepresentationIndex (N + 1) (N + 2)
    have hsecondFormula := by
      letI : Beli2006AlphaLaws.{u, v} K := targetLaws
      exact P.secondRepresentationAlpha_eq_formula hcase
    have hsourceDefectLtSecond : sourceDefect <
        A.representationAlpha B second := by
      rw [← hd, hsecondFormula, ← WithTop.coe_add]
      apply WithTop.coe_lt_coe.mpr
      dsimp only [sourceShift] at hbetaCandidateQ
      push_cast at hbetaCandidateQ ⊢
      have htargetFirstThirdQ :
          (A.order (0 : Fin (N + 4)) : ℚ) <
            (A.order (2 : Fin (N + 4)) : ℚ) := by
        exact_mod_cast hfirstThird
      have hheadQ : (A.order (0 : Fin (N + 4)) : ℚ) =
          (B.order (0 : Fin (N + 4)) : ℚ) := by
        exact_mod_cast hfirst
      linarith
    have hsecondLeComparison :=
      P.normalized.selectedConditions.defectCondition second
    rw [A.coe_representationAlphaValue B second] at hsecondLeComparison
    have hsourceDefectLtComparison : sourceDefect <
        A.truncatedPrefixDefect B 1 2 2 :=
      hsourceDefectLtSecond.trans_le hsecondLeComparison
    have hcomparisonComm : B.truncatedPrefixDefect A 1 2 2 =
        A.truncatedPrefixDefect B 1 2 2 :=
      B.truncatedPrefixDefect_comm A 1 2 2
    have hsharp := B.truncatedPrefixDefect_mul_eq_left_of_lt_right B A
      (-1) 1 0 2 2 (by
        change sourceDefect < B.truncatedPrefixDefect A 1 2 2
        rw [hcomparisonComm]
        exact hsourceDefectLtComparison)
    have htargetDefect : A.truncatedPrefixDefect A (-1) 0 2 =
        sourceDefect := by
      have hzeroLeft := B.truncatedPrefixDefect_zero_left_eq_self A (-1) 2
      change B.truncatedPrefixDefect A (-1) 0 2 =
        A.truncatedPrefixDefect A (-1) 0 2 at hzeroLeft
      rw [← hzeroLeft]
      simpa using hsharp
    have htargetLower := by
      letI : Beli2006AlphaLaws.{u, v} K := targetLaws
      exact A.order_sub_add_alpha_le_cappedAdjacent (0 : Fin (N + 3))
    change
      (((((A.order (0 : Fin (N + 4)) -
        A.order (1 : Fin (N + 4)) : Int) : ℚ) +
          A.alphaValue (0 : Fin (N + 3)) : ℚ)) : WithTop ℚ) ≤
        A.truncatedPrefixDefect A (-1) 0 2 at htargetLower
    rw [htargetDefect, ← hd] at htargetLower
    have htargetLowerQ := WithTop.coe_le_coe.mp htargetLower
    have hheadQ : (A.order (0 : Fin (N + 4)) : ℚ) =
        (B.order (0 : Fin (N + 4)) : ℚ) := by
      exact_mod_cast hfirst
    have hendpointBase :
        -(A.order (1 : Fin (N + 4)) : ℚ) +
            A.alphaValue (0 : Fin (N + 3)) ≤
          -(B.order (1 : Fin (N + 4)) : ℚ) +
            B.alphaValue (0 : Fin (N + 3)) := by
      dsimp only [sourceShift] at hbetaCandidateQ
      push_cast at htargetLowerQ hbetaCandidateQ
      linarith
    have hendpoint := by
      letI : Beli2006AlphaLaws.{u, v} K := targetLaws
      exact A.alphaRightEndpoint_antitone
        (show (0 : Fin (N + 3)) ≤ (2 : Fin (N + 3)) by norm_num)
    have hzeroSucc : (0 : Fin (N + 3)).succ =
        (1 : Fin (N + 4)) := by
      apply Fin.ext
      simp
    have htwoSucc : (2 : Fin (N + 3)).succ =
        (3 : Fin (N + 4)) := by
      apply Fin.ext
      change 2 % (N + 3) + 1 = 3 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    unfold alphaRightEndpoint at hendpoint
    rw [hzeroSucc, htwoSucc] at hendpoint
    have halphaThreeLeQ : A.alphaValue (2 : Fin (N + 3)) ≤
        ((A.order (3 : Fin (N + 4)) -
          B.order (1 : Fin (N + 4)) : Int) : ℚ) +
          B.alphaValue (0 : Fin (N + 3)) := by
      push_cast at hendpoint
      push_cast
      linarith
    have halphaThreeLeThird :
        (A.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) ≤
          A.representationAlpha B third := by
      rw [hthirdFormula, ← WithTop.coe_add]
      exact_mod_cast halphaThreeLeQ
    have halphaThreeLeBeta :
        (A.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) ≤
          (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) :=
      halphaThreeLeThird.trans (by
        simpa only [A, B, third] using hthirdLeBeta)
    exact (not_lt_of_ge halphaThreeLeBeta) hcase.2.2
  · exact (not_lt_of_ge hfourthLeSecond)
      (hsecondFourth.1 ▸ hsecondFourth.2)

end BONG.GoodBONG

end Bong
