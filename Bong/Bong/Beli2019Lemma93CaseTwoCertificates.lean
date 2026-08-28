/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93CaseTwoNonessential

/-!
# Beli (2019), Lemma 9.3: Case-2 nonessentiality certificates

This file connects the two nonessential triples in ordinary Case 2 to the
uniform low reverse certificate used by the Lemma 9.3 descent.  It is the
formal content of the paper's repeated sentence that an equality
`Aᵢ = Aᵢ*` is “not required” when neither adjacent index is essential.
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

/-- A low comparison equality is needed only when at least one of its two
adjacent tail indices is essential.  Thus “equality or neither endpoint is
essential” is exactly enough to construct the ordinary low reverse
certificate. -/
theorem Beli2019Lemma93LowReverseCertificate.ofEqOrNotImportant
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (D : Beli2019Lemma93NormalizedPair a b)
    (hlocal : ∀ i : RepresentationIndex (N + 3) (N + 3),
      i.val ≤ 4 →
        D.targetTransform.transformed.tail.representationAlpha
            D.sourceTransform.transformed.tail i =
          D.targetTransform.transformed.representationAlpha
            D.sourceTransform.transformed i.tailShift ∨
        ((¬D.targetTransform.transformed.tail.IsCurrentEssential
            D.sourceTransform.transformed.tail i) ∧
          (¬D.targetTransform.transformed.tail.IsNextEssential
            D.sourceTransform.transformed.tail i))) :
    Beli2019Lemma93LowReverseCertificate a b D where
  reverseAtImportant i himportant hlow := by
    rcases hlocal i hlow with heq | hnot
    · exact heq.le
    · exact False.elim (himportant.elim hnot.1 hnot.2)

/-- If tail indices `2,3,4` in paper notation are nonessential, then the
possible exceptional comparison boundaries `A₃,A₄` can be omitted.  Exact
transport is required only at the other low boundaries. -/
theorem Beli2019Lemma93LowReverseCertificate.ofFirstNonessentialTriple
    {a : GoodBONG q L (N + 6)} {b : GoodBONG r M (N + 6)}
    (D : Beli2019Lemma93NormalizedPair (N := N + 2) a b)
    (htriple :
      (¬D.targetTransform.transformed.tail.IsEssentialFor
          D.sourceTransform.transformed.tail
          (⟨1, by omega⟩ : Fin (N + 5))) ∧
        (¬D.targetTransform.transformed.tail.IsEssentialFor
          D.sourceTransform.transformed.tail
          (⟨2, by omega⟩ : Fin (N + 5))) ∧
        (¬D.targetTransform.transformed.tail.IsEssentialFor
          D.sourceTransform.transformed.tail
          (⟨3, by omega⟩ : Fin (N + 5))))
    (heqOutside : ∀ i : RepresentationIndex (N + 5) (N + 5),
      i.val ≤ 4 → i.val ≠ 2 → i.val ≠ 3 →
        D.targetTransform.transformed.tail.representationAlpha
            D.sourceTransform.transformed.tail i =
          D.targetTransform.transformed.representationAlpha
            D.sourceTransform.transformed i.tailShift) :
    Beli2019Lemma93LowReverseCertificate (N := N + 2) a b D := by
  apply Beli2019Lemma93LowReverseCertificate.ofEqOrNotImportant D
  intro i hlow
  by_cases htwo : i.val = 2
  · right
    constructor
    · intro hcurrent
      apply htriple.1
      unfold IsCurrentEssential at hcurrent
      have hindex : currentEssentialIndex i =
          (⟨1, by omega⟩ : Fin (N + 5)) := by
        apply Fin.ext
        simp only [currentEssentialIndex]
        omega
      rwa [hindex] at hcurrent
    · intro hnext
      apply htriple.2.1
      unfold IsNextEssential at hnext
      have hindex : nextEssentialIndex i =
          (⟨2, by omega⟩ : Fin (N + 5)) := by
        apply Fin.ext
        simp only [nextEssentialIndex]
        omega
      rwa [hindex] at hnext
  · by_cases hthree : i.val = 3
    · right
      constructor
      · intro hcurrent
        apply htriple.2.1
        unfold IsCurrentEssential at hcurrent
        have hindex : currentEssentialIndex i =
            (⟨2, by omega⟩ : Fin (N + 5)) := by
          apply Fin.ext
          simp only [currentEssentialIndex]
          omega
        rwa [hindex] at hcurrent
      · intro hnext
        apply htriple.2.2
        unfold IsNextEssential at hnext
        have hindex : nextEssentialIndex i =
            (⟨3, by omega⟩ : Fin (N + 5)) := by
          apply Fin.ext
          simp only [nextEssentialIndex]
          omega
        rwa [hindex] at hnext
    · exact Or.inl (heqOutside i hlow htwo hthree)

/-- The shifted version: nonessentiality of paper indices `3,4,5` removes
the only possible obligations at `A₄,A₅`. -/
theorem Beli2019Lemma93LowReverseCertificate.ofSecondNonessentialTriple
    {a : GoodBONG q L (N + 7)} {b : GoodBONG r M (N + 7)}
    (D : Beli2019Lemma93NormalizedPair (N := N + 3) a b)
    (htriple :
      (¬D.targetTransform.transformed.tail.IsEssentialFor
          D.sourceTransform.transformed.tail
          (⟨2, by omega⟩ : Fin (N + 6))) ∧
        (¬D.targetTransform.transformed.tail.IsEssentialFor
          D.sourceTransform.transformed.tail
          (⟨3, by omega⟩ : Fin (N + 6))) ∧
        (¬D.targetTransform.transformed.tail.IsEssentialFor
          D.sourceTransform.transformed.tail
          (⟨4, by omega⟩ : Fin (N + 6))))
    (heqOutside : ∀ i : RepresentationIndex (N + 6) (N + 6),
      i.val ≤ 4 → i.val ≠ 3 → i.val ≠ 4 →
        D.targetTransform.transformed.tail.representationAlpha
            D.sourceTransform.transformed.tail i =
          D.targetTransform.transformed.representationAlpha
            D.sourceTransform.transformed i.tailShift) :
    Beli2019Lemma93LowReverseCertificate (N := N + 3) a b D := by
  apply Beli2019Lemma93LowReverseCertificate.ofEqOrNotImportant D
  intro i hlow
  by_cases hthree : i.val = 3
  · right
    constructor
    · intro hcurrent
      apply htriple.1
      unfold IsCurrentEssential at hcurrent
      have hindex : currentEssentialIndex i =
          (⟨2, by omega⟩ : Fin (N + 6)) := by
        apply Fin.ext
        simp only [currentEssentialIndex]
        omega
      rwa [hindex] at hcurrent
    · intro hnext
      apply htriple.2.1
      unfold IsNextEssential at hnext
      have hindex : nextEssentialIndex i =
          (⟨3, by omega⟩ : Fin (N + 6)) := by
        apply Fin.ext
        simp only [nextEssentialIndex]
        omega
      rwa [hindex] at hnext
  · by_cases hfour : i.val = 4
    · right
      constructor
      · intro hcurrent
        apply htriple.2.1
        unfold IsCurrentEssential at hcurrent
        have hindex : currentEssentialIndex i =
            (⟨3, by omega⟩ : Fin (N + 6)) := by
          apply Fin.ext
          simp only [currentEssentialIndex]
          omega
        rwa [hindex] at hcurrent
      · intro hnext
        apply htriple.2.2
        unfold IsNextEssential at hnext
        have hindex : nextEssentialIndex i =
            (⟨4, by omega⟩ : Fin (N + 6)) := by
          apply Fin.ext
          simp only [nextEssentialIndex]
          omega
        rwa [hindex] at hnext
    · exact Or.inl (heqOutside i hlow hthree hfour)

/-- End-to-end certificate for the first exceptional-candidate branch in
Case 2.  The arithmetic hypotheses are precisely those of the first claim
in the v2 proof; all nonexceptional low alpha equalities are kept explicit. -/
theorem Beli2019Lemma93LowReverseCertificate.ofFirstCaseTwoBranch
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    {a : GoodBONG q L (N + 6)} {b : GoodBONG r M (N + 6)}
    (D : Beli2019Lemma93NormalizedPair (N := N + 2) a b)
    (hcross : D.sourceTransform.transformed.order
        (⟨2, by omega⟩ : Fin (N + 6)) <
      D.targetTransform.transformed.order
        (⟨4, by omega⟩ : Fin (N + 6)))
    (hthirdStrict :
      D.targetTransform.transformed.representationAlpha
          D.sourceTransform.transformed
          (lemma93ThirdRepresentationIndex (N + 2)) <
        D.targetTransform.transformed.representationPrimaryDefect
          D.sourceTransform.transformed
          (lemma93ThirdRepresentationIndex (N + 2)))
    (hfourthEq :
      D.targetTransform.transformed.representationAlpha
          D.sourceTransform.transformed
          (lemma93FourthRepresentationIndex (N + 1)) =
        D.targetTransform.transformed.representationSecondaryPreviousDefect
          D.sourceTransform.transformed
          (lemma93FourthRepresentationIndex (N + 1)) (by
            simp only [lemma93FourthRepresentationIndex]
            omega))
    (heqOutside : ∀ i : RepresentationIndex (N + 5) (N + 5),
      i.val ≤ 4 → i.val ≠ 2 → i.val ≠ 3 →
        D.targetTransform.transformed.tail.representationAlpha
            D.sourceTransform.transformed.tail i =
          D.targetTransform.transformed.representationAlpha
            D.sourceTransform.transformed i.tailShift) :
    Beli2019Lemma93LowReverseCertificate (N := N + 2) a b D :=
  Beli2019Lemma93LowReverseCertificate.ofFirstNonessentialTriple D
    (tail_lowThree_not_essential_of_thirdPrimaryStrict_fourthPrevious
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      D.targetTransform.transformed D.sourceTransform.transformed
      hcross hthirdStrict hfourthEq)
    heqOutside

/-- End-to-end certificate for the shifted exceptional-candidate branch in
Case 2, corresponding to the paper's “Similarly” paragraph. -/
theorem Beli2019Lemma93LowReverseCertificate.ofSecondCaseTwoBranch
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    {a : GoodBONG q L (N + 7)} {b : GoodBONG r M (N + 7)}
    (D : Beli2019Lemma93NormalizedPair (N := N + 3) a b)
    (hcross : D.sourceTransform.transformed.order
        (⟨3, by omega⟩ : Fin (N + 7)) <
      D.targetTransform.transformed.order
        (⟨5, by omega⟩ : Fin (N + 7)))
    (hfourthStrict :
      D.targetTransform.transformed.representationAlpha
          D.sourceTransform.transformed
          (lemma93FourthRepresentationIndex (N + 2)) <
        D.targetTransform.transformed.representationPrimaryDefect
          D.sourceTransform.transformed
          (lemma93FourthRepresentationIndex (N + 2)))
    (hfifthEq :
      D.targetTransform.transformed.representationAlpha
          D.sourceTransform.transformed
          (lemma93FifthRepresentationIndex (N + 1)) =
        D.targetTransform.transformed.representationSecondaryPreviousDefect
          D.sourceTransform.transformed
          (lemma93FifthRepresentationIndex (N + 1)) (by
            simp only [lemma93FifthRepresentationIndex]
            omega))
    (heqOutside : ∀ i : RepresentationIndex (N + 6) (N + 6),
      i.val ≤ 4 → i.val ≠ 3 → i.val ≠ 4 →
        D.targetTransform.transformed.tail.representationAlpha
            D.sourceTransform.transformed.tail i =
          D.targetTransform.transformed.representationAlpha
            D.sourceTransform.transformed i.tailShift) :
    Beli2019Lemma93LowReverseCertificate (N := N + 3) a b D :=
  Beli2019Lemma93LowReverseCertificate.ofSecondNonessentialTriple D
    (tail_nextThree_not_essential_of_fourthPrimaryStrict_fifthPrevious
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      D.targetTransform.transformed D.sourceTransform.transformed
      hcross hfourthStrict hfifthEq)
    heqOutside

end BONG.GoodBONG

end Bong
