/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailSource
import Bong.Bong.Beli2019Lemma79MixedAssembly

/-!
# Beli (2019), Lemma 7.9(ii): assembling case 8

On the unchanged right suffix, Lemma 6.3 supplies the exact alpha required
by Remark 6.16, while the preceding file discharges its source-defect
branch.  Consequently case 8 reduces exactly to the remaining target-alpha
bound proved in the long tail calculation of the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Lemma 7.9(ii), case 8, reduced to the target-alpha branch.  The source
branch is a theorem once the source and intermediate order suffixes agree. -/
theorem beli2019Lemma79_ii_caseEight_of_beta_bound
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hsuffix : ∀ k, i.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k)
    (hbeta : (b.alphaValue ⟨i.val - 1, by
          have hiPos := i.pos
          have hiLarge := i.lt_large
          omega⟩ : WithTop ℚ) ≤
        a.truncatedPrefixDefect c 1 i.val i.val →
      (b.representationAlphaValue c i : WithTop ℚ) ≤
        (b.alphaValue ⟨i.val - 1, by
          have hiPos := i.pos
          have hiLarge := i.lt_large
          omega⟩ : WithTop ℚ)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hAlpha := a.beli2019Lemma63_sameRank_right_value
    b hdefectAB i hsuffix
  apply lemma79_ii_of_rightMixedPrefix_branches
    a b c hdefectAB hdefectAC i hAlpha
  · intro _
    exact lemma79_rightTail_alpha_le_sourceAlpha
      a b c hdefectAB i hsuffix
  · exact hbeta

end BONG.GoodBONG

end Bong
