/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Remark616MixedPrefix

/-!
# Beli (2019), Lemma 7.9(ii): mixed-prefix assembly

This file isolates the two branches created by Remark 6.16.  It is the
profile-neutral assembly used in the type-I middle case.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Assemble a condition-2.1(ii) bound from the two alternatives in Remark
6.16.  In the source-defect branch one compares the new invariant with the
old one; in the target-alpha branch one compares it directly with `beta`. -/
theorem lemma79_ii_of_rightMixedPrefix_branches
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hAlpha : a.representationAlphaValue b i =
      b.alphaValue ⟨i.val - 1, by
        have := i.pos
        have := i.lt_large
        omega⟩)
    (hsource : a.truncatedPrefixDefect c 1 i.val i.val ≤
        (b.alphaValue ⟨i.val - 1, by
          have := i.pos
          have := i.lt_large
          omega⟩ : WithTop ℚ) →
      (b.representationAlphaValue c i : WithTop ℚ) ≤
        (a.representationAlphaValue c i : WithTop ℚ))
    (hbeta : (b.alphaValue ⟨i.val - 1, by
          have := i.pos
          have := i.lt_large
          omega⟩ : WithTop ℚ) ≤
        a.truncatedPrefixDefect c 1 i.val i.val →
      (b.representationAlphaValue c i : WithTop ℚ) ≤
        (b.alphaValue ⟨i.val - 1, by
          have := i.pos
          have := i.lt_large
          omega⟩ : WithTop ℚ)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have htransfer := a.beli2019Remark616_rightMixedPrefix
    b c hdefectAB i hAlpha 1
  rw [htransfer]
  by_cases hsourceLe : a.truncatedPrefixDefect c 1 i.val i.val ≤
      (b.alphaValue ⟨i.val - 1, by
        have := i.pos
        have := i.lt_large
        omega⟩ : WithTop ℚ)
  · rw [min_eq_left hsourceLe]
    exact (hsource hsourceLe).trans (hdefectAC i)
  · have hbetaLe : (b.alphaValue ⟨i.val - 1, by
        have := i.pos
        have := i.lt_large
        omega⟩ : WithTop ℚ) ≤
        a.truncatedPrefixDefect c 1 i.val i.val :=
      le_of_not_ge hsourceLe
    rw [min_eq_right hbetaLe]
    exact hbeta hbetaLe

end BONG.GoodBONG

end Bong
