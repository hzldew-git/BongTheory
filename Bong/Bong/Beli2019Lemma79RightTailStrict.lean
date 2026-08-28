/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailAssembly
import Bong.Bong.Beli2019Lemma79RightTailParity

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the strict beta branch

The mixed-prefix minimum only needs a new beta estimate when the source
defect is strictly larger than beta.  In that branch Remark 6.16 identifies
the intermediate comparison defect with beta, so the strict-defect parity
argument applies.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The generic case-8 assembly only needs the target-alpha estimate in
the strict beta/source branch. -/
theorem beli2019Lemma79_ii_caseEight_of_strict_beta_bound
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hsuffix : forall k, i.val <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k)
    (hbeta : (b.alphaValue (Fin.mk (i.val - 1) (by
          have hiLarge := i.lt_large
          omega)) :
          WithTop Rat) < a.truncatedPrefixDefect c 1 i.val i.val ->
      (b.representationAlphaValue c i : WithTop Rat) <=
        (b.alphaValue (Fin.mk (i.val - 1) (by
          have hiLarge := i.lt_large
          omega)) : WithTop Rat)) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      b.truncatedPrefixDefect c 1 i.val i.val := by
  apply beli2019Lemma79_ii_caseEight_of_beta_bound
    a b c hdefectAB hdefectAC i hsuffix
  intro hbetaLe
  by_cases hsourceLe : a.truncatedPrefixDefect c 1 i.val i.val <=
      (b.alphaValue (Fin.mk (i.val - 1) (by
        have hiLarge := i.lt_large
        omega)) : WithTop Rat)
  · calc
      (b.representationAlphaValue c i : WithTop Rat) <=
          (a.representationAlphaValue c i : WithTop Rat) :=
        lemma79_rightTail_alpha_le_sourceAlpha
          a b c hdefectAB i hsuffix
      _ <= a.truncatedPrefixDefect c 1 i.val i.val := hdefectAC i
      _ <= (b.alphaValue (Fin.mk (i.val - 1) (by
          have hiLarge := i.lt_large
          omega)) :
          WithTop Rat) := hsourceLe
  · exact hbeta (lt_of_not_ge hsourceLe)

/-- In the strict beta/source branch, the intermediate and third prefix
sums have the same parity. -/
theorem caseEight_prefixSum_modEq_comparison_of_beta_lt_source
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hdefectAB : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hsuffix : forall k, i.val <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k)
    (hab : Int.ModEq 2 (a.orderSequence.prefixSum i.val)
      (b.orderSequence.prefixSum i.val))
    (hbeta : (b.alphaValue (Fin.mk (i.val - 1) (by
        have hiLarge := i.lt_large
        omega)) :
        WithTop Rat) < a.truncatedPrefixDefect c 1 i.val i.val) :
    Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val) := by
  have hAlpha := a.beli2019Lemma63_sameRank_right_value
    b hdefectAB i hsuffix
  have hformula := beli2019Remark616_rightMixedPrefix_at
    a b c hdefectAB i hAlpha 1 i.val
  have hstrict : b.truncatedPrefixDefect c 1 i.val i.val <
      a.truncatedPrefixDefect c 1 i.val i.val := by
    rw [hformula, min_eq_right hbeta.le]
    exact hbeta
  exact caseEight_prefixSum_modEq_comparison_of_strict_defect
    a b c i hab hstrict

end BONG.GoodBONG

end Bong
