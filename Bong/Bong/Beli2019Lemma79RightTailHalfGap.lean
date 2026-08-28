/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailAssembly
import Bong.Bong.Beli2019RepresentationSourceHalfGap

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the half-gap branch

Section 2.6 bounds the new representation alpha by the intermediate
BONG's self half-gap.  Therefore case 8 is complete whenever its final
beta attains that half-gap.  This includes the boundary subcase `i = u`
at the start of the long strict-tail argument in the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Lemma 7.9(ii), case 8, when the final intermediate alpha attains its
self half-gap. -/
theorem beli2019Lemma79_ii_caseEight_of_finalBeta_attainsHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hsuffix : forall k, i.val <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k)
    (hattains : b.alphaValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)) =
      b.halfGapValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega))) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      b.truncatedPrefixDefect c 1 i.val i.val := by
  apply beli2019Lemma79_ii_caseEight_of_beta_bound
    a b c hdefectAB hdefectAC i hsuffix
  intro _
  exact_mod_cast
    b.representationAlphaValue_le_sourceAlpha_of_attainsHalfGap
      c horderBC i hattains

end BONG.GoodBONG

end Bong
