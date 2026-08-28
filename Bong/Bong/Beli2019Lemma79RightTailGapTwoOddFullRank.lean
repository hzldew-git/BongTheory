/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoIndexPrefixes
import Bong.Bong.Beli2019Lemma78TargetPropagation

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the odd full-rank prefix

For an odd representation index the numerical argument uses the even prefix
of length `i + 1`.  The existing endpoint propagation proves its target
identity below full rank.  At the final index the source propagation still
reaches the full prefix, and full-rank self-prefix invariance transfers that
identity to the target BONG.  Thus the artificial nonterminal restriction is
removed.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- At every odd current index, including the terminal one, the source prefix
of length `i + 1` has the central gap-two defect. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_sourcePrefixDefect_at_oddIndex
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 <= i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.profile.last hlast) (caseEightLastAlphaIndex i))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i))
    (hiOdd : Odd i.val) :
    a.truncatedPrefixDefect a ((-1) ^ ((i.val + 1) / 2)) 0 (i.val + 1) =
      ((((b.order (Fin.mk D.profile.last hlast).castSucc -
          b.order (Fin.mk D.profile.last hlast).succ : Int) : Rat) +
        b.alphaValue (Fin.mk D.profile.last hlast) : Rat) : WithTop Rat) := by
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_initialData
    a b D hfirst hgapTwo with ⟨I⟩
  rcases I.last_even with ⟨u, hu⟩
  rcases hiOdd with ⟨r, hr⟩
  let pairs := r - u
  have hlength : i.val + 1 = D.profile.last + 2 + 2 * pairs := by
    simp only [pairs]
    omega
  have hfirstTail : (Fin.mk D.profile.last hlast : Fin (n + 1)) <=
      caseEightLastAlphaIndex i := by
    change D.profile.last <= i.val - 1
    omega
  have hraw := beli2019Lemma79_typeI_caseEight_gapTwo_sourcePrefixDefect
    a b D hfirst hgapTwo hlast horder hdefect H hfirstTail hstrictLast
      pairs (by
        simp only [pairs, caseEightLastAlphaIndex_val]
        omega)
  rw [hlength]
  simpa only [hlength] using hraw

/-- The odd target prefix identity at every index, with the terminal case
obtained from full-rank self-prefix invariance. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_targetPrefixDefect_at_oddIndex_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 <= i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.profile.last hlast) (caseEightLastAlphaIndex i))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i))
    (hiOdd : Odd i.val) :
    b.truncatedPrefixDefect b ((-1) ^ ((i.val + 1) / 2)) 0 (i.val + 1) =
      ((((b.order (Fin.mk D.profile.last hlast).castSucc -
          b.order (Fin.mk D.profile.last hlast).succ : Int) : Rat) +
        b.alphaValue (Fin.mk D.profile.last hlast) : Rat) : WithTop Rat) := by
  by_cases hiNonterminal : i.val < n + 1
  · exact
      beli2019Lemma79_typeI_caseEight_gapTwo_targetPrefixDefect_at_oddIndex
        a b D hfirst hgapTwo hlast horder hdefect i hafter H hstrictLast
          hiOdd hiNonterminal
  · have hiTerminal : i.val = n + 1 := by
      have hi := i.lt_large
      omega
    have hsource :=
      beli2019Lemma79_typeI_caseEight_gapTwo_sourcePrefixDefect_at_oddIndex
        a b D hfirst hgapTwo hlast horder hdefect i hafter H hstrictLast
          hiOdd
    have hlength : i.val + 1 = n + 2 := by omega
    rw [hlength]
    rw [a.truncatedPrefixDefect_self_full_eq b
      ((-1) ^ ((n + 2) / 2))]
    simpa only [hlength] using hsource

end BONG.GoodBONG

end Bong
