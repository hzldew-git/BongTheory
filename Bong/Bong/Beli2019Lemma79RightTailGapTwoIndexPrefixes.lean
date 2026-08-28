/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoTargetPropagation
import Bong.Bong.Beli2019Lemma79RightTailGapTwoTargetEndpoint
import Bong.Bong.Beli2019Lemma79RightTailGapOneAssembly

/-!
# Beli (2019), Lemma 7.9(ii), case 8: prefixes at the current index

The preceding propagation results are parametrized by the number of pairs
after the gap-two boundary.  This file rewrites them at the paper's current
representation index `i`.  When `i` is even, both source and target prefixes
of length `i` have the central defect.  When `i` is odd, the target prefix of
length `i + 1` has that defect.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- In the even-index branch, the source prefix of length `i` has the
central gap-two defect. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_sourcePrefixDefect_at_evenIndex
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
    (hiEven : Even i.val) :
    a.truncatedPrefixDefect a ((-1) ^ (i.val / 2)) 0 i.val =
      ((((b.order (Fin.mk D.profile.last hlast).castSucc -
          b.order (Fin.mk D.profile.last hlast).succ : Int) : Rat) +
        b.alphaValue (Fin.mk D.profile.last hlast) : Rat) : WithTop Rat) := by
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_initialData
    a b D hfirst hgapTwo with ⟨I⟩
  rcases I.last_even with ⟨u, hu⟩
  rcases hiEven with ⟨r, hr⟩
  let pairs := r - u - 1
  have hlength : i.val = D.profile.last + 2 + 2 * pairs := by
    simp only [pairs]
    omega
  have hfirstTail : (Fin.mk D.profile.last hlast : Fin (n + 1)) <=
      caseEightLastAlphaIndex i := by
    change D.profile.last <= i.val - 1
    omega
  have hraw := beli2019Lemma79_typeI_caseEight_gapTwo_sourcePrefixDefect
    a b D hfirst hgapTwo hlast horder hdefect H hfirstTail hstrictLast
      pairs (by
        change D.profile.last + 2 * pairs <= i.val - 1
        omega)
  rw [hlength]
  simpa only [hlength] using hraw

/-- In the even-index branch, the target prefix of length `i` has the same
central gap-two defect. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_targetPrefixDefect_at_evenIndex
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
    (hiEven : Even i.val) :
    b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val =
      ((((b.order (Fin.mk D.profile.last hlast).castSucc -
          b.order (Fin.mk D.profile.last hlast).succ : Int) : Rat) +
        b.alphaValue (Fin.mk D.profile.last hlast) : Rat) : WithTop Rat) := by
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_initialData
    a b D hfirst hgapTwo with ⟨I⟩
  rcases I.last_even with ⟨u, hu⟩
  rcases hiEven with ⟨r, hr⟩
  let pairs := r - u - 1
  have hlength : i.val = D.profile.last + 2 + 2 * pairs := by
    simp only [pairs]
    omega
  have hfirstTail : (Fin.mk D.profile.last hlast : Fin (n + 1)) <=
      caseEightLastAlphaIndex i := by
    change D.profile.last <= i.val - 1
    omega
  have hraw := beli2019Lemma79_typeI_caseEight_gapTwo_targetPrefixDefect
    a b D hfirst hgapTwo hlast horder hdefect H hfirstTail hstrictLast
      pairs (by
        change D.profile.last + 1 + 2 * pairs <= i.val - 1
        omega) (by
          rw [<- hlength]
          exact i.lt_large)
  rw [hlength]
  simpa only [hlength] using hraw

/-- In the odd-index branch, the target prefix of length `i + 1` has the
central gap-two defect.  The explicit nonterminal hypothesis is exactly the
condition needed for the alpha boundary at `i`. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_targetPrefixDefect_at_oddIndex
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
    (hiOdd : Odd i.val) (hiNonterminal : i.val < n + 1) :
    b.truncatedPrefixDefect b ((-1) ^ ((i.val + 1) / 2)) 0 (i.val + 1) =
      ((((b.order (Fin.mk D.profile.last hlast).castSucc -
          b.order (Fin.mk D.profile.last hlast).succ : Int) : Rat) +
        b.alphaValue (Fin.mk D.profile.last hlast) : Rat) : WithTop Rat) := by
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_initialData
    a b D hfirst hgapTwo with ⟨I⟩
  have hfirstTail : (Fin.mk D.profile.last hlast : Fin (n + 1)) <=
      caseEightLastAlphaIndex i := by
    change D.profile.last <= i.val - 1
    omega
  have hparity : Even
      ((caseEightLastAlphaIndex i).val - D.profile.last) := by
    rcases I.last_even with ⟨u, hu⟩
    rcases hiOdd with ⟨r, hr⟩
    refine ⟨r - u, ?_⟩
    simp only [caseEightLastAlphaIndex_val]
    omega
  have hraw :=
    beli2019Lemma79_typeI_caseEight_gapTwo_targetPrefixDefect_endpoint
      a b D hfirst hgapTwo hlast horder hdefect H hfirstTail hstrictLast
        (by
          simp only [caseEightLastAlphaIndex_val]
          omega) hparity
  have hlength : (caseEightLastAlphaIndex i).val + 2 = i.val + 1 := by
    simp only [caseEightLastAlphaIndex_val]
    omega
  rw [hlength] at hraw
  exact hraw

end BONG.GoodBONG

end Bong
