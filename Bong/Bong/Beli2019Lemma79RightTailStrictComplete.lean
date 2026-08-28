/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneAssembly
import Bong.Bong.Beli2019Lemma79RightTailBoundaryData

/-!
# Beli (2019), Lemma 7.9(ii), case 8: complete strict-tail data

The strict-tail construction previously had separate statements for the
singleton boundary `i = u` and the proper tail `i > u`.  These theorems
join the two statements for each Lemma 6.7 type.  Their endpoint is the
canonical alpha index immediately left of the representation boundary.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Complete type-I strict data at or after the last changed coordinate. -/
theorem beli2019Lemma79_typeI_caseEight_strictData_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 ≤ i.val)
    (hnotAttains : b.alphaValue (caseEightLastAlphaIndex i) ≠
      b.halfGapValue (caseEightLastAlphaIndex i))
    (hbeta : (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) <
      a.truncatedPrefixDefect c 1 i.val i.val) :
    CaseEightStrictBetaTailConsequences b
        (Fin.mk D.profile.last (by
          have hi := i.lt_large
          omega))
        (caseEightLastAlphaIndex i) ∧
      Int.ModEq 2 (b.orderSequence.prefixSum i.val)
        (c.orderSequence.prefixSum i.val) := by
  by_cases hboundary : D.profile.last + 1 = i.val
  · have hdata := beli2019Lemma79_typeI_caseEight_boundary_strictData
      a b c D hdefect htotal i hboundary
      (by simpa only [caseEightLastAlphaIndex] using hnotAttains)
      (by simpa only [caseEightLastAlphaIndex] using hbeta)
    have hlast : D.profile.last = i.val - 1 := by omega
    simpa only [caseEightLastAlphaIndex, hlast] using hdata
  · have hproper : D.profile.last + 1 < i.val := by omega
    have hdata := beli2019Lemma79_typeI_caseEight_strictData
      a b c D horder hdefect htotal i hproper
      (by simpa only [caseEightLastAlphaIndex] using hbeta)
    simpa only [caseEightLastAlphaIndex] using hdata

/-- Complete type-II strict data at or after the last changed coordinate. -/
theorem beli2019Lemma79_typeII_caseEight_strictData_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 ≤ i.val)
    (hnotAttains : b.alphaValue (caseEightLastAlphaIndex i) ≠
      b.halfGapValue (caseEightLastAlphaIndex i))
    (hbeta : (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) <
      a.truncatedPrefixDefect c 1 i.val i.val) :
    CaseEightStrictBetaTailConsequences b
        (Fin.mk D.outer.last (by
          have hi := i.lt_large
          omega))
        (caseEightLastAlphaIndex i) ∧
      Int.ModEq 2 (b.orderSequence.prefixSum i.val)
        (c.orderSequence.prefixSum i.val) := by
  by_cases hboundary : D.outer.last + 1 = i.val
  · have hdata := beli2019Lemma79_typeII_caseEight_boundary_strictData
      a b c D hdefect htotal i hboundary
      (by simpa only [caseEightLastAlphaIndex] using hnotAttains)
      (by simpa only [caseEightLastAlphaIndex] using hbeta)
    have hlast : D.outer.last = i.val - 1 := by omega
    simpa only [caseEightLastAlphaIndex, hlast] using hdata
  · have hproper : D.outer.last + 1 < i.val := by omega
    have hdata := beli2019Lemma79_typeII_caseEight_strictData
      a b c D horder hdefect htotal i hproper
      (by simpa only [caseEightLastAlphaIndex] using hbeta)
    simpa only [caseEightLastAlphaIndex] using hdata

/-- Complete type-III strict data at or after the last changed coordinate. -/
theorem beli2019Lemma79_typeIII_caseEight_strictData_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 ≤ i.val)
    (hnotAttains : b.alphaValue (caseEightLastAlphaIndex i) ≠
      b.halfGapValue (caseEightLastAlphaIndex i))
    (hbeta : (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) <
      a.truncatedPrefixDefect c 1 i.val i.val) :
    CaseEightStrictBetaTailConsequences b
        (Fin.mk D.outer.last (by
          have hi := i.lt_large
          omega))
        (caseEightLastAlphaIndex i) ∧
      Int.ModEq 2 (b.orderSequence.prefixSum i.val)
        (c.orderSequence.prefixSum i.val) := by
  by_cases hboundary : D.outer.last + 1 = i.val
  · have hdata := beli2019Lemma79_typeIII_caseEight_boundary_strictData
      a b c D hdefect htotal i hboundary
      (by simpa only [caseEightLastAlphaIndex] using hnotAttains)
      (by simpa only [caseEightLastAlphaIndex] using hbeta)
    have hlast : D.outer.last = i.val - 1 := by omega
    simpa only [caseEightLastAlphaIndex, hlast] using hdata
  · have hproper : D.outer.last + 1 < i.val := by omega
    have hdata := beli2019Lemma79_typeIII_caseEight_strictData
      a b c D horder hdefect htotal i hproper
      (by simpa only [caseEightLastAlphaIndex] using hbeta)
    simpa only [caseEightLastAlphaIndex] using hdata

end BONG.GoodBONG

end Bong
