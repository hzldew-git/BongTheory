/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailSingleton
import Bong.Bong.Beli2019Lemma79RightTailStrictData

/-!
# Beli (2019), Lemma 7.9(ii), case 8: boundary strict data

This file covers the boundary `i = u`, where the last intermediate alpha
is exactly the alpha at the final changed coordinate.  If it does not attain
its half-gap, the singleton profile supplies all strict beta facts.  The
same strict mixed-defect argument as on a longer tail supplies the parity
of the intermediate and comparison prefixes.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Generic strict data at a singleton case-8 boundary. -/
theorem caseEight_boundary_strictData
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hsuffix : forall k, i.val <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k)
    (hab : Int.ModEq 2 (a.orderSequence.prefixSum i.val)
      (b.orderSequence.prefixSum i.val))
    (hnotAttains : b.alphaValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)) ≠
      b.halfGapValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)))
    (hbeta : (b.alphaValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)) : WithTop Rat) <
      a.truncatedPrefixDefect c 1 i.val i.val) :
    CaseEightStrictBetaTailConsequences b
        (Fin.mk (i.val - 1) (by
          have hi := i.lt_large
          omega))
        (Fin.mk (i.val - 1) (by
          have hi := i.lt_large
          omega)) /\
      Int.ModEq 2 (b.orderSequence.prefixSum i.val)
        (c.orderSequence.prefixSum i.val) := by
  let last : Fin (n + 1) := Fin.mk (i.val - 1) (by
    have hi := i.lt_large
    omega)
  have hstrictHalf : b.alphaValue last < b.halfGapValue last := by
    apply lt_of_le_of_ne (b.alphaValue_le_halfGapValue last)
    simpa only [last] using hnotAttains
  have H := caseEight_strictBetaSingletonConsequences
    b last hstrictHalf
  have hcomparison :=
    caseEight_prefixSum_modEq_comparison_of_beta_lt_source
      a b c hdefect i hsuffix hab hbeta
  exact ⟨by simpa only [last] using H, hcomparison⟩

/-- Type-I boundary strict data. -/
theorem beli2019Lemma79_typeI_caseEight_boundary_strictData
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hboundary : D.profile.last + 1 = i.val)
    (hnotAttains : b.alphaValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)) ≠
      b.halfGapValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)))
    (hbeta : (b.alphaValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)) : WithTop Rat) <
      a.truncatedPrefixDefect c 1 i.val i.val) :
    CaseEightStrictBetaTailConsequences b
        (Fin.mk (i.val - 1) (by
          have hi := i.lt_large
          omega))
        (Fin.mk (i.val - 1) (by
          have hi := i.lt_large
          omega)) /\
      Int.ModEq 2 (b.orderSequence.prefixSum i.val)
        (c.orderSequence.prefixSum i.val) := by
  have hsuffix := beli2019Lemma79_typeI_caseEight_suffix
    a b D i (by omega)
  have hab := beli2019Lemma79_typeI_caseEight_prefix_modEq
    a b D htotal i (by omega)
  exact caseEight_boundary_strictData
    a b c hdefect i hsuffix hab hnotAttains hbeta

/-- Type-II boundary strict data. -/
theorem beli2019Lemma79_typeII_caseEight_boundary_strictData
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hboundary : D.outer.last + 1 = i.val)
    (hnotAttains : b.alphaValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)) ≠
      b.halfGapValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)))
    (hbeta : (b.alphaValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)) : WithTop Rat) <
      a.truncatedPrefixDefect c 1 i.val i.val) :
    CaseEightStrictBetaTailConsequences b
        (Fin.mk (i.val - 1) (by
          have hi := i.lt_large
          omega))
        (Fin.mk (i.val - 1) (by
          have hi := i.lt_large
          omega)) /\
      Int.ModEq 2 (b.orderSequence.prefixSum i.val)
        (c.orderSequence.prefixSum i.val) := by
  have hsuffix := beli2019Lemma79_typeII_caseEight_suffix
    a b D i (by omega)
  have hab := beli2019Lemma79_typeII_caseEight_prefix_modEq
    a b D htotal i (by omega)
  exact caseEight_boundary_strictData
    a b c hdefect i hsuffix hab hnotAttains hbeta

/-- Type-III boundary strict data. -/
theorem beli2019Lemma79_typeIII_caseEight_boundary_strictData
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hboundary : D.outer.last + 1 = i.val)
    (hnotAttains : b.alphaValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)) ≠
      b.halfGapValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)))
    (hbeta : (b.alphaValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)) : WithTop Rat) <
      a.truncatedPrefixDefect c 1 i.val i.val) :
    CaseEightStrictBetaTailConsequences b
        (Fin.mk (i.val - 1) (by
          have hi := i.lt_large
          omega))
        (Fin.mk (i.val - 1) (by
          have hi := i.lt_large
          omega)) /\
      Int.ModEq 2 (b.orderSequence.prefixSum i.val)
        (c.orderSequence.prefixSum i.val) := by
  have hsuffix := beli2019Lemma79_typeIII_caseEight_suffix
    a b D i (by omega)
  have hab := beli2019Lemma79_typeIII_caseEight_prefix_modEq
    a b D htotal i (by omega)
  exact caseEight_boundary_strictData
    a b c hdefect i hsuffix hab hnotAttains hbeta

end BONG.GoodBONG

end Bong
