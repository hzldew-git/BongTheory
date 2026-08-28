/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoEvenComparison

/-!
# Beli (2019), Lemma 7.9(ii), case 8: strict gap-two beta estimate

The strict source/comparison-prefix branch makes the final target beta
strictly smaller than the corresponding source alpha.  The propagated
gap-two prefix identities are then available.  At an even index sharp
multiplication first supplies the comparison self-prefix identity and the
complete even calculation applies; at an odd index the propagated target
prefix feeds the complete odd calculation.  This assembles lines
5902--5975 of the v2 paper for every nonterminal index.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 4000000 in
-- Both parity branches expand the full propagated gap-two prefix identities.
/-- The target representation alpha is bounded by the final target beta in
the strict type-I gap-two branch, away from the terminal boundary. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_strict_beta_bound
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 <= i.val)
    (hiNonterminal : i.val < n + 1)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.profile.last hlast) (caseEightLastAlphaIndex i))
    (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val))
    (hmixedStrict :
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) <
        a.truncatedPrefixDefect c 1 i.val i.val) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
  have hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i) := by
    have hstrict := caseEight_beta_lt_sourceAlpha_of_lt_sourceDefect
      a c i (b.alphaValue (caseEightLastAlphaIndex i)) hmixedStrict
    simpa only [caseEightLastAlphaIndex] using hstrict
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · have hiTwo : 2 <= i.val := by
      rcases hiEven with ⟨d, hd⟩
      omega
    have hself :=
      beli2019Lemma79_typeI_caseEight_gapTwo_even_comparisonPrefixDefect
        a b c D hfirst hgapTwo hlast horder hdefect i hafter H hstrictLast
          hiEven hmixedStrict
    exact beli2019Lemma79_typeI_caseEight_gapTwo_even_beta_bound
      a b c D hfirst hgapTwo hlast hnorm i hafter H hiEven hiTwo hself hprefix
  · have htarget :=
      beli2019Lemma79_typeI_caseEight_gapTwo_targetPrefixDefect_at_oddIndex
        a b D hfirst hgapTwo hlast horder hdefect i hafter H hstrictLast
          hiOdd hiNonterminal
    exact beli2019Lemma79_typeI_caseEight_gapTwo_odd_beta_bound
      a b c D hfirst hgapTwo hlast hnorm i hafter H hiOdd htarget hprefix

end BONG.GoodBONG

end Bong
