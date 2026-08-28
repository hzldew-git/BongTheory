/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixTypeITerminalComplete
import Bong.Bong.Beli2019Lemma79EvenTypeICanonicalTerminalComplete
import Bong.Bong.Beli2019Lemma79EvenTypeILeftComplete
import Bong.Bong.Beli2019Lemma79DefectTypeIOdd
import Bong.Bong.Beli2019Lemma79TypeICentralOddTerminalComplete
import Bong.Bong.Beli2019Lemma79RightTailGapTwoComplete

/-!
# Beli (2019), Lemma 7.9(ii): pointwise type-I assembly

This file assembles cases 2, 3, 4, 6, and 8 of the published proof.  The
coordinate and parity comparisons are internal to the theorem: callers only
supply a representation index.  The hypothesis `i + 1 < rank` excludes the
single final internal boundary, whose source self-prefix needs the endpoint
form of Lemma 7.4(iii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 9000000 in
-- All profile intervals and both coordinate parities are dispatched here.
/-- Lemma 7.9(ii) at every nonfinal representation coordinate in type I. -/
theorem beli2019Lemma79_ii_typeI_pointwise_nonfinal
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hcentralAB : a.CentralRepresentationConditions b)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hcentralAC : a.CentralRepresentationConditions c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hafter : D.profile.last + 1 ≤ i.val
  · exact beli2019Lemma79_ii_typeI_caseEight
      a b c D hfirst hnorm horderAB horderBC hdefectAB hdefectAC
        htotal i hafter
  · have hthroughLast : i.val ≤ D.profile.last := by omega
    rcases Nat.even_or_odd i.val with hiEven | hiOdd
    · have hiTwo : 2 ≤ i.val := by
        rcases hiEven with ⟨d, hd⟩
        have hiPos := i.pos
        omega
      by_cases hbeforeLeft : i.val < C.leftSwitch
      · exact beli2019Lemma79_ii_typeI_even_beforeLeftSwitch_complete
          a b c D C hfirst hdefectAB hdefectAC horderBC hnorm
            i hiTwo hiNext hiEven hbeforeLeft
      · have hiLeft : C.leftSwitch ≤ i.val := by omega
        by_cases hthroughRight : i.val ≤ C.rightSwitch
        · exact beli2019Lemma79_ii_typeI_even_canonical_terminalComplete
            a b c D C hfirst horderAB hdefectAB hcentralAB horderAC
              hdefectAC hcentralAC horderBC hnorm i
                ⟨by omega, hiNext⟩ hiEven hiLeft hthroughRight
        · exact beli2019Lemma79_ii_typeI_caseSix_terminalComplete
            a b c D C hfirst hdefectAB hdefectAC horderBC hnorm
              i (by omega) hthroughLast hiEven
    · by_cases hbeforeLeft : i.val < C.leftSwitch + 1
      · have hleftPos : 0 < C.leftSwitch := by
          have hiPos := i.pos
          omega
        exact beli2019Lemma79_ii_typeI_odd_left
          a b c D C hfirst hleftPos horderAC hnorm i hiOdd hbeforeLeft
      · have hleft : C.leftSwitch ≤ i.val - 1 := by omega
        have hlastEven : Even D.profile.last := by
          rcases C.right_le_last.lt_or_eq with hrightLast | hrightLast
          · exact lemma79_typeI_last_even a b D C hfirst hrightLast
          · simpa only [← hrightLast] using C.right_even
        have hbeforeLast : i.val < D.profile.last := by
          rcases hiOdd with ⟨d, hd⟩
          rcases hlastEven with ⟨e, he⟩
          omega
        exact beli2019Lemma79_ii_typeI_caseFour_complete
          a b c D C hfirst horderAB hdefectAB hdefectAC horderBC
            hnorm i hiOdd hleft hbeforeLast

end BONG.GoodBONG

end Bong
