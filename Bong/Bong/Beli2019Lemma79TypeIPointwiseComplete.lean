/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIPointwiseNonfinal
import Bong.Bong.Beli2019Lemma79EvenTypeICanonicalEndpointComplete

/-!
# Beli (2019), Lemma 7.9(ii): complete pointwise type-I assembly

The earlier dispatcher covers every coordinate having a successor order.  At
the only remaining coordinate, either the common suffix has already begun
(case 8), or the coordinate is the final unequal order.  In the latter branch
the profile forces even parity, leaving exactly the endpoint-complete canonical
and case-6 theorems.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 10000000 in
-- The final-coordinate branch reconstructs its profile position and parity
-- before invoking the endpoint-complete local theorems.
/-- Lemma 7.9(ii) at every representation coordinate in type I. -/
theorem beli2019Lemma79_ii_typeI_pointwise_complete
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
    (i : RepresentationIndex (n + 2) (n + 2)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hiNext : i.val + 1 < n + 2
  · exact beli2019Lemma79_ii_typeI_pointwise_nonfinal
      a b c D C hfirst horderAB hdefectAB hcentralAB horderAC hdefectAC
        hcentralAC horderBC hnorm htotal i hiNext
  · have hiFinal : i.val + 1 = n + 2 := by
      have hiBound : i.val < n + 2 := i.lt_large
      omega
    by_cases hafter : D.profile.last + 1 ≤ i.val
    · exact beli2019Lemma79_ii_typeI_caseEight
        a b c D hfirst hnorm horderAB horderBC hdefectAB hdefectAC
          htotal i hafter
    · have hthroughLast : i.val ≤ D.profile.last := by omega
      have hlastBound := D.profile.lastDifference.bound
      have hlastEq : i.val = D.profile.last := by omega
      have hlastEven : Even D.profile.last := by
        rcases C.right_le_last.lt_or_eq with hrightLast | hrightLast
        · exact lemma79_typeI_last_even a b D C hfirst hrightLast
        · simpa only [← hrightLast] using C.right_even
      have hiEven : Even i.val := by
        simpa only [hlastEq] using hlastEven
      have hiLeft : C.leftSwitch ≤ i.val := by
        have hleftLast := C.left_le_anchor.trans D.profile.anchor_le_last
        omega
      by_cases hthroughRight : i.val ≤ C.rightSwitch
      · exact beli2019Lemma79_ii_typeI_even_canonical_endpointComplete
          a b c D C hfirst horderAB hdefectAB hcentralAB horderAC
            hdefectAC hcentralAC horderBC hnorm i hiEven hiLeft hthroughRight
      · exact beli2019Lemma79_ii_typeI_caseSix_terminalComplete
          a b c D C hfirst hdefectAB hdefectAC horderBC hnorm
            i (by omega) hthroughLast hiEven

end BONG.GoodBONG

end Bong
