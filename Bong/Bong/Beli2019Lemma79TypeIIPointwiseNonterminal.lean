/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenLeftComplete
import Bong.Bong.Beli2019Lemma79DefectOddLeftOuter
import Bong.Bong.Beli2019Lemma79DefectTypeIICore
import Bong.Bong.Beli2019Lemma79CaseSixAssembly
import Bong.Bong.Beli2019Lemma79TypeIIRight

/-!
# Beli (2019), Lemma 7.9(ii): pointwise type-II assembly before the last difference

This file assembles cases 2, 3, 5, 6, and 7 of the published proof for a
normalized full-span type-II profile.  The interval and parity dispatch is
internal to the theorem; callers only supply a coordinate strictly before the
last difference.
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
-- The left profile, constant core, and two right-profile parity classes meet
-- without uncovered internal coordinates.
/-- Lemma 7.9(ii) at every coordinate before the final type-II difference. -/
theorem beli2019Lemma79_ii_typeII_pointwise_beforeLast
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbeforeLast : i.val < D.outer.last) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hleft : i.val ≤ D.outer.transition.lastZero
  · rcases Nat.even_or_odd i.val with hiEven | hiOdd
    · have hiTwo : 2 ≤ i.val := by
        rcases hiEven with ⟨d, hd⟩
        have hiPos := i.pos
        omega
      have hiNext : i.val + 1 < n + 2 := by omega
      exact beli2019Lemma79_ii_typeII_even_left
        a b c D hfirst hdefectAB hdefectAC horderBC hnorm
          i hiTwo hiNext hiEven hleft
    · exact beli2019Lemma79_ii_typeII_odd_left
        a b c D hfirst horderAC hnorm i hiOdd (by omega)
  · have hafterLeft : D.outer.transition.lastZero < i.val := by omega
    by_cases hcore : i.val + 1 < D.outer.transition.firstTwo
    · exact beli2019Lemma79_ii_typeII_core
        a b c D hfirst horderAC hdefectAC hnorm i hafterLeft hcore
    · have hright : D.outer.transition.firstTwo - 1 ≤ i.val := by omega
      rcases Nat.even_or_odd
          (i.val - (D.outer.transition.firstTwo - 1)) with hiEven | hiOdd
      · exact beli2019Lemma79_ii_typeII_caseSix
          a b c D hfirst hlast horderAB horderAC hdefectAB hdefectAC
            htotal hnorm i hright hbeforeLast hiEven
      · have hrightStrict : D.outer.transition.firstTwo ≤ i.val := by
          rcases hiOdd with ⟨d, hd⟩
          omega
        exact beli2019Lemma79_ii_typeII_caseSeven
          a b c D hfirst hlast horderAB hdefectAB hdefectAC htotal
            hnorm i hrightStrict hbeforeLast hiOdd

end BONG.GoodBONG

end Bong
