/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenTypeICentralAssembly
import Bong.Bong.Beli2019Lemma79EvenTypeILeftSwitch
import Bong.Bong.Beli2019Lemma79EvenTypeIRightSwitch

/-!
# Beli (2019), Lemma 7.9(ii), case 3: complete even type-I interval

The first switch, strict central interval, and right switch are now covered
by separate proofs.  Parity shows that every non-right even coordinate is
at least two places before the right switch, so these three pieces exhaust
the canonical interval, including coincident switches.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 5000000 in
-- The split transports dependent indices through all three local theorems.
/-- Lemma 7.9(ii), case 3, at every even coordinate of the canonical
type-I interval. -/
theorem beli2019Lemma79_ii_typeI_even_canonical
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hiLeft : C.leftSwitch ≤ i.val)
    (hiRight : i.val ≤ C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hrightEq : i.val = C.rightSwitch
  · exact beli2019Lemma79_ii_typeI_even_rightSwitch
      a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
        hnorm i hi hiEven hrightEq hcross
  · have hfarRight : i.val + 2 ≤ C.rightSwitch := by
      rcases hiEven with ⟨d, hd⟩
      rcases C.right_even with ⟨e, he⟩
      omega
    by_cases hleftEq : i.val = C.leftSwitch
    · exact beli2019Lemma79_ii_typeI_even_leftSwitch
        a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
          hnorm i hi hiEven hleftEq hfarRight hcross
    · have hiLeftStrict : C.leftSwitch < i.val := by omega
      exact beli2019Lemma79_ii_typeI_even_central
        a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
          horderBC hnorm i hi hiEven hiLeftStrict hfarRight

end BONG.GoodBONG

end Bong
