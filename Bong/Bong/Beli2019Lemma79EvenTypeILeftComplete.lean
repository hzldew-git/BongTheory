/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenTypeIBoundaryAssembly

/-!
# Beli (2019), Lemma 7.9(ii), case 3: complete early type-I interval

The current coordinate and the first canonical switch are both even.
Consequently a coordinate strictly before the switch is either at least
four places before it or exactly two places before it.  The interior and
boundary theorems cover these alternatives.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Lemma 7.9(ii), case 3, on every even coordinate strictly before the
first canonical type-I switch. -/
theorem beli2019Lemma79_ii_typeI_even_beforeLeftSwitch_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiNext : i.val + 1 < n + 2)
    (hiEven : Even i.val) (hbefore : i.val < C.leftSwitch) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hi : 1 < i.val ∧ i.val + 1 < n + 2 := ⟨by omega, hiNext⟩
  have hfarLe : i.val + 2 ≤ C.leftSwitch := by
    rcases hiEven with ⟨d, hd⟩
    rcases C.left_even with ⟨e, he⟩
    omega
  by_cases hfarBefore : i.val + 2 < C.leftSwitch
  · exact beli2019Lemma79_ii_typeI_even_left_interior
      a b c D C hfirst hdefectAB hdefectAC horderBC hnorm
        i hi hiEven hfarBefore
  · have hboundary : i.val + 2 = C.leftSwitch := by omega
    exact beli2019Lemma79_ii_typeI_even_leftBoundary
      a b c D C hfirst hdefectAB hdefectAC horderBC hnorm
        i hi hiEven hboundary

end BONG.GoodBONG

end Bong
