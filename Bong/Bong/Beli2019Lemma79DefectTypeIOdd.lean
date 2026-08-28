/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79DefectTypeIOddBoundary

/-!
# Beli (2019), Lemma 7.9(ii): odd coordinates in type I

The early and canonical-boundary arguments exhaust the odd paper indices
`1 ≤ i < t`.  In zero-based canonical coordinates, the final possibility
is exactly `i = leftSwitch - 1` because `leftSwitch` is even.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Lemma 7.9(ii), case 2, for every odd coordinate before the first
type-I switch in the paper's indexing. -/
theorem beli2019Lemma79_ii_typeI_odd_left
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeI a b)
    (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val) (hbefore : i.val < C.leftSwitch + 1) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hearly : i.val + 1 < C.leftSwitch
  · exact a.beli2019Lemma79_ii_typeI_odd_early b c D C hfirst
      hleftPos hac hnorm i hodd hearly
  · have hboundary : i.val + 1 = C.leftSwitch := by
      rcases hodd with ⟨d, hd⟩
      rcases C.left_even with ⟨e, he⟩
      omega
    exact a.beli2019Lemma79_ii_typeI_odd_boundary b c D C hfirst
      hleftPos hac hnorm i hboundary

end BONG.GoodBONG

end Bong
