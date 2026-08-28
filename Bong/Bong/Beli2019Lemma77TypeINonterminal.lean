/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeILeft
import Bong.Bong.Beli2019Lemma69TypeIRightComplete
import Bong.Bong.Beli2019Lemma69TypeIBoundary

/-!
# Beli (2019), Lemma 7.7: the nonterminal type-I branch

When the canonical right switch precedes the last unequal order, the two
neighboring estimates in Lemma 6.9(v) are now theorems.  The boundary
rounding argument and equality of the middle `W`-block therefore give the
type-I contribution to Lemma 7.7 without any local-law premise.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Lemma 7.7 in type I when the right switch is not the last unequal
order.  The endpoint case is separated because the paper proves it through
reverse-dual transport. -/
theorem beli2019Lemma77_typeI_of_rightSwitch_lt_last
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [parity : Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (hW : BeliOrderLE a.weightSequence b.weightSequence)
    (i : Nat) (hiTwo : 2 ≤ i) (hiBound : i ≤ n + 2)
    (hiEven : Even i) (hleft : C.leftSwitch ≤ i - 2)
    (hright : i - 2 < C.rightSwitch) :
    (((((a.order ⟨i - 2, by omega⟩ -
          a.order ⟨i - 1, by omega⟩ : Int) : ℚ) + 2 : ℚ)) :
        WithTop ℚ) ≤ a.alternatingPrefixDefect i := by
  apply beli2019Lemma77_typeI_of_neighborBounds
    a b D C hfirst hW
  · intro hleftPos
    exact beli2019Lemma69_v_typeI_leftNeighbor
      a b D C hfirst hleftPos hdefect
  · intro _
    exact beli2019Lemma69_v_typeI_rightNeighbor
      a b D C hfirst hrightLast hdefect
  · exact hiTwo
  · exact hiBound
  · exact hiEven
  · exact hleft
  · exact hright

end BONG.GoodBONG

end Bong
