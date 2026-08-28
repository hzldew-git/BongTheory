/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRight
import Bong.Bong.Beli2019Lemma69TypeIRightNeighbor

/-!
# Beli (2019), Lemma 6.9: the complete type-I right tail

The concrete maximal-pivot estimate propagates to every odd alpha on the
right tail.  In particular it supplies the neighboring weight-coordinate
comparison required in part (v).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The target alpha is at most one at every odd index on the type-I right
tail. -/
theorem beli2019Lemma69_i_typeI_targetRightTail
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (k : Nat) (hright : C.rightSwitch < k)
    (hlast : k < D.profile.last) (hodd : Odd k) :
    b.alphaValue ⟨k, by
      have hlastBound := D.profile.lastDifference.bound
      omega⟩ ≤ 1 := by
  rcases lemma69_i_typeI_rightPivotData
    a b D C hfirst hrightLast with ⟨P⟩
  apply lemma69_i_typeI_rightTailAlpha_le_of_pivot
    a b D C hfirst hrightLast P
  · exact beli2019Lemma69_i_typeI_rightPivotAlpha
      a b D C hfirst P hdefect
  · exact hright
  · exact hlast
  · exact hodd

/-- In particular, the first target alpha after the canonical right switch
is at most one. -/
theorem beli2019Lemma69_i_typeI_nextTargetAlpha
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b) :
    b.alphaValue ⟨C.rightSwitch + 1, by
      rcases lemma69_i_typeI_rightPivotData
        a b D C hfirst hrightLast with ⟨P⟩
      have hnextPivot := P.next_le_pivot
      have hpivotLast := P.pivot_le_last_previous
      have hlastBound := D.profile.lastDifference.bound
      omega⟩ ≤ 1 := by
  apply beli2019Lemma69_i_typeI_targetRightTail
    a b D C hfirst hrightLast hdefect (C.rightSwitch + 1)
  · omega
  · rcases lemma69_i_typeI_rightPivotData
      a b D C hfirst hrightLast with ⟨P⟩
    have hnextPivot := P.next_le_pivot
    have hpivotLast := P.pivot_le_last_previous
    omega
  · rcases C.right_even with ⟨d, hd⟩
    exact ⟨d, by omega⟩

/-- The right neighboring-coordinate comparison in Lemma 6.9(v), with the
right-tail alpha input fully discharged. -/
theorem beli2019Lemma69_v_typeI_rightNeighbor
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [parity : Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b) :
    b.weightSequence.entryOrZero (2 * C.rightSwitch) ≤
      a.weightSequence.entryOrZero (2 * C.rightSwitch) + 1 / 2 := by
  apply lemma69_v_typeI_rightNeighbor_of_nextAlpha_le_one
    a b D C hfirst hrightLast
  exact beli2019Lemma69_i_typeI_nextTargetAlpha
    a b D C hfirst hrightLast hdefect

end BONG.GoodBONG

end Bong
