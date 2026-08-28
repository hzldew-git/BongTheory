/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma78TargetLocal
import Bong.Bong.Beli2019Lemma78AlphasLocal
import Bong.Bong.Beli2019Lemma69TypeIIIRightValueLocal
import Bong.Bong.Beli2019Remark616

/-!
# Beli (2019), Lemma 7.8: local target-prefix propagation

This is the target-prefix part of Lemma 7.8 on an even prefix strictly
before the last unequal order.  It combines the local source-prefix theorem,
the local right representation value, and the target-alpha lower bound, so
no full-span normalization is needed.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

set_option maxHeartbeats 5000000 in
/-- Every even target prefix strictly before the last unequal order has the
central type-III defect. -/
theorem beli2019Lemma78_targetPrefixDefect_beforeLast_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (i : Nat) (hiStart : D.outer.transition.lastZero + 2 ≤ i)
    (hiLast : i < D.outer.last) (hiEven : Even i) :
    b.truncatedPrefixDefect b ((-1) ^ (i / 2)) 0 i =
      (((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : ℚ) : WithTop ℚ) := by
  have hiNonterminal : i < n + 2 :=
    hiLast.trans D.outer.lastDifference.bound
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i, by omega, hiNonterminal, hiNonterminal.le⟩
  have hright : D.outer.transition.firstTwo ≤ i := by
    rw [D.adjacent]
    exact hiStart
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hparity : Odd (i - (D.outer.transition.firstTwo - 1)) := by
    rcases hleftEven with ⟨e, he⟩
    rcases hiEven with ⟨d, hd⟩
    refine ⟨d - e - 1, ?_⟩
    rw [D.adjacent]
    omega
  have htargetCenter :=
    (a.beli2019Lemma78_alphas_and_gap_local b D hfirst horder hdefect
      htotal hnotOverlap hinitial).2.1
  have hclassification :=
    a.beli2019Lemma69_ii_typeIII_targetRightValue_of_center_local
      b D horder hdefect htotal htargetCenter i hright hparity hiLast
  have hremark := a.beli2019Remark616_rightPrefix
    b hdefect idx (by simpa only [idx] using hclassification)
      ((-1) ^ (i / 2))
  have hsource := a.beli2019Lemma78_sourcePrefixDefect_local
    b D hfirst hdefect hnotOverlap hinitial i hiStart (by omega) hiEven
  have hbeta := a.lemma78_typeIII_targetAlpha_ge_mixedShift_local
    b D hfirst hdefect hnotOverlap hinitial i hiStart (by omega)
      hiEven hiNonterminal
  rw [hremark, hsource]
  apply min_eq_left
  exact_mod_cast hbeta

end BONG.GoodBONG

end Bong
