/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoEvenPrimaryParity

/-!
# Beli (2019), Lemma 7.9(ii), case 8: closing the nonintegral even branch

If `B_i > beta_i`, the exceptional-order lemma fixes both the boundary
alpha and the comparison order preceding the nonintegral gap.  That gap is
larger than `2e`, so the next comparison order is at least the first target
order.  Prefix parity makes the mixed primary defect zero, contradicting
the assumed failure of the beta bound.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The strict-coefficient, nonintegral even subcase of the gap-two tail
cannot violate `B_i <= beta_i`. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_even_beta_bound_of_nonintegral_failure
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 <= i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.profile.last hlast) (caseEightLastAlphaIndex i))
    (hiEven : Even i.val) (hiTwo : 2 <= i.val)
    (hfloor : b.order (Fin.mk D.profile.last hlast).castSucc =
      c.order (0 : Fin (n + 2)) + 1)
    (hfailure : b.alphaValue (caseEightLastAlphaIndex i) <
      b.representationAlphaValue c i)
    (hnot : ¬ IsRationalInteger
      (c.alphaValue (evenTargetPreviousAlphaIndex i))) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
  let first : Fin (n + 1) := Fin.mk D.profile.last hlast
  let p : Fin (n + 1) := evenTargetPreviousAlphaIndex i
  have hfirstLast : first <= caseEightLastAlphaIndex i := by
    change D.profile.last <= i.val - 1
    omega
  rcases caseEight_gapTwo_even_nonintegral_failure_orders
      b c i first hfirstLast H hiEven hiTwo (by
        simpa only [first] using hfloor) hfailure hnot with
    ⟨_, hboundary, hprevious⟩
  have halphaLarge : 2 * (ramificationIndex K : Rat) <
      c.alphaValue p := by
    rcases c.beli2009Corollary28_iii p with hsmall | hlarge
    · exact False.elim (hnot (by simpa only [p] using hsmall.2.2))
    · exact hlarge.1
  have hgapLarge : 2 * (ramificationIndex K : Int) <
      c.orderGap p :=
    ((c.beli2009Corollary28_ii p).2.2).mp halphaLarge
  have hePos := ramificationIndex_pos (K := K)
  have hcomparison : b.order first.castSucc <=
      c.order (evenTargetPreviousIndex i) := by
    have hpSucc : p.succ = evenTargetPreviousIndex i := by
      apply Fin.ext
      simp only [p, evenTargetPreviousAlphaIndex,
        evenTargetPreviousIndex, Fin.succ_mk]
      omega
    change 2 * (ramificationIndex K : Int) <
      c.order p.succ - c.order p.castSucc at hgapLarge
    rw [hpSucc] at hgapLarge
    have hfloor' : b.order first.castSucc =
        c.order (0 : Fin (n + 2)) + 1 := by
      simpa only [first] using hfloor
    have hprevious' : c.order p.castSucc =
        c.order (0 : Fin (n + 2)) := by
      simpa only [p] using hprevious
    rw [hprevious'] at hgapLarge
    omega
  have hodd :=
    beli2019Lemma79_typeI_caseEight_gapTwo_even_primaryProduct_odd
      a b c D hfirst hgapTwo hlast i hafter H hiEven hiTwo hfloor
        (by simpa only [first] using hboundary)
        (by simpa only [p] using hprevious)
  exact caseEight_gapTwo_even_beta_bound_of_primaryProduct_odd
    b c i first hfirstLast H (by simpa only [first] using hboundary)
      hcomparison hodd

end BONG.GoodBONG

end Bong
