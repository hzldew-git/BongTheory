/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenCrossGap
import Bong.Bong.Beli2019Lemma69TypeIBetaPrevious
import Bong.Bong.Beli2019Lemma79RightTailGapTwoPreviousAlpha

/-!
# Beli (2019), Lemma 7.9(ii), case 8: strict target prefix

This proves the claim in lines 5879--5892.  If the preceding target gap is
at most `2e`, the preceding-alpha identity supplies the strict bound.  The
only remaining possibility is the odd gap `2e + 1`, where Lemma 2.7 makes
the preceding alpha strictly larger than `2e`.  The strict form of Lemma
7.6 then lifts either scalar comparison to the whole alternating prefix.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- For `u > 1`, the alternating target prefix is strictly larger than
`S_u - S_(u+1) + beta_u`. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_targetPrefix_gt_central
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (hlastPos : 0 < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    {tailLast : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.profile.last, hlast⟩ tailLast)
    (hfirstTail : (⟨D.profile.last, hlast⟩ : Fin (n + 1)) ≤ tailLast)
    (hstrictTail : b.alphaValue tailLast < a.alphaValue tailLast) :
    ((((b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).castSucc -
          b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).succ : Int) : Rat) +
        b.alphaValue ⟨D.profile.last, hlast⟩ : Rat) : WithTop Rat) <
      b.truncatedPrefixDefect b ((-1) ^ (D.profile.last / 2))
        0 D.profile.last := by
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_initialData
    a b D hfirst hgapTwo with ⟨I⟩
  let C := I.canonical
  let first : Fin (n + 1) := ⟨D.profile.last, hlast⟩
  let previous : Fin (n + 1) := ⟨D.profile.last - 1, by omega⟩
  let x : Rat :=
    ((b.order first.castSucc - b.order first.succ : Int) : Rat) +
      b.alphaValue first
  have hxTwoE : x < 2 * (ramificationIndex K : Rat) := by
    simpa only [x, first] using H.centralCoefficient_lt_twoE hfirstTail
  have hlastTwo : 2 ≤ D.profile.last := by
    rcases I.last_even with ⟨d, hd⟩
    omega
  have hxPrevious : x < b.alphaValue previous := by
    by_cases hcoincident : C.leftSwitch = D.profile.last
    · have hleftPos : 0 < C.leftSwitch := by omega
      have hupperRaw := lemma79_typeI_leftSwitch_gap_le_twoE_add_one
        a b D C hleftPos
      have hupper : b.orderGap previous ≤
          2 * (ramificationIndex K : Int) + 1 := by
        simpa only [previous, hcoincident] using hupperRaw
      have hoddRaw := lemma76_leftSwitch_gap_odd
        a b D C hfirst hleftPos
      have hodd : Odd (b.orderGap previous) := by
        simpa only [previous, hcoincident] using hoddRaw
      by_cases hgapLe : b.orderGap previous ≤
          2 * (ramificationIndex K : Int)
      · simpa only [x, first, previous] using
          beli2019Lemma79_typeI_caseEight_centralCoefficient_lt_previousAlpha
            a b D hfirst hgapTwo hlast hlastPos horder hdefect H
              hfirstTail hstrictTail hgapLe
      · have hgapGt : 2 * (ramificationIndex K : Int) <
            b.orderGap previous := lt_of_not_ge hgapLe
        have hgapEq : b.orderGap previous =
            2 * (ramificationIndex K : Int) + 1 := by omega
        have hbeta := b.beli2009Lemma27_ii previous hgapGt.le
        unfold halfGapValue at hbeta
        rw [hgapEq] at hbeta
        push_cast at hbeta
        rw [hbeta]
        linarith
    · have hleftLe : C.leftSwitch ≤ D.profile.last :=
        C.left_le_anchor.trans C.anchor_le_right |>.trans
          I.rightSwitch_eq_last.le
      have hleftLt : C.leftSwitch < D.profile.last :=
        lt_of_le_of_ne hleftLe hcoincident
      have hleftPrevious : C.leftSwitch ≤ D.profile.last - 2 := by
        rcases C.left_even with ⟨dl, hdl⟩
        rcases I.last_even with ⟨dr, hdr⟩
        omega
      have hpreviousEven : Even (D.profile.last - 2) := by
        rcases I.last_even with ⟨d, hd⟩
        exact ⟨d - 1, by omega⟩
      have htargetEarlier := lemma69_v_typeI_even_entry_gap_two
        a b D C hfirst (D.profile.last - 2) hpreviousEven
          hleftPrevious (by rw [I.rightSwitch_eq_last]; omega)
      have htargetLast := lemma69_v_typeI_even_entry_gap_two
        a b D C hfirst D.profile.last I.last_even
          hleftLe (by rw [I.rightSwitch_eq_last])
      have hsourceEarlier := lemma69_typeI_source_even_eq_anchor
        a b D C hfirst (D.profile.last - 2) hpreviousEven (by
          rw [I.rightSwitch_eq_last]
          omega)
      have hsourceLast := lemma69_typeI_source_even_eq_anchor
        a b D C hfirst D.profile.last I.last_even (by
          rw [I.rightSwitch_eq_last])
      have htwoStepEntry :
          b.orderSequence.entryOrZero (D.profile.last - 2) =
            b.orderSequence.entryOrZero D.profile.last := by omega
      let idx : RepresentationIndex (n + 2) (n + 2) :=
        ⟨D.profile.last, hlastPos, by omega, by omega⟩
      have htwoStep : b.order ⟨idx.val - 2,
          lt_of_le_of_lt (Nat.sub_le idx.val 2) idx.lt_large⟩ =
          b.order ⟨idx.val, idx.lt_large⟩ := by
        rw [← b.orderSequence_entryOrZero_eq_order,
          ← b.orderSequence_entryOrZero_eq_order]
        simpa only [idx] using htwoStepEntry
      have hgapLeRaw := b.orderGap_previous_le_twoE_of_twoStep
        idx hlastTwo htwoStep
      have hgapLe : b.orderGap previous ≤
          2 * (ramificationIndex K : Int) := by
        simpa only [idx, previous] using hgapLeRaw
      simpa only [x, first, previous] using
        beli2019Lemma79_typeI_caseEight_centralCoefficient_lt_previousAlpha
          a b D hfirst hgapTwo hlast hlastPos horder hdefect H
            hfirstTail hstrictTail hgapLe
  have hprefix := beli2019Lemma76_typeI_central_prefix_gt
    a b D C hfirst D.profile.last hlastTwo hlast I.last_even
      (C.left_le_anchor.trans C.anchor_le_right |>.trans
        I.rightSwitch_eq_last.le)
      (by rw [I.rightSwitch_eq_last]) x
      (by simpa only [previous] using hxPrevious) hxTwoE
  simpa only [x] using hprefix

end BONG.GoodBONG

end Bong
