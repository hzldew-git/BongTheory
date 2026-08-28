/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma77TypeIFullTerminal
import Bong.Bong.Beli2019Lemma79OrderTypeILeftBoundaryComplete
import Bong.Bong.Beli2019Lemma79OrderTypeIRight

/-!
# Beli (2019), Lemma 7.9(i): source-prefix dispatch at the left boundary

The Lemma 7.7 estimate needed at the exceptional predecessor has three
structural sources.  A strict central interval uses Lemma 6.9(v), a
coincident but nonterminal switch uses the right-tail form of Lemma 7.7,
and a switch coincident with the last unequal order uses the full-terminal
theorem.  These cases exhaust the canonical type-I profile.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Lemma 7.7 puts the source prefix at the first type-I switch strictly
above the exceptional mixed-defect order cut in every canonical shape. -/
theorem lemma79_typeI_leftPredecessor_sourcePrefix_gt_orderCut
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (hinterior : C.leftSwitch + 1 < n + 2) :
    (((a.order
        ⟨C.leftSwitch, C.left_le_anchor.trans_lt D.anchor_bound⟩ + 1 -
      a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) : WithTop ℚ) <
      a.truncatedPrefixDefect a
        ((-1) ^ ((C.leftSwitch + 2) / 2)) 0
          (C.leftSwitch + 2) := by
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  have hleftRight : C.leftSwitch ≤ C.rightSwitch :=
    C.left_le_anchor.trans C.anchor_le_right
  have hplateau : a.order (0 : Fin (n + 2)) =
      a.order ⟨C.leftSwitch, hleftBound⟩ := by
    have hraw := lemma77_typeI_source_plateau
      a b D C hfirst (C.leftSwitch + 2) (by omega) (by omega)
        (by
          rcases C.left_even with ⟨d, hd⟩
          exact ⟨d + 1, by omega⟩) hleftRight
    simpa only [show C.leftSwitch + 2 - 2 = C.leftSwitch by omega] using
      hraw
  by_cases hstrict : C.leftSwitch < C.rightSwitch
  · have htwoRight : C.leftSwitch + 2 ≤ C.rightSwitch := by
      rcases C.left_even with ⟨d, hd⟩
      rcases C.right_even with ⟨e, he⟩
      omega
    have hkTwo : C.leftSwitch + 2 < n + 2 :=
      htwoRight.trans_lt
        (C.right_le_last.trans_lt D.profile.lastDifference.bound)
    have hraw :=
      lemma79_typeI_even_sourcePrefix_gt_primaryCut_completeCentral
        a b D C hfirst horder hdefect C.leftSwitch hinterior hkTwo
          C.left_even le_rfl hstrict
    rw [hplateau] at hraw
    simpa only [hleftBound] using hraw
  · have hleftRightEq : C.leftSwitch = C.rightSwitch := by omega
    by_cases hrightLast : C.rightSwitch < D.profile.last
    · have hrightTwo := lemma69_typeI_rightSwitch_add_two_le_last
        a b D C hfirst hrightLast
      have hkTwo : C.leftSwitch + 2 < n + 2 := by
        rw [hleftRightEq]
        exact hrightTwo.trans_lt D.profile.lastDifference.bound
      have hraw := lemma79_typeI_even_sourcePrefix_gt_primaryCut_right
        a b D C hfirst hrightLast hdefect C.leftSwitch hleftBound
          hinterior hkTwo C.left_even (by rw [hleftRightEq]) (by omega)
      rw [hplateau] at hraw
      simpa only [hleftBound] using hraw
    · have hrightLastEq : C.rightSwitch = D.profile.last :=
        Nat.le_antisymm C.right_le_last (Nat.le_of_not_gt hrightLast)
      have hleftLast : C.leftSwitch = D.profile.last :=
        hleftRightEq.trans hrightLastEq
      have hlower := beli2019Lemma77_typeI_coincident_terminal_sourceCapped
        a b D C hfirst hleftPos hdefect hleftLast hinterior
      have hstrictCut :
          (((a.order ⟨C.leftSwitch, hleftBound⟩ + 1 -
              a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) :
            WithTop ℚ) <
          ((((a.order ⟨C.leftSwitch, hleftBound⟩ -
              a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 2 : ℚ) :
            WithTop ℚ) := by
        norm_cast
        linarith
      exact hstrictCut.trans_le hlower

/-- Condition 2.1(i) at the exceptional predecessor of the first type-I
switch, now with the Lemma 7.7 premise discharged internally. -/
theorem beli2019Lemma79_i_typeI_leftPredecessor
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.orderSequence.entry (C.leftSwitch - 1) (by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega) ≤
        c.orderSequence.entry (C.leftSwitch - 1) (by
          have hbound := C.left_le_anchor.trans_lt D.anchor_bound
          omega) ∨
      ∃ (hk0 : 0 < C.leftSwitch - 1)
          (hkNext : C.leftSwitch - 1 + 1 < n + 2),
        b.orderSequence.entry (C.leftSwitch - 1) (by omega) +
            b.orderSequence.entry (C.leftSwitch - 1 + 1) hkNext ≤
          c.orderSequence.entry (C.leftSwitch - 1 - 1) (by omega) +
            c.orderSequence.entry (C.leftSwitch - 1) (by omega) := by
  apply beli2019Lemma79_i_typeI_leftPredecessor_of_sourcePrefix
    a b c D C hfirst hleftPos horderAC hdefectAB hdefectAC hnorm
  intro hinterior
  have hsource := lemma79_typeI_leftPredecessor_sourcePrefix_gt_orderCut
    a b D C hfirst hleftPos horderAB hdefectAB hinterior
  convert hsource using 1 <;>
    simp only [Int.cast_sub, Int.cast_add, Int.cast_one] <;> ring

end BONG.GoodBONG

end Bong
