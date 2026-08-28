/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeILeftBoundary

/-!
# Beli (2019), Lemma 7.9(i): domination at the exceptional left boundary

This is the domination argument in lines 5157--5161.  Every even order of
the third BONG before the exceptional coordinate is bounded below by its
first order, and every following odd order is bounded above by the
exceptional current order.  Hence every adjacent capped defect in the short
prefix has the same lower bound; Lemma 7.4 joins them by domination.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The third self-prefix occurring at the exceptional type-I predecessor
is at least two units above the mixed-defect cut. -/
theorem lemma79_typeI_leftPredecessor_thirdPrefix_ge_orderCut_add_two
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hleftFour : 4 ≤ C.leftSwitch)
    (hinterior : C.leftSwitch + 1 < n + 2)
    (F : Lemma79TypeILeftPredecessorFailureData a c C.leftSwitch) :
    ((((a.order
          ⟨C.leftSwitch, C.left_le_anchor.trans_lt D.anchor_bound⟩ -
        a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 3 : ℚ) :
          WithTop ℚ) ≤
      c.truncatedPrefixDefect c ((-1) ^ ((C.leftSwitch - 2) / 2))
        0 (C.leftSwitch - 2) := by
  rcases C.left_even with ⟨d, hd⟩
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  have hsourceZero := C.source_to_anchor 0
    (Nat.zero_le D.anchor) ⟨0, by omega⟩
  have hsourceLeft := C.source_to_anchor C.leftSwitch
    C.left_le_anchor ⟨d, hd⟩
  have hsourceZeroLeft :
      a.orderSequence.entryOrZero 0 =
        a.orderSequence.entryOrZero C.leftSwitch :=
    hsourceZero.trans hsourceLeft.symm
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstLower : a.orderSequence.entryOrZero 0 + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    calc
      a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
      _ ≤ c.order 0 := hnormOrder
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
  have hsourceTail := a.orderSequence.entryOrZero_le_of_evenGap
    (C.leftSwitch - 1) (C.leftSwitch + 1) (by omega) hinterior
      ⟨1, by omega⟩
  have hthirdCurrent :
      c.orderSequence.entryOrZero (C.leftSwitch - 1) ≤
        a.orderSequence.entryOrZero (C.leftSwitch + 1) - 2 :=
    F.targetCurrent_le.trans (by omega)
  let critical : WithTop ℚ :=
    ((((a.order ⟨C.leftSwitch, hleftBound⟩ -
      a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 3 : ℚ) :
        WithTop ℚ)
  have hlocal (t : Nat) (ht : t ≤ d - 2) :
      critical ≤ c.truncatedPrefixDefect c (-1) (2 * t) (2 * t + 2) := by
    have htEven : Even (2 * t) := ⟨t, by omega⟩
    have hthirdEven := c.orderSequence.entryOrZero_le_of_evenGap
      0 (2 * t) (Nat.zero_le _) (by omega) htEven
    have hthirdOddDistance :
        Even ((C.leftSwitch - 1) - (2 * t + 1)) :=
      ⟨d - t - 1, by omega⟩
    have hthirdOdd := c.orderSequence.entryOrZero_le_of_evenGap
      (2 * t + 1) (C.leftSwitch - 1) (by omega) (by omega)
        hthirdOddDistance
    have horderGap :
        a.orderSequence.entryOrZero C.leftSwitch -
            a.orderSequence.entryOrZero (C.leftSwitch + 1) + 3 ≤
          c.orderSequence.entryOrZero (2 * t) -
            c.orderSequence.entryOrZero (2 * t + 1) := by
      omega
    let j : Fin (n + 1) := ⟨2 * t, by omega⟩
    have hadjacent := c.order_sub_add_alpha_le_cappedAdjacent j
    have halphaNonnegative := (c.alpha_p2 j).1
    have hcriticalQ :
        ((a.order ⟨C.leftSwitch, hleftBound⟩ -
            a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 3 ≤
          ((c.order j.castSucc - c.order j.succ : Int) : ℚ) +
            c.alphaValue j := by
      have horderGap' :
          a.order ⟨C.leftSwitch, hleftBound⟩ -
              a.order ⟨C.leftSwitch + 1, hinterior⟩ + 3 ≤
            c.order j.castSucc - c.order j.succ := by
        rw [← a.orderSequence_entryOrZero_eq_order,
          ← a.orderSequence_entryOrZero_eq_order,
          ← c.orderSequence_entryOrZero_eq_order,
          ← c.orderSequence_entryOrZero_eq_order]
        simpa only [j, Fin.val_castSucc, Fin.val_succ] using horderGap
      have horderGapQ :
          ((a.order ⟨C.leftSwitch, hleftBound⟩ -
              a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 3 ≤
            ((c.order j.castSucc - c.order j.succ : Int) : ℚ) := by
        exact_mod_cast horderGap'
      exact horderGapQ.trans (by linarith)
    exact (WithTop.coe_le_coe.mpr hcriticalQ).trans hadjacent
  have hjoined := c.truncatedPrefixDefect_alternating_ge
    0 (d - 2) (by omega) critical (by
      intro t ht
      simpa only [zero_add] using hlocal t ht)
  have hend : 0 + 2 * (d - 2 + 1) = C.leftSwitch - 2 := by omega
  have hexponent : d - 2 + 1 = (C.leftSwitch - 2) / 2 := by omega
  rw [hend, hexponent] at hjoined
  simpa only [critical] using hjoined

end BONG.GoodBONG

end Bong
