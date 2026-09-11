/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma75Necessity
import Bong.Bong.BeliUniversalTheorem31

/-!
# He (2025), Theorem 7.4

This file derives the compact odd-rank classification in Theorem 7.4 from
the four-condition characterization in Lemma 7.5, in both directions.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The four compact invariant clauses on the right-hand side of He,
Theorem 7.4, for odd paper rank `n=2*k+3`. -/
structure HeADCTheorem74Conditions (k : Nat)
    (a : GoodBONG q L (2 * k + 5)) : Prop where
  initial : a.HeHuI1E (2 * k + 2) (by omega)
  penultimate :
    Even (a.order ⟨2 * k + 3, by omega⟩) ∧
      -(2 * (ramificationIndex K : Int)) ≤
        a.order ⟨2 * k + 3, by omega⟩ ∧
      a.order ⟨2 * k + 3, by omega⟩ ≤ 0
  last : a.order ⟨2 * k + 4, by omega⟩ = 0 ∨
    a.order ⟨2 * k + 4, by omega⟩ = 1
  alpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 0 ∨
    a.alphaValue ⟨2 * k + 2, by omega⟩ = 1

/-- The order gap at `alpha_n` is just `R_(n+1)`, because Theorem 7.4(i)
sets `R_n=0`. -/
private theorem heADC2025Theorem74_boundaryGap (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hInitial : a.HeHuI1E (2 * k + 2) (by omega)) :
    a.orderGap ⟨2 * k + 2, by omega⟩ =
      a.order ⟨2 * k + 3, by omega⟩ := by
  let boundary : Fin (2 * k + 4) := ⟨2 * k + 2, by omega⟩
  have hprevious : a.order ⟨2 * k + 2, by omega⟩ = 0 := by
    apply hInitial.oddOrder ⟨2 * k + 2, by omega⟩
    change Odd (2 * k + 3)
    exact ⟨k + 1, by omega⟩
  have hcast : boundary.castSucc =
      (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 5)) := Fin.ext (by rfl)
  have hsucc : boundary.succ =
      (⟨2 * k + 3, by omega⟩ : Fin (2 * k + 5)) := Fin.ext (by rfl)
  change a.order boundary.succ - a.order boundary.castSucc = _
  rw [hcast, hsucc, hprevious, sub_zero]

/-- Necessity in He, Theorem 7.4. -/
theorem heADC2025Theorem74Necessity (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3)) :
    a.HeADCTheorem74Conditions k := by
  have C := (a.heADC2025Lemma75 k).mp hADC
  have hgap := a.heADC2025Theorem74_boundaryGap k C.initial
  have hboundary : a.alphaValue ⟨2 * k + 2, by omega⟩ = 0 ∨
      a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 ∧
        a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ =
          ((((1 : ℚ) -
            (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ) := by
    simpa only [HeHuI2E, heADCAdjacentCappedDefect] using C.boundary
  have hlastNonnegative : 0 ≤ a.order ⟨2 * k + 4, by omega⟩ := by
    have heven : Even (2 * k + 4) := ⟨k + 2, by omega⟩
    exact ((a.heHu2022Proposition27i hADC.isIntegral).oddIndexed
      ⟨2 * k + 4, by omega⟩ ⟨2 * k + 4, by omega⟩ le_rfl
        heven heven).1
  have hpenultimate :
      Even (a.order ⟨2 * k + 3, by omega⟩) ∧
        -(2 * (ramificationIndex K : Int)) ≤
          a.order ⟨2 * k + 3, by omega⟩ ∧
        a.order ⟨2 * k + 3, by omega⟩ ≤ 0 := by
    rcases hboundary with hzero | hone
    · have horder :=
        (a.heADC2025Proposition34 ⟨2 * k + 2, by omega⟩).alphaZero.mp hzero
      rw [hgap] at horder
      rw [horder]
      refine ⟨?_, le_rfl, ?_⟩
      · exact ⟨-(ramificationIndex K : Int), by ring⟩
      · have hePositive : (0 : Int) < ramificationIndex K := by
          exact_mod_cast ramificationIndex_pos (K := K)
        omega
    · have htail := C.alphaOneTail hone.1
      exact ⟨htail.1, by omega, htail.2.2.1⟩
  have hlast : a.order ⟨2 * k + 4, by omega⟩ = 0 ∨
      a.order ⟨2 * k + 4, by omega⟩ = 1 := by
    rcases hboundary with hzero | hone
    · have hpen :=
        (a.heADC2025Proposition34 ⟨2 * k + 2, by omega⟩).alphaZero.mp hzero
      rw [hgap] at hpen
      by_cases hlarge : 2 * (ramificationIndex K : Int) <
          a.order ⟨2 * k + 4, by omega⟩ -
            a.order ⟨2 * k + 3, by omega⟩
      · exact Or.inr (C.largeGap hlarge).2
      · left
        have hle : a.order ⟨2 * k + 4, by omega⟩ -
            a.order ⟨2 * k + 3, by omega⟩ ≤
              2 * (ramificationIndex K : Int) := le_of_not_gt hlarge
        omega
    · exact C.alphaOneTail hone.1 |>.2.2.2
  exact
    { initial := C.initial
      penultimate := hpenultimate
      last := hlast
      alpha := hboundary.elim (fun h ↦ Or.inl h) (fun h ↦ Or.inr h.1) }

/-- Sufficiency in He, Theorem 7.4. -/
theorem heADC2025Theorem74Sufficiency (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (C : a.HeADCTheorem74Conditions k) :
    Lattice.IsNADC.{u, u, u} q L (2 * k + 3) := by
  apply (a.heADC2025Lemma75 k).mpr
  have hgap := a.heADC2025Theorem74_boundaryGap k C.initial
  have hboundary : a.HeHuI2E (2 * k + 2) (by omega) := by
    change a.alphaValue ⟨2 * k + 2, by omega⟩ = 0 ∨
      a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 ∧
        a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ =
          ((((1 : ℚ) -
            (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ)
    rcases C.alpha with hzero | hone
    · exact Or.inl hzero
    · right
      refine ⟨hone, ?_⟩
      have hdefect :=
        (a.heADC2025Proposition34 ⟨2 * k + 2, by omega⟩).alphaOneDefect hone
      by_cases hendpoint : a.order ⟨2 * k + 3, by omega⟩ =
          2 - 2 * (ramificationIndex K : Int)
      · have hlastLe : a.order ⟨2 * k + 4, by omega⟩ ≤ 1 := by
          rcases C.last with hlast | hlast <;> omega
        let next : Fin (2 * k + 4) := ⟨2 * k + 3, by omega⟩
        have hnextGap : a.orderGap next <
            2 * (ramificationIndex K : Int) := by
          unfold orderGap
          change a.order ⟨2 * k + 4, by omega⟩ -
            a.order ⟨2 * k + 3, by omega⟩ < _
          omega
        have halphaNext : a.alphaValue next ≤
            ((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) :=
          (a.alphaValue_le_two_e_sub_one_iff_orderGap_lt_two_e next).2 hnextGap
        have hcap : a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ ≤
            (a.alphaValue next : WithTop ℚ) := by
          have hbound := a.truncatedPrefixDefect_le_rightCap a (-1)
            (2 * k + 2) (2 * k + 4)
          rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hbound
          simpa only [heADCAdjacentCappedDefect, heHuAdjacentCappedDefect,
            next, show 2 * k + 4 - 1 = 2 * k + 3 by omega] using hbound
        have hupper : a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ ≤
            (((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) :
              WithTop ℚ) := hcap.trans (by exact_mod_cast halphaNext)
        have hlower :
            (((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) :
                WithTop ℚ) ≤
              a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ := by
          have hlowerRaw := hdefect.1
          rw [hgap, hendpoint] at hlowerRaw
          have hnum :
              ((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) =
                (1 : ℚ) -
                  ((2 - 2 * (ramificationIndex K : Int) : Int) : ℚ) := by
            push_cast
            ring
          rw [hnum]
          exact hlowerRaw
        have htarget :
            ((((1 : ℚ) -
                (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ) =
              (((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) :
                WithTop ℚ) := by
          rw [hendpoint]
          congr 1
          push_cast
          ring
        rw [htarget]
        exact le_antisymm hupper hlower
      · have hneGap : a.orderGap ⟨2 * k + 2, by omega⟩ ≠
            2 - 2 * (ramificationIndex K : Int) := by
          rw [hgap]
          exact hendpoint
        simpa only [heADCAdjacentCappedDefect, hgap] using hdefect.2 hneGap
  refine
    { initial := C.initial
      boundary := hboundary
      largeGap := ?_
      alphaOneTail := ?_ }
  · intro hlarge
    have hlastLe : a.order ⟨2 * k + 4, by omega⟩ ≤ 1 := by
      rcases C.last with hlast | hlast <;> omega
    have hpenLower := C.penultimate.2.1
    exact ⟨by omega, by omega⟩
  · intro hone
    have hshape :=
      (a.heADC2025Proposition34 ⟨2 * k + 2, by omega⟩).alphaOne.mp hone
    rw [hgap] at hshape
    have hePositive : (0 : Int) < ramificationIndex K := by
      exact_mod_cast ramificationIndex_pos (K := K)
    refine ⟨C.penultimate.1, ?_, C.penultimate.2.2, C.last⟩
    rcases hshape with (hendpoint | honeOrder) | hmiddle
    · omega
    · omega
    · omega

/-- He (2025), Theorem 7.4. -/
theorem heADC2025Theorem74 (k : Nat)
    (a : GoodBONG q L (2 * k + 5)) :
    Lattice.IsNADC.{u, u, u} q L (2 * k + 3) ↔
      a.HeADCTheorem74Conditions k := by
  constructor
  · exact a.heADC2025Theorem74Necessity k
  · exact a.heADC2025Theorem74Sufficiency k

end BONG.GoodBONG

end Bong
