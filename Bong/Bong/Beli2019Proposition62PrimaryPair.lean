/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Proposition62PreviousPrimary

/-!
# Beli (2019), Proposition 6.2: closing the primary branch

When two consecutive representation invariants use their primary candidates,
the earlier cross defect is strictly below the current diagonal comparison
defect.  Sharp capped-defect multiplication identifies it with the target
adjacent defect.  The target alpha bound then gives the even pair comparison.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- A preceding primary cross defect, strictly below the diagonal comparison
defect, is the adjacent target defect. -/
theorem previousPrimaryCross_eq_targetAdjacent_of_lt_diagonal
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1)) (i : Nat)
    (hlt : a.truncatedPrefixDefect b (-1) i (i - 2) <
      a.truncatedPrefixDefect b 1 i i) :
    a.truncatedPrefixDefect b (-1) i (i - 2) =
      b.truncatedPrefixDefect b (-1) (i - 2) i := by
  have hlt' : b.truncatedPrefixDefect a (-1) (i - 2) i <
      a.truncatedPrefixDefect b 1 i i := by
    rw [b.truncatedPrefixDefect_comm a (-1) (i - 2) i]
    exact hlt
  have hmul := b.truncatedPrefixDefect_mul_eq_left_of_lt_right a b
    (-1) 1 (i - 2) i i hlt'
  have hmul' : b.truncatedPrefixDefect b (-1) (i - 2) i =
      b.truncatedPrefixDefect a (-1) (i - 2) i := by
    simpa using hmul
  calc
    a.truncatedPrefixDefect b (-1) i (i - 2) =
        b.truncatedPrefixDefect a (-1) (i - 2) i :=
      a.truncatedPrefixDefect_comm b (-1) i (i - 2)
    _ = b.truncatedPrefixDefect b (-1) (i - 2) i := hmul'.symm

set_option maxHeartbeats 1200000 in
-- Several dependent indices and nested `WithTop` inequalities are normalized together.
/-- The primary branch of Proposition 6.2 forces the even pair comparison. -/
theorem representationWeightEvenPair_of_primary
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 1 < i.val)
    (hprimary : a.representationAlpha b i =
      a.representationPrimaryDefect b i)
    (hdirect : ¬a.representationWeightEvenDirect b i) :
    a.representationWeightEvenPair b i hi := by
  by_contra hpair
  let p : Fin n := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let qIndex : Fin n := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  have hpSucc : p.succ = ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have hpCast : p.castSucc = ⟨i.val - 1,
      (Nat.sub_le _ _).trans_lt i.lt_large⟩ := by
    apply Fin.ext
    rfl
  have hqSucc : qIndex.succ = p.castSucc := by
    apply Fin.ext
    simp only [qIndex, p, Fin.val_succ, Fin.val_castSucc]
    omega
  have hqCast : qIndex.castSucc = ⟨i.val - 2, by
      have := i.lt_large
      omega⟩ := by
    apply Fin.ext
    rfl
  let D := a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1)
  let E := a.truncatedPrefixDefect b (-1) i.val (i.val - 2)
  let C := a.truncatedPrefixDefect b 1 i.val i.val
  let shiftCurrent : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ : Int) : ℚ)
  let shiftPrevious : ℚ :=
    ((a.order ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ -
      b.order ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ : Int) : ℚ)
  let coefficient : ℚ :=
    ((a.order ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ + a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ - b.order ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ : Int) : ℚ)
  have hpairLt :
      2 * (b.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : ℚ) +
          b.alphaValue ⟨i.val - 1, by
            have := i.lt_large
            omega⟩ -
          b.alphaValue ⟨i.val - 2, by
            have := i.lt_large
            omega⟩ <
        (a.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : ℚ) + (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
    exact lt_of_not_ge hpair
  have hb := a.order_bounds_of_weightPair_lt b horder i hi hpairLt
  have hstrict := hb.2.2
  have hcoefficientInt : 0 <
      a.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ + a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 2, by
          have := i.lt_large
          omega⟩ - b.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ := by
    omega
  have hcoefficient : 0 < coefficient := by
    dsimp only [coefficient]
    exact_mod_cast hcoefficientInt
  have hshift : coefficient = shiftCurrent + shiftPrevious := by
    dsimp only [coefficient, shiftCurrent, shiftPrevious]
    push_cast
    ring
  have hprevious := a.representationAlpha_previous_le_primaryCross
    b hdefect i hi hprimary hdirect
  have hpreviousPrimary := a.representationAlpha_previous_eq_primary
    b horder hdefect i hi hprimary hdirect hpair
  rw [hpreviousPrimary] at hprevious
  unfold representationPrimaryDefect at hprevious
  simp only [previousRepresentationIndex,
    show i.val - 1 + 1 = i.val by omega,
    show i.val - 1 - 1 = i.val - 2 by omega] at hprevious
  change (shiftPrevious : WithTop ℚ) + E ≤ D at hprevious
  have hcurrent := hdefect i
  rw [a.coe_representationAlphaValue b i, hprimary] at hcurrent
  unfold representationPrimaryDefect at hcurrent
  change (shiftCurrent : WithTop ℚ) + D ≤ C at hcurrent
  have hcombined : (coefficient : WithTop ℚ) + E ≤ C := by
    calc
      (coefficient : WithTop ℚ) + E =
          (shiftCurrent : WithTop ℚ) +
            ((shiftPrevious : WithTop ℚ) + E) := by
        rw [hshift]
        norm_num [add_assoc]
      _ ≤ (shiftCurrent : WithTop ℚ) + D := by gcongr
      _ ≤ C := hcurrent
  have hEcap : E ≤ a.prefixAlphaCap i.val :=
    a.truncatedPrefixDefect_le_leftCap b (-1) i.val (i.val - 2)
  have hcapNe : a.prefixAlphaCap i.val ≠ ⊤ := by
    rw [a.prefixAlphaCap_of_internal i.pos i.lt_large]
    exact WithTop.coe_ne_top
  have hEne : E ≠ ⊤ := ne_top_of_le_ne_top hcapNe hEcap
  have hEsmall : E < (coefficient : WithTop ℚ) + E := by
    rw [← WithTop.coe_untop E hEne]
    norm_cast
    linarith
  have hEC : E < C := hEsmall.trans_le hcombined
  have hEtarget := a.previousPrimaryCross_eq_targetAdjacent_of_lt_diagonal
    b i.val hEC
  have hbetaCurrent := a.representationAlpha_le_rightAlpha b hdefect i
  rw [hprimary] at hbetaCurrent
  unfold representationPrimaryDefect at hbetaCurrent
  rw [← hpSucc, ← hpCast] at hbetaCurrent
  have hbetaCurrent' : (shiftCurrent : WithTop ℚ) + D ≤
      (b.alphaValue p : WithTop ℚ) := by
    simpa only [shiftCurrent, p, Fin.succ_mk, Fin.castSucc_mk,
      Nat.sub_add_cancel i.pos] using hbetaCurrent
  have htotal : (coefficient : WithTop ℚ) + E ≤
      (b.alphaValue p : WithTop ℚ) := by
    calc
      (coefficient : WithTop ℚ) + E =
          (shiftCurrent : WithTop ℚ) +
            ((shiftPrevious : WithTop ℚ) + E) := by
        rw [hshift]
        norm_num [add_assoc]
      _ ≤ (shiftCurrent : WithTop ℚ) + D := by gcongr
      _ ≤ (b.alphaValue p : WithTop ℚ) := hbetaCurrent'
  have hbetaPrevious := b.alpha_le_orderGap_add_cappedAdjacent qIndex
  rw [hqSucc] at hbetaPrevious
  have hbetaPrevious' : (b.alphaValue qIndex : WithTop ℚ) ≤
      (((b.order p.castSucc - b.order qIndex.castSucc : Int) : ℚ) :
        WithTop ℚ) +
        b.truncatedPrefixDefect b (-1) (i.val - 2) i.val := by
    simpa only [qIndex, show i.val - 2 + 2 = i.val by omega]
      using hbetaPrevious
  rw [← hEtarget] at hbetaPrevious'
  change (b.alphaValue qIndex : WithTop ℚ) ≤
    (((b.order p.castSucc - b.order qIndex.castSucc : Int) : ℚ) :
      WithTop ℚ) + E at hbetaPrevious'
  rw [← WithTop.coe_untop E hEne] at htotal hbetaPrevious'
  norm_cast at htotal hbetaPrevious'
  have hpairQ : (a.order p.castSucc : ℚ) + (a.order p.succ : ℚ) ≤
      2 * (b.order p.castSucc : ℚ) + b.alphaValue p -
        b.alphaValue qIndex := by
    dsimp only [coefficient, shiftCurrent, shiftPrevious] at htotal
    push_cast at htotal hbetaPrevious'
    rw [hpCast, hqCast] at hbetaPrevious'
    rw [hpSucc, hpCast]
    linarith
  apply hpair
  simpa only [representationWeightEvenPair, p, qIndex, Fin.castSucc_mk,
    Fin.succ_mk, Nat.sub_add_cancel i.pos] using hpairQ

end BONG.GoodBONG

end Bong
