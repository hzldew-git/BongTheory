/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeICaseOneSourceRepresentation
import Bong.Bong.Beli2019Lemma79TypeICaseOnePrefixDefect
import Bong.Bong.Beli2019Lemma216Complete

/-!
# Beli (2019), Lemma 7.9(ii), case 1: the comparison prefix representation

The first central target alpha is nonnegative, so its primary candidate
places the source-comparison defect strictly above the condition (iii') cut.
The `2e` comparison-prefix defect and multiplicative domination transfer this
strict inequality to the second comparison BONG.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 4000000 in
-- The proof combines dependent central indices with three capped defects.
/-- Condition 2.1(iii') represents the exceptional comparison prefix in
Lemma 7.9(ii), case 1. -/
theorem beli2019Lemma79_typeI_caseOne_targetPrefixRepresentation
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hcentralAC : a.CentralRepresentationConditions c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hnextBound : i.val + 1 < n + 2)
    (hgap : b.orderGap ⟨i.val - 1, by omega⟩ =
      2 * (ramificationIndex K : Int) + 1)
    (hprevious : c.order ⟨i.val - 1, by omega⟩ =
      b.order ⟨i.val - 1, by omega⟩) :
    DiagonalRepresents
      (c.prefixValues i.val i.lt_large.le)
      (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large)) := by
  have hiEven : Even i.val := by
    simpa only [hleft] using C.left_even
  have hiTwo : 2 ≤ i.val := by
    rcases hiEven with ⟨k, hk⟩
    have hiPos := i.pos
    omega
  have hleftPos : 0 < C.leftSwitch := by omega
  have hiPreviousBound : i.val - 1 < n + 2 :=
    (Nat.sub_le i.val 1).trans_lt i.lt_large
  let j : CentralRepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hnextBound, by omega⟩
  have hjCurrent : j.val ≤ n + 2 := by
    simp only [j]
    omega
  let previous : Fin (n + 2) := ⟨i.val - 1, hiPreviousBound⟩
  let current : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let next : Fin (n + 2) := ⟨i.val + 1, hnextBound⟩
  let p : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have horderB :=
    beli2019Lemma79_typeI_caseOne_centralOrderTrigger_complete
      a b D C hfirst i hleft hnextBound hgap
  have horderB' : b.order previous < a.order next := by
    simpa only [previous, next] using horderB
  have horderC : c.order previous < a.order next := by
    rw [hprevious]
    exact horderB'
  have hpSucc : p.succ = current := by
    apply Fin.ext
    simp only [p, current, Fin.val_succ]
    omega
  have hpCast : p.castSucc = previous := by
    apply Fin.ext
    rfl
  have hgapOrder : b.order current - b.order previous =
      2 * (ramificationIndex K : Int) + 1 := by
    unfold orderGap at hgap
    rw [hpSucc, hpCast] at hgap
    exact hgap
  have hcurrentValue :=
    a.beli2019Lemma69_ii_typeI_firstTargetValue_complete
      b D C hfirst hleftPos horderAB hdefectAB
        (j.current hjCurrent) (by
          simp only [j, CentralRepresentationIndex.current]
          omega)
  have hcurrentNonneg : 0 ≤
      a.representationAlphaValue b (j.current hjCurrent) := by
    rw [hcurrentValue]
    exact (b.alpha_p2 _).1
  have hprimary :=
    a.representationAlpha_le_primary b (j.current hjCurrent)
  rw [← a.coe_representationAlphaValue b (j.current hjCurrent),
    a.representationPrimaryDefect_current_eq b j hjCurrent] at hprimary
  let shift : ℚ := ((a.order next - b.order current : Int) : ℚ)
  let cut : ℚ := 2 * (ramificationIndex K : ℚ) +
    (b.order previous : ℚ) - (a.order next : ℚ)
  have hprimary' :
      (a.representationAlphaValue b (j.current hjCurrent) : WithTop ℚ) ≤
        (shift : WithTop ℚ) + a.centralCurrentDefect b j := by
    simpa only [shift, j, current, next, CentralRepresentationIndex.current,
      Nat.add_one_sub_one] using hprimary
  have hzeroLe : (0 : WithTop ℚ) ≤
      (shift : WithTop ℚ) + a.centralCurrentDefect b j := by
    have hnonnegTop : (0 : WithTop ℚ) ≤
        (a.representationAlphaValue b (j.current hjCurrent) : WithTop ℚ) := by
      exact_mod_cast hcurrentNonneg
    exact hnonnegTop.trans hprimary'
  have hminusShiftLe : ((-shift : ℚ) : WithTop ℚ) ≤
      a.centralCurrentDefect b j := by
    have htranslated := add_le_add_right hzeroLe ((-shift : ℚ) : WithTop ℚ)
    have htranslated' : ((-shift : ℚ) : WithTop ℚ) ≤
        ((-shift : ℚ) : WithTop ℚ) +
          ((shift : ℚ) : WithTop ℚ) + a.centralCurrentDefect b j := by
      simpa only [zero_add, add_comm, add_left_comm, add_assoc] using htranslated
    calc
      ((-shift : ℚ) : WithTop ℚ) ≤
          ((-shift : ℚ) : WithTop ℚ) +
            ((shift : ℚ) : WithTop ℚ) +
              a.centralCurrentDefect b j := htranslated'
      _ = a.centralCurrentDefect b j := by
        have hcancel : ((-shift : ℚ) : WithTop ℚ) +
            ((shift : ℚ) : WithTop ℚ) = 0 := by
          norm_cast
          ring
        rw [hcancel, zero_add]
  have hgapOrderQ : (b.order current : ℚ) - (b.order previous : ℚ) =
      2 * (ramificationIndex K : ℚ) + 1 := by
    have hcast := congrArg (fun z : Int => (z : ℚ)) hgapOrder
    push_cast at hcast
    exact hcast
  have hcutLtMinusShift : cut < -shift := by
    dsimp only [cut, shift]
    push_cast
    linarith
  have hsourceCurrent : (cut : WithTop ℚ) <
      a.centralCurrentDefect b j :=
    (WithTop.coe_lt_coe.mpr hcutLtMinusShift).trans_le hminusShiftLe
  have hcomparisonLower :=
    beli2019Lemma79_typeI_caseOne_comparisonDefect_ge_twoE
      a b c D C horderBC hnorm i hleft hgap hprevious
  have hcutLtTwoE : cut < 2 * (ramificationIndex K : ℚ) := by
    have horderQ : (b.order previous : ℚ) < (a.order next : ℚ) := by
      exact_mod_cast horderB'
    dsimp only [cut]
    linarith
  have hcomparison : (cut : WithTop ℚ) <
      b.truncatedPrefixDefect c 1 i.val i.val := by
    have hcutTop : (cut : WithTop ℚ) <
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      exact_mod_cast hcutLtTwoE
    exact hcutTop.trans_le hcomparisonLower
  have hdomRaw := a.truncatedPrefixDefect_domination b c
    (-1) 1 (i.val + 2) i.val i.val
  have hdom : min (a.centralCurrentDefect b j)
      (b.truncatedPrefixDefect c 1 i.val i.val) ≤
        a.centralCurrentDefect c j := by
    unfold centralCurrentDefect
    simpa only [j, Nat.add_one_sub_one, mul_one,
      show i.val + 1 + 1 = i.val + 2 by omega] using hdomRaw
  have htargetCurrent : (cut : WithTop ℚ) <
      a.centralCurrentDefect c j :=
    (lt_min hsourceCurrent hcomparison).trans_le hdom
  have hpreviousNonneg : (0 : WithTop ℚ) ≤
      a.centralPreviousDefect c j := by
    unfold centralPreviousDefect
    exact a.truncatedPrefixDefect_nonneg c (-1) j.val (j.val - 2)
  have htargetSum : (cut : WithTop ℚ) <
      a.centralPreviousDefect c j + a.centralCurrentDefect c j := by
    apply htargetCurrent.trans_le
    have hadd := add_le_add_right hpreviousNonneg (a.centralCurrentDefect c j)
    simpa only [zero_add, add_comm] using hadd
  have hdefectTrigger : a.centralDefectTrigger c j := by
    constructor
    · simpa only [j, previous, next,
        show i.val + 1 - 2 = i.val - 1 by omega] using horderC
    · convert htargetSum using 1
      norm_cast
      dsimp only [cut, j, previous, next]
      push_cast
      rw [hprevious]
  have hequiv := a.beli2019Lemma216 c le_rfl horderAC hdefectAC
  have hrepresented := hcentralAC j ((hequiv j).mpr hdefectTrigger)
  simpa only [j, Nat.add_one_sub_one] using hrepresented

end BONG.GoodBONG

end Bong
