/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourCentralLow
import Bong.Bong.Beli2019AdjacentCappedDefect

/-!
# Beli (2019), Lemma 4.3: candidates below a low outer pair

This file expands the invariant `B_(i-2)` in the secondary branch of the
low-pair proof.  It proves separately that its half-gap, primary, and current
secondary candidates all contradict the strict inequality on line 2475.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M N : Lattice K V} {n : Nat}

/-- The ordinary boundary carrying the paper's invariant `B_(i-2)`. -/
def centralPreviousPreviousIndex
    (i : CentralRepresentationIndex (n + 1) (n + 1)) (hiTwo : 2 < i.val) :
    RepresentationIndex (n + 1) (n + 1) where
  val := i.val - 2
  pos := by omega
  lt_large := by have := i.lt_large; omega
  le_small := by have := i.lt_large; omega

@[simp]
theorem centralPreviousPreviousIndex_val
    (i : CentralRepresentationIndex (n + 1) (n + 1)) (hiTwo : 2 < i.val) :
    (centralPreviousPreviousIndex i hiTwo).val = i.val - 2 := by
  rfl

/-- Failure of the first comparison at the secondary candidate is exactly
the strict shifted inequality preceding line 2470. -/
theorem sectionFourLowPair_secondaryShift_lt_currentAlpha
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1)
    (hsecondary :
      a.representationAlphaPrime b (i.current i.lt_large.le) =
        a.representationSecondaryDefect b (i.current i.lt_large.le)
          ⟨i.one_lt, hiNext⟩)
    (hnotFirst :
      ¬((((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.representationAlpha c (i.current i.lt_large.le) <=
          (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.representationAlphaPrime b (i.current i.lt_large.le))) :
    ((((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ -
        b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
        c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)) :
          WithTop ℚ) +
        a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) <
      a.representationAlpha c (i.current i.lt_large.le) := by
  let commonShift : ℚ := ((a.order ⟨i.val, i.lt_large⟩ +
    a.order ⟨i.val + 1, hiNext⟩ -
    b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
    c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let sourceDefect :=
    a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2)
  have hstrict := lt_of_not_ge hnotFirst
  have hsourceForm :
      (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlphaPrime b (i.current i.lt_large.le) =
        (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + ((commonShift : WithTop ℚ) + sourceDefect) := by
    rw [hsecondary]
    unfold representationSecondaryDefect CentralRepresentationIndex.current
    dsimp only [commonShift, sourceDefect]
    rw [← add_assoc, ← add_assoc]
    congr 1
    norm_cast
    push_cast
    ring
  change (commonShift : WithTop ℚ) + sourceDefect < _
  apply (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp
  calc
    ((((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + ((commonShift : WithTop ℚ) + sourceDefect)) =
        (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
            a.representationAlphaPrime b
              (i.current i.lt_large.le) := hsourceForm.symm
    _ < (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
            a.representationAlpha c
              (i.current i.lt_large.le) := hstrict

/-- The strict crossing `T_(i-2)<S_i` used to apply Lemma 2.7(ii) to
`B_(i-2)`. -/
theorem sectionFourLowPair_targetTwoPrevious_lt_middleCurrent
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiTwo : 2 < i.val) (hiNext : i.val + 1 < n + 1)
    (htrigger : a.centralAlphaTrigger c i)
    (hlow :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ <=
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩) :
    c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ <
      b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
  have hessential := a.isEssentialFor_of_centralAlphaTrigger c i htrigger
  have hraw := hessential.2 (by
    change 1 < i.val - 1
    omega) (by
    change i.val - 1 + 2 < n + 1
    omega)
  simp only [orderSequence_at] at hraw
  have hcLeft :
      (⟨i.val - 1 - 2, by omega⟩ : Fin (n + 1)) =
        ⟨i.val - 3, by omega⟩ := by
    apply Fin.ext
    change i.val - 1 - 2 = i.val - 3
    omega
  have hcRight :
      (⟨i.val - 1 - 1, by omega⟩ : Fin (n + 1)) =
        ⟨i.val - 2, by omega⟩ := by
    apply Fin.ext
    change i.val - 1 - 1 = i.val - 2
    omega
  have haCurrent :
      (⟨i.val - 1 + 1, by omega⟩ : Fin (n + 1)) =
        ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  have haNext :
      (⟨i.val - 1 + 2, by omega⟩ : Fin (n + 1)) =
        ⟨i.val + 1, hiNext⟩ := by
    apply Fin.ext
    change i.val - 1 + 2 = i.val + 1
    omega
  have hpair :
      c.order ⟨i.val - 3, by omega⟩ + c.order ⟨i.val - 2, by omega⟩ <
        a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ := by
    simpa only [hcLeft, hcRight, haCurrent, haNext] using hraw
  omega

/-- Essentiality at the active central index, in the exact four-entry form
used by all three candidate estimates. -/
theorem sectionFourLowPair_targetPreviousPair_lt_sourceCurrentPair
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiTwo : 2 < i.val) (hiNext : i.val + 1 < n + 1)
    (htrigger : a.centralAlphaTrigger c i) :
    c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ +
        c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ := by
  have hessential := a.isEssentialFor_of_centralAlphaTrigger c i htrigger
  have hraw := hessential.2 (by
    change 1 < i.val - 1
    omega) (by
    change i.val - 1 + 2 < n + 1
    omega)
  simp only [orderSequence_at] at hraw
  have hcLeft :
      (⟨i.val - 1 - 2, by omega⟩ : Fin (n + 1)) =
        ⟨i.val - 3, by omega⟩ := by
    apply Fin.ext
    change i.val - 1 - 2 = i.val - 3
    omega
  have hcRight :
      (⟨i.val - 1 - 1, by omega⟩ : Fin (n + 1)) =
        ⟨i.val - 2, by omega⟩ := by
    apply Fin.ext
    change i.val - 1 - 1 = i.val - 2
    omega
  have haCurrent :
      (⟨i.val - 1 + 1, by omega⟩ : Fin (n + 1)) =
        ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  have haNext :
      (⟨i.val - 1 + 2, by omega⟩ : Fin (n + 1)) =
        ⟨i.val + 1, hiNext⟩ := by
    apply Fin.ext
    change i.val - 1 + 2 = i.val + 1
    omega
  simpa only [hcLeft, hcRight, haCurrent, haNext] using hraw

/-- Lines 2481--2483: after the common shift, the half-gap candidate of
`B_(i-2)` lies strictly above `C_i`. -/
theorem sectionFourLowPair_currentAlpha_lt_previousHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiTwo : 2 < i.val) (hiNext : i.val + 1 < n + 1)
    (htrigger : a.centralAlphaTrigger c i)
    (hprevious :
      b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <=
        c.order ⟨i.val - 2, by have := i.lt_large; omega⟩) :
    a.representationAlpha c (i.current i.lt_large.le) <
      ((((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ -
        b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
        c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)) :
          WithTop ℚ) +
        b.representationHalfGap c (centralPreviousPreviousIndex i hiTwo) := by
  have hupper := a.centralCurrentAlpha_le_leftAverage c i hiNext
  apply hupper.trans_lt
  have hessential := a.isEssentialFor_of_centralAlphaTrigger c i htrigger
  have hraw := hessential.2 (by
    change 1 < i.val - 1
    omega) (by
    change i.val - 1 + 2 < n + 1
    omega)
  simp only [orderSequence_at] at hraw
  have hcLeft :
      (⟨i.val - 1 - 2, by omega⟩ : Fin (n + 1)) =
        ⟨i.val - 3, by omega⟩ := by
    apply Fin.ext
    change i.val - 1 - 2 = i.val - 3
    omega
  have hcRight :
      (⟨i.val - 1 - 1, by omega⟩ : Fin (n + 1)) =
        ⟨i.val - 2, by omega⟩ := by
    apply Fin.ext
    change i.val - 1 - 1 = i.val - 2
    omega
  have haCurrent :
      (⟨i.val - 1 + 1, by omega⟩ : Fin (n + 1)) =
        ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  have haNext :
      (⟨i.val - 1 + 2, by omega⟩ : Fin (n + 1)) =
        ⟨i.val + 1, hiNext⟩ := by
    apply Fin.ext
    change i.val - 1 + 2 = i.val + 1
    omega
  have hpair :
      c.order ⟨i.val - 3, by omega⟩ + c.order ⟨i.val - 2, by omega⟩ <
        a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ := by
    simpa only [hcLeft, hcRight, haCurrent, haNext] using hraw
  unfold centralLeftAverage representationHalfGap
  simp only [centralPreviousPreviousIndex, previousRepresentationIndex,
    CentralRepresentationIndex.previous, Nat.sub_sub]
  norm_cast
  simp only [Rat.divInt_eq_div]
  push_cast
  have hpreviousQ :
      (b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : ℚ) <=
        (c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : ℚ) := by
    exact_mod_cast hprevious
  have hpairQ :
      (c.order ⟨i.val - 3, by omega⟩ : ℚ) +
          c.order ⟨i.val - 2, by omega⟩ <
        a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hiNext⟩ := by
    exact_mod_cast hpair
  linarith

/-- Lines 2484--2489: after the common shift, the primary candidate of
`B_(i-2)` is at least `C_i`.  If its prefix defect dominates the current
middle-to-target defect, this follows from the fallback bound.  Otherwise
the strict triangle replaces it by the adjacent target defect, and the
secondary right cap of `C_i` applies. -/
theorem sectionFourLowPair_currentAlpha_le_previousPrimary
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hlocal : SectionFourLocalConditions a b c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiTwo : 2 < i.val) (hiNext : i.val + 1 < n + 1)
    (htrigger : a.centralAlphaTrigger c i)
    (hlow :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ <=
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩) :
    a.representationAlpha c (i.current i.lt_large.le) <=
      ((((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ -
        b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
        c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)) :
          WithTop ℚ) +
        b.representationPrimaryDefect c
          (centralPreviousPreviousIndex i hiTwo) := by
  let outerShift : ℚ := ((a.order ⟨i.val, i.lt_large⟩ +
    a.order ⟨i.val + 1, hiNext⟩ -
    b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
    c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let baseShift : ℚ := ((a.order ⟨i.val, i.lt_large⟩ +
    a.order ⟨i.val + 1, hiNext⟩ -
    c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ -
    c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let fallbackShift : ℚ := ((c.order ⟨i.val - 2, by
      have := i.lt_large
      omega⟩ - c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let targetCapShift : ℚ := ((a.order ⟨i.val, i.lt_large⟩ +
    a.order ⟨i.val + 1, hiNext⟩ -
    c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
    c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let primaryDefect := b.truncatedPrefixDefect c (-1)
    (i.val - 1) (i.val - 3)
  let middleDefect := b.truncatedPrefixDefect c 1
    (i.val - 1) (i.val - 1)
  let adjacentDefect := c.truncatedPrefixDefect c (-1)
    (i.val - 3) (i.val - 1)
  let pp := centralPreviousPreviousIndex i hiTwo
  have hleft : i.val - 2 + 1 = i.val - 1 := by omega
  have hright : i.val - 2 - 1 = i.val - 3 := by omega
  have hppPrimary :
      b.representationPrimaryDefect c pp =
        ((((b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
          c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ : Int) : ℚ)) :
            WithTop ℚ) + primaryDefect := by
    unfold representationPrimaryDefect
    have hbIndex :
        (⟨pp.val, pp.lt_large⟩ : Fin (n + 1)) =
          ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
      apply Fin.ext
      rfl
    have hcIndex :
        (⟨pp.val - 1, by have := pp.le_small; omega⟩ : Fin (n + 1)) =
          ⟨i.val - 3, by have := i.lt_large; omega⟩ := by
      apply Fin.ext
      change i.val - 2 - 1 = i.val - 3
      omega
    rw [hbIndex, hcIndex]
    change _ + b.truncatedPrefixDefect c (-1)
      (i.val - 2 + 1) (i.val - 2 - 1) = _
    rw [hleft, hright]
  have hprimaryForm :
      (outerShift : WithTop ℚ) +
          b.representationPrimaryDefect c
            (centralPreviousPreviousIndex i hiTwo) =
        (baseShift : WithTop ℚ) + primaryDefect := by
    change (outerShift : WithTop ℚ) +
      b.representationPrimaryDefect c pp = _
    rw [hppPrimary]
    dsimp only [outerShift, baseShift, primaryDefect]
    rw [← add_assoc]
    congr 1
    norm_cast
    push_cast
    ring
  have hpair := a.sectionFourLowPair_targetPreviousPair_lt_sourceCurrentPair
    c i hiTwo hiNext htrigger
  have hshift : fallbackShift <= baseShift := by
    dsimp only [fallbackShift, baseShift]
    push_cast
    have hpairQ :
        (c.order ⟨i.val - 3, by omega⟩ : ℚ) +
            c.order ⟨i.val - 2, by omega⟩ <
          a.order ⟨i.val, i.lt_large⟩ +
            a.order ⟨i.val + 1, hiNext⟩ := by
      exact_mod_cast hpair
    linarith
  have hfallback := a.sectionFourLowPair_currentAlpha_le_fallback
    b c hlocal i hiNext htrigger hlow
  have hfallback' : a.representationAlpha c (i.current i.lt_large.le) <=
      (fallbackShift : WithTop ℚ) + b.representationAlpha c i.previous := by
    simpa only [currentFallbackBound, fallbackShift,
      CentralRepresentationIndex.current, CentralRepresentationIndex.previous,
      previousRepresentationIndex, Nat.sub_sub, one_add_one_eq_two] using hfallback
  have hmiddle : b.representationAlpha c i.previous <= middleDefect := by
    have hcondition := hlocal.hbcDefect i.previous
    rw [b.coe_representationAlphaValue c i.previous] at hcondition
    simpa only [middleDefect, CentralRepresentationIndex.previous] using hcondition
  change a.representationAlpha c (i.current i.lt_large.le) <=
    (outerShift : WithTop ℚ) + _
  by_cases hdefects : middleDefect <= primaryDefect
  · calc
      a.representationAlpha c (i.current i.lt_large.le) <=
          (fallbackShift : WithTop ℚ) +
            b.representationAlpha c i.previous := hfallback'
      _ <= (fallbackShift : WithTop ℚ) + middleDefect :=
        add_le_add_right hmiddle _
      _ <= (baseShift : WithTop ℚ) + primaryDefect :=
        add_le_add (by exact_mod_cast hshift) hdefects
      _ = (outerShift : WithTop ℚ) +
          b.representationPrimaryDefect c
            (centralPreviousPreviousIndex i hiTwo) := hprimaryForm.symm
  · have hstrict : primaryDefect < middleDefect := lt_of_not_ge hdefects
    have htriangle : primaryDefect = adjacentDefect := by
      exact b.truncatedPrefixDefect_neg_eq_neg_of_lt_pos c c
        (i.val - 1) (i.val - 3) (i.val - 1) (by
          simpa only [primaryDefect, middleDefect] using hstrict)
    let p : Fin n := ⟨i.val - 3, by omega⟩
    have htargetCap :=
      (a.representationAlpha_le_prime c (i.current i.lt_large.le)).trans
        (a.representationAlphaPrime_le_secondaryRightCap c
          (i.current i.lt_large.le) ⟨i.one_lt, hiNext⟩)
    have htargetCap' :
        a.representationAlpha c (i.current i.lt_large.le) <=
          (targetCapShift : WithTop ℚ) + (c.alphaValue p : WithTop ℚ) := by
      simp only [CentralRepresentationIndex.current] at htargetCap
      rw [c.prefixAlphaCap_of_internal (i := i.val - 2) (by omega) (by omega)]
        at htargetCap
      have hp :
          (⟨i.val - 2 - 1, by omega⟩ : Fin n) = p := by
        apply Fin.ext
        dsimp only [p]
        omega
      simpa only [targetCapShift, CentralRepresentationIndex.current, hp]
        using htargetCap
    have hadjacent := c.order_sub_add_alpha_le_cappedAdjacent p
    have hpCast : p.castSucc =
        (⟨i.val - 3, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hpSucc : p.succ =
        (⟨i.val - 2, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      change p.val + 1 = i.val - 2
      dsimp only [p]
      have := hiTwo
      omega
    have htargetAdjacent :
        a.representationAlpha c (i.current i.lt_large.le) <=
          (baseShift : WithTop ℚ) + adjacentDefect := by
      calc
        a.representationAlpha c (i.current i.lt_large.le) <=
            (targetCapShift : WithTop ℚ) +
              (c.alphaValue p : WithTop ℚ) := htargetCap'
        _ = (baseShift : WithTop ℚ) +
            (((((c.order p.castSucc - c.order p.succ : Int) : ℚ) +
                c.alphaValue p : ℚ)) : WithTop ℚ) := by
          rw [hpCast, hpSucc]
          dsimp only [targetCapShift, baseShift]
          norm_cast
          push_cast
          ring
        _ <= (baseShift : WithTop ℚ) + adjacentDefect := by
          apply add_le_add_right
          have hpTwo : p.val + 2 = i.val - 1 := by
            dsimp only [p]
            omega
          simpa only [adjacentDefect, p, hpTwo] using hadjacent
    calc
      a.representationAlpha c (i.current i.lt_large.le) <=
          (baseShift : WithTop ℚ) + adjacentDefect := htargetAdjacent
      _ = (baseShift : WithTop ℚ) + primaryDefect := by rw [htriangle]
      _ = (outerShift : WithTop ℚ) +
          b.representationPrimaryDefect c
            (centralPreviousPreviousIndex i hiTwo) := hprimaryForm.symm

/-- Lines 2490--2494: the current-secondary candidate of `B_(i-2)` is
also at least `C_i`.  The primary upper bound for `B_(i-1)` supplies its
defect term, and essentiality plus two-step monotonicity gives the remaining
strict order shift. -/
theorem sectionFourLowPair_currentAlpha_le_previousCurrent
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hlocal : SectionFourLocalConditions a b c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiThree : 3 < i.val) (hiNext : i.val + 1 < n + 1)
    (htrigger : a.centralAlphaTrigger c i)
    (hlow :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ <=
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩) :
    let hiTwo : 2 < i.val := by omega
    let pp := centralPreviousPreviousIndex i hiTwo
    let hppInterior : 1 < pp.val ∧ pp.val + 1 < n + 1 := by
      dsimp only [pp, centralPreviousPreviousIndex]
      have := i.lt_large
      omega
    a.representationAlpha c (i.current i.lt_large.le) <=
      ((((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ -
        b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
        c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)) :
          WithTop ℚ) +
        b.representationSecondaryCurrentDefect c pp hppInterior := by
  dsimp only
  let hiTwo : 2 < i.val := by omega
  let pp := centralPreviousPreviousIndex i hiTwo
  let hppInterior : 1 < pp.val ∧ pp.val + 1 < n + 1 := by
    dsimp only [pp, centralPreviousPreviousIndex]
    have := i.lt_large
    omega
  let outerShift : ℚ := ((a.order ⟨i.val, i.lt_large⟩ +
    a.order ⟨i.val + 1, hiNext⟩ -
    b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
    c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let fallbackShift : ℚ := ((c.order ⟨i.val - 2, by
      have := i.lt_large
      omega⟩ - c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let middleBase : ℚ := ((b.order ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ - c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let candidateBase : ℚ := ((a.order ⟨i.val, i.lt_large⟩ +
    a.order ⟨i.val + 1, hiNext⟩ +
    b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ -
    c.order ⟨i.val - 4, by have := i.lt_large; omega⟩ -
    c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ -
    c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let defect := b.truncatedPrefixDefect c (-1) i.val (i.val - 2)
  have hmiddleForm :
      (fallbackShift : WithTop ℚ) +
          b.representationPrimaryDefect c i.previous =
        (middleBase : WithTop ℚ) + defect := by
    rw [b.representationPrimaryDefect_previous_eq c i]
    dsimp only [fallbackShift, middleBase, defect]
    unfold centralPreviousDefect
    rw [← add_assoc]
    congr 1
    norm_cast
    push_cast
    ring
  have hppSecondary :
      b.representationSecondaryCurrentDefect c pp hppInterior =
        ((((b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ +
          b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ -
          c.order ⟨i.val - 4, by have := i.lt_large; omega⟩ -
          c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ : Int) : ℚ)) :
            WithTop ℚ) + defect := by
    unfold representationSecondaryCurrentDefect
    have hbCurrent :
        (⟨pp.val, pp.lt_large⟩ : Fin (n + 1)) =
          ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
      apply Fin.ext
      rfl
    have hbNext :
        (⟨pp.val + 1, hppInterior.2⟩ : Fin (n + 1)) =
          ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
      apply Fin.ext
      change i.val - 2 + 1 = i.val - 1
      omega
    have hcTwoPrevious :
        (⟨pp.val - 2, by have := pp.le_small; omega⟩ : Fin (n + 1)) =
          ⟨i.val - 4, by have := i.lt_large; omega⟩ := by
      apply Fin.ext
      change i.val - 2 - 2 = i.val - 4
      omega
    have hcPrevious :
        (⟨pp.val - 1, by have := pp.le_small; omega⟩ : Fin (n + 1)) =
          ⟨i.val - 3, by have := i.lt_large; omega⟩ := by
      apply Fin.ext
      change i.val - 2 - 1 = i.val - 3
      omega
    rw [hbCurrent, hbNext, hcTwoPrevious, hcPrevious]
    change _ + b.truncatedPrefixDefect c (-1)
      (i.val - 2 + 2) (i.val - 2) = _
    have hdefectLeft : i.val - 2 + 2 = i.val := by omega
    rw [hdefectLeft]
  have hcTwoStep :
      c.order ⟨i.val - 4, by have := i.lt_large; omega⟩ <=
        c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
    have h := c.orderSequence.twoStep (i.val - 4) (by omega)
    change c.order ⟨i.val - 4, by omega⟩ <=
      c.order ⟨i.val - 4 + 2, by omega⟩ at h
    have hindex : i.val - 4 + 2 = i.val - 2 := by omega
    simpa only [hindex] using h
  have hessential := a.sectionFourLowPair_targetPreviousPair_lt_sourceCurrentPair
    c i (by omega) hiNext htrigger
  have hbase : middleBase <= candidateBase := by
    dsimp only [middleBase, candidateBase]
    push_cast
    have htwoQ :
        (c.order ⟨i.val - 4, by have := i.lt_large; omega⟩ : ℚ) <=
          (c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : ℚ) := by
      exact_mod_cast hcTwoStep
    have hessentialQ :
        (c.order ⟨i.val - 3, by omega⟩ : ℚ) +
            c.order ⟨i.val - 2, by omega⟩ <
          a.order ⟨i.val, i.lt_large⟩ +
            a.order ⟨i.val + 1, hiNext⟩ := by
      exact_mod_cast hessential
    linarith
  have hfallback := a.sectionFourLowPair_currentAlpha_le_fallback
    b c hlocal i hiNext htrigger hlow
  have hfallback' : a.representationAlpha c (i.current i.lt_large.le) <=
      (fallbackShift : WithTop ℚ) + b.representationAlpha c i.previous := by
    simpa only [currentFallbackBound, fallbackShift,
      CentralRepresentationIndex.current, CentralRepresentationIndex.previous,
      previousRepresentationIndex, Nat.sub_sub, one_add_one_eq_two] using hfallback
  have hmiddlePrimary := b.representationAlpha_le_primary c i.previous
  change a.representationAlpha c (i.current i.lt_large.le) <=
    (outerShift : WithTop ℚ) +
      b.representationSecondaryCurrentDefect c pp hppInterior
  calc
    a.representationAlpha c (i.current i.lt_large.le) <=
        (fallbackShift : WithTop ℚ) +
          b.representationAlpha c i.previous := hfallback'
    _ <= (fallbackShift : WithTop ℚ) +
          b.representationPrimaryDefect c i.previous :=
      add_le_add_right hmiddlePrimary _
    _ = (middleBase : WithTop ℚ) + defect := hmiddleForm
    _ <= (candidateBase : WithTop ℚ) + defect :=
      add_le_add_left (by exact_mod_cast hbase) _
    _ = (outerShift : WithTop ℚ) +
        b.representationSecondaryCurrentDefect c pp hppInterior := by
      rw [hppSecondary]
      dsimp only [candidateBase, outerShift]
      rw [← add_assoc]
      congr 1
      norm_cast
      push_cast
      ring

/-- Lines 2481--2494, assembled: under the low outer-pair hypothesis, the
current target invariant is bounded by the common shift plus `B_(i-2)`.
The proof expands `B_(i-2)` into its half-gap and prime parts; internally the
prime part expands once more into its primary and current-secondary parts. -/
theorem sectionFourLowPair_currentAlpha_le_shiftedPreviousAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hlocal : SectionFourLocalConditions a b c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiTwo : 2 < i.val) (hiNext : i.val + 1 < n + 1)
    (htrigger : a.centralAlphaTrigger c i)
    (hlow :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ <=
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩) :
    a.representationAlpha c (i.current i.lt_large.le) <=
      ((((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ -
        b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
        c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)) :
          WithTop ℚ) +
        b.representationAlpha c (centralPreviousPreviousIndex i hiTwo) := by
  let shift : ℚ := ((a.order ⟨i.val, i.lt_large⟩ +
    a.order ⟨i.val + 1, hiNext⟩ -
    b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
    c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let pp := centralPreviousPreviousIndex i hiTwo
  have hprevious := a.sectionFourLowPair_middlePrevious_le_targetPrevious
    b c hlocal i hiNext htrigger hlow
  have hhalf := a.sectionFourLowPair_currentAlpha_lt_previousHalfGap
    b c i hiTwo hiNext htrigger hprevious
  have hprimary := a.sectionFourLowPair_currentAlpha_le_previousPrimary
    b c hlocal i hiTwo hiNext htrigger hlow
  change a.representationAlpha c (i.current i.lt_large.le) <=
    (shift : WithTop ℚ) + b.representationAlpha c pp
  rw [b.representationAlpha_eq_min_halfGap_prime c pp]
  apply withTop_le_shift_add_min
  · simpa only [shift, pp] using hhalf.le
  · by_cases hiThree : i.val = 3
    · have hnotInterior : ¬(1 < pp.val ∧ pp.val + 1 < n + 1) := by
        dsimp only [pp, centralPreviousPreviousIndex]
        omega
      rw [b.representationAlphaPrime_eq_primary_of_not_interior
        c pp hnotInterior]
      simpa only [shift, pp] using hprimary
    · have hiThree' : 3 < i.val := by omega
      have hppInterior : 1 < pp.val ∧ pp.val + 1 < n + 1 := by
        dsimp only [pp, centralPreviousPreviousIndex]
        have := i.lt_large
        omega
      have hcrossRaw := a.sectionFourLowPair_targetTwoPrevious_lt_middleCurrent
        b c i hiTwo hiNext htrigger hlow
      have hcross :
          c.order ⟨pp.val - 1, by have := pp.le_small; omega⟩ <=
            b.order ⟨pp.val + 1, hppInterior.2⟩ := by
        have hcIndex :
            (⟨pp.val - 1, by have := pp.le_small; omega⟩ : Fin (n + 1)) =
              ⟨i.val - 3, by have := i.lt_large; omega⟩ := by
          apply Fin.ext
          dsimp only [pp, centralPreviousPreviousIndex]
          omega
        have hbIndex :
            (⟨pp.val + 1, hppInterior.2⟩ : Fin (n + 1)) =
              ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
          apply Fin.ext
          dsimp only [pp, centralPreviousPreviousIndex]
          omega
        rw [hcIndex, hbIndex]
        exact hcrossRaw.le
      rw [b.representationAlphaPrime_eq_min_primary_current
        c pp hppInterior hcross]
      apply withTop_le_shift_add_min
      · simpa only [shift, pp] using hprimary
      · have hcurrent := a.sectionFourLowPair_currentAlpha_le_previousCurrent
          b c hlocal i hiThree' hiNext htrigger hlow
        simpa only [shift, pp] using hcurrent

/-- Lines 2470--2495: the secondary realization of `A'_i` cannot make the
first comparison fail in the low outer-pair case.  The strict defect triangle
identifies its source-to-middle defect with the middle-to-target defect; the
ordinary defect condition then inserts `B_(i-2)`, contradicting the assembled
candidate bound above. -/
theorem sectionFourLowPair_secondary_impossible
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hlocal : SectionFourLocalConditions a b c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1)
    (htrigger : a.centralAlphaTrigger c i)
    (hlow :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ <=
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩)
    (hsecondary :
      a.representationAlphaPrime b (i.current i.lt_large.le) =
        a.representationSecondaryDefect b (i.current i.lt_large.le)
          ⟨i.one_lt, hiNext⟩)
    (hnotFirst :
      ¬((((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.representationAlpha c (i.current i.lt_large.le) <=
          (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.representationAlphaPrime b (i.current i.lt_large.le))) : False := by
  have hprevious := a.sectionFourLowPair_middlePrevious_le_targetPrevious
    b c hlocal i hiNext htrigger hlow
  have hdefect := a.sectionFourLowPair_secondaryDefect_lt_targetDefect
    b c i hiNext hprevious hsecondary hnotFirst
  by_cases hiTwoEq : i.val = 2
  · exact a.sectionFourLowPair_secondary_impossible_of_eq_two
      b c i hiNext hiTwoEq hdefect
  · have hiTwo : 2 < i.val := by
      have := i.one_lt
      omega
    let pp := centralPreviousPreviousIndex i hiTwo
    let shift : ℚ := ((a.order ⟨i.val, i.lt_large⟩ +
      a.order ⟨i.val + 1, hiNext⟩ -
      b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
      c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
    let sourceDefect :=
      a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2)
    have htriangle : sourceDefect =
        b.truncatedPrefixDefect c 1 (i.val - 2) (i.val - 2) := by
      exact a.truncatedPrefixDefect_eq_middle_of_lt_composite
        b c 1 1 (by simp) (by simp) (i.val + 2) (i.val - 2)
          (i.val - 2) (by simpa only [one_mul, sourceDefect] using hdefect)
    have hmiddle : b.representationAlpha c pp <=
        b.truncatedPrefixDefect c 1 (i.val - 2) (i.val - 2) := by
      have hcondition := hlocal.hbcDefect pp
      rw [b.coe_representationAlphaValue c pp] at hcondition
      simpa only [pp, centralPreviousPreviousIndex] using hcondition
    have hinsert : (shift : WithTop ℚ) + b.representationAlpha c pp <=
        (shift : WithTop ℚ) + sourceDefect := by
      rw [htriangle]
      exact add_le_add_right hmiddle _
    have hassembled :=
      a.sectionFourLowPair_currentAlpha_le_shiftedPreviousAlpha
        b c hlocal i hiTwo hiNext htrigger hlow
    have hsourceStrict := a.sectionFourLowPair_secondaryShift_lt_currentAlpha
      b c i hiNext hsecondary hnotFirst
    have hle : a.representationAlpha c (i.current i.lt_large.le) <=
        (shift : WithTop ℚ) + sourceDefect := by
      have hassembled' :
          a.representationAlpha c (i.current i.lt_large.le) <=
            (shift : WithTop ℚ) + b.representationAlpha c pp := by
        simpa only [shift, pp] using hassembled
      exact hassembled'.trans hinsert
    exact (not_lt_of_ge hle) (by
      simpa only [shift, sourceDefect] using hsourceStrict)

/-- Lemma 4.3(a) in the low outer-pair branch.  Definition 5 leaves two
possible realizations of `A'_i`: its primary candidate gives the comparison
by the primary shifted bound, while its secondary candidate is excluded by
the preceding strict-triangle argument. -/
theorem sectionFourForwardFirst_of_lowPair
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hlocal : SectionFourLocalConditions a b c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1)
    (htrigger : a.centralAlphaTrigger c i)
    (hlow :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ <=
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩) :
    (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.representationAlpha c (i.current i.lt_large.le) <=
      (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.representationAlphaPrime b (i.current i.lt_large.le) := by
  by_contra hnotFirst
  let current : RepresentationIndex (n + 1) (n + 1) :=
    i.current i.lt_large.le
  let hinterior : 1 < current.val ∧ current.val + 1 < n + 1 := by
    dsimp only [current, CentralRepresentationIndex.current]
    exact ⟨i.one_lt, hiNext⟩
  have hnormal := a.representationAlphaPrime_eq_min_primary_secondary
    b current hinterior
  rcases min_choice (a.representationPrimaryDefect b current)
      (a.representationSecondaryDefect b current hinterior) with
    hprimaryChoice | hsecondaryChoice
  · have hprimary :
        a.representationAlphaPrime b (i.current i.lt_large.le) =
          a.representationPrimaryDefect b (i.current i.lt_large.le) := by
      simpa only [current] using hnormal.trans hprimaryChoice
    have hbound := a.sectionFourLowPair_currentAlpha_le_primaryShift
      b c hlocal i hiNext htrigger hlow
    apply hnotFirst
    rw [hprimary]
    unfold representationPrimaryDefect CentralRepresentationIndex.current
    calc
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) <=
        (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          (((((a.order ⟨i.val, i.lt_large⟩ -
            c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)) :
              WithTop ℚ) +
            a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1)) :=
        add_le_add_right hbound _
      _ = (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            (((((a.order ⟨i.val, i.lt_large⟩ -
              b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)) :
                WithTop ℚ) +
              a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1)) := by
        rw [← add_assoc, ← add_assoc]
        congr 1
        norm_cast
        ring
  · have hsecondary :
        a.representationAlphaPrime b (i.current i.lt_large.le) =
          a.representationSecondaryDefect b (i.current i.lt_large.le)
            ⟨i.one_lt, hiNext⟩ := by
      simpa only [current, hinterior] using hnormal.trans hsecondaryChoice
    exact (a.sectionFourLowPair_secondary_impossible
      b c hlocal i hiNext htrigger hlow hsecondary hnotFirst).elim

/-- Lines 2497--2499: if the low outer-pair inequality fails, condition
2.1(i) for `(b,c)` and essentiality force the source middle pair itself to be
strictly below the outer source pair. -/
theorem sectionFourHighMiddlePair_of_not_lowPair
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hlocal : SectionFourLocalConditions a b c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1)
    (htrigger : a.centralAlphaTrigger c i)
    (hnotLow :
      ¬(a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ <=
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩)) :
    b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ +
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ <
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ := by
  let k : Fin (n + 1) := ⟨i.val - 2, by have := i.lt_large; omega⟩
  have hstrict :
      b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <
        a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ :=
    lt_of_not_ge hnotLow
  rcases hlocal.hbcOrder k with hcurrent | ⟨hkPos, hkNext, hpair⟩
  · have hcurrent' :
        b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <=
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
      simpa only [k] using hcurrent
    omega
  · have hiTwo : 2 < i.val := by
      dsimp only [k] at hkPos
      omega
    have hessential :=
      a.sectionFourLowPair_targetPreviousPair_lt_sourceCurrentPair
        c i hiTwo hiNext htrigger
    have hpair' :
        b.order ⟨i.val - 2, by omega⟩ +
            b.order ⟨i.val - 1, by omega⟩ <=
          c.order ⟨i.val - 3, by omega⟩ +
            c.order ⟨i.val - 2, by omega⟩ := by
      have hkSucc :
          (⟨k.val + 1, hkNext⟩ : Fin (n + 1)) =
            ⟨i.val - 1, by omega⟩ := by
        apply Fin.ext
        change k.val + 1 = i.val - 1
        dsimp only [k]
        omega
      have hcPrevious :
          (⟨k.val - 1, by omega⟩ : Fin (n + 1)) =
            ⟨i.val - 3, by omega⟩ := by
        apply Fin.ext
        change k.val - 1 = i.val - 3
        dsimp only [k]
        omega
      simpa only [k, hkSucc, hcPrevious] using hpair
    omega

/-- Lemma 4.3 in the equality branch `A_i=A'_i`, with its low-pair,
high-pair, and terminal cases assembled. -/
theorem sectionFourForwardComparison_of_current_eq_prime_of_localConditions
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hlocal : SectionFourLocalConditions a b c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (heqAB : a.representationAlpha b (i.current i.lt_large.le) =
      a.representationAlphaPrime b (i.current i.lt_large.le)) :
    SectionFourForwardComparison a b c i := by
  by_cases hiNext : i.val + 1 < n + 1
  · by_cases hlow :
        a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ <=
          b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
            c.order ⟨i.val - 2, by have := i.lt_large; omega⟩
    · exact Or.inl (a.sectionFourForwardFirst_of_lowPair
        b c hlocal i hiNext htrigger hlow)
    · have hpair := a.sectionFourHighMiddlePair_of_not_lowPair
        b c hlocal i hiNext htrigger hlow
      exact a.sectionFourForwardComparison_of_current_eq_prime_highPair
        b c hlocal i hiNext htrigger heqAB hpair
  · exact a.sectionFourForwardComparison_of_terminal b c hlocal i hiNext

/-- Full representation conditions imply the local hypotheses used by the
equality branch of Lemma 4.3. -/
theorem sectionFourForwardComparison_of_current_eq_prime
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (heqAB : a.representationAlpha b (i.current i.lt_large.le) =
      a.representationAlphaPrime b (i.current i.lt_large.le)) :
    SectionFourForwardComparison a b c i := by
  exact a.sectionFourForwardComparison_of_current_eq_prime_of_localConditions
    b c (SectionFourLocalConditions.ofRepresentationConditions
      a b c hab hbc) i htrigger heqAB
end BONG.GoodBONG

end Bong
