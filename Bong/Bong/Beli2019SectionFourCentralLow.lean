/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourCentralComparison

/-!
# Beli (2019), Lemma 4.3: the low outer-pair branch

This file formalizes the paragraph on lines 2459--2495.  Its hypothesis is

`R_(i+1) + R_(i+2) <= S_i + T_(i-1)`.

The proof first extracts the preceding order comparison and the fallback
half of Lemma 4.2(ii).  It then treats the primary and secondary candidates
of `A'_i` separately.
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

/-- Lines 2459--2462.  Essentiality gives
`T_(i-2)+T_(i-1)<R_(i+1)+R_(i+2)`.  Together with the low-pair hypothesis,
condition 2.1(i) for `(b,c)` forces `S_(i-1) <= T_(i-1)`.  The endpoint
`i=2` is included because the second alternative of condition 2.1(i) is
then impossible. -/
theorem sectionFourLowPair_middlePrevious_le_targetPrevious
    [Beli2006AlphaLaws.{u, v} K]
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
    b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <=
      c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
  let k : Fin (n + 1) := ⟨i.val - 2, by have := i.lt_large; omega⟩
  rcases hlocal.hbcOrder k with hcurrent | ⟨hkPos, hkNext, hpair⟩
  · simpa only [k] using hcurrent
  · have hiTwo : 2 < i.val := by
      dsimp only [k] at hkPos
      omega
    have hessential := a.isEssentialFor_of_centralAlphaTrigger c i htrigger
    have hessentialRaw := hessential.2 (by
      change 1 < i.val - 1
      omega) (by
      change i.val - 1 + 2 < n + 1
      omega)
    simp only [orderSequence_at] at hessentialRaw
    have hessentialPair :
        c.order ⟨i.val - 3, by omega⟩ +
            c.order ⟨i.val - 2, by omega⟩ <
          a.order ⟨i.val, i.lt_large⟩ +
            a.order ⟨i.val + 1, hiNext⟩ := by
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
      simpa only [hcLeft, hcRight, haCurrent, haNext] using hessentialRaw
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

/-- Lines 2462--2463.  The low-pair inequality is precisely the negation of
the direct test in Lemma 4.2(ii), so the current target alpha is bounded by
`T_(i-1)-T_i+B_(i-1)`. -/
theorem sectionFourLowPair_currentAlpha_le_fallback
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
    a.representationAlpha c (i.current i.lt_large.le) <=
      a.currentFallbackBound b c (i.current i.lt_large.le) i.one_lt := by
  have hfailure :
      ¬a.KeyLemmaRightDirectTrigger b c
        (currentEssentialIndex (i.current i.lt_large.le)) := by
    intro hdirect
    have hstrict := hdirect (by
      simp only [currentEssentialIndex, CentralRepresentationIndex.current]
      change 0 < i.val - 1
      have := i.one_lt
      omega) (by
      simp only [currentEssentialIndex, CentralRepresentationIndex.current]
      change i.val - 1 + 2 < n + 1
      have hval : i.val - 1 + 2 = i.val + 1 := by
        have := i.one_lt
        omega
      simpa only [hval] using hiNext)
    simp only [currentEssentialIndex, CentralRepresentationIndex.current] at hstrict
    have hcPrevious :
        (⟨i.val - 1 - 1, by omega⟩ : Fin (n + 1)) =
          ⟨i.val - 2, by omega⟩ := by
      apply Fin.ext
      change i.val - 1 - 1 = i.val - 2
      omega
    have haNext :
        (⟨i.val - 1 + 2, by
          have := i.one_lt
          have := hiNext
          omega⟩ : Fin (n + 1)) =
          ⟨i.val + 1, hiNext⟩ := by
      apply Fin.ext
      change i.val - 1 + 2 = i.val + 1
      have := i.one_lt
      omega
    have hstrict' :
        b.order ⟨i.val - 1, by omega⟩ + c.order ⟨i.val - 2, by omega⟩ <
          a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ := by
      simpa only [hcPrevious, haNext, Nat.sub_add_cancel i.one_lt.le]
        using hstrict
    exact (not_lt_of_ge hlow) hstrict'
  obtain ⟨hprev, hbound⟩ :=
    (a.sectionFourCurrentBounds_of_centralAlphaTrigger
      b c hlocal i htrigger).2 hfailure
  simpa only [CentralRepresentationIndex.current] using hbound

/-- Lines 2466--2469.  The primary candidate in `S_i+A'_i` is at least
`T_i+C_i`.  Otherwise its source-to-middle defect is strictly below the
source-to-target defect; the strict capped triangle identifies it with the
middle-to-target defect, contradicting the fallback bound and
`R_(i+1)>T_(i-1)`. -/
theorem sectionFourLowPair_currentAlpha_le_primaryShift
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
    a.representationAlpha c (i.current i.lt_large.le) <=
      ((((a.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)) :
          WithTop ℚ) +
        a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) := by
  let sourceShift : ℚ := ((a.order ⟨i.val, i.lt_large⟩ -
    c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let fallbackShift : ℚ := ((c.order ⟨i.val - 2, by
      have := i.lt_large
      omega⟩ - c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let sourceDefect :=
    a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1)
  let targetDefect :=
    a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)
  let middleDefect :=
    b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1)
  have htarget : a.representationAlpha c (i.current i.lt_large.le) <=
      (sourceShift : WithTop ℚ) + targetDefect := by
    simpa only [sourceShift, targetDefect, representationPrimaryDefect,
      CentralRepresentationIndex.current] using
        a.representationAlpha_le_primary c (i.current i.lt_large.le)
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
  by_contra hnot
  have hsourceStrict : (sourceShift : WithTop ℚ) + sourceDefect <
      a.representationAlpha c (i.current i.lt_large.le) :=
    lt_of_not_ge hnot
  have hdefect : sourceDefect < targetDefect := by
    apply (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp
    exact hsourceStrict.trans_le htarget
  have htriangle : sourceDefect = middleDefect := by
    exact a.truncatedPrefixDefect_neg_eq_pos_of_lt_neg b c
      (i.val + 1) (i.val - 1) (i.val - 1) (by
        simpa only [sourceDefect, targetDefect] using hdefect)
  have hshift : fallbackShift < sourceShift := by
    dsimp only [fallbackShift, sourceShift]
    push_cast
    have hcrossQ :
        (c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : ℚ) <
          (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
      exact_mod_cast htrigger.1
    linarith
  have hmiddleFinite : b.representationAlpha c i.previous ≠ ⊤ :=
    b.representationAlpha_ne_top c i.previous
  have hcontradiction :
      a.representationAlpha c (i.current i.lt_large.le) <
        (sourceShift : WithTop ℚ) + sourceDefect := by
    calc
      a.representationAlpha c (i.current i.lt_large.le) <=
          (fallbackShift : WithTop ℚ) +
            b.representationAlpha c i.previous := hfallback'
      _ < (sourceShift : WithTop ℚ) +
            b.representationAlpha c i.previous :=
        WithTop.add_lt_add_right hmiddleFinite (by exact_mod_cast hshift)
      _ <= (sourceShift : WithTop ℚ) + middleDefect :=
        add_le_add_right hmiddle _
      _ = (sourceShift : WithTop ℚ) + sourceDefect := by rw [htriangle]
  exact (not_lt_of_ge hsourceStrict.le) hcontradiction

/-! ## The secondary candidate -/

/-- Lines 2470--2474.  If the secondary candidate realizes `A'_i` while
the first conclusion of Lemma 4.3 fails, then the positive source-to-middle
prefix defect is strictly smaller than the corresponding source-to-target
defect.  The only order input needed here is `S_(i-1) <= T_(i-1)`. -/
theorem sectionFourLowPair_secondaryDefect_lt_targetDefect
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1)
    (hprevious :
      b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <=
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
            a.representationAlphaPrime b (i.current i.lt_large.le))) :
    a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) <
      a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) := by
  let commonShift : ℚ := ((a.order ⟨i.val, i.lt_large⟩ +
    a.order ⟨i.val + 1, hiNext⟩ -
    b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
    c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let targetShift : ℚ := ((a.order ⟨i.val, i.lt_large⟩ +
    a.order ⟨i.val + 1, hiNext⟩ -
    c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
    c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let sourceDefect :=
    a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2)
  let targetDefect :=
    a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2)
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
  have hsourceStrict : (commonShift : WithTop ℚ) + sourceDefect <
      a.representationAlpha c (i.current i.lt_large.le) := by
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
  have htarget : a.representationAlpha c (i.current i.lt_large.le) <=
      (targetShift : WithTop ℚ) + targetDefect := by
    simpa only [targetShift, targetDefect, representationSecondaryDefect,
      CentralRepresentationIndex.current] using
        a.representationAlpha_le_secondary c (i.current i.lt_large.le)
          ⟨i.one_lt, hiNext⟩
  have hshift : targetShift <= commonShift := by
    dsimp only [targetShift, commonShift]
    push_cast
    have hpreviousQ :
        (b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : ℚ) <=
          (c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : ℚ) := by
      exact_mod_cast hprevious
    linarith
  have hshifted : (commonShift : WithTop ℚ) + sourceDefect <
      (commonShift : WithTop ℚ) + targetDefect := by
    calc
      (commonShift : WithTop ℚ) + sourceDefect <
          a.representationAlpha c (i.current i.lt_large.le) := hsourceStrict
      _ <= (targetShift : WithTop ℚ) + targetDefect := htarget
      _ <= (commonShift : WithTop ℚ) + targetDefect :=
        add_le_add (by exact_mod_cast hshift) le_rfl
  exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hshifted

/-- At the endpoint `i=2`, the comparison defect produced by the strict
triangle is `d[1]=top`; this contradicts the strict inequality above.  This
is the endpoint convention implicit in the paper's notation `B_(i-2)`. -/
theorem sectionFourLowPair_secondary_impossible_of_eq_two
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1)
    (hi : i.val = 2)
    (hdefect :
      a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) <
        a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2)) : False := by
  have htriangle := a.truncatedPrefixDefect_eq_middle_of_lt_composite
    b c 1 1 (by simp) (by simp) (i.val + 2) (i.val - 2) (i.val - 2)
      (by simpa only [one_mul] using hdefect)
  have htop : b.truncatedPrefixDefect c 1 (i.val - 2) (i.val - 2) = ⊤ := by
    rw [hi]
    norm_num [truncatedPrefixDefect, GoodBONG.prefixProduct,
      BONG.prefixProduct_zero, defectOrder_one, prefixAlphaCap_zero]
  have hsourceTop :
      a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) = ⊤ :=
    htriangle.trans htop
  rw [hsourceTop] at hdefect
  exact (not_lt_of_ge le_top) hdefect

end BONG.GoodBONG

end Bong
