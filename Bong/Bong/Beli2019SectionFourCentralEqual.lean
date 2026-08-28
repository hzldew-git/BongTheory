/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourCentralAsymmetric

/-!
# Beli (2019), Section 4: both central alphas are primed

This file formalizes case (d), the final and longest central case in the
proof of Theorem 2.1(iii).
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

/-! ## Negations of the two Lemma 4.2 direct tests -/

/-- Failure of the left direct test is the first low-pair inequality in the
last paragraph of Section 4. -/
theorem sectionFourLeftLow_of_not_direct
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hnot : ¬a.KeyLemmaLeftDirectTrigger b c
      (nextEssentialIndex i.previous)) :
    ∃ hiPrev : 2 < i.val,
      a.order ⟨i.val, i.lt_large⟩ +
          b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ ≤
        c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ +
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
  unfold KeyLemmaLeftDirectTrigger at hnot
  push Not at hnot
  rcases hnot with ⟨hiTwo, hiNext, hlow⟩
  have hiPrev : 2 < i.val := by
    simp only [nextEssentialIndex, CentralRepresentationIndex.previous] at hiTwo
    omega
  refine ⟨hiPrev, ?_⟩
  have hleft : i.val - 1 - 2 = i.val - 3 := by omega
  have hright : i.val - 1 - 1 = i.val - 2 := by omega
  have hnext : i.val - 1 + 1 = i.val := by omega
  simp only [nextEssentialIndex, CentralRepresentationIndex.previous,
    hleft, hright, hnext] at hlow
  exact hlow

/-- Failure of the right direct test is the second low-pair inequality in
the last paragraph of Section 4. -/
theorem sectionFourRightLow_of_not_direct
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hnot : ¬a.KeyLemmaRightDirectTrigger b c
      (currentEssentialIndex (i.current i.lt_large.le))) :
    ∃ hiNext : i.val + 1 < n + 1,
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ ≤
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
  unfold KeyLemmaRightDirectTrigger at hnot
  push Not at hnot
  rcases hnot with ⟨hiPos, hiTwo, hlow⟩
  have hiNext : i.val + 1 < n + 1 := by
    change i.val - 1 + 2 < n + 1 at hiTwo
    have := i.one_lt
    omega
  refine ⟨hiNext, ?_⟩
  have hprevious : i.val - 1 - 1 = i.val - 2 := by omega
  have hcurrent : i.val - 1 + 1 = i.val := by
    have := i.one_lt
    omega
  have hnext : i.val - 1 + 2 = i.val + 1 := by
    have := i.one_lt
    omega
  simp only [currentEssentialIndex, CentralRepresentationIndex.current,
    hprevious, hcurrent, hnext] at hlow
  exact hlow

/-! ## The two "moreover" clauses of Lemma 4.3 and Corollary 4.4 -/

/-- The low left pair forces the first alternative of Corollary 4.4.  This
is the reverse-dual of the already proved low-pair clause of Lemma 4.3. -/
theorem sectionFourBackwardFirst_of_leftLow
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hlocal : SectionFourLocalConditions a b c)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hiPrev : 2 < i.val)
    (hlow :
      a.order ⟨i.val, i.lt_large⟩ +
          b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ ≤
        c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ +
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩) :
    ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
          ℚ) : WithTop ℚ) + a.representationAlpha c i.previous ≤
      ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
          ℚ) : WithTop ℚ) + b.representationAlphaPrime c i.previous := by
  rcases a.exists_sectionFourReverseDualTriple b c with
    ⟨aDual, bDual, cDual, haOrders, hbOrders, hcOrders,
      habAlpha, hacAlpha, hbcAlpha, habDefect, hbcDefect⟩
  let j := i.reversePrevious
  have hdualLocal : SectionFourLocalConditions cDual bDual aDual := by
    exact {
      habOrder := b.representationOrderCondition_reverseDual_swap
        c bDual cDual hbOrders hcOrders hlocal.hbcOrder
      habDefect := b.representationDefectCondition_reverseDual_swap
        c bDual cDual hbOrders hcOrders hbcDefect hlocal.hbcDefect
      hbcOrder := a.representationOrderCondition_reverseDual_swap
        b aDual bDual haOrders hbOrders hlocal.habOrder
      hbcDefect := a.representationDefectCondition_reverseDual_swap
        b aDual bDual haOrders hbOrders habDefect hlocal.habDefect }
  have hdualTrigger : cDual.centralAlphaTrigger aDual j := by
    simpa only [j] using a.centralAlphaTrigger_reverseDual_swap
      c aDual cDual haOrders hcOrders hacAlpha i htrigger
  have hCurrentIndex :
      j.current j.lt_large.le = i.previous.reverse := by
    simpa only [j] using i.reversePrevious_current_eq
  have hprimeCurrent :
      cDual.representationAlphaPrime bDual (j.current j.lt_large.le) =
        b.representationAlphaPrime c i.previous := by
    rw [hCurrentIndex]
    exact b.representationAlphaPrime_reverseDual_swap
      c bDual cDual hbOrders hcOrders hbcDefect i.previous
  have hiNext : j.val + 1 < n + 1 := by
    simp only [j, CentralRepresentationIndex.reversePrevious_val]
    have := i.lt_large
    have := i.one_lt
    omega
  have haPrevious :
      aDual.order ⟨j.val - 1, by have := j.lt_large; omega⟩ =
        -a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
    rw [haOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, CentralRepresentationIndex.reversePrevious_val]
    have := i.one_lt
    have := i.lt_large
    omega
  have hbPrevious :
      bDual.order ⟨j.val - 1, by have := j.lt_large; omega⟩ =
        -b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
    rw [hbOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, CentralRepresentationIndex.reversePrevious_val]
    have := i.one_lt
    have := i.lt_large
    omega
  have hcCurrent :
      cDual.order ⟨j.val, j.lt_large⟩ =
        -c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
    rw [hcOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, CentralRepresentationIndex.reversePrevious_val]
    have := i.one_lt
    have := i.lt_large
    omega
  have hcNext :
      cDual.order ⟨j.val + 1, hiNext⟩ =
        -c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ := by
    rw [hcOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, CentralRepresentationIndex.reversePrevious_val]
    have := i.lt_large
    omega
  have haTwoPrevious :
      aDual.order ⟨j.val - 2, by have := j.lt_large; omega⟩ =
        -a.order ⟨i.val, i.lt_large⟩ := by
    rw [haOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, j, CentralRepresentationIndex.reversePrevious_val]
    have := i.one_lt
    have := i.lt_large
    omega
  have hacCurrent :
      cDual.representationAlpha aDual (j.current j.lt_large.le) =
        a.representationAlpha c i.previous := by
    rw [hCurrentIndex]
    exact hacAlpha i.previous
  have hdualLow :
      cDual.order ⟨j.val, j.lt_large⟩ +
          cDual.order ⟨j.val + 1, hiNext⟩ ≤
        bDual.order ⟨j.val - 1, by have := j.lt_large; omega⟩ +
          aDual.order ⟨j.val - 2, by have := j.lt_large; omega⟩ := by
    rw [hcCurrent, hcNext, hbPrevious, haTwoPrevious]
    omega
  have hfirst := cDual.sectionFourForwardFirst_of_lowPair
    bDual aDual hdualLocal j hiNext hdualTrigger hdualLow
  rw [haPrevious, hacCurrent, hbPrevious, hprimeCurrent] at hfirst
  exact hfirst

/-! ## Low-pair consequences -/

/-- Essentiality turns the low left pair into the right boundary of profile
two. -/
theorem sectionFourRightBoundary_of_leftLow
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hiPrev : 2 < i.val)
    (hlow :
      a.order ⟨i.val, i.lt_large⟩ +
          b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ ≤
        c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ +
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩) :
    (∃ hiNext : i.val + 1 < n + 1,
      b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ <
        a.order ⟨i.val + 1, hiNext⟩) ∨
      i.val + 1 = n + 1 := by
  by_cases hiNext : i.val + 1 < n + 1
  · apply Or.inl
    refine ⟨hiNext, ?_⟩
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
    rw [hcLeft, hcRight, haCurrent, haNext] at hraw
    omega
  · apply Or.inr
    have := i.lt_large
    omega

/-- Essentiality turns the low right pair into the left boundary of profile
three. -/
theorem sectionFourLeftBoundary_of_rightLow
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hiNext : i.val + 1 < n + 1)
    (hlow :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ ≤
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
          c.order ⟨i.val - 2, by have := i.lt_large; omega⟩) :
    (∃ hiPrev : 2 < i.val,
      c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ <
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩) ∨
      i.val = 2 := by
  by_cases hi : i.val = 2
  · exact Or.inr hi
  · apply Or.inl
    have hiPrev : 2 < i.val := by
      have := i.one_lt
      omega
    refine ⟨hiPrev, ?_⟩
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
    rw [hcLeft, hcRight, haCurrent, haNext] at hraw
    omega

/-- Lemma 4.2(i)'s fallback bound in the shifted form used by profile two. -/
theorem sectionFourPreviousFallback_shift
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hnext : i.previous.val + 1 < n + 1)
    (hbound : a.representationAlpha c i.previous ≤
      a.nextFallbackBound b i.previous hnext) :
    ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
          ℚ) : WithTop ℚ) + a.representationAlpha c i.previous ≤
      ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) : WithTop ℚ) +
        a.representationAlpha b (i.current i.lt_large.le) := by
  have hnextIndex :
      nextRepresentationIndex i.previous hnext =
        i.current i.lt_large.le := by
    apply RepresentationIndex.ext
    simp only [nextRepresentationIndex, CentralRepresentationIndex.previous,
      CentralRepresentationIndex.current]
    have := i.one_lt
    omega
  unfold nextFallbackBound at hbound
  rw [hnextIndex] at hbound
  rw [← a.coe_representationAlphaValue c i.previous,
    ← a.coe_representationAlphaValue b (i.current i.lt_large.le)] at hbound
  have hval : i.val - 1 + 1 = i.val := by
    have := i.one_lt
    omega
  simp only [CentralRepresentationIndex.previous, hval] at hbound
  norm_cast at hbound
  push_cast at hbound
  rw [← a.coe_representationAlphaValue c i.previous,
    ← a.coe_representationAlphaValue b (i.current i.lt_large.le)]
  simp only [CentralRepresentationIndex.previous,
    CentralRepresentationIndex.current] at hbound ⊢
  norm_cast
  push_cast
  linarith

/-- Lemma 4.2(ii)'s fallback bound in the shifted form used by profile
three. -/
theorem sectionFourCurrentFallback_shift
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hbound : a.representationAlpha c (i.current i.lt_large.le) ≤
      a.currentFallbackBound b c (i.current i.lt_large.le) i.one_lt) :
    (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + a.representationAlpha c (i.current i.lt_large.le) ≤
      (((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + b.representationAlpha c i.previous := by
  have hpreviousIndex :
      previousRepresentationIndex (i.current i.lt_large.le) i.one_lt =
        i.previous := by
    apply RepresentationIndex.ext
    simp only [previousRepresentationIndex,
      CentralRepresentationIndex.current,
      CentralRepresentationIndex.previous]
  unfold currentFallbackBound at hbound
  rw [hpreviousIndex] at hbound
  rw [← a.coe_representationAlphaValue c (i.current i.lt_large.le),
    ← b.coe_representationAlphaValue c i.previous] at hbound
  simp only [CentralRepresentationIndex.current] at hbound
  norm_cast at hbound
  push_cast at hbound
  rw [← a.coe_representationAlphaValue c (i.current i.lt_large.le),
    ← b.coe_representationAlphaValue c i.previous]
  simp only [CentralRepresentationIndex.current,
    CentralRepresentationIndex.previous] at hbound ⊢
  norm_cast
  push_cast
  linarith

/-- The right half-gap cap at `i-1`, written as the finite average used in
the final symmetric contradiction of Section 4. -/
theorem sectionFourPreviousAlpha_le_rightAverage
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiPrev : 2 < i.val) :
    a.representationAlpha c i.previous ≤
      (((a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : ℚ) -
          ((c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ : ℚ) +
            (c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : ℚ)) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
  calc
    a.representationAlpha c i.previous ≤
        a.representationAlphaPrime c i.previous :=
      a.representationAlpha_le_prime c i.previous
    _ ≤
        (((a.order ⟨i.previous.val, i.previous.lt_large⟩ -
          c.order ⟨i.previous.val - 1, by
            have := i.previous.le_small
            omega⟩ : Int) : ℚ) : WithTop ℚ) +
          (c.halfGapValue ⟨i.previous.val - 2, by
            simp only [CentralRepresentationIndex.previous]
            have := i.lt_large
            omega⟩ : WithTop ℚ) :=
      a.representationAlphaPrime_le_primaryRightHalfGap
        c i.previous (by
          change 1 < i.val - 1
          omega)
    _ = _ := by
      unfold halfGapValue orderGap
      have hsource :
          (⟨i.previous.val, i.previous.lt_large⟩ : Fin (n + 1)) =
            ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
        apply Fin.ext
        simp only [CentralRepresentationIndex.previous]
      have htargetPrevious :
          (⟨i.previous.val - 1, by
            have := i.previous.le_small
            omega⟩ : Fin (n + 1)) =
            ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_castSucc, CentralRepresentationIndex.previous]
        omega
      have hsucc :
          (⟨i.previous.val - 2, by
            simp only [CentralRepresentationIndex.previous]
            have := i.lt_large
            omega⟩ : Fin n).succ =
            ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_succ, CentralRepresentationIndex.previous]
        omega
      have hcast :
          (⟨i.previous.val - 2, by
            simp only [CentralRepresentationIndex.previous]
            have := i.lt_large
            omega⟩ : Fin n).castSucc =
            ⟨i.val - 3, by have := i.lt_large; omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_castSucc, CentralRepresentationIndex.previous]
        omega
      rw [hsource, htargetPrevious, hsucc, hcast]
      norm_cast
      simp only [Rat.divInt_eq_div]
      push_cast
      ring

/-! ## Boundary consequences in the double-direct branch -/

/-- If Lemma 4.3 supplies its second comparison while Corollary 4.4 supplies
its first, the right neighbouring-order boundary of profile two follows.
This is the first average-value contradiction in the last paragraph of
Section 4. -/
theorem sectionFourRightBoundary_of_forwardSecond_backwardFirst
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hnotForward : ¬(
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le)))
    (hforwardSecond :
      ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + b.representationAlpha c i.previous ≤
        ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le))
    (hbackwardFirst :
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + b.representationAlpha c i.previous) :
    (∃ hiNext : i.val + 1 < n + 1,
      b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ <
        a.order ⟨i.val + 1, hiNext⟩) ∨
      i.val + 1 = n + 1 := by
  by_cases hend : i.val + 1 = n + 1
  · exact Or.inr hend
  · have hiNext : i.val + 1 < n + 1 := by
      have := i.lt_large
      omega
    apply Or.inl
    refine ⟨hiNext, ?_⟩
    by_contra hnotBoundary
    have hboundaryLe :
        a.order ⟨i.val + 1, hiNext⟩ ≤
          b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ :=
      le_of_not_gt hnotBoundary
    have hboundaryLeQ :
        (a.order ⟨i.val + 1, hiNext⟩ : ℚ) ≤
          (b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : ℚ) := by
      exact_mod_cast hboundaryLe
    have hforwardStrict := lt_of_not_ge hnotForward
    have hupper := a.centralCurrentAlpha_le_leftAverage c i hiNext
    have hsum := htrigger.2
    unfold centralAdjustedAlpha at hsum
    rw [dif_pos i.lt_large.le] at hsum
    unfold centralLeftAverage at hupper
    rw [← a.coe_representationAlphaValue b
      (i.current i.lt_large.le),
      ← a.coe_representationAlphaValue c
        (i.current i.lt_large.le)] at hforwardStrict
    rw [← b.coe_representationAlphaValue c i.previous,
      ← a.coe_representationAlphaValue b
        (i.current i.lt_large.le)] at hforwardSecond
    rw [← a.coe_representationAlphaValue c i.previous,
      ← b.coe_representationAlphaValue c i.previous] at hbackwardFirst
    rw [← a.coe_representationAlphaValue c
      (i.current i.lt_large.le)] at hupper
    norm_cast at hforwardStrict hforwardSecond hbackwardFirst hupper hsum
    simp only [Rat.divInt_eq_div] at hupper
    norm_num [div_eq_mul_inv] at hupper
    push_cast at hforwardStrict hforwardSecond hbackwardFirst hupper hsum
    simp only [CentralRepresentationIndex.current,
      CentralRepresentationIndex.previous] at hforwardStrict hforwardSecond hbackwardFirst hupper hsum
    linarith

/-- If Lemma 4.3 supplies its first comparison while Corollary 4.4 supplies
its second, the left neighbouring-order boundary of profile three follows.
This is the reverse average-value contradiction in the last paragraph of
Section 4. -/
theorem sectionFourLeftBoundary_of_forwardFirst_backwardSecond
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hnotBackward : ¬(
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + b.representationAlpha c i.previous))
    (hforwardFirst :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le))
    (hbackwardSecond :
      (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le) ≤
        (((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + b.representationAlpha c i.previous) :
    (∃ hiPrev : 2 < i.val,
      c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ <
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩) ∨
      i.val = 2 := by
  by_cases hend : i.val = 2
  · exact Or.inr hend
  · have hiPrev : 2 < i.val := by
      have := i.one_lt
      omega
    apply Or.inl
    refine ⟨hiPrev, ?_⟩
    by_contra hnotBoundary
    have hboundaryLe :
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ ≤
          c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ :=
      le_of_not_gt hnotBoundary
    have hboundaryLeQ :
        (b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : ℚ) ≤
          (c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ : ℚ) := by
      exact_mod_cast hboundaryLe
    have hbackwardStrict := lt_of_not_ge hnotBackward
    have hupper := a.sectionFourPreviousAlpha_le_rightAverage c i hiPrev
    have hsum := htrigger.2
    unfold centralAdjustedAlpha at hsum
    rw [dif_pos i.lt_large.le] at hsum
    rw [← a.coe_representationAlphaValue c
      (i.current i.lt_large.le),
      ← a.coe_representationAlphaValue b
        (i.current i.lt_large.le)] at hforwardFirst
    rw [← a.coe_representationAlphaValue b
      (i.current i.lt_large.le),
      ← b.coe_representationAlphaValue c i.previous] at hbackwardSecond
    rw [← b.coe_representationAlphaValue c i.previous,
      ← a.coe_representationAlphaValue c i.previous] at hbackwardStrict
    rw [← a.coe_representationAlphaValue c i.previous] at hupper
    norm_cast at hforwardFirst hbackwardSecond hbackwardStrict hupper hsum
    simp only [Rat.divInt_eq_div] at hupper
    norm_num [div_eq_mul_inv] at hupper
    push_cast at hforwardFirst hbackwardSecond hbackwardStrict hupper hsum
    simp only [CentralRepresentationIndex.current,
      CentralRepresentationIndex.previous] at hforwardFirst hbackwardSecond hbackwardStrict hupper hsum
    linarith

/-! ## The two fallback profiles -/

/-- In case (d), failure of the left direct test gives the paper's first
low-pair subcase and therefore profile two. -/
theorem sectionFourCentralCertificate_of_both_eq_leftLow
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (heqBC : b.representationAlphaPrime c i.previous =
      b.representationAlpha c i.previous)
    (hnotLeft : ¬a.KeyLemmaLeftDirectTrigger b c
      (nextEssentialIndex i.previous)) :
    CentralRepresentationCertificate a b c i := by
  let hlocal := SectionFourLocalConditions.ofRepresentationConditions
    a b c hab hbc
  obtain ⟨hiPrev, hlow⟩ :=
    a.sectionFourLeftLow_of_not_direct b c i hnotLeft
  have hbackwardPrime := a.sectionFourBackwardFirst_of_leftLow
    b c hlocal i htrigger hiPrev hlow
  have hbackward :
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + b.representationAlpha c i.previous := by
    simpa only [heqBC] using hbackwardPrime
  obtain ⟨hnext, hbound⟩ :=
    (a.sectionFourPreviousBounds_of_centralAlphaTrigger
      b c hlocal i htrigger).2 hnotLeft
  have hshift := a.sectionFourPreviousFallback_shift
    b c i hnext hbound
  have hboundary := a.sectionFourRightBoundary_of_leftLow
    b c i htrigger hiPrev hlow
  exact a.sectionFourCentralCertificate_of_profileTwo
    b c hab hbc i htrigger hboundary hbackward hshift

/-- In case (d), failure of the right direct test gives the paper's second
low-pair subcase and therefore profile three. -/
theorem sectionFourCentralCertificate_of_both_eq_rightLow
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (heqAB : a.representationAlphaPrime b (i.current i.lt_large.le) =
      a.representationAlpha b (i.current i.lt_large.le))
    (hnotRight : ¬a.KeyLemmaRightDirectTrigger b c
      (currentEssentialIndex (i.current i.lt_large.le))) :
    CentralRepresentationCertificate a b c i := by
  let hlocal := SectionFourLocalConditions.ofRepresentationConditions
    a b c hab hbc
  obtain ⟨hiNext, hlow⟩ :=
    a.sectionFourRightLow_of_not_direct b c i hnotRight
  have hforwardPrime := a.sectionFourForwardFirst_of_lowPair
    b c hlocal i hiNext htrigger hlow
  have hforward :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le) := by
    simpa only [heqAB] using hforwardPrime
  obtain ⟨hprev, hbound⟩ :=
    (a.sectionFourCurrentBounds_of_centralAlphaTrigger
      b c hlocal i htrigger).2 hnotRight
  have hshift := a.sectionFourCurrentFallback_shift
    b c i hbound
  have hboundary := a.sectionFourLeftBoundary_of_rightLow
    b c i htrigger hiNext hlow
  exact a.sectionFourCentralCertificate_of_profileThree
    b c hab hbc i htrigger hboundary hforward hshift

/-! ## The double-direct profile split -/

/-- Case (d) when both tests of Lemma 4.2 are direct.  Lemma 4.3 and its
reverse Corollary 4.4 leave precisely the three parity profiles; their two
second alternatives cannot occur simultaneously because condition (iii)
has `T_(i-1) < R_(i+1)`. -/
theorem sectionFourCentralCertificate_of_both_eq_bothDirect
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (heqAB : a.representationAlpha b (i.current i.lt_large.le) =
      a.representationAlphaPrime b (i.current i.lt_large.le))
    (heqBC : b.representationAlpha c i.previous =
      b.representationAlphaPrime c i.previous)
    (hleft : a.KeyLemmaLeftDirectTrigger b c
      (nextEssentialIndex i.previous))
    (hright : a.KeyLemmaRightDirectTrigger b c
      (currentEssentialIndex (i.current i.lt_large.le))) :
    CentralRepresentationCertificate a b c i := by
  have hcrossAB := a.sectionFour_targetCurrent_gt_middlePrevious_of_leftDirect
    b c hbc.orderCondition i htrigger hleft
  have hcrossBC := a.sectionFour_middleNext_gt_sourcePrevious_of_rightDirect
    b c hab.orderCondition i htrigger hright
  have hforwardComparison :=
    a.sectionFourForwardComparison_of_current_eq_prime
      b c hab hbc i htrigger heqAB
  have hbackwardComparison :=
    a.sectionFourBackwardComparison_of_previous_eq_prime
      b c hab hbc i htrigger heqBC
  unfold SectionFourForwardComparison at hforwardComparison
  unfold SectionFourBackwardComparison at hbackwardComparison
  rw [← heqAB] at hforwardComparison
  rw [← heqBC] at hbackwardComparison
  by_cases hforwardFirst :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le)
  · by_cases hbackwardFirst :
        ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
              ℚ) : WithTop ℚ) + a.representationAlpha c i.previous ≤
          ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
              ℚ) : WithTop ℚ) + b.representationAlpha c i.previous
    · exact a.sectionFourCentralCertificate_of_profileOne_direct
        b c hab hbc i htrigger hleft hright hforwardFirst hbackwardFirst
    · have hbackwardSecond :
          (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
                WithTop ℚ) +
              a.representationAlpha b (i.current i.lt_large.le) ≤
            (((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ) :
                WithTop ℚ) + b.representationAlpha c i.previous := by
        rcases hbackwardComparison with hfirst | hsecond | hthird
        · exact (hbackwardFirst hfirst).elim
        · exact hsecond
        · exact (not_lt_of_ge hcrossBC.le hthird).elim
      have hshift := hforwardFirst.trans hbackwardSecond
      have hboundary :=
        a.sectionFourLeftBoundary_of_forwardFirst_backwardSecond
          b c i htrigger hbackwardFirst hforwardFirst hbackwardSecond
      exact a.sectionFourCentralCertificate_of_profileThree
        b c hab hbc i htrigger hboundary hforwardFirst hshift
  · have hforwardSecond :
        ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
              ℚ) : WithTop ℚ) + b.representationAlpha c i.previous ≤
          ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) :
              WithTop ℚ) +
            a.representationAlpha b (i.current i.lt_large.le) := by
      rcases hforwardComparison with hfirst | hsecond | hthird
      · exact (hforwardFirst hfirst).elim
      · exact hsecond
      · exact (not_lt_of_ge hcrossAB.le hthird).elim
    have hbackwardFirst :
        ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
              ℚ) : WithTop ℚ) + a.representationAlpha c i.previous ≤
          ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
              ℚ) : WithTop ℚ) + b.representationAlpha c i.previous := by
      by_contra hnotBackward
      have hbackwardSecond :
          (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
                WithTop ℚ) +
              a.representationAlpha b (i.current i.lt_large.le) ≤
            (((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : Int) : ℚ) :
                WithTop ℚ) + b.representationAlpha c i.previous := by
        rcases hbackwardComparison with hfirst | hsecond | hthird
        · exact (hnotBackward hfirst).elim
        · exact hsecond
        · exact (not_lt_of_ge hcrossBC.le hthird).elim
      have houterQ :
          (c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ : ℚ) <
            (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
        exact_mod_cast htrigger.1
      rw [← b.coe_representationAlphaValue c i.previous,
        ← a.coe_representationAlphaValue b
          (i.current i.lt_large.le)] at hforwardSecond
      rw [← a.coe_representationAlphaValue b
        (i.current i.lt_large.le),
        ← b.coe_representationAlphaValue c i.previous] at hbackwardSecond
      norm_cast at hforwardSecond hbackwardSecond
      push_cast at hforwardSecond hbackwardSecond
      simp only [CentralRepresentationIndex.current,
        CentralRepresentationIndex.previous] at hforwardSecond hbackwardSecond
      linarith
    have hshift := hbackwardFirst.trans hforwardSecond
    have hboundary :=
      a.sectionFourRightBoundary_of_forwardSecond_backwardFirst
        b c i htrigger hforwardFirst hforwardSecond hbackwardFirst
    exact a.sectionFourCentralCertificate_of_profileTwo
      b c hab hbc i htrigger hboundary hbackwardFirst hshift

/-- Complete case (d): both central representation alphas equal their
primed counterparts.  The two direct/fallback tests of Lemma 4.2 are now
exhaustive, and each branch has one of the three Section 4 certificates. -/
theorem sectionFourCentralCertificate_of_both_eq
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (heqAB : a.representationAlpha b (i.current i.lt_large.le) =
      a.representationAlphaPrime b (i.current i.lt_large.le))
    (heqBC : b.representationAlpha c i.previous =
      b.representationAlphaPrime c i.previous) :
    CentralRepresentationCertificate a b c i := by
  by_cases hleft : a.KeyLemmaLeftDirectTrigger b c
      (nextEssentialIndex i.previous)
  · by_cases hright : a.KeyLemmaRightDirectTrigger b c
        (currentEssentialIndex (i.current i.lt_large.le))
    · exact a.sectionFourCentralCertificate_of_both_eq_bothDirect
        b c hab hbc i htrigger heqAB heqBC hleft hright
    · exact a.sectionFourCentralCertificate_of_both_eq_rightLow
        b c hab hbc i htrigger heqAB.symm hright
  · exact a.sectionFourCentralCertificate_of_both_eq_leftLow
      b c hab hbc i htrigger heqBC.symm hleft

end BONG.GoodBONG

end Bong
