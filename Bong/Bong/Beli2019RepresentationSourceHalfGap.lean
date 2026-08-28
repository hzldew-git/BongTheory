/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma214Bounds

/-!
# Beli (2019), Section 2.6: the source self half-gap bound

Condition 2.1(i) makes a representation alpha no larger than the source
self half-gap at the same boundary.  This is the source-side companion to
`representationAlpha_le_targetHalfGap_of_orderCondition`.

The direct order alternative bounds the defining mixed half-gap.  In the
adjacent-pair alternative, the primary right-half-gap estimate bounds the
auxiliary alpha instead.  The proof also works at the final boundary,
where the adjacent-pair alternative is automatically impossible.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Section 2.6: condition 2.1(i) bounds a representation alpha by the
source BONG's self half-gap at the same boundary. -/
theorem representationAlpha_le_sourceHalfGap_of_orderCondition
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2)) :
    a.representationAlpha b i <=
      a.halfGapCandidate (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)) := by
  let previous : Fin (n + 1) := Fin.mk (i.val - 1) (by
    have hi := i.lt_large
    omega)
  have hpreviousSucc : previous.succ =
      (Fin.mk i.val i.lt_large : Fin (n + 2)) := by
    apply Fin.ext
    simp only [previous, Fin.val_succ]
    have hiPos := i.pos
    omega
  have hpreviousCast : previous.castSucc =
      (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega) : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hsequence :=
    (a.representationOrderCondition_iff b le_rfl).mp horder
  rcases hsequence.compare (i.val - 1) (by
      have hi := i.lt_large
      omega) with hdirect | hpair
  · have hdirectOrder :
        a.order (Fin.mk (i.val - 1) (by
            have hi := i.lt_large
            omega)) <=
          b.order (Fin.mk (i.val - 1) (by
            have hi := i.lt_large
            omega)) := by
      simpa only [orderSequence_at] using hdirect
    apply (a.representationAlpha_le_halfGap b i).trans
    unfold representationHalfGap halfGapCandidate
    rw [hpreviousSucc, hpreviousCast]
    norm_cast
    simp only [Rat.divInt_eq_div]
    have hdirectQ :
        (a.order (Fin.mk (i.val - 1) (by
            have hi := i.lt_large
            omega)) : Rat) <=
          (b.order (Fin.mk (i.val - 1) (by
            have hi := i.lt_large
            omega)) : Rat) := by
      exact_mod_cast hdirectOrder
    push_cast
    linarith
  · rcases hpair with ⟨hiPrevious, hiCurrent, hpair⟩
    have hiTwo : 1 < i.val := by omega
    have hpairOrder :
        a.order (Fin.mk (i.val - 1) (by
            have hi := i.lt_large
            omega)) +
            a.order (Fin.mk i.val i.lt_large) <=
          b.order (Fin.mk (i.val - 2) (by
            have hi := i.lt_large
            omega)) +
            b.order (Fin.mk (i.val - 1) (by
              have hi := i.lt_large
              omega)) := by
      have hcurrentValue : i.val - 1 + 1 = i.val :=
        Nat.sub_add_cancel i.pos
      have hpreviousValue : i.val - 1 - 1 = i.val - 2 := by
        omega
      simpa only [orderSequence_at, hcurrentValue,
        hpreviousValue] using hpair
    have hprime :=
      a.representationAlphaPrime_le_primaryRightHalfGap b i hiTwo
    let targetPrevious : Fin (n + 1) := Fin.mk (i.val - 2) (by
      have hi := i.lt_large
      omega)
    have htargetPreviousSucc : targetPrevious.succ =
        (Fin.mk (i.val - 1) (by
          have hi := i.lt_large
          omega) : Fin (n + 2)) := by
      apply Fin.ext
      simp only [targetPrevious, Fin.val_succ]
      omega
    have htargetPreviousCast : targetPrevious.castSucc =
        (Fin.mk (i.val - 2) (by
          have hi := i.lt_large
          omega) : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    apply (a.representationAlpha_le_prime b i).trans
    apply hprime.trans
    rw [b.coe_halfGapValue targetPrevious]
    unfold halfGapCandidate
    rw [htargetPreviousSucc, htargetPreviousCast,
      hpreviousSucc, hpreviousCast]
    norm_cast
    simp only [Rat.divInt_eq_div]
    have hpairQ :
        (a.order (Fin.mk (i.val - 1) (by
            have hi := i.lt_large
            omega)) : Rat) +
            (a.order (Fin.mk i.val i.lt_large) : Rat) <=
          (b.order (Fin.mk (i.val - 2) (by
            have hi := i.lt_large
            omega)) : Rat) +
            (b.order (Fin.mk (i.val - 1) (by
              have hi := i.lt_large
              omega)) : Rat) := by
      exact_mod_cast hpairOrder
    push_cast
    linarith

/-- Finite-value form of the source self half-gap estimate. -/
theorem representationAlphaValue_le_sourceHalfGapValue_of_orderCondition
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2)) :
    a.representationAlphaValue b i <=
      a.halfGapValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)) := by
  have h := representationAlpha_le_sourceHalfGap_of_orderCondition
    a b horder i
  rw [<- a.coe_representationAlphaValue b i,
    <- a.coe_halfGapValue] at h
  exact WithTop.coe_le_coe.mp h

/-- If the source alpha attains its self half-gap, it itself bounds the
representation alpha. -/
theorem representationAlphaValue_le_sourceAlpha_of_attainsHalfGap
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hattains : a.alphaValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)) =
      a.halfGapValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega))) :
    a.representationAlphaValue b i <=
      a.alphaValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)) := by
  calc
    a.representationAlphaValue b i <=
        a.halfGapValue (Fin.mk (i.val - 1) (by
          have hi := i.lt_large
          omega)) :=
      representationAlphaValue_le_sourceHalfGapValue_of_orderCondition
        a b horder i
    _ = a.alphaValue (Fin.mk (i.val - 1) (by
          have hi := i.lt_large
          omega)) := hattains.symm

end BONG.GoodBONG

end Bong
