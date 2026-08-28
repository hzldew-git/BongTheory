/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyNoncrossCommonLower

/-!
# Beli (2019), Lemma 4.2: removing the noncrossed half-gap candidate

The first term in the expansion of the common shifted `A_i` is strictly
larger than `C_(i-1)`.  Hence `A_i` cannot attain its half-gap candidate.
This is the first deletion on lines 2274--2280.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U} {n : Nat}

/-- Lines 2274--2280: the common lower bound rules out the half-gap
candidate at the next source boundary. -/
theorem nextSourceAlpha_ne_halfGap_of_noncross_failure
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hnoncross : b.order ⟨j.val, j.lt_large⟩ <
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩)
    (hfailure : ¬a.representationAlpha c j ≤
      a.representationAlpha b j) :
    a.representationAlpha b (nextRepresentationIndex j hi.2) ≠
      a.representationHalfGap b (nextRepresentationIndex j hi.2) := by
  intro hhalf
  let commonShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ +
    b.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  have hcommon :=
    a.commonNextSourceAlpha_le_sourcePrimary_of_noncross_failure
      (middleLaws := middleLaws) (targetLaws := targetLaws)
      b c hab habDefect hbcOrder hbcDefect
      j hi hessential hdirect hnoncross hfailure
  obtain ⟨_, hprimary⟩ := a.leftDirect_sourceFailure_eq_primary
    (middleLaws := middleLaws) (targetLaws := targetLaws)
    b c hab hbcOrder hbcDefect j hi hessential hdirect hfailure
  have hstrict : (commonShift : WithTop ℚ) +
      a.representationAlpha b (nextRepresentationIndex j hi.2) <
        a.representationAlpha c j :=
    hcommon.trans_lt hprimary
  have htargetHalf : a.representationAlpha c j ≤
      (((a.order ⟨j.val, j.lt_large⟩ : ℚ) -
        (c.order ⟨j.val - 2, by omega⟩ : ℚ) / 2 -
        (c.order ⟨j.val - 1, by omega⟩ : ℚ) / 2 +
        (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    let targetPair : Fin n := ⟨j.val - 2, by omega⟩
    have hraw := (a.representationAlpha_le_prime c j).trans
      (a.representationAlphaPrime_le_primaryRightHalfGap c j hi.1)
    have hcast : targetPair.castSucc =
        (⟨j.val - 2, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hsucc : targetPair.succ =
        (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [targetPair, Fin.val_succ]
      omega
    calc
      a.representationAlpha c j ≤
          (((a.order ⟨j.val, j.lt_large⟩ -
            c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
            (c.halfGapValue targetPair : WithTop ℚ) := hraw
      _ = _ := by
        unfold halfGapValue orderGap
        rw [hcast, hsucc]
        norm_cast
        simp only [Rat.divInt_eq_div]
        push_cast
        ring
  have hdirectRaw := hdirect hi.1 hi.2
  simp only [nextEssentialIndex] at hdirectRaw
  have hcontradiction := hstrict.trans_le htargetHalf
  rw [hhalf] at hcontradiction
  unfold representationHalfGap at hcontradiction
  norm_cast at hcontradiction
  simp only [nextRepresentationIndex, Rat.divInt_eq_div] at hcontradiction
  push_cast at hcontradiction
  have hdirectQ :
      (c.order ⟨j.val - 2, by omega⟩ : ℚ) +
          c.order ⟨j.val - 1, by omega⟩ <
        a.order ⟨j.val + 1, hi.2⟩ + b.order ⟨j.val, j.lt_large⟩ := by
    exact_mod_cast hdirectRaw
  dsimp only [commonShift] at hcontradiction
  push_cast at hcontradiction
  linarith

end BONG.GoodBONG

end Bong
