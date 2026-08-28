/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma214Bounds
import Bong.Bong.Beli2019Lemma79CaseSixInteriorAssembly

/-!
# Beli (2019), Section 2.6: the target self half-gap bound

Condition 2.1(i) makes each representation alpha no larger than either
self half-gap at the same boundary.  This file isolates the target-side
bound used in the zero-gamma subcase of Lemma 7.9(ii), case 6.
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

/-- The local comparison alternative in condition 2.1(i) bounds a
representation alpha by the target BONG's half-gap at that boundary. -/
theorem representationAlpha_le_targetHalfGap_of_compare
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (hcompare :
      a.orderSequence.entry i.val i.lt_large ≤
          b.orderSequence.entry i.val i.lt_large ∨
        ∃ (hi0 : 0 < i.val) (hiNext' : i.val + 1 < n + 2),
          a.orderSequence.entry i.val i.lt_large +
              a.orderSequence.entry (i.val + 1) hiNext' ≤
            b.orderSequence.entry (i.val - 1) (by omega) +
              b.orderSequence.entry i.val i.lt_large) :
    a.representationAlpha b i ≤
      b.halfGapCandidate ⟨i.val - 1, by omega⟩ := by
  let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hpreviousSucc : previous.succ = ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    exact Nat.sub_add_cancel i.pos
  have hpreviousCast : previous.castSucc =
      ⟨i.val - 1, by omega⟩ := by
    apply Fin.ext
    rfl
  rcases hcompare with hdirect | ⟨hi0, hiNext', hpair⟩
  · have hdirectOrder : a.order ⟨i.val, i.lt_large⟩ ≤
        b.order ⟨i.val, i.lt_large⟩ := by
      simpa only [orderSequence_at] using hdirect
    apply (a.representationAlpha_le_halfGap b i).trans
    rw [← b.coe_halfGapValue previous]
    unfold representationHalfGap halfGapValue orderGap
    rw [hpreviousSucc, hpreviousCast]
    norm_cast
    simp only [Rat.divInt_eq_div]
    push_cast
    have hdirectQ : (a.order ⟨i.val, i.lt_large⟩ : ℚ) ≤
        (b.order ⟨i.val, i.lt_large⟩ : ℚ) := by
      exact_mod_cast hdirectOrder
    linarith
  · have hpairOrder :
        a.order ⟨i.val, i.lt_large⟩ +
            a.order ⟨i.val + 1, hiNext'⟩ ≤
          b.order ⟨i.val - 1, by omega⟩ +
            b.order ⟨i.val, i.lt_large⟩ := by
      simpa only [orderSequence_at] using hpair
    have hprime :=
      a.representationAlphaPrime_le_primaryLeftHalfGap b i hiNext
    let current : Fin (n + 1) := ⟨i.val, by omega⟩
    have hprime' : a.representationAlphaPrime b i ≤
        (((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          (a.halfGapValue current : WithTop ℚ) := by
      simpa only [current] using hprime
    have hcurrentSucc : current.succ =
        ⟨i.val + 1, hiNext'⟩ := by
      apply Fin.ext
      rfl
    have hcurrentCast : current.castSucc =
        ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      rfl
    apply (a.representationAlpha_le_prime b i).trans
    apply hprime'.trans
    rw [← b.coe_halfGapValue previous]
    norm_cast
    unfold halfGapValue orderGap
    rw [hcurrentSucc, hcurrentCast, hpreviousSucc, hpreviousCast]
    have hpairQ :
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) +
            (a.order ⟨i.val + 1, hiNext'⟩ : ℚ) ≤
          (b.order ⟨i.val - 1, by omega⟩ : ℚ) +
            (b.order ⟨i.val, i.lt_large⟩ : ℚ) := by
      exact_mod_cast hpairOrder
    push_cast
    linarith

/-- The target self half-gap bound, packaged directly from condition
2.1(i). -/
theorem representationAlpha_le_targetHalfGap_of_orderCondition
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2) :
    a.representationAlpha b i ≤
      b.halfGapCandidate ⟨i.val - 1, by omega⟩ := by
  have hsequence := (a.representationOrderCondition_iff b le_rfl).mp horder
  exact representationAlpha_le_targetHalfGap_of_compare
    a b i hiNext (hsequence.compare i.val i.lt_large)

/-- Finite-valued target half-gap bound, including the final ordinary
boundary. At the final boundary, condition 2.1(i)'s pair alternative is
impossible, so its direct order comparison supplies the same estimate. -/
theorem representationAlphaValue_le_targetHalfGapValue_of_orderCondition
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2)) :
    a.representationAlphaValue b i ≤
      b.halfGapValue ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
  let previous : Fin (n + 1) :=
    ⟨i.val - 1, by have := i.lt_large; omega⟩
  have hcomparison :=
    ((a.representationOrderCondition_iff b le_rfl).mp horder).compare
      i.val i.lt_large
  rcases hcomparison with hdirect | ⟨hi0, hiNext, hpair⟩
  · have hdirectOrder : a.order ⟨i.val, i.lt_large⟩ ≤
        b.order ⟨i.val, i.lt_large⟩ := by
      simpa only [orderSequence_at] using hdirect
    have htop : a.representationAlpha b i ≤
        b.halfGapCandidate previous := by
      have hpreviousSucc : previous.succ = ⟨i.val, i.lt_large⟩ := by
        apply Fin.ext
        simp only [previous, Fin.val_succ]
        have := i.pos
        omega
      have hpreviousCast : previous.castSucc =
          (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        rfl
      apply (a.representationAlpha_le_halfGap b i).trans
      rw [← b.coe_halfGapValue previous]
      unfold representationHalfGap halfGapValue orderGap
      rw [hpreviousSucc, hpreviousCast]
      norm_cast
      simp only [Rat.divInt_eq_div]
      have hdirectQ : (a.order ⟨i.val, i.lt_large⟩ : ℚ) ≤
          (b.order ⟨i.val, i.lt_large⟩ : ℚ) := by
        exact_mod_cast hdirectOrder
      push_cast
      linarith
    rw [← a.coe_representationAlphaValue b i,
      ← b.coe_halfGapValue previous] at htop
    exact WithTop.coe_le_coe.mp htop
  · have htop := representationAlpha_le_targetHalfGap_of_compare
      a b i hiNext (Or.inr ⟨hi0, hiNext, hpair⟩)
    rw [← a.coe_representationAlphaValue b i,
      ← b.coe_halfGapValue previous] at htop
    exact WithTop.coe_le_coe.mp htop

/-- If the target alpha at a boundary vanishes, its self half-gap is zero;
condition 2.1(i) therefore makes the representation alpha nonpositive. -/
theorem representationAlpha_le_zero_of_targetAlpha_eq_zero
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (hcompare :
      a.orderSequence.entry i.val i.lt_large ≤
          b.orderSequence.entry i.val i.lt_large ∨
        ∃ (hi0 : 0 < i.val) (hiNext' : i.val + 1 < n + 2),
          a.orderSequence.entry i.val i.lt_large +
              a.orderSequence.entry (i.val + 1) hiNext' ≤
            b.orderSequence.entry (i.val - 1) (by omega) +
              b.orderSequence.entry i.val i.lt_large)
    (hzero : b.alphaValue ⟨i.val - 1, by omega⟩ = 0) :
    a.representationAlpha b i ≤ 0 := by
  let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have htarget := representationAlpha_le_targetHalfGap_of_compare
    (sourceLaws := sourceLaws) a b i hiNext hcompare
  letI : Beli2006AlphaLaws.{u, w} K := targetLaws
  have hgap := (b.alpha_p2 previous).2.mp (by
    simpa only [previous] using hzero)
  have hhalfZero : b.halfGapCandidate previous = 0 := by
    rw [← b.coe_halfGapValue previous]
    unfold halfGapValue
    rw [hgap]
    norm_cast
    simp only [Rat.divInt_eq_div]
    change (((-(2 * (ramificationIndex K : Int)) : Int) : ℚ) / 2 +
      (ramificationIndex K : ℚ) : ℚ) = 0
    push_cast
    ring
  calc
    a.representationAlpha b i ≤ b.halfGapCandidate previous := by
      simpa only [previous] using htarget
    _ = 0 := hhalfZero

/-- The zero-gamma branch of condition 2.1(ii), using the local comparison
already supplied by part (i). -/
theorem lemma79_caseSix_of_gamma_eq_zero_and_compare
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (c : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (hcompare :
      b.orderSequence.entry i.val i.lt_large ≤
          c.orderSequence.entry i.val i.lt_large ∨
        ∃ (hi0 : 0 < i.val) (hiNext' : i.val + 1 < n + 2),
          b.orderSequence.entry i.val i.lt_large +
              b.orderSequence.entry (i.val + 1) hiNext' ≤
            c.orderSequence.entry (i.val - 1) (by omega) +
              c.orderSequence.entry i.val i.lt_large)
    (hgamma : c.alphaValue ⟨i.val - 1, by omega⟩ = 0) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  calc
    (b.representationAlphaValue c i : WithTop ℚ) =
        b.representationAlpha c i := b.coe_representationAlphaValue c i
    _ ≤ 0 := representationAlpha_le_zero_of_targetAlpha_eq_zero
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b c i hiNext hcompare hgamma
    _ ≤ b.truncatedPrefixDefect c 1 i.val i.val :=
      b.truncatedPrefixDefect_nonneg
        (alphaV := sourceLaws) (alphaW := targetLaws)
        c 1 i.val i.val

end BONG.GoodBONG

end Bong
