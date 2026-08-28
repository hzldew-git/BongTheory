/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma216Prime
import Bong.Bong.Beli2019OrderSequence

/-!
# Beli (2019), Lemma 2.14: preliminary bounds

This file isolates the order consequences of `A_i ≠ A'_i`.  They are the
first part of Lemma 2.14 and will be reused for both adjacent central indices.
-/

namespace Bong

open Dyadic

universe u v w

/-- Cancel a finite additive shift on the right of a strict `WithTop` bound. -/
theorem withTop_sub_lt_of_lt_add (x y : ℚ) (z : WithTop ℚ)
    (h : (x : WithTop ℚ) < (y : WithTop ℚ) + z) :
    ((x - y : ℚ) : WithTop ℚ) < z := by
  have h' := WithTop.add_lt_add_left
    (x := ((-y : ℚ) : WithTop ℚ)) WithTop.coe_ne_top h
  have hleft : ((-y : ℚ) : WithTop ℚ) + (x : WithTop ℚ) =
      ((x - y : ℚ) : WithTop ℚ) := by
    norm_cast
    ring
  have hright : ((-y : ℚ) : WithTop ℚ) +
      ((y : WithTop ℚ) + z) = z := by
    rw [← add_assoc]
    have hzero : ((-y : ℚ) : WithTop ℚ) + (y : WithTop ℚ) = 0 := by
      norm_cast
      ring
    rw [hzero, zero_add]
  rwa [hleft, hright] at h'

/-- Restore a finite additive shift after a strict `WithTop` comparison. -/
theorem withTop_lt_add_of_sub_lt (x y : ℚ) (z : WithTop ℚ)
    (h : ((x - y : ℚ) : WithTop ℚ) < z) :
    (x : WithTop ℚ) < (y : WithTop ℚ) + z := by
  have h' := WithTop.add_lt_add_left
    (x := (y : WithTop ℚ)) WithTop.coe_ne_top h
  have hleft : (y : WithTop ℚ) + ((x - y : ℚ) : WithTop ℚ) =
      (x : WithTop ℚ) := by
    norm_cast
    ring
  rwa [hleft] at h'

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Since `A_i = min {H_i, A'_i}`, inequality of `A_i` and `A'_i` means
that the finite half-gap candidate is strictly smaller. -/
theorem representationAlpha_eq_halfGap_and_lt_prime_of_ne
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (h : a.representationAlpha b i ≠ a.representationAlphaPrime b i) :
    a.representationAlpha b i = a.representationHalfGap b i ∧
      a.representationHalfGap b i < a.representationAlphaPrime b i := by
  have hnotLe : ¬ a.representationAlphaPrime b i ≤
      a.representationHalfGap b i := by
    intro hle
    exact h (a.representationAlpha_eq_prime_of_prime_le_halfGap b i hle)
  have hlt : a.representationHalfGap b i <
      a.representationAlphaPrime b i := lt_of_not_ge hnotLe
  exact ⟨a.representationAlpha_eq_halfGap_of_halfGap_le_prime b i hlt.le, hlt⟩

/-- The primary left cap, sharpened by the defining half-gap bound for the
source alpha. -/
theorem representationAlphaPrime_le_primaryLeftHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : i.val + 1 < m + 1) :
    a.representationAlphaPrime b i ≤
      (((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        (a.halfGapValue ⟨i.val, by omega⟩ : WithTop ℚ) := by
  have hcap := a.representationAlphaPrime_le_primaryLeftCap b i
  rw [a.prefixAlphaCap_of_internal (by omega) hi] at hcap
  have hindex : (⟨i.val + 1 - 1, by omega⟩ : Fin m) =
      ⟨i.val, by omega⟩ := by
    apply Fin.ext
    change i.val + 1 - 1 = i.val
    omega
  rw [hindex] at hcap
  exact hcap.trans (add_le_add_right (by
    exact_mod_cast a.alphaValue_le_halfGapValue ⟨i.val, by omega⟩) _)

/-- The primary right cap, sharpened by the defining half-gap bound for the
target alpha. -/
theorem representationAlphaPrime_le_primaryRightHalfGap
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val) :
    a.representationAlphaPrime b i ≤
      (((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        (b.halfGapValue ⟨i.val - 2, by
          have := i.le_small
          omega⟩ : WithTop ℚ) := by
  have hcap := a.representationAlphaPrime_le_primaryRightCap b i
  rw [b.prefixAlphaCap_of_internal (by omega) (by
    have := i.le_small
    omega)] at hcap
  have hindex : (⟨i.val - 1 - 1, by
      have := i.le_small
      omega⟩ : Fin n) = ⟨i.val - 2, by
        have := i.le_small
        omega⟩ := by
    apply Fin.ext
    change i.val - 1 - 1 = i.val - 2
    omega
  rw [hindex] at hcap
  exact hcap.trans (add_le_add_right (by
    exact_mod_cast b.alphaValue_le_halfGapValue ⟨i.val - 2, by
      have := i.le_small
      omega⟩) _)

/-- The source-side half-gap bound turns `H_i < A'_i` into
`R_(i+2) > S_i`. -/
theorem sourceNext_gt_targetCurrent_of_halfGap_lt_alphaPrime
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : i.val + 1 < m + 1)
    (h : a.representationHalfGap b i < a.representationAlphaPrime b i) :
    b.order ⟨i.val - 1, by have := i.le_small; omega⟩ <
      a.order ⟨i.val + 1, hi⟩ := by
  have hfinite := h.trans_le
    (a.representationAlphaPrime_le_primaryLeftHalfGap b i hi)
  let p : Fin m := ⟨i.val, by omega⟩
  have hpSucc : p.succ = ⟨i.val + 1, hi⟩ := by
    apply Fin.ext
    rfl
  have hpCast : p.castSucc = ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    rfl
  unfold representationHalfGap at hfinite
  rw [halfGapValue, orderGap, hpSucc, hpCast] at hfinite
  norm_cast at hfinite
  push_cast at hfinite
  simp only [Rat.divInt_eq_div] at hfinite
  push_cast at hfinite
  exact_mod_cast (show
    (b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : ℚ) <
      (a.order ⟨i.val + 1, hi⟩ : ℚ) by linarith)

/-- The target-side half-gap bound turns `H_i < A'_i` into
`R_(i+1) > S_(i-1)`. -/
theorem sourceCurrent_gt_targetPrevious_of_halfGap_lt_alphaPrime
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val)
    (h : a.representationHalfGap b i < a.representationAlphaPrime b i) :
    b.order ⟨i.val - 2, by have := i.le_small; omega⟩ <
      a.order ⟨i.val, i.lt_large⟩ := by
  have hfinite := h.trans_le
    (a.representationAlphaPrime_le_primaryRightHalfGap b i hi)
  let p : Fin n := ⟨i.val - 2, by
    have := i.le_small
    omega⟩
  have hpSucc : p.succ = ⟨i.val - 1, by
      have := i.le_small
      omega⟩ := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have hpCast : p.castSucc = ⟨i.val - 2, by
      have := i.le_small
      omega⟩ := by
    apply Fin.ext
    rfl
  unfold representationHalfGap at hfinite
  rw [halfGapValue, orderGap, hpSucc, hpCast] at hfinite
  norm_cast at hfinite
  push_cast at hfinite
  simp only [Rat.divInt_eq_div] at hfinite
  push_cast at hfinite
  exact_mod_cast (show
    (b.order ⟨i.val - 2, by have := i.le_small; omega⟩ : ℚ) <
      (a.order ⟨i.val, i.lt_large⟩ : ℚ) by linarith)

/-- The order consequence of condition 2.1(i) used throughout Lemmas
2.14 and 2.16: `R_(i+1) > S_(i-1)` forces `R_i ≤ S_i`. -/
theorem centralPreviousOrder_le_targetCurrent
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hRank : n ≤ m) (horder : a.RepresentationOrderCondition b hRank)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hi : i.val ≤ n + 1)
    (hcross : b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ ≤ a.order ⟨i.val, i.lt_large⟩) :
    a.order ⟨i.val - 1, by have := i.one_lt; have := i.lt_large; omega⟩ ≤
      b.order ⟨i.val - 1, by have := i.one_lt; have := hi; omega⟩ := by
  have hone := i.one_lt
  have hlarge := i.lt_large
  have hsmall := i.le_small_succ
  have hseq := (a.representationOrderCondition_iff b hRank).mp horder
  have hbound := hseq.current_le_of_next_ge_previous
    (i.val - 1) (by have := i.one_lt; omega)
    (by have := hi; omega)
    (by have := i.one_lt; have := i.lt_large; omega) (by
      have hbIndex : (⟨i.val - 1 - 1, by omega⟩ : Fin (n + 1)) =
          ⟨i.val - 2, by omega⟩ := by
        apply Fin.ext
        change i.val - 1 - 1 = i.val - 2
        omega
      have haIndex : (⟨i.val - 1 + 1, by omega⟩ : Fin (m + 1)) =
          ⟨i.val, by omega⟩ := by
        apply Fin.ext
        change i.val - 1 + 1 = i.val
        omega
      change b.order ⟨i.val - 1 - 1, by omega⟩ ≤
        a.order ⟨i.val - 1 + 1, by omega⟩
      rw [hbIndex, haIndex]
      exact hcross)
  simpa only [orderSequence_at] using hbound

end BONG.GoodBONG

end Bong
