/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019CappedDefectMin
import Bong.Bong.Beli2019Approximation

/-!
# Beli (2019), the capped adjacent-defect bound

Remark 1.1 allows the raw adjacent defect in the definition of `α_i` to be
replaced by its bracketed, endpoint-capped version.  This is the cut estimate
used in Lemma 2.7(i).
-/

namespace Bong

open Dyadic

universe u v

/-- A convenient order lemma for distributing a common shift over a binary
minimum. -/
theorem withTop_le_shift_add_min
    (x : WithTop ℚ) (y : ℚ) (a b : WithTop ℚ)
    (ha : x ≤ (y : WithTop ℚ) + a)
    (hb : x ≤ (y : WithTop ℚ) + b) :
    x ≤ (y : WithTop ℚ) + min a b := by
  by_cases hab : a ≤ b
  · simpa [min_eq_left hab] using ha
  · have hba : b ≤ a := le_of_not_ge hab
    simpa [min_eq_right hba] using hb

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {m : Nat}

/-- The raw defect of two prefixes two places apart is the adjacent defect:
the omitted earlier prefix occurs as a square. -/
theorem defectOrder_prefixPair_eq_adjacentDefect
    (a : GoodBONG q L (m + 1)) (i : Fin m) :
    defectOrder (K := K)
        ((-1) * a.prefixProduct i.val * a.prefixProduct (i.val + 2)) =
      a.adjacentDefect i := by
  have hunit :
      (-1 : Kˣ) * a.prefixProduct i.val * a.prefixProduct (i.val + 2) =
        a.adjacentProduct i * (a.prefixProduct i.val) ^ 2 := by
    rw [a.prefixProduct_add_two i.val (by omega)]
    have hzero : (⟨i.val, by omega⟩ : Fin (m + 1)) = i.castSucc := by
      apply Fin.ext
      rfl
    have hone : (⟨i.val + 1, by omega⟩ : Fin (m + 1)) = i.succ := by
      apply Fin.ext
      rfl
    rw [hzero, hone]
    apply Units.ext
    simp only [adjacentProduct, GoodBONG.valueUnit, Units.val_mul,
      Units.val_neg, Units.val_one, Units.val_pow_eq_pow_val]
    ring
  rw [hunit, defectOrder_mul_square]
  rfl

/-- Remark 1.1 in endpoint-safe form:
`α_i ≤ R_(i+1) - R_i + d[-a_(1,i) a_(1,i+2)]`.

The two alpha caps in the bracketed defect are handled by property P1; at
either exterior endpoint the corresponding cap is `⊤` and is automatic. -/
theorem alpha_le_orderGap_add_cappedAdjacent
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (i : Fin m) :
    (a.alphaValue i : WithTop ℚ) ≤
      ((((a.order i.succ - a.order i.castSucc : Int) : ℚ) :
          WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) i.val (i.val + 2)) := by
  let shift : ℚ := ((a.order i.succ - a.order i.castSucc : Int) : ℚ)
  have hraw : (a.alphaValue i : WithTop ℚ) ≤
      (shift : WithTop ℚ) +
        defectOrder (K := K)
          ((-1) * a.prefixProduct i.val * a.prefixProduct (i.val + 2)) := by
    rw [a.defectOrder_prefixPair_eq_adjacentDefect i]
    rw [a.coe_alphaValue]
    simpa only [shift, leftDefectCandidate] using
      (a.alpha_le_leftDefectCandidate (i := i) (j := i) le_rfl)
  have hleft : (a.alphaValue i : WithTop ℚ) ≤
      (shift : WithTop ℚ) + a.prefixAlphaCap i.val := by
    by_cases hi0 : i.val = 0
    · rw [hi0, a.prefixAlphaCap_zero]
      simp
    · have hipos : 0 < i.val := Nat.pos_of_ne_zero hi0
      let previous : Fin m := ⟨i.val - 1, by omega⟩
      have hprevious : previous.val + 1 < m := by
        dsimp only [previous]
        omega
      rw [a.prefixAlphaCap_of_internal hipos (by omega)]
      have hp1 := (a.alpha_p1 previous hprevious).2
      have hindex : (⟨previous.val + 1, hprevious⟩ : Fin m) = i := by
        apply Fin.ext
        dsimp only [previous]
        omega
      unfold alphaRightEndpoint at hp1
      have horder : previous.succ = i.castSucc := by
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_castSucc, previous]
        omega
      rw [hindex, horder] at hp1
      have hrational : a.alphaValue i ≤
          shift + a.alphaValue previous := by
        dsimp only [shift]
        push_cast
        linarith
      simpa only [previous] using (show
        (a.alphaValue i : WithTop ℚ) ≤
          (shift : WithTop ℚ) + (a.alphaValue previous : WithTop ℚ) by
            exact_mod_cast hrational)
  have hright : (a.alphaValue i : WithTop ℚ) ≤
      (shift : WithTop ℚ) + a.prefixAlphaCap (i.val + 2) := by
    by_cases hinternal : i.val + 1 < m
    · let next : Fin m := ⟨i.val + 1, hinternal⟩
      rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
      have hp1 := (a.alpha_p1 i hinternal).1
      have hindex : (⟨i.val + 2 - 1, by omega⟩ : Fin m) = next := by
        apply Fin.ext
        dsimp only [next]
        omega
      rw [hindex]
      unfold alphaLeftEndpoint at hp1
      have horder : next.castSucc = i.succ := by
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.val_succ, next]
      rw [horder] at hp1
      have hrational : a.alphaValue i ≤
          shift + a.alphaValue next := by
        dsimp only [shift]
        push_cast
        linarith
      exact_mod_cast hrational
    · have hlast : i.val + 2 = m + 1 := by omega
      rw [hlast, a.prefixAlphaCap_last]
      simp
  change (a.alphaValue i : WithTop ℚ) ≤
    (shift : WithTop ℚ) +
      min (defectOrder (K := K)
        ((-1) * a.prefixProduct i.val * a.prefixProduct (i.val + 2)))
        (min (a.prefixAlphaCap i.val) (a.prefixAlphaCap (i.val + 2)))
  exact withTop_le_shift_add_min _ shift _ _ hraw
    (withTop_le_shift_add_min _ shift _ _ hleft hright)

/-- The defining alpha candidate, rearranged as the lower bound on the
capped defect of its adjacent pair. -/
theorem order_sub_add_alpha_le_cappedAdjacent
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (m + 1)) (i : Fin m) :
    (((((b.order i.castSucc - b.order i.succ : Int) : ℚ) +
        b.alphaValue i : ℚ)) : WithTop ℚ) ≤
      b.truncatedPrefixDefect b (-1) i.val (i.val + 2) := by
  have hbound := b.alpha_le_orderGap_add_cappedAdjacent i
  by_cases htop : b.truncatedPrefixDefect b (-1) i.val (i.val + 2) = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hd] at hbound ⊢
    norm_cast at hbound ⊢
    push_cast at hbound ⊢
    linarith

end BONG.GoodBONG

end Bong
