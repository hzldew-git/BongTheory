/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006AlphaProperties

/-!
# Beli (2006), property P1

Property P1 is a consequence of the finite candidate definition of `alpha`
and the two-step order inequality defining a good BONG.  No local-field law
is used in this proof.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

/-- The cast of an adjacent order gap in the codomain of `alpha`. -/
noncomputable def orderGapTop
    (b : GoodBONG q L (n + 1)) (i : Fin n) : WithTop ℚ :=
  (((b.orderGap i : Int) : ℚ) : WithTop ℚ)

/-- The half-gap candidate at `i` is bounded by the shifted half-gap
candidate at `i+1`. -/
theorem halfGapCandidate_le_orderGapTop_add_halfGapCandidate_succ
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hi : i.1 + 1 < n) :
    b.halfGapCandidate i ≤
      b.orderGapTop i +
        b.halfGapCandidate ⟨i.1 + 1, hi⟩ := by
  have hbound : i.castSucc.val + 2 < n + 1 := by
    change i.val + 2 < n + 1
    omega
  have hgood := b.good i.castSucc hbound
  have htarget :
      (⟨i.castSucc.val + 2, hbound⟩ : Fin (n + 1)) =
        (⟨i.val + 1, hi⟩ : Fin n).succ := by
    apply Fin.ext
    rfl
  have hmiddle : (⟨i.val + 1, hi⟩ : Fin n).castSucc = i.succ := by
    apply Fin.ext
    rfl
  rw [htarget] at hgood
  unfold halfGapCandidate orderGapTop orderGap
  rw [hmiddle]
  norm_cast
  push_cast
  have hgoodQ : (b.order i.castSucc : ℚ) ≤
      (b.order (⟨i.val + 1, hi⟩ : Fin n).succ : ℚ) := by
    exact_mod_cast hgood
  simp only [Rat.divInt_eq_div]
  push_cast
  linarith

/-- The half-gap candidate at `i+1` is bounded by the shifted half-gap
candidate at `i`. -/
theorem halfGapCandidate_succ_le_orderGapTop_succ_add_halfGapCandidate
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hi : i.1 + 1 < n) :
    b.halfGapCandidate ⟨i.1 + 1, hi⟩ ≤
      b.orderGapTop ⟨i.1 + 1, hi⟩ + b.halfGapCandidate i := by
  have hbound : i.castSucc.val + 2 < n + 1 := by
    change i.val + 2 < n + 1
    omega
  have hgood := b.good i.castSucc hbound
  have htarget :
      (⟨i.castSucc.val + 2, hbound⟩ : Fin (n + 1)) =
        (⟨i.val + 1, hi⟩ : Fin n).succ := by
    apply Fin.ext
    rfl
  have hmiddle : (⟨i.val + 1, hi⟩ : Fin n).castSucc = i.succ := by
    apply Fin.ext
    rfl
  rw [htarget] at hgood
  unfold halfGapCandidate orderGapTop orderGap
  rw [hmiddle]
  norm_cast
  push_cast
  have hgoodQ : (b.order i.castSucc : ℚ) ≤
      (b.order (⟨i.val + 1, hi⟩ : Fin n).succ : ℚ) := by
    exact_mod_cast hgood
  simp only [Rat.divInt_eq_div]
  push_cast
  linarith

/-- A left candidate whose source remains to the left changes by at least
the current order gap. -/
theorem leftDefectCandidate_le_orderGapTop_add_leftDefectCandidate_succ
    (b : GoodBONG q L (n + 1)) (i j : Fin n)
    (hi : i.1 + 1 < n) :
    b.leftDefectCandidate i j ≤
      b.orderGapTop i +
        b.leftDefectCandidate ⟨i.1 + 1, hi⟩ j := by
  have hbound : i.castSucc.val + 2 < n + 1 := by
    change i.val + 2 < n + 1
    omega
  have hgood := b.good i.castSucc hbound
  have htarget :
      (⟨i.castSucc.val + 2, hbound⟩ : Fin (n + 1)) =
        (⟨i.val + 1, hi⟩ : Fin n).succ := by
    apply Fin.ext
    rfl
  have hmiddle : (⟨i.val + 1, hi⟩ : Fin n).castSucc = i.succ := by
    apply Fin.ext
    rfl
  rw [htarget] at hgood
  change b.order i.castSucc ≤
    b.order (⟨i.val + 1, hi⟩ : Fin n).succ at hgood
  have hcoeff :
      (((b.order i.succ - b.order j.castSucc : Int) : ℚ) :
          WithTop ℚ) ≤
        (((b.orderGap i +
          (b.order (⟨i.val + 1, hi⟩ : Fin n).succ -
            b.order j.castSucc) : Int) : ℚ) : WithTop ℚ) := by
    norm_cast
    unfold orderGap
    omega
  unfold leftDefectCandidate orderGapTop
  calc
    _ ≤ (((b.orderGap i +
          (b.order (⟨i.val + 1, hi⟩ : Fin n).succ -
            b.order j.castSucc) : Int) : ℚ) : WithTop ℚ) +
        b.adjacentDefect j := by
          simpa only [add_comm] using
            add_le_add_right hcoeff (b.adjacentDefect j)
    _ = _ := by
      rw [← add_assoc]
      congr 1
      norm_cast <;> ring

/-- A right candidate is transported exactly from `i+1` to `i` after
adding the current order gap. -/
theorem orderGapTop_add_rightDefectCandidate_succ
    (b : GoodBONG q L (n + 1)) (i j : Fin n)
    (hi : i.1 + 1 < n) :
    b.orderGapTop i +
        b.rightDefectCandidate ⟨i.1 + 1, hi⟩ j =
      b.rightDefectCandidate i j := by
  have hmiddle : (⟨i.val + 1, hi⟩ : Fin n).castSucc = i.succ := by
    apply Fin.ext
    rfl
  unfold orderGapTop orderGap rightDefectCandidate
  rw [hmiddle]
  rw [← add_assoc]
  congr 1
  norm_cast <;> ring

/-- The local left candidate at `i+1` becomes a right candidate at `i`. -/
theorem orderGapTop_add_leftDefectCandidate_succ_self
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hi : i.1 + 1 < n) :
    b.orderGapTop i +
        b.leftDefectCandidate ⟨i.1 + 1, hi⟩ ⟨i.1 + 1, hi⟩ =
      b.rightDefectCandidate i ⟨i.1 + 1, hi⟩ := by
  have hmiddle : (⟨i.val + 1, hi⟩ : Fin n).castSucc = i.succ := by
    apply Fin.ext
    rfl
  unfold orderGapTop orderGap leftDefectCandidate rightDefectCandidate
  rw [hmiddle]
  rw [← add_assoc]
  congr 1
  norm_cast <;> ring

/-- A left candidate is transported exactly from `i` to `i+1` after
adding the next order gap. -/
theorem orderGapTop_succ_add_leftDefectCandidate
    (b : GoodBONG q L (n + 1)) (i j : Fin n)
    (hi : i.1 + 1 < n) :
    b.orderGapTop ⟨i.1 + 1, hi⟩ + b.leftDefectCandidate i j =
      b.leftDefectCandidate ⟨i.1 + 1, hi⟩ j := by
  have hmiddle : (⟨i.val + 1, hi⟩ : Fin n).castSucc = i.succ := by
    apply Fin.ext
    rfl
  unfold orderGapTop orderGap leftDefectCandidate
  rw [hmiddle]
  rw [← add_assoc]
  congr 1
  norm_cast <;> ring

/-- A right candidate whose source remains to the right changes by at least
the next order gap. -/
theorem rightDefectCandidate_succ_le_orderGapTop_succ_add_rightDefectCandidate
    (b : GoodBONG q L (n + 1)) (i j : Fin n)
    (hi : i.1 + 1 < n) :
    b.rightDefectCandidate ⟨i.1 + 1, hi⟩ j ≤
      b.orderGapTop ⟨i.1 + 1, hi⟩ +
        b.rightDefectCandidate i j := by
  have hbound : i.castSucc.val + 2 < n + 1 := by
    change i.val + 2 < n + 1
    omega
  have hgood := b.good i.castSucc hbound
  have htarget :
      (⟨i.castSucc.val + 2, hbound⟩ : Fin (n + 1)) =
        (⟨i.val + 1, hi⟩ : Fin n).succ := by
    apply Fin.ext
    rfl
  have hmiddle : (⟨i.val + 1, hi⟩ : Fin n).castSucc = i.succ := by
    apply Fin.ext
    rfl
  rw [htarget] at hgood
  change b.order i.castSucc ≤
    b.order (⟨i.val + 1, hi⟩ : Fin n).succ at hgood
  have hcoeff :
      (((b.order j.succ - b.order i.succ : Int) : ℚ) :
          WithTop ℚ) ≤
        (((b.orderGap ⟨i.1 + 1, hi⟩ +
          (b.order j.succ - b.order i.castSucc) : Int) : ℚ) :
            WithTop ℚ) := by
    norm_cast
    unfold orderGap
    rw [hmiddle]
    omega
  unfold rightDefectCandidate orderGapTop
  rw [hmiddle]
  calc
    _ ≤ (((b.orderGap (⟨i.val + 1, hi⟩ : Fin n) +
          (b.order j.succ - b.order i.castSucc) : Int) : ℚ) :
            WithTop ℚ) + b.adjacentDefect j := by
          simpa only [add_comm] using
            add_le_add_right hcoeff (b.adjacentDefect j)
    _ = _ := by
      rw [← add_assoc]
      congr 1
      norm_cast <;> ring

/-- The local right candidate at `i` becomes a left candidate at `i+1`. -/
theorem orderGapTop_succ_add_rightDefectCandidate_self
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hi : i.1 + 1 < n) :
    b.orderGapTop ⟨i.1 + 1, hi⟩ + b.rightDefectCandidate i i =
      b.leftDefectCandidate ⟨i.1 + 1, hi⟩ i := by
  have hmiddle : (⟨i.val + 1, hi⟩ : Fin n).castSucc = i.succ := by
    apply Fin.ext
    rfl
  unfold orderGapTop orderGap leftDefectCandidate rightDefectCandidate
  rw [hmiddle]
  rw [← add_assoc]
  congr 1
  norm_cast <;> ring

/-- One half of P1 in the `WithTop` definition of `alpha`. -/
theorem alpha_le_orderGapTop_add_alpha_succ
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hi : i.1 + 1 < n) :
    b.alpha i ≤ b.orderGapTop i + b.alpha ⟨i.1 + 1, hi⟩ := by
  let next : Fin n := ⟨i.1 + 1, hi⟩
  have hmem : b.alpha next ∈ b.alphaCandidates next :=
    Finset.min'_mem _ _
  simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  rcases hmem with hhalf | hleft | hright
  · rw [hhalf]
    exact (b.alpha_le_halfGapCandidate i).trans
      (b.halfGapCandidate_le_orderGapTop_add_halfGapCandidate_succ i hi)
  · rcases hleft with ⟨j, hjle, hj⟩
    rw [← hj]
    by_cases hji : j ≤ i
    · exact (b.alpha_le_leftDefectCandidate hji).trans
        (b.leftDefectCandidate_le_orderGapTop_add_leftDefectCandidate_succ
          i j hi)
    · have hjeq : j = next := by
        apply Fin.ext
        change j.val = i.val + 1
        have hjle' : j.val ≤ i.val + 1 := hjle
        have hnot : ¬j.val ≤ i.val := by
          intro h
          exact hji h
        omega
      subst j
      rw [b.orderGapTop_add_leftDefectCandidate_succ_self i hi]
      apply b.alpha_le_rightDefectCandidate
      change i.val ≤ i.val + 1
      omega
  · rcases hright with ⟨j, hnextj, hj⟩
    rw [← hj, b.orderGapTop_add_rightDefectCandidate_succ i j hi]
    apply b.alpha_le_rightDefectCandidate
    change i.val ≤ j.val
    have hnextj' : i.val + 1 ≤ j.val := hnextj
    omega

/-- The other half of P1 in the `WithTop` definition of `alpha`. -/
theorem alpha_succ_le_orderGapTop_succ_add_alpha
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hi : i.1 + 1 < n) :
    b.alpha ⟨i.1 + 1, hi⟩ ≤
      b.orderGapTop ⟨i.1 + 1, hi⟩ + b.alpha i := by
  let next : Fin n := ⟨i.1 + 1, hi⟩
  have hmem : b.alpha i ∈ b.alphaCandidates i :=
    Finset.min'_mem _ _
  simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  rcases hmem with hhalf | hleft | hright
  · rw [hhalf]
    exact (b.alpha_le_halfGapCandidate next).trans
      (b.halfGapCandidate_succ_le_orderGapTop_succ_add_halfGapCandidate i hi)
  · rcases hleft with ⟨j, hji, hj⟩
    rw [← hj, b.orderGapTop_succ_add_leftDefectCandidate i j hi]
    apply b.alpha_le_leftDefectCandidate
    change j.val ≤ i.val + 1
    have hji' : j.val ≤ i.val := hji
    omega
  · rcases hright with ⟨j, hij, hj⟩
    rw [← hj]
    by_cases hnextj : next ≤ j
    · exact (b.alpha_le_rightDefectCandidate hnextj).trans
        (b.rightDefectCandidate_succ_le_orderGapTop_succ_add_rightDefectCandidate
          i j hi)
    · have hjeq : j = i := by
        apply Fin.ext
        change j.val = i.val
        have hij' : i.val ≤ j.val := hij
        have hnot : ¬i.val + 1 ≤ j.val := by
          intro h
          exact hnextj h
        omega
      subst j
      rw [b.orderGapTop_succ_add_rightDefectCandidate_self i hi]
      apply b.alpha_le_leftDefectCandidate
      change i.val ≤ i.val + 1
      omega

/-- Beli (2006), property P1, proved from the definition of `alpha`. -/
theorem satisfiesAlphaP1_proved (b : GoodBONG q L (n + 1)) :
    b.SatisfiesAlphaP1 := by
  intro i hi
  let next : Fin n := ⟨i.1 + 1, hi⟩
  have hleftTop := b.alpha_le_orderGapTop_add_alpha_succ i hi
  have hrightTop := b.alpha_succ_le_orderGapTop_succ_add_alpha i hi
  rw [← b.coe_alphaValue, ← b.coe_alphaValue] at hleftTop hrightTop
  unfold orderGapTop at hleftTop hrightTop
  have hleft : b.alphaValue i ≤
      (b.orderGap i : ℚ) + b.alphaValue next := by
    norm_cast at hleftTop
  have hright : b.alphaValue next ≤
      (b.orderGap next : ℚ) + b.alphaValue i := by
    norm_cast at hrightTop
  have hnextCast : next.castSucc = i.succ := by
    apply Fin.ext
    rfl
  constructor
  · unfold alphaLeftEndpoint
    change (b.order i.castSucc : ℚ) + b.alphaValue i ≤
      (b.order next.castSucc : ℚ) + b.alphaValue next
    rw [hnextCast]
    unfold orderGap at hleft
    push_cast at hleft
    linarith
  · unfold alphaRightEndpoint
    change -(b.order next.succ : ℚ) + b.alphaValue next ≤
      -(b.order i.succ : ℚ) + b.alphaValue i
    rw [← hnextCast]
    unfold orderGap at hright
    push_cast at hright
    linarith

end BONG.GoodBONG

end Bong
