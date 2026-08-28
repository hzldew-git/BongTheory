/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma75Arithmetic
import Bong.Bong.BeliCorollary44ThreeBlockProof

/-!
# Beli (2019), Lemma 7.5: binary-block splitting

The arithmetic part of Lemma 7.5 makes the orders alternate between `R` and
`R - 2e`.  Corollary 4.4(ii) therefore splits every descending adjacent pair
as the middle component of a three-block orthogonal decomposition.  At every
boundary between two such pairs, Corollary 4.4(i) gives the complementary
two-block split.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Every descending pair in the interval of Lemma 7.5 splits as an
orthogonal binary block of the ambient lattice. -/
theorem beli2019Lemma75_pairBlock_split
    [Beli2006AlphaLaws.{u, v} K]
    [BeliCorollary44Laws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (i j k : Fin (n + 1)) (R : Int)
    (hij : i ≤ j) (heven : Even (j.val - i.val))
    (hiOrder : b.order i.castSucc = R)
    (hterminal :
      b.order j.succ = R - 2 * (ramificationIndex K : Int))
    (hik : i ≤ k) (hkj : k ≤ j)
    (hkEven : Even (k.val - i.val)) :
    b.toBONG.HasThreeBlockSplit k.castSucc
      (Nat.succ_lt_succ k.isLt) := by
  let C := b.beli2019Lemma75_arithmetic i j R hij heven
    hiOrder hterminal
  have hkHigh : b.order k.castSucc = R :=
    C.even_order k hik hkj hkEven
  have hkLow : b.order k.succ =
      R - 2 * (ramificationIndex K : Int) := by
    apply C.odd_order k.succ
    · simp only [Fin.val_succ]
      omega
    · simp only [Fin.val_succ]
      omega
    · rcases hkEven with ⟨d, hd⟩
      refine ⟨d, ?_⟩
      simp only [Fin.val_succ]
      omega
  apply b.toBONG.beliCorollary44_ii_unconditional b.good k.castSucc
    (Nat.succ_lt_succ k.isLt)
  change b.order k.succ < b.order k.castSucc
  rw [hkLow, hkHigh]
  have hePos := ramificationIndex_pos (K := K)
  omega

/-- The cut between any two consecutive binary blocks in Lemma 7.5 is an
orthogonal two-block split. -/
theorem beli2019Lemma75_betweenPair_split
    [Beli2006AlphaLaws.{u, v} K]
    [BeliCorollary44Laws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (i j k : Fin (n + 1)) (R : Int)
    (hij : i ≤ j) (heven : Even (j.val - i.val))
    (hiOrder : b.order i.castSucc = R)
    (hterminal :
      b.order j.succ = R - 2 * (ramificationIndex K : Int))
    (hik : i ≤ k) (hkNext : k.val + 2 ≤ j.val)
    (hkEven : Even (k.val - i.val)) :
    b.toBONG.HasTwoBlockSplit (k.val + 2) (by omega) := by
  let C := b.beli2019Lemma75_arithmetic i j R hij heven
    hiOrder hterminal
  let next : Fin (n + 1) := ⟨k.val + 2, by omega⟩
  have hkLe : k ≤ j := by
    change k.val ≤ j.val
    omega
  have hkLow : b.order k.succ =
      R - 2 * (ramificationIndex K : Int) := by
    apply C.odd_order k.succ
    · simp only [Fin.val_succ]
      omega
    · simp only [Fin.val_succ]
      omega
    · rcases hkEven with ⟨d, hd⟩
      refine ⟨d, ?_⟩
      simp only [Fin.val_succ]
      omega
  have hnextEven : Even (next.val - i.val) := by
    rcases hkEven with ⟨d, hd⟩
    refine ⟨d + 1, ?_⟩
    dsimp [next]
    omega
  have hnextHigh : b.order next.castSucc = R := by
    apply C.even_order next
    · change i.val ≤ next.val
      dsimp [next]
      omega
    · change next.val ≤ j.val
      exact hkNext
    · exact hnextEven
  have hboundary : k.succ.val + 1 < n + 2 := by
    simp only [Fin.val_succ]
    omega
  apply b.toBONG.beliCorollary44_i_unconditional b.good k.succ hboundary
  change b.order k.succ ≤
    b.order ⟨k.succ.val + 1, hboundary⟩
  have hnextIndex :
      (⟨k.succ.val + 1, hboundary⟩ : Fin (n + 2)) =
        next.castSucc := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castSucc]
    rfl
  rw [hnextIndex, hkLow, hnextHigh]
  have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
  omega

end BONG.GoodBONG

end Bong
