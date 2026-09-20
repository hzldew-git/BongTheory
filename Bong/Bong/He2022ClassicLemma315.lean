/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma314

/-!
# He (2024), Lemma 3.15

The even- and odd-target cases with two extra source variables are assembled
from Corollaries 3.10--3.13 and Theorem 2.5.  Endpoint alpha propagation and
the signed-prefix parity calculations are made explicit.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace BONG.GoodBONG

private theorem he2022ClassicNegOnePowOrder (k : Nat) :
    ordUnit K ((-1 : Kˣ) ^ k) = 0 := by
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  rw [ordUnit_pow, ordUnit_neg, hone]
  simp

private theorem he2022ClassicPrefixSumZero {s : Nat}
    (a : GoodBONG q L s) (k : Nat) (hk : k <= s)
    (hzero : forall i : Fin s, i.val < k -> a.order i = 0) :
    a.orderSequence.prefixSum k = 0 := by
  unfold BeliOrderSequence.prefixSum
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
  exact hzero ⟨i, by omega⟩ hi

private theorem he2022ClassicSignedFullDefectZeroOfLastOne {s : Nat}
    (a : GoodBONG q L (s + 1)) (epsilon : Kˣ)
    (hSign : ordUnit K epsilon = 0)
    (hzero : forall i : Fin (s + 1), i.val < s -> a.order i = 0)
    (hlast : a.order ⟨s, by omega⟩ = 1) :
    a.truncatedPrefixDefect a epsilon 0 (s + 1) = 0 := by
  have hprefixZero : a.orderSequence.prefixSum s = 0 := by
    unfold BeliOrderSequence.prefixSum
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
    exact hzero ⟨i, by omega⟩ (by omega)
  have hfullOdd : Odd (ordUnit K (a.prefixProduct (s + 1))) := by
    rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum (s + 1) le_rfl,
      a.orderSequence.prefixSum_succ,
      a.orderSequence_entryOrZero_eq_order (⟨s, by omega⟩ : Fin (s + 1)),
      hprefixZero, hlast]
    exact odd_one
  have hpzero : ordUnit K (a.prefixProduct 0) = 0 := by
    rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum 0 (by omega)]
    rfl
  have hodd : Odd (ordUnit K
      (epsilon * a.prefixProduct 0 * a.prefixProduct (s + 1))) := by
    rw [ordUnit_mul, ordUnit_mul, hSign, hpzero]
    simpa only [zero_add] using hfullOdd
  exact a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed
    (alphaV := beliUniversalAlphaLaws)
    (alphaW := beliUniversalAlphaLaws)
    a epsilon 0 (s + 1) hodd

/-- Lemma 3.15(i): even target rank and two extra source variables. -/
theorem he2022ClassicLemma315i (t : Nat)
    (a : GoodBONG q L (2 * t + 4))
    (b : GoodBONG r M (2 * t + 2))
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRn : a.order ⟨2 * t + 1, by omega⟩ = 0)
    (hRnOne : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hterminal :
      (a.order ⟨2 * t + 3, by omega⟩ = 0 ∧
        a.alphaValue ⟨2 * t + 2, by omega⟩ = 1 ∧
        defectOrder (K := K)
          (((-1 : Kˣ) ^ (t + 2)) * a.prefixProduct (2 * t + 4)) = 1) ∨
      a.order ⟨2 * t + 3, by omega⟩ = 1)
    (ambient : q.Represents r) :
    Lattice.Represents q r L M := by
  let zeroGap : Fin (2 * t + 3) := ⟨2 * t + 1, by omega⟩
  let terminalGap : Fin (2 * t + 3) := ⟨2 * t + 2, by omega⟩
  have hzeroThrough : forall i : Fin (2 * t + 4),
      i <= zeroGap.succ -> a.order i = 0 := by
    apply (a.he2022ClassicProposition24 hAClassic).zeroPairForcesPrefixZero
      zeroGap
    · have hindex : zeroGap.castSucc =
          (⟨2 * t + 1, by omega⟩ : Fin (2 * t + 4)) := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact hRn
    · have hindex : zeroGap.succ =
          (⟨2 * t + 2, by omega⟩ : Fin (2 * t + 4)) := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact hRnOne
  have hzero : forall i : Fin (2 * t + 4),
      i.val < 2 * t + 3 -> a.order i = 0 := by
    intro i hi
    apply hzeroThrough i
    apply Fin.mk_le_mk.mpr
    change i.val <= 2 * t + 2
    omega
  have hlast : a.order ⟨2 * t + 3, by omega⟩ = 0 ∨
      a.order ⟨2 * t + 3, by omega⟩ = 1 := by
    rcases hterminal with hfirst | hsecond
    · exact Or.inl hfirst.1
    · exact Or.inr hsecond
  have hAlphaTerminal : a.alphaValue terminalGap = 1 := by
    rcases hterminal with hfirst | hsecond
    · simpa only [terminalGap] using hfirst.2.1
    · apply a.alphaValue_eq_one_of_orderGap_eq_endpoint terminalGap
      right
      unfold orderGap
      change a.order (⟨2 * t + 3, by omega⟩ : Fin (2 * t + 4)) -
          a.order (⟨2 * t + 2, by omega⟩ : Fin (2 * t + 4)) = 1
      rw [hRnOne, hsecond]
      omega
  have halpha : forall i : Fin (2 * t + 3),
      i.val < 2 * t + 2 -> a.alphaValue i = 1 := by
    intro i hi
    have hthrough := a.he2022ClassicAlphaOneThrough hAClassic terminalGap
      (by
        intro k hk
        apply hzero k
        have hle := Fin.mk_le_mk.mp hk
        simp only [terminalGap] at hle
        omega)
      hAlphaTerminal i
      (by apply Fin.mk_le_mk.mpr; omega)
    exact hthrough
  have hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)) := by
    rcases hterminal with hfirst | hsecond
    · have hdefect := a.he2022ClassicFullSelfDefect
        ((-1 : Kˣ) ^ (t + 2)) hfirst.2.2
      rw [hfirst.1]
      norm_num at hdefect ⊢
      exact hdefect
    · have hdefect := a.he2022ClassicSignedFullDefectZeroOfLastOne
        ((-1 : Kˣ) ^ (t + 2))
        (he2022ClassicNegOnePowOrder (K := K) (t + 2)) hzero hsecond
      rw [hsecond]
      norm_num at hdefect ⊢
      exact hdefect
  have hgap : a.order ⟨2 * t + 3, by omega⟩ -
      a.order ⟨2 * t + 2, by omega⟩ <=
        2 * (ramificationIndex K : Int) := by
    have hePos := ramificationIndex_pos (K := K)
    rcases hlast with hzeroLast | honeLast
    · rw [hzeroLast, hRnOne]
      omega
    · rw [honeLast, hRnOne]
      omega
  apply a.he2022ClassicRepresents_of_pointwisePrime b (by omega) ambient
  · intro i
    exact a.he2022ClassicCorollary310i (m := 2 * t + 2) t b
      (by omega) (by omega) hBClassic
      (by intro k hk; exact hzero k (by omega)) (Or.inl hRnOne) i
  · intro i
    exact a.he2022ClassicCorollary311ii (m := 2 * t + 1) t b
      (by omega) hAClassic hBClassic
      (by intro k hk; exact hzero k (by omega)) halpha hRnOne
      hAlphaTerminal
      (by
        by_cases he : ramificationIndex K = 1
        · exact Or.inl he
        · right
          exact ⟨by have := ramificationIndex_pos (K := K); omega,
            hSourceEquality⟩)
      i
  · intro i
    exact a.he2022ClassicCorollary312ii (m := 2 * t) t b (by omega)
      hAClassic hBClassic (by intro k hk; exact hzero k (by omega))
      hRnOne hAlphaTerminal hSourceEquality i
  · intro i
    exact a.he2022ClassicCorollary313ii (2 * t) b
      (by intro k hk; exact hzero k (by omega)) (Or.inl hRnOne)
      hgap i (by have := i.succ_lt_large; omega)

/-- Lemma 3.15(ii): odd target rank and two extra source variables. -/
theorem he2022ClassicLemma315ii (t : Nat)
    (a : GoodBONG q L (2 * t + 5))
    (b : GoodBONG r M (2 * t + 3))
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRn : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hRnOne : a.order ⟨2 * t + 3, by omega⟩ = 0)
    (hterminal :
      (a.order ⟨2 * t + 4, by omega⟩ = 0 ∧
        a.alphaValue ⟨2 * t + 2, by omega⟩ = 1) ∨
      a.order ⟨2 * t + 4, by omega⟩ = 1)
    (ambient : q.Represents r) :
    Lattice.Represents q r L M := by
  let zeroGap : Fin (2 * t + 4) := ⟨2 * t + 2, by omega⟩
  let alphaN : Fin (2 * t + 4) := ⟨2 * t + 2, by omega⟩
  let alphaNOne : Fin (2 * t + 4) := ⟨2 * t + 3, by omega⟩
  have hzeroThrough : forall i : Fin (2 * t + 5),
      i <= zeroGap.succ -> a.order i = 0 := by
    apply (a.he2022ClassicProposition24 hAClassic).zeroPairForcesPrefixZero
      zeroGap
    · have hindex : zeroGap.castSucc =
          (⟨2 * t + 2, by omega⟩ : Fin (2 * t + 5)) := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact hRn
    · have hindex : zeroGap.succ =
          (⟨2 * t + 3, by omega⟩ : Fin (2 * t + 5)) := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact hRnOne
  have hzero : forall i : Fin (2 * t + 5),
      i.val < 2 * t + 4 -> a.order i = 0 := by
    intro i hi
    apply hzeroThrough i
    apply Fin.mk_le_mk.mpr
    change i.val <= 2 * t + 3
    omega
  have hlast : a.order ⟨2 * t + 4, by omega⟩ = 0 ∨
      a.order ⟨2 * t + 4, by omega⟩ = 1 := by
    rcases hterminal with hfirst | hsecond
    · exact Or.inl hfirst.1
    · exact Or.inr hsecond
  have hAlphaN : a.alphaValue alphaN = 1 := by
    rcases hterminal with hfirst | hsecond
    · simpa only [alphaN] using hfirst.2
    · have hAlphaNext : a.alphaValue alphaNOne = 1 := by
        apply a.alphaValue_eq_one_of_orderGap_eq_endpoint alphaNOne
        right
        unfold orderGap
        change a.order (⟨2 * t + 4, by omega⟩ : Fin (2 * t + 5)) -
            a.order (⟨2 * t + 3, by omega⟩ : Fin (2 * t + 5)) = 1
        rw [hRnOne, hsecond]
        omega
      have hthrough := a.he2022ClassicAlphaOneThrough hAClassic alphaNOne
        (by
          intro k hk
          apply hzero k
          have hle := Fin.mk_le_mk.mp hk
          simp only [alphaNOne] at hle
          omega)
        hAlphaNext alphaN
        (by apply Fin.mk_le_mk.mpr; omega)
      exact hthrough
  have hAlphaNOne : a.alphaValue alphaNOne = 1 := by
    rcases hterminal with hfirst | hsecond
    · let leftGap : Fin (2 * t + 4) := ⟨2 * t + 2, by omega⟩
      let rightGap : Fin (2 * t + 4) := ⟨2 * t + 3, by omega⟩
      have hconstant := (a.he2022ClassicProposition22).constantAdjacentSum
        leftGap rightGap (by apply Fin.mk_le_mk.mpr; omega)
        (by
          unfold adjacentOrderSum
          change a.order (⟨2 * t + 2, by omega⟩ : Fin (2 * t + 5)) +
              a.order (⟨2 * t + 3, by omega⟩ : Fin (2 * t + 5)) =
            a.order (⟨2 * t + 3, by omega⟩ : Fin (2 * t + 5)) +
              a.order (⟨2 * t + 4, by omega⟩ : Fin (2 * t + 5))
          rw [hRn, hRnOne, hfirst.1])
        rightGap (by apply Fin.mk_le_mk.mpr; omega) le_rfl
      unfold alphaLeftEndpoint at hconstant
      have hleft : a.order leftGap.castSucc = 0 := by
        have hindex : leftGap.castSucc =
            (⟨2 * t + 2, by omega⟩ : Fin (2 * t + 5)) := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact hRn
      have hright : a.order rightGap.castSucc = 0 := by
        have hindex : rightGap.castSucc =
            (⟨2 * t + 3, by omega⟩ : Fin (2 * t + 5)) := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact hRnOne
      rw [hleft, hright] at hconstant
      norm_num at hconstant
      simpa only [alphaNOne, rightGap, alphaN, leftGap] using
        hconstant.trans hfirst.2
    · apply a.alphaValue_eq_one_of_orderGap_eq_endpoint alphaNOne
      right
      unfold orderGap
      change a.order (⟨2 * t + 4, by omega⟩ : Fin (2 * t + 5)) -
          a.order (⟨2 * t + 3, by omega⟩ : Fin (2 * t + 5)) = 1
      rw [hRnOne, hsecond]
      omega
  have halpha : forall i : Fin (2 * t + 4),
      i.val < 2 * t + 3 -> a.alphaValue i = 1 := by
    intro i hi
    exact a.he2022ClassicAlphaOneThrough hAClassic alphaNOne
      (by
        intro k hk
        apply hzero k
        have hle := Fin.mk_le_mk.mp hk
        simp only [alphaNOne] at hle
        omega)
      hAlphaNOne i (by apply Fin.mk_le_mk.mpr; omega)
  have hprefixZero : a.orderSequence.prefixSum (2 * t + 4) = 0 := by
    exact a.he2022ClassicPrefixSumZero (2 * t + 4) (by omega) hzero
  have hprefixOrderZero : ordUnit K (a.prefixProduct (2 * t + 4)) = 0 := by
    rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (2 * t + 4) (by omega), hprefixZero]
  have hrawEven : Even (ordUnit K
      (((-1 : Kˣ) ^ (t + 2)) * a.prefixProduct 0 *
        a.prefixProduct (2 * t + 4))) := by
    have hpzero : ordUnit K (a.prefixProduct 0) = 0 := by
      rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum 0 (by omega)]
      rfl
    rw [ordUnit_mul, ordUnit_mul,
      he2022ClassicNegOnePowOrder (K := K) (t + 2), hpzero,
      hprefixOrderZero]
    exact Even.zero
  have hrawOne : (1 : WithTop ℚ) <= defectOrder (K := K)
      (((-1 : Kˣ) ^ (t + 2)) * a.prefixProduct 0 *
        a.prefixProduct (2 * t + 4)) :=
    defectOrder_one_le_of_even _ hrawEven
  have hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)) := by
    have hcap : a.prefixAlphaCap (2 * t + 4) =
        ((1 : ℚ) : WithTop ℚ) := by
      rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
      have hindex : (⟨2 * t + 4 - 1, by omega⟩ : Fin (2 * t + 4)) =
          alphaNOne := by
        apply Fin.ext
        simp only [alphaNOne]
        omega
      rw [hindex, hAlphaNOne]
    unfold truncatedPrefixDefect
    rw [a.prefixAlphaCap_zero, hcap, hRnOne]
    simp only [min_top_left]
    change ((1 : ℚ) : WithTop ℚ) <=
      defectOrder (K := K)
        (((-1 : Kˣ) ^ (t + 2)) * a.prefixProduct 0 *
          a.prefixProduct (2 * t + 4)) at hrawOne
    rw [min_eq_right hrawOne]
    norm_num
  have hgap : a.order ⟨2 * t + 4, by omega⟩ -
      a.order ⟨2 * t + 3, by omega⟩ <=
        2 * (ramificationIndex K : Int) := by
    have hePos := ramificationIndex_pos (K := K)
    rcases hlast with hzeroLast | honeLast
    · rw [hzeroLast, hRnOne]
      omega
    · rw [honeLast, hRnOne]
      omega
  apply a.he2022ClassicRepresents_of_pointwisePrime b (by omega) ambient
  · intro i
    exact a.he2022ClassicCorollary310ii (m := 2 * t + 3) t b
      (by omega) hBClassic (by intro k hk; exact hzero k (by omega)) i
  · intro i
    exact a.he2022ClassicCorollary311iii (m := 2 * t + 2) t b
      (by omega) hAClassic hBClassic
      (by intro k hk; exact hzero k (by omega)) halpha
      hSourceEquality i
  · intro i
    exact a.he2022ClassicCorollary312iii (m := 2 * t) t b
      (by omega) hAClassic hBClassic
      (by intro k hk; exact hzero k (by omega)) hAlphaN
      hSourceEquality hRnOne hlast i
  · intro i
    exact a.he2022ClassicCorollary313ii (2 * t + 1) b
      (by intro k hk; exact hzero k (by omega)) (Or.inl hRnOne)
      hgap i (by have := i.succ_lt_large; omega)

end BONG.GoodBONG

end Bong
