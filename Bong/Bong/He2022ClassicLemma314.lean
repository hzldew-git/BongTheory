/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicCorollary313
import Bong.Bong.Beli2019Lemma216Complete
import Bong.Bong.Beli2019OddPrefixDefect

/-!
# He (2024), Lemma 3.14

This file first packages the four pointwise conclusions of Corollaries
3.10--3.13 into the revised representation criterion.  It then proves the
odd-rank, one-extra-variable representation lemma exactly as stated in the
publisher version.
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

/-- The assembly step used in Lemmas 3.14 and 3.15.  The hypotheses are the
four pointwise predicates in the notation of Section 3; Lemma 2.16 changes
the publisher's condition (iii') back to Theorem 2.5(iii). -/
theorem he2022ClassicRepresents_of_pointwisePrime {m n : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 2))
    (hRank : n + 1 <= m + 1) (ambient : q.Represents r)
    (hOrder : forall i, a.HeClassicOrderConditionAt b hRank i)
    (hDefect : forall i, a.HeClassicDefectConditionAt b i)
    (hCentral : forall i, a.HeClassicPublishedCentralConditionAt b i)
    (hLong : forall i, a.HeClassicLongConditionAt b i) :
    Lattice.Represents q r L M := by
  have horder : a.RepresentationOrderCondition b hRank :=
    (a.heClassicOrderCondition_iff_forall_at b hRank).2 hOrder
  have hdefect : a.RepresentationDefectCondition b :=
    (a.heClassicDefectCondition_iff_forall_at b).2 hDefect
  have hcentral : a.CentralRepresentationConditionsPrime b :=
    (a.heClassicPublishedCentralConditions_iff_forall_at b).2 hCentral
  have hlong : a.LongRepresentationConditions b :=
    (a.heClassicLongConditions_iff_forall_at b).2 hLong
  let sourceLaws : Beli2006AlphaLaws.{u, v} K :=
    beliUniversalAlphaLaws
  let targetLaws : Beli2006AlphaLaws.{u, w} K :=
    beliUniversalAlphaLaws
  have htrigger : a.CentralTriggerEquivalence b :=
    a.beli2019Lemma216 (sourceLaws := sourceLaws)
      (targetLaws := targetLaws) b hRank horder hdefect
  have hprime : RepresentationConditionsPrime a b hRank :=
    { orderCondition := horder
      defectCondition := hdefect
      centralRepresentations := hcentral
      longRepresentations := hlong }
  have hconditions : RepresentationConditions a b hRank :=
    (representationConditions_iff_prime a b hRank htrigger).2 hprime
  exact (a.he2022ClassicTheorem25 hRank ambient b).2 hconditions

/-- If a prefix of source orders vanishes through `j` and `alpha_j=1`,
Proposition 2.4(vi) gives alpha one at every gap through `j`. -/
theorem he2022ClassicAlphaOneThrough {s : Nat}
    (a : GoodBONG q L (s + 2))
    (hClassic : Lattice.IsClassicIntegral q L)
    (j : Fin (s + 1))
    (horders : forall i : Fin (s + 2), i <= j.castSucc -> a.order i = 0)
    (hterminal : a.alphaValue j = 1) :
    forall i : Fin (s + 1), i <= j -> a.alphaValue i = 1 := by
  have hbefore :=
    (a.he2022ClassicProposition24 hClassic).alphaOneOnZeroPrefix
      j horders j le_rfl (le_of_eq hterminal)
  intro i hi
  by_cases heq : i = j
  · simpa only [heq] using hterminal
  · exact hbefore i (lt_of_le_of_ne hi heq)

/-- A signed full-prefix defect is unchanged by the two omitted endpoint
caps. -/
theorem he2022ClassicFullSelfDefect {s : Nat}
    (a : GoodBONG q L (s + 1)) (epsilon : Kˣ)
    (hraw : defectOrder (K := K) (epsilon * a.prefixProduct (s + 1)) = 1) :
    a.truncatedPrefixDefect a epsilon 0 (s + 1) = 1 := by
  unfold truncatedPrefixDefect
  rw [a.prefixAlphaCap_zero, a.prefixAlphaCap_last]
  simpa [GoodBONG.prefixProduct] using hraw

/-- Lemma 3.14.  Here the target rank is `2t+3` and the source rank is one
larger.  The disjunction is the publisher's two displayed terminal cases. -/
theorem he2022ClassicLemma314 (t : Nat)
    (a : GoodBONG q L (2 * t + 4))
    (b : GoodBONG r M (2 * t + 3))
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRnMinusOne : a.order ⟨2 * t + 1, by omega⟩ = 0)
    (hRn : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hterminal :
      (a.order ⟨2 * t + 3, by omega⟩ = 0 ∧
        a.alphaValue ⟨2 * t + 2, by omega⟩ = 1 ∧
        defectOrder (K := K)
          (((-1 : Kˣ) ^ (t + 2)) * a.prefixProduct (2 * t + 4)) = 1) ∨
      a.order ⟨2 * t + 3, by omega⟩ = 1)
    (ambient : q.Represents r) :
    Lattice.Represents q r L M := by
  let terminalGap : Fin (2 * t + 3) := ⟨2 * t + 2, by omega⟩
  let zeroGap : Fin (2 * t + 3) := ⟨2 * t + 1, by omega⟩
  have hzeroThrough : forall i : Fin (2 * t + 4),
      i <= zeroGap.succ -> a.order i = 0 := by
    apply (a.he2022ClassicProposition24 hAClassic).zeroPairForcesPrefixZero
      zeroGap
    · have hindex : zeroGap.castSucc =
          (⟨2 * t + 1, by omega⟩ : Fin (2 * t + 4)) := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact hRnMinusOne
    · have hindex : zeroGap.succ =
          (⟨2 * t + 2, by omega⟩ : Fin (2 * t + 4)) := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact hRn
  have hzero : forall i : Fin (2 * t + 4),
      i.val < 2 * t + 3 -> a.order i = 0 := by
    intro i hi
    apply hzeroThrough i
    apply Fin.mk_le_mk.mpr
    change i.val <= 2 * t + 2
    omega
  have hnext : a.order ⟨2 * t + 3, by omega⟩ = 0 ∨
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
      rw [hRn, hsecond]
      omega
  have halpha : forall i : Fin (2 * t + 3),
      i.val < 2 * t + 3 -> a.alphaValue i = 1 := by
    intro i _hi
    apply a.he2022ClassicAlphaOneThrough hAClassic terminalGap
    · intro k hk
      apply hzero k
      have := Fin.mk_le_mk.mp hk
      simp only [terminalGap] at this
      omega
    · exact hAlphaTerminal
    · apply Fin.mk_le_mk.mpr
      omega
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
    · have hprefixZero : a.orderSequence.prefixSum (2 * t + 3) = 0 := by
        unfold BeliOrderSequence.prefixSum
        apply Finset.sum_eq_zero
        intro i hi
        simp only [Finset.mem_range] at hi
        rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
        exact hzero ⟨i, by omega⟩ (by omega)
      have hfullPrefixOdd : Odd (ordUnit K (a.prefixProduct (2 * t + 4))) := by
        rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
          (2 * t + 4) le_rfl,
          a.orderSequence.prefixSum_succ,
          a.orderSequence_entryOrZero_eq_order
            (⟨2 * t + 3, by omega⟩ : Fin (2 * t + 4)),
          hprefixZero, hsecond]
        exact odd_one
      have hsignOrder : ordUnit K ((-1 : Kˣ) ^ (t + 2)) = 0 := by
        have hone : ordUnit K (1 : Kˣ) = 0 := by
          have h := ordUnit_mul K (1 : Kˣ) 1
          simp only [mul_one] at h
          omega
        rw [ordUnit_pow, ordUnit_neg, hone]
        simp
      have hodd : Odd (ordUnit K
          (((-1 : Kˣ) ^ (t + 2)) * a.prefixProduct 0 *
            a.prefixProduct (2 * t + 4))) := by
        rw [ordUnit_mul, ordUnit_mul, hsignOrder]
        have hpzero : ordUnit K (a.prefixProduct 0) = 0 := by
          rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum 0
            (by omega)]
          rfl
        rw [hpzero, zero_add]
        simpa only [zero_add] using hfullPrefixOdd
      have hdefect :
          a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
              (2 * t + 4) = 0 :=
        a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed
          (alphaV := beliUniversalAlphaLaws)
          (alphaW := beliUniversalAlphaLaws)
          a ((-1) ^ (t + 2)) 0 (2 * t + 4) hodd
      rw [hsecond]
      norm_num at hdefect ⊢
      exact hdefect
  apply a.he2022ClassicRepresents_of_pointwisePrime b (by omega) ambient
  · intro i
    exact a.he2022ClassicCorollary310ii (m := 2 * t + 2) t b
      (by omega) hBClassic hzero i
  · intro i
    exact a.he2022ClassicCorollary311iii (m := 2 * t + 1) t b
      (by omega) hAClassic hBClassic hzero halpha hSourceEquality i
  · intro i
    exact a.he2022ClassicCorollary312iiiInitial (m := 2 * t) t b
      (by omega) hAClassic hBClassic hzero hAlphaTerminal
      hSourceEquality i (by have := i.lt_large; omega)
  · intro i
    exact a.he2022ClassicCorollary313i (2 * t + 1) b hzero hnext i
      (by have := i.succ_lt_large; omega)

end BONG.GoodBONG

end Bong
