/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalLemma48
import Bong.Bong.Beli2006AlphaBounds
import Bong.Bong.Beli2009AlphaMonotonicity
import Bong.Bong.Beli2019Lemma715Prefix
import Bong.Bong.Beli2019Lemma79TypeICaseOnePrefixDefect
import Bong.Bong.TwoBlockProductIsometry
import Bong.Lattice.OmearaStableModularCancellation

/-!
# Beli's residual invariants after a half-hyperbolic tower

This file formalizes Lemma 4.9 of "Universal integral quadratic forms over
dyadic local fields".  Paper indices are one based.  Thus deleting the first
`2 * k` coefficients sends the paper invariant `R'_i` to `R_{2k+i}` and
`alpha'_i` to `alpha_{2k+i}`.
-/

namespace Bong

open Dyadic Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

noncomputable local instance universalLemma49Discriminant :
    DyadicDiscriminantClassLaws K :=
  dyadicDiscriminantClassLawsProved

namespace BONG.GoodBONG

variable {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {k n : Nat}

/-- A scalar square has infinite `WithTop`-valued quadratic defect. -/
private theorem adjacentDefect_eq_top_of_isSquare
    (a : GoodBONG q L (n + 1)) (j : Fin n)
    (h : IsSquare (a.adjacentProduct j)) :
    a.adjacentDefect j = ⊤ := by
  unfold adjacentDefect defectOrder
  rw [quadraticDefect_eq_top_of_isSquare K h]
  rfl

/-- Adjacent order sums are monotone whenever the ambient BONG has at least
two entries.  This is the arbitrary-length form of
`GoodBONG.adjacentOrderSum_monotone`. -/
private theorem adjacentOrderSum_monotone_of_pos
    {N : Nat} (a : GoodBONG q L (N + 1)) (hN : 0 < N) :
    Monotone a.adjacentOrderSum := by
  have hlength : N + 1 = (N - 1) + 2 := by omega
  let c : GoodBONG q L ((N - 1) + 2) := a.castLength hlength
  have hc : Monotone c.adjacentOrderSum := c.adjacentOrderSum_monotone
  intro i j hij
  let i' : Fin ((N - 1) + 1) := ⟨i.val, by omega⟩
  let j' : Fin ((N - 1) + 1) := ⟨j.val, by omega⟩
  have hij' : i' ≤ j' := Fin.mk_le_mk.mpr hij
  have h := hc hij'
  unfold adjacentOrderSum at h ⊢
  simp only [c, GoodBONG.order_castLength] at h
  exact h

/--
The alpha invariant is local after a literal standard half-hyperbolic prefix.

The only ambient alpha candidates absent from the residual BONG begin inside
the deleted prefix.  At an even prefix index the endpoint dichotomy makes the
adjacent defect either infinite or exactly `2e`; at an odd prefix index the
adjacent sum monotonicity of a good BONG bounds the candidate by the residual
half-gap.  This is the candidate-compression calculation used in Lemma 4.9(i).
-/
theorem alphaValue_suffix_eq_of_standardHalfHyperbolicPrefix
    (a : GoodBONG q L ((2 * k + n) + 1))
    (b : GoodBONG r M (n + 1))
    (hprefix : ∀ i : Fin (2 * k),
      a.valueUnit ⟨i.val, by omega⟩ =
        standardHalfHyperbolicTowerValues (K := K) k i)
    (hsuffix : ∀ i : Fin (n + 1),
      a.valueUnit ⟨2 * k + i.val, by omega⟩ = b.valueUnit i)
    (hresidualHead : 0 ≤ b.order (0 : Fin (n + 1)))
    (i : Fin n) :
    a.alphaValue ⟨2 * k + i.val, by omega⟩ = b.alphaValue i := by
  let ia : Fin (2 * k + n) := ⟨2 * k + i.val, by omega⟩
  have horderSuffix (j : Fin (n + 1)) :
      a.order ⟨2 * k + j.val, by omega⟩ = b.order j := by
    rw [GoodBONG.order, GoodBONG.order,
      a.toBONG.order_eq_ordUnit, b.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) (hsuffix j)
  have hadjacentSuffix (j : Fin n) :
      a.adjacentDefect ⟨2 * k + j.val, by omega⟩ =
        b.adjacentDefect j := by
    unfold adjacentDefect adjacentProduct
    have hcast :
        (⟨2 * k + j.val, by omega⟩ : Fin (2 * k + n)).castSucc =
          ⟨2 * k + j.val, by omega⟩ := Fin.ext rfl
    have hsucc :
        (⟨2 * k + j.val, by omega⟩ : Fin (2 * k + n)).succ =
          ⟨2 * k + j.val + 1, by omega⟩ := Fin.ext rfl
    rw [hcast, hsucc]
    have h₀ := hsuffix j.castSucc
    have h₁ := hsuffix j.succ
    have hprod := congrArg₂ (fun x y : Kˣ ↦ -(x * y)) h₀ h₁
    exact congrArg (defectOrder (K := K)) hprod
  have hhalf : a.halfGapCandidate ia = b.halfGapCandidate i := by
    unfold halfGapCandidate
    have hcast : ia.castSucc = ⟨2 * k + i.val, by omega⟩ := Fin.ext rfl
    have hsucc : ia.succ = ⟨2 * k + i.val + 1, by omega⟩ := Fin.ext rfl
    rw [hcast, hsucc]
    have h₀ : a.order ⟨2 * k + i.val, by omega⟩ =
        b.order i.castSucc := by
      convert horderSuffix i.castSucc using 1
      apply congrArg a.order
      apply Fin.ext
      simp
    have h₁ : a.order ⟨2 * k + i.val + 1, by omega⟩ =
        b.order i.succ := by
      convert horderSuffix i.succ using 1
      apply congrArg a.order
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [h₀, h₁]
  have hleftLocal (j : Fin n) :
      a.leftDefectCandidate ia ⟨2 * k + j.val, by omega⟩ =
        b.leftDefectCandidate i j := by
    unfold leftDefectCandidate
    have hiSucc : ia.succ =
        ⟨2 * k + i.val + 1, by omega⟩ := Fin.ext rfl
    have hjCast :
        (⟨2 * k + j.val, by omega⟩ : Fin (2 * k + n)).castSucc =
          ⟨2 * k + j.val, by omega⟩ := Fin.ext rfl
    rw [hiSucc, hjCast]
    have hiOrder : a.order ⟨2 * k + i.val + 1, by omega⟩ =
        b.order i.succ := by
      convert horderSuffix i.succ using 1
      apply congrArg a.order
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    have hjOrder : a.order ⟨2 * k + j.val, by omega⟩ =
        b.order j.castSucc := by
      convert horderSuffix j.castSucc using 1
      apply congrArg a.order
      apply Fin.ext
      simp
    rw [hiOrder, hjOrder, hadjacentSuffix j]
  have hrightLocal (j : Fin n) :
      a.rightDefectCandidate ia ⟨2 * k + j.val, by omega⟩ =
        b.rightDefectCandidate i j := by
    unfold rightDefectCandidate
    have hjSucc :
        (⟨2 * k + j.val, by omega⟩ : Fin (2 * k + n)).succ =
          ⟨2 * k + j.val + 1, by omega⟩ := Fin.ext rfl
    have hiCast : ia.castSucc =
        ⟨2 * k + i.val, by omega⟩ := Fin.ext rfl
    rw [hjSucc, hiCast]
    have hjOrder : a.order ⟨2 * k + j.val + 1, by omega⟩ =
        b.order j.succ := by
      convert horderSuffix j.succ using 1
      apply congrArg a.order
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    have hiOrder : a.order ⟨2 * k + i.val, by omega⟩ =
        b.order i.castSucc := by
      convert horderSuffix i.castSucc using 1
      apply congrArg a.order
      apply Fin.ext
      simp
    rw [hjOrder, hiOrder, hadjacentSuffix j]
  have hprefixOrderEven (t : Fin k) :
      a.order ⟨2 * t.val, by omega⟩ = 0 := by
    let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
    letI : AddCommGroup T.Carrier := T.addCommGroup
    letI : Module K T.Carrier := T.module
    let c := standardHalfHyperbolicTowerBONG (K := K) k
    have hv := congrArg (ordUnit K)
      (hprefix (⟨2 * t.val, by omega⟩ : Fin (2 * k)))
    change a.order ⟨2 * t.val, by omega⟩ =
      c.order ⟨2 * t.val, by omega⟩ at hv
    have hp := standardHalfHyperbolicTowerBONG_orderPattern (K := K)
      (k := k) (Nat.one_le_iff_ne_zero.mpr (by
        intro hk
        subst k
        exact Fin.elim0 t)) t
    have hindex : (⟨2 * t.val, by omega⟩ : Fin (2 * k)) =
        halfModularPairIndexEquiv k (t, (0 : Fin 2)) := by
      apply Fin.ext
      simp
    rw [hindex, hp.1] at hv
    exact hv
  have hprefixOrderOdd (t : Fin k) :
      a.order ⟨2 * t.val + 1, by omega⟩ =
        -2 * (ramificationIndex K : Int) := by
    let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
    letI : AddCommGroup T.Carrier := T.addCommGroup
    letI : Module K T.Carrier := T.module
    let c := standardHalfHyperbolicTowerBONG (K := K) k
    have hv := congrArg (ordUnit K)
      (hprefix (⟨2 * t.val + 1, by omega⟩ : Fin (2 * k)))
    change a.order ⟨2 * t.val + 1, by omega⟩ =
      c.order ⟨2 * t.val + 1, by omega⟩ at hv
    have hp := standardHalfHyperbolicTowerBONG_orderPattern (K := K)
      (k := k) (Nat.one_le_iff_ne_zero.mpr (by
        intro hk
        subst k
        exact Fin.elim0 t)) t
    have hindex : (⟨2 * t.val + 1, by omega⟩ : Fin (2 * k)) =
        halfModularPairIndexEquiv k (t, (1 : Fin 2)) := by
      apply Fin.ext
      simp
    rw [hindex, hp.2] at hv
    simpa using hv
  have hevenDefectLower (t : Fin k) :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) ≤
        a.adjacentDefect ⟨2 * t.val, by omega⟩ := by
    let j : Fin (2 * k + n) := ⟨2 * t.val, by omega⟩
    let jFull : Fin ((2 * k + n) + 1) := ⟨2 * t.val, by omega⟩
    have hjNext : jFull.val + 1 < (2 * k + n) + 1 := by
      simp only [jFull]
      omega
    have hgap : a.order ⟨jFull.val + 1, hjNext⟩ - a.order jFull =
        -(2 * (ramificationIndex K : Int)) := by
      have hzero := hprefixOrderEven t
      have hone := hprefixOrderOdd t
      change a.order ⟨2 * t.val + 1, by omega⟩ -
          a.order ⟨2 * t.val, by omega⟩ = _
      rw [hzero, hone]
      ring
    have hcases := a.toBONG.adjacentSignedProduct_endpoint_cases jFull hjNext
      (a.toBONG.adjacentUnitSquareClass_endpoint_cases jFull hjNext hgap)
    have hcases' :
        IsSquare (a.adjacentProduct j) ∨
          IsSquare (a.adjacentProduct j *
            (universalLemma49Discriminant (K := K)).discriminantUnit) := by
      simpa [adjacentProduct, BONG.GoodBONG.valueUnit, j, jFull] using hcases
    change (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) (a.adjacentProduct j)
    rcases hcases' with hsquare | htwisted
    · rw [defectOrder_eq_top_of_isSquare hsquare]
      exact le_top
    · rw [defectOrder_eq_twoE_of_mul_discriminant_isSquare _ htwisted]
  apply WithTop.coe_injective
  rw [a.coe_alphaValue, b.coe_alphaValue]
  apply le_antisymm
  · have hmem := Finset.min'_mem (b.alphaCandidates i)
      (b.alphaCandidates_nonempty i)
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rcases hmem with hhalfEq | ⟨j, hji, hj⟩ | ⟨j, hij, hj⟩
    · exact (a.alpha_le_halfGapCandidate ia).trans_eq
        (hhalf.trans hhalfEq.symm)
    · have hlocal : (⟨2 * k + j.val, by omega⟩ : Fin (2 * k + n)) ≤ ia := by
        exact Fin.mk_le_mk.mpr (by omega)
      exact (a.alpha_le_leftDefectCandidate hlocal).trans_eq
        ((hleftLocal j).trans hj)
    · have hlocal : ia ≤
          (⟨2 * k + j.val, by omega⟩ : Fin (2 * k + n)) := by
        exact Fin.mk_le_mk.mpr (by omega)
      exact (a.alpha_le_rightDefectCandidate hlocal).trans_eq
        ((hrightLocal j).trans hj)
  · apply Finset.le_min'
    intro x hx
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with hhalfEq | ⟨j, hji, hj⟩ | ⟨j, hij, hj⟩
    · rw [hhalfEq, hhalf]
      exact b.alpha_le_halfGapCandidate i
    · by_cases hjSuffix : 2 * k ≤ j.val
      · let jb : Fin n := ⟨j.val - 2 * k, by omega⟩
        have hjEq : j = ⟨2 * k + jb.val, by omega⟩ := by
          apply Fin.ext
          simp only [jb]
          omega
        have hjb : jb ≤ i := by
          change j.val - 2 * k ≤ i.val
          change j.val ≤ ia.val at hji
          simp only [ia] at hji
          omega
        rw [← hj, hjEq, hleftLocal jb]
        exact b.alpha_le_leftDefectCandidate hjb
      · have hjPrefix : j.val < 2 * k := by omega
        obtain ⟨t, ht⟩ : ∃ t : Nat, j.val = 2 * t ∨ j.val = 2 * t + 1 := by
          exact ⟨j.val / 2, by omega⟩
        rcases ht with heven | hodd
        · have htlt : t < k := by omega
          let tf : Fin k := ⟨t, htlt⟩
          have hindex : j = (⟨2 * tf.val, by omega⟩ : Fin (2 * k + n)) := by
            apply Fin.ext
            simpa [tf] using heven
          rw [← hj, hindex]
          have hN : 0 < 2 * k + n := by omega
          have hmono : Monotone a.adjacentOrderSum :=
            adjacentOrderSum_monotone_of_pos a hN
          have hsum :
              a.adjacentOrderSum
                  (⟨2 * tf.val, by omega⟩ : Fin (2 * k + n)) ≤
                a.adjacentOrderSum ia := by
            apply hmono
            change 2 * tf.val ≤ 2 * k + i.val
            omega
          unfold adjacentOrderSum at hsum
          change a.order ⟨2 * tf.val, by omega⟩ +
              a.order ⟨2 * tf.val + 1, by omega⟩ ≤
            a.order ia.castSucc + a.order ia.succ at hsum
          rw [hprefixOrderEven tf, hprefixOrderOdd tf,
            zero_add] at hsum
          have hsumQ :
              ((-2 * (ramificationIndex K : Int) : Int) : ℚ) ≤
                (a.order ia.castSucc : ℚ) + a.order ia.succ := by
            exact_mod_cast hsum
          have hbaseQ :
              ((a.order ia.succ - a.order ia.castSucc : Int) : ℚ) / 2 +
                  (ramificationIndex K : ℚ) ≤
                ((a.order ia.succ - 0 : Int) : ℚ) +
                  (2 * ramificationIndex K : Nat) := by
            push_cast at hsumQ ⊢
            have he : (0 : ℚ) ≤ ramificationIndex K := by positivity
            linarith
          calc
            b.alpha i ≤ b.halfGapCandidate i := b.alpha_le_halfGapCandidate i
            _ = a.halfGapCandidate ia := hhalf.symm
            _ ≤ a.leftDefectCandidate ia
                (⟨2 * tf.val, by omega⟩ : Fin (2 * k + n)) := by
              unfold halfGapCandidate leftDefectCandidate
              have hevenCast :
                  a.order
                    ((⟨2 * tf.val, by omega⟩ : Fin (2 * k + n)).castSucc) =
                    0 := by
                convert hprefixOrderEven tf using 1
                apply congrArg a.order
                apply Fin.ext
                rfl
              rw [hevenCast]
              have hdef := hevenDefectLower tf
              calc
                (((((a.order ia.succ - a.order ia.castSucc : Int) : ℚ) / 2 +
                    (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) ≤
                    ((((a.order ia.succ - 0 : Int) : ℚ) +
                      (2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) :=
                  WithTop.coe_le_coe.mpr hbaseQ
                _ = ((((a.order ia.succ - 0 : Int) : ℚ) : WithTop ℚ) +
                    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) := by
                  rw [← WithTop.coe_add]
                _ ≤ ((((a.order ia.succ - 0 : Int) : ℚ) : WithTop ℚ) +
                    a.adjacentDefect
                      (⟨2 * tf.val, by omega⟩ : Fin (2 * k + n))) :=
                  add_le_add_right hdef _
        · have htlt : t < k := by omega
          let tf : Fin k := ⟨t, htlt⟩
          have hindex : j =
              (⟨2 * tf.val + 1, by omega⟩ : Fin (2 * k + n)) := by
            apply Fin.ext
            simpa [tf] using hodd
          rw [← hj, hindex]
          have hN : 0 < 2 * k + n := by omega
          have hmono : Monotone a.adjacentOrderSum :=
            adjacentOrderSum_monotone_of_pos a hN
          have hsum' :
              -2 * (ramificationIndex K : Int) ≤
                a.order ia.castSucc + a.order ia.succ := by
            have hmono' :
                a.adjacentOrderSum
                    (⟨2 * tf.val + 1, by omega⟩ : Fin (2 * k + n)) ≤
                  a.adjacentOrderSum ia := by
              apply hmono
              change 2 * tf.val + 1 ≤ 2 * k + i.val
              omega
            unfold adjacentOrderSum at hmono'
            change a.order ⟨2 * tf.val + 1, by omega⟩ +
                a.order ⟨2 * tf.val + 2, by omega⟩ ≤
              a.order ia.castSucc + a.order ia.succ at hmono'
            rw [hprefixOrderOdd tf] at hmono'
            have hnextNonneg : 0 ≤
                a.order
                  (⟨2 * tf.val + 2, by omega⟩ : Fin ((2 * k + n) + 1)) := by
              by_cases hlast : tf.val + 1 = k
              · have hidx : 2 * tf.val + 2 = 2 * k := by omega
                rw [show (⟨2 * tf.val + 2, by omega⟩ :
                    Fin ((2 * k + n) + 1)) =
                      ⟨2 * k + (0 : Fin (n + 1)).val, by omega⟩ by
                    apply Fin.ext
                    simp [hidx]]
                rw [horderSuffix]
                exact hresidualHead
              · let tf' : Fin k := ⟨tf.val + 1, by omega⟩
                rw [show a.order
                    (⟨2 * tf.val + 2, by omega⟩ : Fin ((2 * k + n) + 1)) =
                      a.order ⟨2 * tf'.val, by omega⟩ by
                    apply congrArg a.order
                    apply Fin.ext
                    change 2 * tf.val + 2 = 2 * (tf.val + 1)
                    omega]
                rw [hprefixOrderEven tf']
            omega
          have hnonneg := defectOrder_nonneg_for_alpha (K := K)
            (a.adjacentProduct
              (⟨2 * tf.val + 1, by omega⟩ : Fin (2 * k + n)))
          rw [← b.coe_alphaValue]
          calc
            (b.alphaValue i : WithTop ℚ) = b.alpha i := b.coe_alphaValue i
            _ ≤ b.halfGapCandidate i := b.alpha_le_halfGapCandidate i
            _ = a.halfGapCandidate ia := hhalf.symm
            _ ≤ a.leftDefectCandidate ia
                (⟨2 * tf.val + 1, by omega⟩ : Fin (2 * k + n)) := by
              unfold halfGapCandidate leftDefectCandidate
              have hoddCast :
                  a.order
                    ((⟨2 * tf.val + 1, by omega⟩ :
                      Fin (2 * k + n)).castSucc) =
                    -2 * (ramificationIndex K : Int) := by
                convert hprefixOrderOdd tf using 1
                apply congrArg a.order
                apply Fin.ext
                rfl
              rw [hoddCast]
              have hsumQ :
                  ((-2 * (ramificationIndex K : Int) : Int) : ℚ) ≤
                    (a.order ia.castSucc : ℚ) + a.order ia.succ := by
                exact_mod_cast hsum'
              have hdefNonneg : (0 : WithTop ℚ) ≤
                  a.adjacentDefect
                    (⟨2 * tf.val + 1, by omega⟩ : Fin (2 * k + n)) :=
                hnonneg
              have hbaseQ :
                  ((a.order ia.succ - a.order ia.castSucc : Int) : ℚ) / 2 +
                      (ramificationIndex K : ℚ) ≤
                    ((a.order ia.succ -
                      (-2 * (ramificationIndex K : Int)) : Int) : ℚ) := by
                push_cast at hsumQ ⊢
                linarith
              calc
                (((((a.order ia.succ - a.order ia.castSucc : Int) : ℚ) / 2 +
                    (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) ≤
                    ((((a.order ia.succ -
                      (-2 * (ramificationIndex K : Int)) : Int) : ℚ)) :
                        WithTop ℚ) := WithTop.coe_le_coe.mpr hbaseQ
                _ ≤ ((((a.order ia.succ -
                      (-2 * (ramificationIndex K : Int)) : Int) : ℚ)) :
                        WithTop ℚ) +
                    a.adjacentDefect
                      (⟨2 * tf.val + 1, by omega⟩ : Fin (2 * k + n)) :=
                  le_add_of_nonneg_right hdefNonneg
    · have hjSuffix : 2 * k ≤ j.val := by
        change ia.val ≤ j.val at hij
        simp only [ia] at hij
        omega
      let jb : Fin n := ⟨j.val - 2 * k, by omega⟩
      have hjEq : j = ⟨2 * k + jb.val, by omega⟩ := by
        apply Fin.ext
        simp only [jb]
        omega
      have hijb : i ≤ jb := by
        change i.val ≤ j.val - 2 * k
        change ia.val ≤ j.val at hij
        simp only [ia] at hij
        omega
      rw [← hj, hjEq, hrightLocal jb]
      exact b.alpha_le_rightDefectCandidate hijb

/-- The diagonal quadratic space carried by the canonical good BONG of the
standard half-hyperbolic tower.  Over the field this is the paper's `H^k`. -/
noncomputable def standardHalfHyperbolicDiagonalSpace (k : Nat) :
    QuadraticSpace K (Fin (2 * k) → K) :=
  QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients
      (standardHalfHyperbolicTowerValues (K := K) k))
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero
      (standardHalfHyperbolicTowerValues (K := K) k))

/-- The diagonal tower occurring in Lemma 4.9(iii) is isometric to the field
space of the standard lattice `2⁻¹ A(0,0)^k`; this is the paper's `H^k`. -/
theorem standardHalfHyperbolicDiagonalSpace_isIsometric_halfTower (k : Nat) :
    let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
    letI : AddCommGroup T.Carrier := T.addCommGroup
    letI : Module K T.Carrier := T.module
    (standardHalfHyperbolicDiagonalSpace (K := K) k).IsIsometric T.form := by
  dsimp only
  let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  let b := standardHalfHyperbolicTowerBONG (K := K) k
  have hspace : b.toBONG.exactDiagonalSpace =
      standardHalfHyperbolicDiagonalSpace (K := K) k := by
    unfold BONG.exactDiagonalSpace standardHalfHyperbolicDiagonalSpace
    congr 1
  refine ⟨?_⟩
  rw [← hspace]
  exact b.toBONG.exactDiagonalizationIsometry.symm

/-- Internal adapted data behind all three assertions of Beli's Lemma 4.9.
The ambient BONG has a literal standard tower prefix, while the residual BONG
has been transported to the residual lattice specified by the given
splitting. -/
structure UniversalLemma49AdaptedData
    {U W : Type u} [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K U} {r : QuadraticSpace K W}
    {L : Lattice K U} {M : Lattice K W}
    (k n : Nat) (a : GoodBONG q L ((2 * k + n) + 1)) where
  ambient : GoodBONG q L ((2 * k + n) + 1)
  residual : GoodBONG r M (n + 1)
  ambientOrder_eq (i : Fin ((2 * k + n) + 1)) :
    ambient.order i = a.order i
  prefixValues (i : Fin (2 * k)) :
    ambient.valueUnit ⟨i.val, by omega⟩ =
      standardHalfHyperbolicTowerValues (K := K) k i
  residualValues (j : Fin (n + 1)) :
    ambient.valueUnit ⟨2 * k + j.val, by omega⟩ =
      residual.valueUnit j
  prefixIsometric (s : Nat) (hs : 2 * k + 1 ≤ s)
      (hsRank : s ≤ (2 * k + n) + 1) :
    (a.prefixDiagonalSpace s hsRank).IsIsometric
      (ambient.prefixDiagonalSpace s hsRank)

set_option maxHeartbeats 0 in
-- The two-block split, explicit tower identification, and stable cancellation
-- make this construction elaboration-heavy.
/-- Construct the adapted pair of good BONGs used in Lemma 4.9. -/
noncomputable def universalLemma49AdaptedData
    {U W : Type u} [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K U} {r : QuadraticSpace K W}
    {L : Lattice K U} {M : Lattice K W}
    (hk : 1 ≤ k)
    (a : GoodBONG q L ((2 * k + n) + 1))
    (hL : Lattice.IsIntegral q L) (hM : Lattice.IsIntegral r M)
    (presentation : Lattice.Isometry
      (Lattice.halfHyperbolicExtensionForm r k) q
      (Lattice.halfHyperbolicExtensionLattice M k) L) :
    UniversalLemma49AdaptedData (q := q) (r := r) (L := L) (M := M)
      k n a := by
  let residualModel := Lattice.quadraticLatticeModel r M
  have hsplit : (Lattice.quadraticLatticeModel q L).SplitsHalfHyperbolic k :=
    ⟨residualModel, ⟨presentation⟩⟩
  have hconditions : UniversalLemma48Conditions a k :=
    universalLemma48Conditions_of_splitsHalfHyperbolic hk a hL hsplit
  let hnormalized := hconditions.exists_standardTowerPrefix hk
  let c := Classical.choose hnormalized
  have hcPrefix := (Classical.choose_spec hnormalized).1
  have hcOrders := (Classical.choose_spec hnormalized).2.1
  have hcPrefixIso := (Classical.choose_spec hnormalized).2.2
  let boundary : Fin ((2 * k + n) + 1) := ⟨2 * k - 1, by omega⟩
  have hboundaryNext : boundary.val + 1 < (2 * k + n) + 1 := by
    simp only [boundary]
    omega
  let next : Fin ((2 * k + n) + 1) :=
    ⟨boundary.val + 1, hboundaryNext⟩
  let lastPair : Fin k := ⟨k - 1, by omega⟩
  have hboundaryIndex : boundary =
      ⟨2 * lastPair.val + 1, by have := hconditions.bound; omega⟩ := by
    apply Fin.ext
    simp [boundary, lastPair]
    omega
  have hnextIndex : next = ⟨2 * k, by omega⟩ := by
    apply Fin.ext
    simp [next, boundary]
    omega
  have hboundaryOrder : c.order boundary =
      -2 * (ramificationIndex K : Int) := by
    rw [hcOrders, hboundaryIndex]
    exact hconditions.evenOrders lastPair
  let firstPair : Fin k := ⟨0, by omega⟩
  have hzeroIndex : (0 : Fin ((2 * k + n) + 1)) =
      ⟨2 * firstPair.val, by have := hconditions.bound; omega⟩ := by
    apply Fin.ext
    simp [firstPair]
  have hzeroOrder : c.order (0 : Fin ((2 * k + n) + 1)) = 0 := by
    rw [hcOrders, hzeroIndex]
    exact hconditions.oddOrders firstPair
  have htailMono := c.order_le_add_two_mul 0 k (by omega)
  have htailNonneg : 0 ≤ c.order next := by
    calc
      0 = c.order (0 : Fin ((2 * k + n) + 1)) := hzeroOrder.symm
      _ ≤ c.order ⟨0 + 2 * k, by omega⟩ := htailMono
      _ = c.order next := by
        apply congrArg c.order
        apply Fin.ext
        simp [next, boundary]
        omega
  have hboundaryLe : c.order boundary ≤ c.order next := by
    rw [hboundaryOrder]
    have he : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  have hnextAsSucc : next =
      ⟨boundary.val + 1, hboundaryNext⟩ := rfl
  have hboundaryLe' : c.toBONG.order boundary ≤
      c.toBONG.order ⟨boundary.val + 1, hboundaryNext⟩ := by
    change c.order boundary ≤ c.order _
    rw [← hnextAsSucc]
    exact hboundaryLe
  let S := Classical.choice
    (c.toBONG.beliCorollary44_i_unconditional c.good boundary
      hboundaryNext hboundaryLe')
  have hcutEq : boundary.val + 1 = 2 * k := by
    simp only [boundary]
    omega
  have hrightLength :
      ((2 * k + n) + 1) - (boundary.val + 1) = n + 1 := by
    simp only [boundary]
    omega
  let rightRaw := S.right.toGoodBONG c.good
  let right : GoodBONG
      (q.restrict S.right.carrier S.right.nondegenerate)
      S.right.lattice (n + 1) := rightRaw.castLength hrightLength
  let leftRaw := S.left.toGoodBONG c.good
  let left : GoodBONG
      (q.restrict S.left.carrier S.left.nondegenerate)
      S.left.lattice (2 * k) := leftRaw.castLength hcutEq
  let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) k
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  let towerBONG := standardHalfHyperbolicTowerBONG (K := K) k
  have hleftValues : ∀ i : Fin (2 * k),
      towerBONG.toBONG.value i = left.toBONG.value i := by
    intro i
    let j : Fin (boundary.val + 1) := ⟨i.val, by omega⟩
    have hsource : S.left.sourceIndex j =
        (⟨i.val, by omega⟩ : Fin ((2 * k + n) + 1)) := by
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val, Nat.zero_add]
      simp only [j]
    have hcast := GoodBONG.valueUnit_castLength leftRaw hcutEq i
    change (towerBONG.valueUnit i : K) = (left.valueUnit i : K)
    rw [show left.valueUnit i = S.left.bong.valueUnit j by
      have hraw : leftRaw.valueUnit ⟨i.val, by omega⟩ =
          S.left.bong.valueUnit j := by
        change S.left.bong.valueUnit _ = S.left.bong.valueUnit j
        apply congrArg S.left.bong.valueUnit
        apply Fin.ext
        rfl
      exact hcast.trans hraw]
    rw [S.left.valueUnit_eq, hsource]
    exact congrArg Units.val (hcPrefix i).symm
  let leftIso := towerBONG.toBONG.latticeIsometryOfValueEq
    left.toBONG hleftValues
  let displayed : Lattice.Isometry
      (T.form.orthogonalSum
        (q.restrict S.right.carrier S.right.nondegenerate)) q
      (Lattice.product T.lattice S.right.lattice) L :=
    (leftIso.orthogonalProductBasic
      (Lattice.Isometry.refl
        (q.restrict S.right.carrier S.right.nondegenerate)
        S.right.lattice)).trans S.toProductLatticeIsometry
  let zeroLattice := QuadraticSpace.zeroCoordinateBasisLattice (K := K)
  let appendRight : Lattice.Isometry
      (T.form.orthogonalSum
        (q.restrict S.right.carrier S.right.nondegenerate))
      (Lattice.halfHyperbolicExtensionForm
        (q.restrict S.right.carrier S.right.nondegenerate) k)
      (Lattice.product T.lattice S.right.lattice)
      (Lattice.halfHyperbolicExtensionLattice S.right.lattice k) := by
    change Lattice.Isometry
      ((Lattice.omearaPlaneExtensionForm
        (Lattice.zeroCoordinateQuadraticSpace (K := K))
        (Lattice.dyadicHalfUnit (K := K)) k (fun _ ↦ 0)).orthogonalSum
        (q.restrict S.right.carrier S.right.nondegenerate))
      (Lattice.omearaPlaneExtensionForm
        (q.restrict S.right.carrier S.right.nondegenerate)
        (Lattice.dyadicHalfUnit (K := K)) k (fun _ ↦ 0))
      (Lattice.product
        (Lattice.hyperbolicExtensionLattice zeroLattice k)
        S.right.lattice)
      (Lattice.hyperbolicExtensionLattice S.right.lattice k)
    exact Lattice.omearaPlaneExtensionAppendIsometry zeroLattice
      (q.restrict S.right.carrier S.right.nondegenerate)
      S.right.lattice (Lattice.dyadicHalfUnit (K := K)) k (fun _ ↦ 0)
  let rightPresentation := appendRight.symm.trans displayed
  let total := rightPresentation.trans presentation.symm
  let totalRaw : Lattice.Isometry
      (Lattice.omearaPlaneExtensionForm
        (q.restrict S.right.carrier S.right.nondegenerate)
        (Lattice.dyadicHalfUnit (K := K)) k (fun _ ↦ 0))
      (Lattice.omearaPlaneExtensionForm r
        (Lattice.dyadicHalfUnit (K := K)) k (fun _ ↦ 0))
      (Lattice.hyperbolicExtensionLattice S.right.lattice k)
      (Lattice.hyperbolicExtensionLattice M k) := by
    rw [← Lattice.halfHyperbolicExtensionForm_eq
        (q.restrict S.right.carrier S.right.nondegenerate) k,
      ← Lattice.halfHyperbolicExtensionForm_eq r k,
      ← Lattice.halfHyperbolicExtensionLattice_eq S.right.lattice k,
      ← Lattice.halfHyperbolicExtensionLattice_eq M k]
    exact total
  let residualIso := Lattice.cancelScaledZeroOmearaPlaneExtension
    (Lattice.dyadicHalfUnit (K := K)) k totalRaw
  let residual := right.mapLatticeIsometry residualIso
  refine {
    ambient := c
    residual := residual
    ambientOrder_eq := hcOrders
    prefixValues := hcPrefix
    residualValues := ?_
    prefixIsometric := hcPrefixIso }
  intro j
  have hcast := GoodBONG.valueUnit_castLength rightRaw hrightLength j
  have hsource : S.right.sourceIndex
      (⟨j.val, by omega⟩ : Fin (((2 * k + n) + 1) -
        (boundary.val + 1))) =
      (⟨2 * k + j.val, by omega⟩ : Fin ((2 * k + n) + 1)) := by
    apply Fin.ext
    simp only [BONG.SegmentWitness.sourceIndex_val]
    rw [hcutEq]
  calc
    c.valueUnit ⟨2 * k + j.val, by omega⟩ =
        S.right.bong.valueUnit
          (⟨j.val, by omega⟩ : Fin (((2 * k + n) + 1) -
            (boundary.val + 1))) := by
      change c.toBONG.valueUnit ⟨2 * k + j.val, by omega⟩ = _
      rw [S.right.valueUnit_eq, hsource]
    _ = right.valueUnit j := by
      have hraw : rightRaw.valueUnit ⟨j.val, by omega⟩ =
          S.right.bong.valueUnit
            (⟨j.val, by omega⟩ : Fin (((2 * k + n) + 1) -
              (boundary.val + 1))) := by
        rfl
      exact hraw.symm.trans hcast.symm
    _ = residual.valueUnit j := by
      exact (GoodBONG.valueUnit_mapLatticeIsometry residualIso right j).symm

namespace UniversalLemma49AdaptedData

variable {U W : Type u} [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K U} {r : QuadraticSpace K W}
  {L : Lattice K U} {M : Lattice K W}
  {a : GoodBONG q L ((2 * k + n) + 1)}

/-- The residual orders are the shifted ambient orders. -/
theorem order_shift (D : UniversalLemma49AdaptedData
    (q := q) (r := r) (L := L) (M := M) k n a)
    (j : Fin (n + 1)) :
    D.residual.order j =
      a.order ⟨2 * k + j.val, by omega⟩ := by
  have hv := congrArg (ordUnit K) (D.residualValues j)
  change D.ambient.order ⟨2 * k + j.val, by omega⟩ =
    D.residual.order j at hv
  exact hv.symm.trans (D.ambientOrder_eq ⟨2 * k + j.val, by omega⟩)

/-- Part (i), alpha shift, first for the splitting-adapted pair. -/
theorem alpha_shift (D : UniversalLemma49AdaptedData
    (q := q) (r := r) (L := L) (M := M) k n a)
    (hM : Lattice.IsIntegral r M) (i : Fin n) :
    D.residual.alphaValue i =
      a.alphaValue ⟨2 * k + i.val, by omega⟩ := by
  have hhead : 0 ≤ D.residual.order (0 : Fin (n + 1)) :=
    (BONG.beliUniversalLemma22 D.residual.toBONG).mp hM
  have hlocal := alphaValue_suffix_eq_of_standardHalfHyperbolicPrefix
    D.ambient D.residual D.prefixValues D.residualValues hhead i
  letI : GoodBONGClassificationLaws.{u, u, u} K :=
    goodBONGClassificationLawsProved K
  have hambient := a.alpha_invariant D.ambient
    ⟨2 * k + i.val, by omega⟩
  exact hlocal.symm.trans hambient.symm

/-- The prefix product of the adapted ambient BONG factors into the complete
standard tower product and the corresponding residual prefix product. -/
theorem prefixProduct_shift (D : UniversalLemma49AdaptedData
    (q := q) (r := r) (L := L) (M := M) k n a)
    (j : Nat) (hj : j ≤ n + 1) :
    D.ambient.prefixProduct (2 * k + j) =
      D.ambient.prefixProduct (2 * k) * D.residual.prefixProduct j := by
  induction j with
  | zero =>
      simp [GoodBONG.prefixProduct]
  | succ j ih =>
      have hjlt : j < n + 1 := by omega
      have hambientLt : 2 * k + j < (2 * k + n) + 1 := by omega
      unfold GoodBONG.prefixProduct at ih ⊢
      rw [show 2 * k + (j + 1) = (2 * k + j) + 1 by omega,
        D.ambient.toBONG.prefixProduct_succ (2 * k + j) hambientLt,
        D.residual.toBONG.prefixProduct_succ j hjlt, ih (by omega)]
      have hv := D.residualValues (⟨j, hjlt⟩ : Fin (n + 1))
      change D.ambient.toBONG.valueUnit ⟨2 * k + j, by omega⟩ =
        D.residual.toBONG.valueUnit ⟨j, hjlt⟩ at hv
      rw [hv]
      ac_rfl

/-- Internal alpha caps shift together with the residual boundary. -/
theorem prefixAlphaCap_shift (D : UniversalLemma49AdaptedData
    (q := q) (r := r) (L := L) (M := M) k n a)
    (hM : Lattice.IsIntegral r M)
    (j : Nat) (hj0 : 0 < j) (hj : j ≤ n + 1) :
    D.ambient.prefixAlphaCap (2 * k + j) =
      D.residual.prefixAlphaCap j := by
  by_cases hlast : j = n + 1
  · subst j
    rw [show 2 * k + (n + 1) = (2 * k + n) + 1 by omega,
      D.ambient.prefixAlphaCap_last, D.residual.prefixAlphaCap_last]
  · have hjInternal : j < n + 1 := by omega
    rw [D.ambient.prefixAlphaCap_of_internal (by omega) (by omega),
      D.residual.prefixAlphaCap_of_internal hj0 hjInternal]
    have hhead : 0 ≤ D.residual.order (0 : Fin (n + 1)) :=
      (BONG.beliUniversalLemma22 D.residual.toBONG).mp hM
    have hα := alphaValue_suffix_eq_of_standardHalfHyperbolicPrefix
      D.ambient D.residual D.prefixValues D.residualValues hhead
        (⟨j - 1, by omega⟩ : Fin n)
    have hindex :
        (⟨(2 * k + j) - 1, by omega⟩ : Fin (2 * k + n)) =
          ⟨2 * k + (j - 1), by omega⟩ := by
      apply Fin.ext
      simp only
      omega
    rw [hindex]
    exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hα

/-- Part (ii), away from the first residual coefficient, for the adapted
pair. -/
theorem truncatedSegmentDefect_shift (D : UniversalLemma49AdaptedData
    (q := q) (r := r) (L := L) (M := M) k n a)
    (hM : Lattice.IsIntegral r M) (epsilon : Kˣ)
    (i j : Nat) (hi : 1 < i) (hij : i ≤ j) (hj : j ≤ n + 1) :
    D.residual.truncatedSegmentDefect epsilon i j =
      D.ambient.truncatedSegmentDefect epsilon (2 * k + i) (2 * k + j) := by
  have hiBound : i - 1 ≤ n + 1 := by omega
  have hiPos : 0 < i - 1 := by omega
  have hjPos : 0 < j := by omega
  have hleftProduct := D.prefixProduct_shift (i - 1) hiBound
  have hrightProduct := D.prefixProduct_shift j hj
  have hleftCap := D.prefixAlphaCap_shift hM (i - 1) hiPos hiBound
  have hrightCap := D.prefixAlphaCap_shift hM j hjPos hj
  have hindex : (2 * k + i) - 1 = 2 * k + (i - 1) := by omega
  let P := D.ambient.prefixProduct (2 * k)
  let X := D.residual.prefixProduct (i - 1)
  let Y := D.residual.prefixProduct j
  have hraw : defectOrder (K := K)
      (epsilon * (P * X) * (P * Y)) =
        defectOrder (K := K) (epsilon * X * Y) := by
    have hfactor : epsilon * (P * X) * (P * Y) =
        (epsilon * X * Y) * P ^ 2 := by
      simp only [pow_two]
      ac_rfl
    rw [hfactor, defectOrder_mul_square]
  unfold truncatedSegmentDefect truncatedPrefixDefect
  rw [hindex, hleftProduct, hrightProduct, hleftCap, hrightCap]
  exact congrArg (fun z ↦ min z
    (min (D.residual.prefixAlphaCap (i - 1))
      (D.residual.prefixAlphaCap j))) hraw.symm

/-- Part (ii) at the first residual coefficient.  The signed determinant of
the deleted standard tower is a square, which supplies the paper's factor
`(-1)^k`. -/
theorem truncatedInitialSegmentDefect_shift
    (D : UniversalLemma49AdaptedData
      (q := q) (r := r) (L := L) (M := M) k n a)
    (hM : Lattice.IsIntegral r M) (epsilon : Kˣ)
    (j : Nat) (hj : 1 < j) (hjBound : j ≤ n + 1) :
    D.residual.truncatedSegmentDefect epsilon 1 j =
      D.ambient.truncatedSegmentDefect
        (((-1 : Kˣ) ^ k) * epsilon) 1 (2 * k + j) := by
  have hrightProduct := D.prefixProduct_shift j hjBound
  have hrightCap := D.prefixAlphaCap_shift hM j (by omega) hjBound
  have hsquare : IsSquare
      (((-1 : Kˣ) ^ k) * D.ambient.prefixProduct (2 * k)) := by
    simpa [BONG.signedEvenPrefixProduct, GoodBONG.prefixProduct] using
      (isSquare_signedEvenPrefixProduct_of_standardPrefix
        (a := D.ambient) (k := k) (by omega) D.prefixValues)
  rcases hsquare with ⟨s, hs⟩
  have hrightProduct' :
      D.ambient.toBONG.prefixProduct (2 * k + j) =
        D.ambient.toBONG.prefixProduct (2 * k) *
          D.residual.toBONG.prefixProduct j := by
    simpa only [GoodBONG.prefixProduct] using hrightProduct
  have hraw : defectOrder (K := K)
      ((((-1 : Kˣ) ^ k) * epsilon) *
        (D.ambient.prefixProduct (2 * k) *
          D.residual.prefixProduct j)) =
      defectOrder (K := K) (epsilon * D.residual.prefixProduct j) := by
    have hfactor : (((-1 : Kˣ) ^ k) * epsilon) *
        (D.ambient.prefixProduct (2 * k) *
          D.residual.prefixProduct j) =
        (epsilon * D.residual.prefixProduct j) * s ^ 2 := by
      simp only [pow_two]
      rw [← hs]
      ac_rfl
    rw [hfactor, defectOrder_mul_square]
  have hraw' : defectOrder (K := K)
      ((((-1 : Kˣ) ^ k) * epsilon) *
        (D.ambient.toBONG.prefixProduct (2 * k) *
          D.residual.toBONG.prefixProduct j)) =
      defectOrder (K := K)
        (epsilon * D.residual.toBONG.prefixProduct j) := by
    simpa only [GoodBONG.prefixProduct] using hraw
  unfold truncatedSegmentDefect truncatedPrefixDefect
  simp only [Nat.reduceSub, GoodBONG.prefixProduct,
    BONG.prefixProduct_zero, mul_one, D.residual.prefixAlphaCap_zero,
    D.ambient.prefixAlphaCap_zero, min_top_left]
  rw [hrightProduct', hrightCap, hraw']

/-- Part (iii): every nonempty residual prefix splits from the corresponding
ambient prefix after the common standard hyperbolic tower. -/
theorem prefix_split (D : UniversalLemma49AdaptedData
    (q := q) (r := r) (L := L) (M := M) k n a)
    (i : Fin (n + 1)) :
    (a.prefixDiagonalSpace (2 * k + i.val + 1) (by omega)).IsIsometric
      ((standardHalfHyperbolicDiagonalSpace (K := K) k).orthogonalSum
        (D.residual.prefixDiagonalSpace (i.val + 1) (by omega))) := by
  let residualPrefix :=
    D.residual.prefixValueUnits (i.val + 1) (by omega)
  have hcoeff : D.ambient.prefixValueUnits (2 * k + i.val + 1) (by omega) =
      Fin.append (standardHalfHyperbolicTowerValues (K := K) k)
        residualPrefix := by
    funext z
    by_cases hz : z.val < 2 * k
    · let x : Fin (2 * k) := ⟨z.val, hz⟩
      have hzEq : z = Fin.castAdd (i.val + 1) x := by
        apply Fin.ext
        rfl
      rw [hzEq, Fin.append_left]
      change D.ambient.valueUnit ⟨x.val, by omega⟩ = _
      exact D.prefixValues x
    · let y : Fin (i.val + 1) := ⟨z.val - 2 * k, by omega⟩
      have hzEq : z = Fin.natAdd (2 * k) y := by
        apply Fin.ext
        simp only [Fin.natAdd_mk, y]
        omega
      rw [hzEq, Fin.append_right]
      change D.ambient.valueUnit ⟨2 * k + y.val, by omega⟩ = _
      have hv := D.residualValues
        (⟨y.val, by have := y.isLt; omega⟩ : Fin (n + 1))
      change D.ambient.valueUnit ⟨2 * k + y.val, by omega⟩ =
        D.residual.valueUnit ⟨y.val, by omega⟩ at hv
      simpa only [residualPrefix, GoodBONG.prefixValueUnits] using hv
  let splitDiagonal := QuadraticSpace.finiteDiagonalOrthogonalSumIsometry
    (standardHalfHyperbolicTowerValues (K := K) k) residualPrefix
  have hsplitExact :
      QuadraticSpace.Isometry
        ((standardHalfHyperbolicDiagonalSpace (K := K) k).orthogonalSum
          (D.residual.prefixExactDiagonalSpace (i.val + 1) (by omega)))
        (D.ambient.prefixExactDiagonalSpace
          (2 * k + i.val + 1) (by omega)) := by
    unfold standardHalfHyperbolicDiagonalSpace prefixExactDiagonalSpace
    simpa only [hcoeff] using splitDiagonal
  have hsplit :
      QuadraticSpace.Isometry
        ((standardHalfHyperbolicDiagonalSpace (K := K) k).orthogonalSum
          (D.residual.prefixDiagonalSpace (i.val + 1) (by omega)))
        (D.ambient.prefixDiagonalSpace (2 * k + i.val + 1) (by omega)) :=
    hsplitExact
  rcases D.prefixIsometric (2 * k + i.val + 1) (by omega) (by omega) with
    ⟨f⟩
  exact ⟨f.trans hsplit.symm⟩

end UniversalLemma49AdaptedData

/-- The rank assertion in Beli's Lemma 4.9(i), before normalizing the ambient
length to `2 * k + (n + 1)`.  Thus the paper equation is literally
`m + 1 = 2k + (m' + 1)`, equivalently `m' = m - 2k`. -/
theorem beliUniversalLemma49_rankEquation
    {U W : Type u} [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K U} {r : QuadraticSpace K W}
    {L : Lattice K U} {M : Lattice K W} {k m n : Nat}
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (presentation : Lattice.Isometry
      (Lattice.halfHyperbolicExtensionForm r k) q
      (Lattice.halfHyperbolicExtensionLattice M k) L) :
    m + 1 = 2 * k + (n + 1) := by
  let X := Lattice.quadraticLatticeModel q L
  let R := Lattice.quadraticLatticeModel r M
  have hfin := presentation.toLinearEquiv.finrank_eq
  change (R.adjoinHalfHyperbolic k).rank = X.rank at hfin
  rw [Lattice.QuadraticLatticeModel.rank_adjoinHalfHyperbolic] at hfin
  have ha := a.toBONG.length_eq_finrank
  have hb := b.toBONG.length_eq_finrank
  change m + 1 = X.rank at ha
  change n + 1 = R.rank at hb
  omega

/-- Paper-facing conclusion of Beli's Lemma 4.9 after using the rank equation
to write the ambient length as `2 * k + n + 1`.

The first four fields are assertions (i) and (ii) for the arbitrary good BONG
`b` supplied by the statement.  The last two fields express assertion (iii):
one may choose another good BONG of the same residual lattice so that every
nonempty residual prefix splits from the corresponding ambient prefix. -/
structure UniversalLemma49Conclusion
    {U W : Type u} [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K U} {r : QuadraticSpace K W}
    {L : Lattice K U} {M : Lattice K W} (k n : Nat)
    (a : GoodBONG q L ((2 * k + n) + 1))
    (b : GoodBONG r M (n + 1)) : Prop where
  orderShift (i : Fin (n + 1)) :
    b.order i = a.order ⟨2 * k + i.val, by omega⟩
  alphaShift (i : Fin n) :
    b.alphaValue i = a.alphaValue ⟨2 * k + i.val, by omega⟩
  segmentDefectShift (epsilon : Kˣ) (i j : Nat)
      (hi : 1 < i) (hij : i ≤ j) (hj : j ≤ n + 1) :
    b.truncatedSegmentDefect epsilon i j =
      a.truncatedSegmentDefect epsilon (2 * k + i) (2 * k + j)
  initialSegmentDefectShift (epsilon : Kˣ) (j : Nat)
      (hj : 1 < j) (hjBound : j ≤ n + 1) :
    b.truncatedSegmentDefect epsilon 1 j =
      a.truncatedSegmentDefect (((-1 : Kˣ) ^ k) * epsilon)
        1 (2 * k + j)
  chosenResidualPrefixSplits :
    ∃ chosenResidualBONG : GoodBONG r M (n + 1),
      ∀ i : Fin (n + 1),
        (a.prefixDiagonalSpace
          (2 * k + i.val + 1) (by omega)).IsIsometric
          ((standardHalfHyperbolicDiagonalSpace (K := K) k).orthogonalSum
            (chosenResidualBONG.prefixDiagonalSpace
              (i.val + 1) (by omega)))

set_option maxHeartbeats 0 in
-- Classification transports the adapted calculation back to both arbitrary
-- BONGs, and stable cancellation constructs the chosen residual BONG.
/-- Beli, Lemma 4.9, including all three clauses and without any additional
project-specific law parameter in the public theorem statement. -/
theorem beliUniversalLemma49
    {U W : Type u} [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K U} {r : QuadraticSpace K W}
    {L : Lattice K U} {M : Lattice K W} {k n : Nat}
    (hk : 1 ≤ k)
    (a : GoodBONG q L ((2 * k + n) + 1))
    (b : GoodBONG r M (n + 1))
    (hL : Lattice.IsIntegral q L) (hM : Lattice.IsIntegral r M)
    (presentation : Lattice.Isometry
      (Lattice.halfHyperbolicExtensionForm r k) q
      (Lattice.halfHyperbolicExtensionLattice M k) L) :
    UniversalLemma49Conclusion k n a b := by
  let D := universalLemma49AdaptedData hk a hL hM presentation
  letI : GoodBONGClassificationLaws.{u, u, u} K :=
    goodBONGClassificationLawsProved K
  letI : Beli2006PrefixChangeLaws.{u, u} K :=
    prefixChangeLawsOfClassification
  refine
    { orderShift := ?_
      alphaShift := ?_
      segmentDefectShift := ?_
      initialSegmentDefectShift := ?_
      chosenResidualPrefixSplits := ?_ }
  · intro i
    exact (b.order_invariant D.residual i).trans (D.order_shift i)
  · intro i
    exact (b.alpha_invariant D.residual i).trans (D.alpha_shift hM i)
  · intro epsilon i j hi hij hj
    exact (b.truncatedSegmentDefect_invariant D.residual epsilon i j).trans
      ((D.truncatedSegmentDefect_shift hM epsilon i j hi hij hj).trans
        (a.truncatedSegmentDefect_invariant D.ambient epsilon
          (2 * k + i) (2 * k + j)).symm)
  · intro epsilon j hj hjBound
    exact (b.truncatedSegmentDefect_invariant D.residual epsilon 1 j).trans
      ((D.truncatedInitialSegmentDefect_shift hM epsilon j hj hjBound).trans
        (a.truncatedSegmentDefect_invariant D.ambient
          (((-1 : Kˣ) ^ k) * epsilon) 1 (2 * k + j)).symm)
  · exact ⟨D.residual, fun i ↦ D.prefix_split i⟩

end BONG.GoodBONG

end Bong
