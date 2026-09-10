/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma77
import Bong.Bong.He2022ClassicLemma58
import Bong.Bong.He2022ClassicPublishedTestingSet

/-!
# He, corrected v5, Lemma 7.1

This file formalizes the repaired even-target representation step in the
author-corrected v5 of Zilong He's paper *On classic n-universal quadratic
forms over dyadic local fields*.

The publisher version asserted that either one of the two odd `omega` rows
integrally represents every even-rank classic lattice.  That assertion fails
when the ramification index is greater than one.  Version 5 restricts the
large-ramification assertion to the displayed `C₁/C₂` targets whose parameter
has relative defect zero or one, and adds the separate test `C₁(1)`.

The first theorem below is the new terminal estimate used by v5.  The second
packages it with Corollaries 3.10(i), 3.11(ii), 3.12(ii), and 3.13(i), thereby
turning ambient representation into integral representation for precisely the
low-defect targets stated in corrected Lemma 7.1(ii).
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

private theorem he2022Classic71v5_prefixSum_zero {s : Nat}
    (a : GoodBONG q L s) (k : Nat) (hk : k <= s)
    (hzero : forall i : Fin s, i.val < k -> a.order i = 0) :
    a.orderSequence.prefixSum k = 0 := by
  unfold BeliOrderSequence.prefixSum
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
  exact hzero ⟨i, by omega⟩ hi

/-- Corrected Lemma 7.1(i), in diagonal coefficient form.  Every even-rank
diagonal quadratic space embeds in one of the two odd `omega` spaces.

The proof completes the target by its determinant class and then applies the
already verified two-class exhaustion for the two odd models. -/
theorem he2022ClassicLemma71v5_ambient_dichotomy
    [HilbertSymbolLaws K]
    (pairs : Nat) (w : Fin (2 * pairs + 2) -> Kˣ) :
    DiagonalRepresents (diagonalUnitCoefficients w)
        (diagonalUnitCoefficients
          (heClassicOddC1 (K := K) pairs (heClassicOmega (K := K)))) ∨
      DiagonalRepresents (diagonalUnitCoefficients w)
        (diagonalUnitCoefficients
          (heClassicOddC2Even (K := K) pairs (heClassicOmega (K := K))
            (heClassicOmega (K := K))
            (heClassicOmegaSharp (K := K)))) := by
  let first :=
    heClassicOddC1 (K := K) pairs (heClassicOmega (K := K))
  let second :=
    heClassicOddC2Even (K := K) pairs (heClassicOmega (K := K))
      (heClassicOmega (K := K)) (heClassicOmegaSharp (K := K))
  let d := diagonalUnitDeterminant w * diagonalUnitDeterminant first
  let completed : Fin (2 * pairs + 3) -> Kˣ := Fin.snoc w d
  have hdet : IsSquare
      (diagonalUnitDeterminant completed *
        diagonalUnitDeterminant first) := by
    refine ⟨diagonalUnitDeterminant w * diagonalUnitDeterminant first, ?_⟩
    simp only [completed, d, diagonalUnitDeterminant_snoc]
    ac_rfl
  have hp := heClassicOddC_evenOrder_pairProperties
    (K := K) pairs (heClassicOmega (K := K))
      (heClassicOmega (K := K)) (heClassicOmegaSharp (K := K))
      (heClassicOmegaSharp_hilbert_neg (K := K))
  have hclasses :
      DiagonalRepresents (diagonalUnitCoefficients completed)
          (diagonalUnitCoefficients first) ∨
        DiagonalRepresents (diagonalUnitCoefficients completed)
          (diagonalUnitCoefficients second) :=
    hp.exhaustive completed hdet
  have hprefix :
      DiagonalRepresents (diagonalUnitCoefficients w)
        (diagonalUnitCoefficients completed) := by
    convert DiagonalRepresents.prefixSucc
      (diagonalUnitCoefficients completed) using 1
    funext i
    simp only [completed, diagonalUnitCoefficients_snoc,
      Fin.snoc_castSucc]
  rcases hclasses with hfirst | hsecond
  · exact Or.inl (hprefix.trans hfirst)
  · exact Or.inr (hprefix.trans hsecond)

/-- The additional v5 test `C₁^(n+1)(1)` represents the exceptional
`H_e^n(1)` row.  This is the coefficient-level form of the integral identity
used in the corrected proof: delete the final unary coefficient from
`H₀^((n+1)/2) ⊥ <1>`, identify the remaining row with the first
canonical row of Lemma 2.11, and apply the established hyperbolic-pair
change of basis. -/
theorem he2022ClassicLemma71v5_C1One_represents_evenHOne
    (pairs : Nat) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heClassicEvenH (K := K) pairs 1))
      (diagonalUnitCoefficients (heClassicOddC1 (K := K) pairs 1)) := by
  have hprefix := DiagonalRepresents.prefixSucc
    (diagonalUnitCoefficients (heClassicOddC1 (K := K) pairs 1))
  have hfirst : DiagonalRepresents
      (diagonalUnitCoefficients
        (heClassicLemma211First (K := K) pairs))
      (diagonalUnitCoefficients
        (heClassicOddC1 (K := K) pairs 1)) := by
    convert hprefix using 1
    funext i
    simp only [diagonalUnitCoefficients, heClassicOddC1,
      Fin.snoc_castSucc, heClassicScaledHyperbolicTower_zero,
      heClassicLemma211First, heHuHyperbolicPair]
    by_cases hi : i.val < 2 * pairs
    · let j : Fin (2 * pairs) := ⟨i.val, hi⟩
      have hij : i = Fin.castAdd 2 j := Fin.ext rfl
      rw [hij, Fin.append_left]
      rfl
    · have htail : i.val = 2 * pairs ∨ i.val = 2 * pairs + 1 := by
        omega
      rcases htail with hzero | hone
      · have hij : i = Fin.natAdd (2 * pairs) (0 : Fin 2) := by
          apply Fin.ext
          simpa using hzero
        rw [hij, Fin.append_right]
        change (1 : K) =
          (AlternatingEndpointTower.standardHyperbolicEndpointTower
            (K := K) (pairs + 1)
            ⟨2 * pairs, by omega⟩ : Kˣ)
        rw [AlternatingEndpointTower.standardHyperbolicEndpointTower_even
          (t := ⟨pairs, by omega⟩)]
        simp
      · have hij : i = Fin.natAdd (2 * pairs) (1 : Fin 2) := by
          apply Fin.ext
          simpa using hone
        rw [hij, Fin.append_right]
        change (-1 : K) =
          (AlternatingEndpointTower.standardHyperbolicEndpointTower
            (K := K) (pairs + 1)
            ⟨2 * pairs + 1, by omega⟩ : Kˣ)
        rw [AlternatingEndpointTower.standardHyperbolicEndpointTower_odd
          (t := ⟨pairs, by omega⟩)]
        simp
  have honeOrder : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  exact (heClassicLemma211First_represents_evenHOne
    (K := K) pairs honeOrder).symm_of_sameRank.trans hfirst

/-- Every adjacent product in the literal `C₁(1)` row is a square, so
all of its adjacent defects are infinite. -/
theorem heClassicOddC1One_adjacentDefect_top
    (pairs : Nat) (j : Fin (2 * pairs + 2)) :
    let a := heClassicOddC1GoodBONG (K := K) pairs (1 : Kˣ) (by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega)
    a.adjacentDefect j = ⊤ := by
  dsimp only
  let hone : 0 <= ordUnit K (1 : Kˣ) := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  let a := heClassicOddC1GoodBONG (K := K) pairs (1 : Kˣ) hone
  change a.adjacentDefect j = ⊤
  by_cases hlast : j.val = 2 * pairs + 1
  · have hj : j = ⟨2 * pairs + 1, by omega⟩ := Fin.ext hlast
    rw [show a.adjacentDefect j =
        a.adjacentDefect (⟨2 * pairs + 1, by omega⟩ :
          Fin (2 * pairs + 2)) by rw [hj],
      show a.adjacentDefect
          (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
        defectOrder (K := K) (1 : Kˣ) by
          exact heClassicOddC1_lastAdjacentDefect
            (K := K) pairs 1 hone,
      defectOrder_one]
  · have hjNext : j.val + 1 < 2 * (pairs + 1) := by omega
    let current : Fin (2 * (pairs + 1)) := ⟨j.val, by omega⟩
    let next : Fin (2 * (pairs + 1)) := ⟨j.val + 1, hjNext⟩
    have hcast :
        (j.castSucc : Fin (2 * pairs + 3)) = current.castSucc :=
      Fin.ext rfl
    have hsucc :
        (j.succ : Fin (2 * pairs + 3)) = next.castSucc :=
      Fin.ext rfl
    have hratio :
        heClassicScaledHyperbolicTower (K := K) 0 (pairs + 1) next /
            heClassicScaledHyperbolicTower (K := K) 0 (pairs + 1) current =
          -1 := by
      simpa only [current, next] using
        heClassicScaledHyperbolicTower_zero_adjacentRatio
          (K := K) (pairs + 1) current (by
            simpa only [current] using hjNext)
    have hnext :
        heClassicScaledHyperbolicTower (K := K) 0 (pairs + 1) next =
          -(heClassicScaledHyperbolicTower (K := K) 0 (pairs + 1) current) := by
      calc
        _ = (heClassicScaledHyperbolicTower (K := K) 0 (pairs + 1) next /
              heClassicScaledHyperbolicTower (K := K) 0 (pairs + 1) current) *
            heClassicScaledHyperbolicTower (K := K) 0 (pairs + 1) current := by
              simp
        _ = _ := by rw [hratio]; simp
    unfold a heClassicOddC1GoodBONG
    rw [heHuExactGoodBONG_adjacentDefect,
      hcast, hsucc, heClassicOddC1_head, heClassicOddC1_head, hnext]
    apply defectOrder_eq_top_of_isSquare
    refine ⟨heClassicScaledHyperbolicTower (K := K) 0 (pairs + 1) current,
      ?_⟩
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    ring

/-- The literal v5 source `C₁^(n+1)(1)` has `alpha_i=e` at every gap.
The half-gap candidate is `e`, while every defect candidate is infinite by
the preceding square calculation. -/
theorem heClassicOddC1One_alpha_eq_ramificationIndex
    (pairs : Nat) :
    let a := heClassicOddC1GoodBONG (K := K) pairs (1 : Kˣ) (by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega)
    forall i : Fin (2 * pairs + 2),
      a.alphaValue i = (ramificationIndex K : ℚ) := by
  dsimp only
  let hone : 0 <= ordUnit K (1 : Kˣ) := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  let a := heClassicOddC1GoodBONG (K := K) pairs (1 : Kˣ) hone
  have honeOrder : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have horder : forall k : Fin (2 * pairs + 3), a.order k = 0 := by
    intro k
    simp only [a, heClassicOddC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicOddC1_order, honeOrder]
    split <;> rfl
  intro i
  apply WithTop.coe_injective
  rw [a.coe_alphaValue]
  apply le_antisymm
  · calc
      a.alpha i <= a.halfGapCandidate i := a.alpha_le_halfGapCandidate i
      _ = (((ramificationIndex K : ℚ) : WithTop ℚ)) := by
        unfold halfGapCandidate
        rw [horder, horder]
        norm_num
  · apply Finset.le_min'
    intro x hx
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with hhalf | ⟨j, _hji, hleft⟩ | ⟨j, _hij, hright⟩
    · rw [hhalf]
      unfold halfGapCandidate
      rw [horder, horder]
      norm_num
    · rw [← hleft]
      unfold leftDefectCandidate
      rw [horder, horder,
        heClassicOddC1One_adjacentDefect_top (K := K) pairs j]
      simp
    · rw [← hright]
      unfold rightDefectCandidate
      rw [horder, horder,
        heClassicOddC1One_adjacentDefect_top (K := K) pairs j]
      simp

/-- The first `2*k` coefficients of `C₁^(2*pairs+3)(1)` have the
standard hyperbolic determinant `(-1)^k`. -/
theorem heClassicOddC1One_prefixProduct_even
    (pairs k : Nat) (hk : k <= pairs + 1) :
    let a := heClassicOddC1GoodBONG (K := K) pairs (1 : Kˣ) (by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega)
    a.prefixProduct (2 * k) = (-1 : Kˣ) ^ k := by
  dsimp only
  let hone : 0 <= ordUnit K (1 : Kˣ) := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  let a := heClassicOddC1GoodBONG (K := K) pairs (1 : Kˣ) hone
  change a.prefixProduct (2 * k) = (-1 : Kˣ) ^ k
  induction k with
  | zero =>
      simp only [Nat.mul_zero, pow_zero]
      exact a.toBONG.prefixProduct_zero
  | succ k ih =>
      have hkPrev : k <= pairs + 1 := by omega
      have hEvenBound : 2 * k < 2 * pairs + 3 := by omega
      have hOddBound : 2 * k + 1 < 2 * pairs + 3 := by omega
      have hHeadEven : 2 * k < 2 * (pairs + 1) := by omega
      have hHeadOdd : 2 * k + 1 < 2 * (pairs + 1) := by omega
      have hEven : a.toBONG.valueUnit
          (⟨2 * k, hEvenBound⟩ : Fin (2 * pairs + 3)) = 1 := by
        change a.valueUnit _ = 1
        simp only [a, heClassicOddC1GoodBONG,
          heHuExactGoodBONG_valueUnit]
        let j : Fin (2 * (pairs + 1)) := ⟨2 * k, hHeadEven⟩
        have hj : (⟨2 * k, hEvenBound⟩ : Fin (2 * pairs + 3)) =
            j.castSucc := Fin.ext rfl
        rw [hj, heClassicOddC1_head,
          heClassicScaledHyperbolicTower_even
            (j := ⟨k, by omega⟩)]
        simp [uniformizerPowerUnit]
      have hOdd : a.toBONG.valueUnit
          (⟨2 * k + 1, hOddBound⟩ : Fin (2 * pairs + 3)) = -1 := by
        change a.valueUnit _ = -1
        simp only [a, heClassicOddC1GoodBONG,
          heHuExactGoodBONG_valueUnit]
        let j : Fin (2 * (pairs + 1)) := ⟨2 * k + 1, hHeadOdd⟩
        have hj : (⟨2 * k + 1, hOddBound⟩ : Fin (2 * pairs + 3)) =
            j.castSucc := Fin.ext rfl
        rw [hj, heClassicOddC1_head,
          heClassicScaledHyperbolicTower_odd
            (j := ⟨k, by omega⟩)]
        simp [uniformizerPowerUnit]
      change a.toBONG.prefixProduct (2 * (k + 1)) =
        (-1 : Kˣ) ^ (k + 1)
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
        a.toBONG.prefixProduct_succ (2 * k + 1) hOddBound,
        a.toBONG.prefixProduct_succ (2 * k) hEvenBound,
        show a.toBONG.prefixProduct (2 * k) = (-1 : Kˣ) ^ k by
          simpa only [BONG.GoodBONG.prefixProduct] using ih hkPrev,
        hEven, hOdd, pow_succ]
      simp

/-- All instances of condition 2.5(ii) for the v5 integral identity
`C₁^(n+1)(1) -> H_e^n(1)`.  The first and final paper indices are the
only new boundary calculations; Lemma 3.2 handles every intermediate
index. -/
theorem he2022ClassicLemma71v5_C1One_defectConditions
    (pairs : Nat) :
    let oneOrder : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    let a := heClassicOddC1GoodBONG (K := K) pairs (1 : Kˣ) (by omega)
    let b := heClassicEvenHGoodBONG (K := K) pairs (1 : Kˣ)
      (Or.inl rfl) oneOrder
    forall i : RepresentationIndex (2 * pairs + 3) (2 * pairs + 2),
      a.HeClassicDefectConditionAt b i := by
  dsimp only
  have oneOrder : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  let a := heClassicOddC1GoodBONG (K := K) pairs (1 : Kˣ) (by omega)
  let b := heClassicEvenHGoodBONG (K := K) pairs (1 : Kˣ)
    (Or.inl rfl) oneOrder
  change forall i, a.HeClassicDefectConditionAt b i
  have hSourceZero : forall k : Fin (2 * pairs + 3), a.order k = 0 := by
    intro k
    simp only [a, heClassicOddC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicOddC1_order, oneOrder]
    split <;> rfl
  have hSourceAlpha : forall k : Fin (2 * pairs + 2),
      a.alphaValue k = (ramificationIndex K : ℚ) := by
    simpa only [a] using
      (heClassicOddC1One_alpha_eq_ramificationIndex (K := K) pairs)
  have hTargetFirst : b.order (0 : Fin (2 * pairs + 2)) =
      (ramificationIndex K : Int) := by
    simp only [b, heClassicEvenHGoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenH_order pairs 1 oneOrder]
    simp
  have hTargetLast :
      b.order (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
        -(ramificationIndex K : Int) := by
    simp only [b, heClassicEvenHGoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenH_order pairs 1 oneOrder]
    simp only [Nat.not_even_two_mul_add_one, ↓reduceIte]
  intro i
  by_cases hiOne : i.val = 1
  · have hSourceCap : a.truncatedPrefixDefect b (-1)
        (i.val + 1) (i.val - 1) <=
        (((ramificationIndex K : ℚ) : WithTop ℚ)) := by
      calc
        a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) <=
            a.prefixAlphaCap (i.val + 1) :=
          a.truncatedPrefixDefect_le_leftCap b (-1)
            (i.val + 1) (i.val - 1)
        _ = (((ramificationIndex K : ℚ) : WithTop ℚ)) := by
          rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
          have hindex :
              (⟨i.val + 1 - 1, by omega⟩ : Fin (2 * pairs + 2)) =
                (1 : Fin (2 * pairs + 2)) := by
            apply Fin.ext
            simp only [Fin.val_one]
            omega
          rw [hindex, hSourceAlpha]
    have hAlphaUpper : a.representationAlpha b i <= 0 := by
      calc
        a.representationAlpha b i <= a.representationPrimaryDefect b i :=
          a.representationAlpha_le_primary b i
        _ <= 0 := by
          unfold representationPrimaryDefect
          have hSourceIndex :
              (⟨i.val, i.lt_large⟩ : Fin (2 * pairs + 3)) =
                (1 : Fin (2 * pairs + 3)) := Fin.ext hiOne
          have hTargetIndex :
              (⟨i.val - 1, by omega⟩ : Fin (2 * pairs + 2)) =
                (0 : Fin (2 * pairs + 2)) := by
            apply Fin.ext
            simp only [Fin.val_zero]
            omega
          rw [hSourceIndex, hSourceZero, hTargetIndex, hTargetFirst]
          have hshift :
              ((((0 - (ramificationIndex K : Int) : Int) : ℚ) :
                  WithTop ℚ)) =
                ((-(ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
            norm_cast
            rw [Int.subNatNat_eq_coe]
            simp
          rw [hshift]
          calc
            ((-(ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) +
                a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) <=
              ((-(ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) +
                (((ramificationIndex K : ℚ) : WithTop ℚ)) :=
              by
                simpa only [add_comm] using add_le_add_left hSourceCap
                  ((-(ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
            _ = 0 := by
              simp
    unfold HeClassicDefectConditionAt
    rw [a.coe_representationAlphaValue b i]
    exact hAlphaUpper.trans
      (a.truncatedPrefixDefect_nonneg b 1 i.val i.val)
  · by_cases hiLast : i.val = 2 * pairs + 2
    · have hMixedZero : a.truncatedPrefixDefect b (-1)
          (i.val + 1) (i.val - 1) = 0 := by
        apply le_antisymm
        · calc
            a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) <=
                b.prefixAlphaCap (i.val - 1) :=
              a.truncatedPrefixDefect_le_rightCap b (-1)
                (i.val + 1) (i.val - 1)
            _ = 0 := by
              have hindex : i.val - 1 = 2 * pairs + 1 := by omega
              rw [hindex]
              exact heClassicEvenH_primaryPrefixCap
                (K := K) pairs oneOrder
        · exact a.truncatedPrefixDefect_nonneg b (-1)
            (i.val + 1) (i.val - 1)
      have hAlphaUpper : a.representationAlpha b i <=
          (((ramificationIndex K : ℚ) : WithTop ℚ)) := by
        calc
          a.representationAlpha b i <= a.representationPrimaryDefect b i :=
            a.representationAlpha_le_primary b i
          _ = (((ramificationIndex K : ℚ) : WithTop ℚ)) := by
            unfold representationPrimaryDefect
            have hSourceIndex :
                (⟨i.val, i.lt_large⟩ : Fin (2 * pairs + 3)) =
                  ⟨2 * pairs + 2, by omega⟩ := Fin.ext hiLast
            have hTargetIndex :
                (⟨i.val - 1, by omega⟩ : Fin (2 * pairs + 2)) =
                  ⟨2 * pairs + 1, by omega⟩ := by
              apply Fin.ext
              change i.val - 1 = 2 * pairs + 1
              omega
            rw [hSourceIndex, hSourceZero, hTargetIndex, hTargetLast,
              hMixedZero]
            norm_cast
            ring
      have hSourceProduct : a.prefixProduct (2 * pairs + 2) =
          (-1 : Kˣ) ^ (pairs + 1) := by
        rw [show 2 * pairs + 2 = 2 * (pairs + 1) by omega]
        simpa only [a] using (heClassicOddC1One_prefixProduct_even
          (K := K) pairs (pairs + 1) le_rfl)
      have hTargetProduct : b.prefixProduct (2 * pairs + 2) =
          (-1 : Kˣ) ^ (pairs + 1) := by
        simpa only [b, mul_one] using
          (heClassicEvenH_prefixProduct_full
            (K := K) pairs 1 (Or.inl rfl) oneOrder)
      have hRawSquare : IsSquare
          ((1 : Kˣ) * a.prefixProduct i.val * b.prefixProduct i.val) := by
        refine ⟨(-1 : Kˣ) ^ (pairs + 1), ?_⟩
        rw [hiLast, one_mul, hSourceProduct, hTargetProduct]
      have hSourceCap : a.prefixAlphaCap i.val =
          (((ramificationIndex K : ℚ) : WithTop ℚ)) := by
        rw [a.prefixAlphaCap_of_internal i.pos (by omega)]
        have hindex :
            (⟨i.val - 1, by omega⟩ : Fin (2 * pairs + 2)) =
              ⟨2 * pairs + 1, by omega⟩ := by
          apply Fin.ext
          change i.val - 1 = 2 * pairs + 1
          omega
        rw [hindex, hSourceAlpha]
      have hTargetCap : b.prefixAlphaCap i.val = ⊤ := by
        rw [hiLast]
        exact b.prefixAlphaCap_last
      have hSelf : a.truncatedPrefixDefect b 1 i.val i.val =
          (((ramificationIndex K : ℚ) : WithTop ℚ)) := by
        unfold truncatedPrefixDefect
        rw [defectOrder_eq_top_of_isSquare hRawSquare,
          hSourceCap, hTargetCap]
        simp
      unfold HeClassicDefectConditionAt
      rw [a.coe_representationAlphaValue b i, hSelf]
      exact hAlphaUpper
    · have hiPositive := i.pos
      have hiTwo : 2 <= i.val := by omega
      have hiBeforeLast : i.val < 2 * pairs + 2 := by
        have := i.le_small
        omega
      exact a.he2022ClassicLemma32 b
        (heClassicEvenH_isClassicIntegral
          (K := K) pairs 1 (Or.inl rfl) oneOrder)
        (2 * pairs + 2) (by omega)
        (by exact ⟨pairs + 1, by omega⟩) (by omega)
        (fun k _hk => hSourceZero k) i hiTwo hiBeforeLast

/-- Corrected Lemma 7.1(ii), exceptional branch: the literal exact lattice
`C₁^(2*pairs+3)(1)` integrally represents the literal exact lattice
`H_e^(2*pairs+2)(1)`. -/
theorem he2022ClassicLemma71v5_C1OneModel_represents_evenHOneModel
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    (pairs : Nat) :
    let oneOrder : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    (heClassicOddC1Model (K := K) pairs (1 : Kˣ) (by omega)).Represents
      (heClassicEvenHModel (K := K) pairs (1 : Kˣ)
        (Or.inl rfl) oneOrder) := by
  dsimp only
  have oneOrder : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  let a := heClassicOddC1GoodBONG (K := K) pairs (1 : Kˣ) (by omega)
  let b := heClassicEvenHGoodBONG (K := K) pairs (1 : Kˣ)
    (Or.inl rfl) oneOrder
  have hSourceZero : forall k : Fin (2 * pairs + 3), a.order k = 0 := by
    intro k
    simp only [a, heClassicOddC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicOddC1_order, oneOrder]
    split <;> rfl
  have hSourceClassic : Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicOddC1 (K := K) pairs (1 : Kˣ)))
      (heHuExactRealization
        (heClassicOddC1 (K := K) pairs (1 : Kˣ))
        (heClassicOddC1_adjacentAdmissible pairs 1 (by omega))
        (heClassicOddC1_weakTwoStep pairs 1 (by omega))).lattice :=
    heClassicOddC1_isClassicIntegral (K := K) pairs 1 (by omega)
  have hTargetClassic : Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicEvenH (K := K) pairs (1 : Kˣ)))
      (heHuExactRealization
        (heClassicEvenH (K := K) pairs (1 : Kˣ))
        (heClassicEvenH_adjacentAdmissible pairs 1 (Or.inl rfl))
        (heClassicEvenH_weakTwoStep pairs 1 oneOrder)).lattice :=
    heClassicEvenH_isClassicIntegral
      (K := K) pairs 1 (Or.inl rfl) oneOrder
  have hambient :
      (BONG.coefficientDiagonalSpace
        (heClassicOddC1 (K := K) pairs (1 : Kˣ))).Represents
      (BONG.coefficientDiagonalSpace
        (heClassicEvenH (K := K) pairs (1 : Kˣ))) := by
    change
      (QuadraticSpace.finiteDiagonal
        (fun i => ((heClassicOddC1 (K := K) pairs (1 : Kˣ) i) : K))
        (fun i => Units.ne_zero
          (heClassicOddC1 (K := K) pairs (1 : Kˣ) i))).Represents
      (QuadraticSpace.finiteDiagonal
        (fun i => ((heClassicEvenH (K := K) pairs (1 : Kˣ) i) : K))
        (fun i => Units.ne_zero
          (heClassicEvenH (K := K) pairs (1 : Kˣ) i)))
    rw [QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents]
    exact he2022ClassicLemma71v5_C1One_represents_evenHOne
      (K := K) pairs
  change Lattice.Represents
    (BONG.coefficientDiagonalSpace
      (heClassicOddC1 (K := K) pairs (1 : Kˣ)))
    (BONG.coefficientDiagonalSpace
      (heClassicEvenH (K := K) pairs (1 : Kˣ)))
    (heHuExactRealization
      (heClassicOddC1 (K := K) pairs (1 : Kˣ))
      (heClassicOddC1_adjacentAdmissible pairs 1 (by omega))
      (heClassicOddC1_weakTwoStep pairs 1 (by omega))).lattice
    (heHuExactRealization
      (heClassicEvenH (K := K) pairs (1 : Kˣ))
      (heClassicEvenH_adjacentAdmissible pairs 1 (Or.inl rfl))
      (heClassicEvenH_weakTwoStep pairs 1 oneOrder)).lattice
  apply a.he2022ClassicRepresents_of_pointwisePrime b (by omega) hambient
  · exact a.he2022ClassicCorollary310i_of_nextOrderZero
      (m := 2 * pairs + 1) pairs b (by omega) (by omega)
      hTargetClassic (fun k _hk => hSourceZero k) (hSourceZero _)
  · exact he2022ClassicLemma71v5_C1One_defectConditions
      (K := K) pairs
  · intro i
    exact a.he2022ClassicCorollary312iiInitial (m := 2 * pairs) pairs b
      (by omega) hTargetClassic (fun k _hk => hSourceZero k)
      (hSourceZero _) i (by have := i.lt_large; omega)
  · intro i
    exact a.he2022ClassicCorollary313i (2 * pairs) b
      (fun k _hk => hSourceZero k) (Or.inl (hSourceZero _)) i
      (by have := i.succ_lt_large; omega)

/-- Corrected Lemma 7.1(ii), ramification-one branch.  At `e=1`, an
ambient representation from either odd `omega` row lifts integrally for an
arbitrary classic even-rank target.  The only endpoint not covered by the
four Section 3 corollaries is discharged by the endpoint form of Lemma 3.4. -/
theorem he2022ClassicLemma71v5_ramificationOne_represents
    (pairs : Nat)
    (a : GoodBONG q L (2 * pairs + 3))
    (b : GoodBONG r M (2 * pairs + 2))
    (heOne : ramificationIndex K = 1)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hSourceZero : forall k : Fin (2 * pairs + 3), a.order k = 0)
    (hSourceAlpha : forall k : Fin (2 * pairs + 2), a.alphaValue k = 1)
    (ambient : q.Represents r) :
    Lattice.Represents q r L M := by
  apply a.he2022ClassicRepresents_of_pointwisePrime b (by omega) ambient
  · exact a.he2022ClassicCorollary310i_of_nextOrderZero
      (m := 2 * pairs + 1) pairs b (by omega) (by omega)
      hBClassic (fun k _hk => hSourceZero k) (hSourceZero _)
  · intro i
    by_cases hiLast : i.val = 2 * pairs + 2
    · apply a.he2022ClassicLemma34_ramificationOne b hAClassic hBClassic i
        (by exact ⟨pairs + 1, by omega⟩)
        (hSourceZero _) (hSourceZero _) (hSourceAlpha _) heOne
    · exact a.he2022ClassicCorollary311iiInitial (m := 2 * pairs) pairs b
        (by omega) (by omega) hAClassic hBClassic
        (fun k _hk => hSourceZero k)
        (fun k _hk => hSourceAlpha k) (hSourceZero _) i (by
          have hiSmall := i.le_small
          omega)
  · intro i
    exact a.he2022ClassicCorollary312iiInitial (m := 2 * pairs) pairs b
      (by omega) hBClassic (fun k _hk => hSourceZero k)
      (hSourceZero _) i (by have := i.lt_large; omega)
  · intro i
    exact a.he2022ClassicCorollary313i (2 * pairs) b
      (fun k _hk => hSourceZero k) (Or.inl (hSourceZero _)) i
      (by have := i.succ_lt_large; omega)

/-- The new terminal estimate in corrected Lemma 7.1(ii).

The source has rank `2*pairs+3`, all source orders are zero, and all source
alphas are one.  The target has rank `2*pairs+2`, orders zero before its last
coefficient, last order `1-d`, and alphas one, where `d` is zero or one.
Then condition 2.5(ii) holds at the final paper index. -/
theorem he2022ClassicLemma71v5_lowDefect_terminal
    (pairs : Nat)
    (a : GoodBONG q L (2 * pairs + 3))
    (b : GoodBONG r M (2 * pairs + 2))
    (d : Int) (hd : d = 0 ∨ d = 1)
    (hSourceZero : forall k : Fin (2 * pairs + 3), a.order k = 0)
    (hSourceAlpha : forall k : Fin (2 * pairs + 2), a.alphaValue k = 1)
    (hTargetZero : forall k : Fin (2 * pairs + 2),
      k.val < 2 * pairs + 1 -> b.order k = 0)
    (hTargetAlpha : forall k : Fin (2 * pairs + 1),
      b.alphaValue k = 1)
    (hTargetLast : b.order ⟨2 * pairs + 1, by omega⟩ = 1 - d)
    (i : RepresentationIndex (2 * pairs + 3) (2 * pairs + 2))
    (hiLast : i.val = 2 * pairs + 2) :
    a.HeClassicDefectConditionAt b i := by
  have hSourcePrefixZero : forall k : Nat, k <= 2 * pairs + 3 ->
      ordUnit K (a.prefixProduct k) = 0 := by
    intro k hk
    rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum k hk]
    exact he2022Classic71v5_prefixSum_zero a k hk
      (fun j _hj => hSourceZero j)
  have hTargetPrefixBeforeLast :
      ordUnit K (b.prefixProduct (2 * pairs + 1)) = 0 := by
    rw [b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (2 * pairs + 1) (by omega)]
    exact he2022Classic71v5_prefixSum_zero b (2 * pairs + 1)
      (by omega) hTargetZero
  have hTargetPrefixFull :
      ordUnit K (b.prefixProduct (2 * pairs + 2)) = 1 - d := by
    have hTargetPrefixSumBeforeLast :
        b.orderSequence.prefixSum (2 * pairs + 1) = 0 :=
      he2022Classic71v5_prefixSum_zero b (2 * pairs + 1)
        (by omega) hTargetZero
    rw [b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (2 * pairs + 2) le_rfl,
      b.orderSequence.prefixSum_succ,
      b.orderSequence_entryOrZero_eq_order
        (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)),
      hTargetLast, hTargetPrefixSumBeforeLast]
    omega
  have hMixedUpper : a.truncatedPrefixDefect b (-1)
      (i.val + 1) (i.val - 1) <= 1 := by
    calc
      a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) <=
          b.prefixAlphaCap (i.val - 1) :=
        a.truncatedPrefixDefect_le_rightCap b (-1)
          (i.val + 1) (i.val - 1)
      _ = 1 := by
        rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
        have hindex :
            (⟨i.val - 1 - 1, by omega⟩ : Fin (2 * pairs + 1)) =
              ⟨2 * pairs, by omega⟩ := by
          apply Fin.ext
          change i.val - 1 - 1 = 2 * pairs
          omega
        rw [hindex, hTargetAlpha]
        norm_num
  unfold HeClassicDefectConditionAt
  rw [a.coe_representationAlphaValue b i]
  have hAlphaUpper : a.representationAlpha b i <=
      ((d : ℚ) : WithTop ℚ) := by
    calc
      a.representationAlpha b i <= a.representationPrimaryDefect b i :=
        a.representationAlpha_le_primary b i
      _ <= ((d : ℚ) : WithTop ℚ) := by
        unfold representationPrimaryDefect
        have hSourceIndex :
            (⟨i.val, i.lt_large⟩ : Fin (2 * pairs + 3)) =
              ⟨2 * pairs + 2, by omega⟩ := Fin.ext hiLast
        have hTargetIndex :
            (⟨i.val - 1, by omega⟩ : Fin (2 * pairs + 2)) =
              ⟨2 * pairs + 1, by omega⟩ := by
          apply Fin.ext
          change i.val - 1 = 2 * pairs + 1
          omega
        rw [hSourceIndex, hSourceZero, hTargetIndex, hTargetLast]
        calc
          ((((0 - (1 - d) : Int) : ℚ)) : WithTop ℚ) +
                a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) <=
              ((((0 - (1 - d) : Int) : ℚ)) : WithTop ℚ) + 1 :=
            (by
              simpa only [add_comm] using
                add_le_add_left hMixedUpper
                  (((((0 - (1 - d) : Int) : ℚ)) : WithTop ℚ)))
          _ = ((d : ℚ) : WithTop ℚ) := by
            norm_cast
            ring
  rcases hd with rfl | rfl
  · have hSelfOdd : Odd (ordUnit K
        (a.prefixProduct (2 * pairs + 2) *
          b.prefixProduct (2 * pairs + 2))) := by
      rw [ordUnit_mul, hSourcePrefixZero (2 * pairs + 2) (by omega),
        hTargetPrefixFull]
      exact odd_one
    have hSelfZero : a.truncatedPrefixDefect b 1 i.val i.val = 0 := by
      apply a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed
        (alphaV := beliUniversalAlphaLaws)
        (alphaW := beliUniversalAlphaLaws)
      simpa only [one_mul, hiLast] using hSelfOdd
    rw [hSelfZero]
    simpa using hAlphaUpper
  · have hTargetFullZero :
        ordUnit K (b.prefixProduct (2 * pairs + 2)) = 0 := by
      simpa using hTargetPrefixFull
    have hSelfEven : Even (ordUnit K
        (a.prefixProduct (2 * pairs + 2) *
          b.prefixProduct (2 * pairs + 2))) := by
      rw [ordUnit_mul, hSourcePrefixZero (2 * pairs + 2) (by omega),
        hTargetFullZero]
      exact Even.zero
    have hRaw : (1 : WithTop ℚ) <= defectOrder (K := K)
        ((1 : Kˣ) * a.prefixProduct i.val * b.prefixProduct i.val) := by
      simpa only [one_mul, hiLast] using
        he2022Classic_one_le_defectOrder_of_even_ordUnit
          (a.prefixProduct (2 * pairs + 2) *
            b.prefixProduct (2 * pairs + 2)) hSelfEven
    have hSourceCap : a.prefixAlphaCap i.val = 1 := by
      rw [a.prefixAlphaCap_of_internal i.pos (by omega)]
      have hindex :
          (⟨i.val - 1, by omega⟩ : Fin (2 * pairs + 2)) =
            ⟨2 * pairs + 1, by omega⟩ := by
        apply Fin.ext
        change i.val - 1 = 2 * pairs + 1
        omega
      rw [hindex, hSourceAlpha]
      norm_num
    have hTargetCap : b.prefixAlphaCap i.val = ⊤ := by
      rw [hiLast]
      exact b.prefixAlphaCap_last
    have hSelfLower : (1 : WithTop ℚ) <=
        a.truncatedPrefixDefect b 1 i.val i.val := by
      unfold truncatedPrefixDefect
      rw [hSourceCap, hTargetCap]
      exact le_min hRaw (by simp)
    exact hAlphaUpper.trans hSelfLower

/-- Corrected Lemma 7.1(ii), low-defect branch, at the level of arbitrary
good BONGs with the displayed v5 profiles.  An ambient representation lifts
to an integral representation. -/
theorem he2022ClassicLemma71v5_lowDefect_represents
    (pairs : Nat)
    (a : GoodBONG q L (2 * pairs + 3))
    (b : GoodBONG r M (2 * pairs + 2))
    (d : Int) (hd : d = 0 ∨ d = 1)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hSourceZero : forall k : Fin (2 * pairs + 3), a.order k = 0)
    (hSourceAlpha : forall k : Fin (2 * pairs + 2), a.alphaValue k = 1)
    (hTargetZero : forall k : Fin (2 * pairs + 2),
      k.val < 2 * pairs + 1 -> b.order k = 0)
    (hTargetAlpha : forall k : Fin (2 * pairs + 1),
      b.alphaValue k = 1)
    (hTargetLast : b.order ⟨2 * pairs + 1, by omega⟩ = 1 - d)
    (ambient : q.Represents r) :
    Lattice.Represents q r L M := by
  apply a.he2022ClassicRepresents_of_pointwisePrime b (by omega) ambient
  · exact a.he2022ClassicCorollary310i_of_nextOrderZero
      (m := 2 * pairs + 1) pairs b (by omega) (by omega) hBClassic
      (fun k _hk => hSourceZero k) (hSourceZero _)
  · intro i
    by_cases hiLast : i.val = 2 * pairs + 2
    · exact a.he2022ClassicLemma71v5_lowDefect_terminal pairs b d hd
        hSourceZero hSourceAlpha hTargetZero hTargetAlpha hTargetLast i hiLast
    · exact a.he2022ClassicCorollary311iiInitial (m := 2 * pairs) pairs b
        (by omega) (by omega) hAClassic hBClassic
        (fun k _hk => hSourceZero k)
        (fun k _hk => hSourceAlpha k) (hSourceZero _) i (by
          have hiSmall := i.le_small
          omega)
  · intro i
    exact a.he2022ClassicCorollary312iiInitial (m := 2 * pairs) pairs b
      (by omega) hBClassic (fun k _hk => hSourceZero k)
      (hSourceZero _) i (by have := i.lt_large; omega)
  · intro i
    exact a.he2022ClassicCorollary313i (2 * pairs) b
      (fun k _hk => hSourceZero k) (Or.inl (hSourceZero _)) i
      (by have := i.succ_lt_large; omega)

/-- Corrected Lemma 7.1(ii), coefficient-model disjunction.  For a target
good BONG with the v5 low-defect profile, one of the two literal odd `omega`
models integrally represents the target. -/
theorem he2022ClassicLemma71v5_lowDefect_coefficient_dichotomy
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    (pairs : Nat)
    (homega : ordUnit K (heClassicOmega (K := K)) = 0)
    (homegaSharp : ordUnit K (heClassicOmegaSharp (K := K)) = 0)
    (homegaNonnegative : 0 <= ordUnit K (heClassicOmega (K := K)))
    (w : Fin (2 * pairs + 2) -> Kˣ)
    {M : Lattice K (Fin (2 * pairs + 2) -> K)}
    (b : GoodBONG (BONG.coefficientDiagonalSpace w) M (2 * pairs + 2))
    (d : Int) (hd : d = 0 ∨ d = 1)
    (hBClassic : Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace w) M)
    (hTargetZero : forall k : Fin (2 * pairs + 2),
      k.val < 2 * pairs + 1 -> b.order k = 0)
    (hTargetAlpha : forall k : Fin (2 * pairs + 1),
      b.alphaValue k = 1)
    (hTargetLast : b.order ⟨2 * pairs + 1, by omega⟩ = 1 - d) :
    let omega := heClassicOmega (K := K)
    let omegaSharp := heClassicOmegaSharp (K := K)
    let L1 := (heHuExactRealization
      (heClassicOddC1 (K := K) pairs omega)
      (heClassicOddC1_adjacentAdmissible pairs omega homegaNonnegative)
      (heClassicOddC1_weakTwoStep pairs omega homegaNonnegative)).lattice
    let L2 := (heHuExactRealization
      (heClassicOddC2Even (K := K) pairs omega omega omegaSharp)
      (heClassicOddC2Even_adjacentAdmissible pairs omega omega omegaSharp
        homega homega homegaSharp)
      (heClassicOddC2Even_weakTwoStep pairs omega omega omegaSharp
        homega homega homegaSharp)).lattice
    Lattice.Represents
        (BONG.coefficientDiagonalSpace
          (heClassicOddC1 (K := K) pairs omega))
        (BONG.coefficientDiagonalSpace w) L1 M ∨
      Lattice.Represents
        (BONG.coefficientDiagonalSpace
          (heClassicOddC2Even (K := K) pairs omega omega omegaSharp))
        (BONG.coefficientDiagonalSpace w) L2 M := by
  dsimp only
  let omega := heClassicOmega (K := K)
  let omegaSharp := heClassicOmegaSharp (K := K)
  let L1 := (heHuExactRealization
    (heClassicOddC1 (K := K) pairs omega)
    (heClassicOddC1_adjacentAdmissible pairs omega homegaNonnegative)
    (heClassicOddC1_weakTwoStep pairs omega homegaNonnegative)).lattice
  let L2 := (heHuExactRealization
    (heClassicOddC2Even (K := K) pairs omega omega omegaSharp)
    (heClassicOddC2Even_adjacentAdmissible pairs omega omega omegaSharp
      homega homega homegaSharp)
    (heClassicOddC2Even_weakTwoStep pairs omega omega omegaSharp
      homega homega homegaSharp)).lattice
  let a1 := heClassicOddC1GoodBONG (K := K) pairs omega
    homegaNonnegative
  let a2 := heClassicOddC2EvenGoodBONG (K := K) pairs omega omega
    omegaSharp homega homega homegaSharp
  have hSource1Zero : forall k : Fin (2 * pairs + 3), a1.order k = 0 := by
    intro k
    simp only [a1, heClassicOddC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicOddC1_order, homega]
    simp
  have hSource2Zero : forall k : Fin (2 * pairs + 3), a2.order k = 0 := by
    intro k
    simp only [a2, heClassicOddC2EvenGoodBONG, heHuExactGoodBONG_order]
    exact heClassicOddC2Even_order_zero pairs omega omega omegaSharp
      homega homega homegaSharp k
  have hSource1Alpha : forall k : Fin (2 * pairs + 2),
      a1.alphaValue k = 1 := by
    intro k
    exact heClassicOddC1_alpha_eq_one (K := K) pairs omega 1
      homegaNonnegative (Or.inr rfl) (by
        have h : ordUnit K omega = 0 := by simpa only [omega] using homega
        omega)
        (by rw [heClassicOmega_defect (K := K)]; norm_num) k
  have hSource2Alpha : forall k : Fin (2 * pairs + 2),
      a2.alphaValue k = 1 := by
    intro k
    exact heClassicOddC2Even_alpha_eq_one (K := K) pairs omega omega
      omegaSharp homega homega homegaSharp
        (by rw [heClassicOmega_defect (K := K)]; norm_num) k
  have hSource1Classic : Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicOddC1 (K := K) pairs omega)) L1 := by
    exact heClassicOddC1_isClassicIntegral (K := K) pairs omega
      homegaNonnegative
  have hSource2Classic : Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicOddC2Even (K := K) pairs omega omega omegaSharp)) L2 := by
    exact heClassicOddC2Even_isClassicIntegral (K := K) pairs omega omega
      omegaSharp homega homega homegaSharp
  rcases he2022ClassicLemma71v5_ambient_dichotomy
      (K := K) pairs w with hfirst | hsecond
  · left
    have hambient :
        (BONG.coefficientDiagonalSpace
          (heClassicOddC1 (K := K) pairs omega)).Represents
            (BONG.coefficientDiagonalSpace w) := by
      change
        (QuadraticSpace.finiteDiagonal
          (fun i => ((heClassicOddC1 (K := K) pairs omega i) : K))
          (fun i => Units.ne_zero
            (heClassicOddC1 (K := K) pairs omega i))).Represents
        (QuadraticSpace.finiteDiagonal (fun i => ((w i) : K))
          (fun i => Units.ne_zero (w i)))
      rw [QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents]
      change DiagonalRepresents (diagonalUnitCoefficients w)
        (diagonalUnitCoefficients
          (heClassicOddC1 (K := K) pairs omega))
      simpa only [omega] using hfirst
    exact a1.he2022ClassicLemma71v5_lowDefect_represents pairs b d hd
      hSource1Classic hBClassic hSource1Zero hSource1Alpha
      hTargetZero hTargetAlpha hTargetLast hambient
  · right
    have hambient :
        (BONG.coefficientDiagonalSpace
          (heClassicOddC2Even (K := K) pairs omega omega omegaSharp)).Represents
            (BONG.coefficientDiagonalSpace w) := by
      change
        (QuadraticSpace.finiteDiagonal
          (fun i => ((heClassicOddC2Even (K := K) pairs omega omega
            omegaSharp i) : K))
          (fun i => Units.ne_zero
            (heClassicOddC2Even (K := K) pairs omega omega
              omegaSharp i))).Represents
        (QuadraticSpace.finiteDiagonal (fun i => ((w i) : K))
          (fun i => Units.ne_zero (w i)))
      rw [QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents]
      change DiagonalRepresents (diagonalUnitCoefficients w)
        (diagonalUnitCoefficients
          (heClassicOddC2Even (K := K) pairs omega omega omegaSharp))
      simpa only [omega, omegaSharp] using hsecond
    exact a2.he2022ClassicLemma71v5_lowDefect_represents pairs b d hd
      hSource2Classic hBClassic hSource2Zero hSource2Alpha
      hTargetZero hTargetAlpha hTargetLast hambient

/-- Corrected Lemma 7.1(ii), coefficient-model disjunction at ramification
index one.  No special target profile is required beyond classic
integrality. -/
theorem he2022ClassicLemma71v5_ramificationOne_coefficient_dichotomy
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    (pairs : Nat)
    (homega : ordUnit K (heClassicOmega (K := K)) = 0)
    (homegaSharp : ordUnit K (heClassicOmegaSharp (K := K)) = 0)
    (homegaNonnegative : 0 <= ordUnit K (heClassicOmega (K := K)))
    (heOne : ramificationIndex K = 1)
    (w : Fin (2 * pairs + 2) -> Kˣ)
    {M : Lattice K (Fin (2 * pairs + 2) -> K)}
    (b : GoodBONG (BONG.coefficientDiagonalSpace w) M (2 * pairs + 2))
    (hBClassic : Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace w) M) :
    let omega := heClassicOmega (K := K)
    let omegaSharp := heClassicOmegaSharp (K := K)
    let L1 := (heHuExactRealization
      (heClassicOddC1 (K := K) pairs omega)
      (heClassicOddC1_adjacentAdmissible pairs omega homegaNonnegative)
      (heClassicOddC1_weakTwoStep pairs omega homegaNonnegative)).lattice
    let L2 := (heHuExactRealization
      (heClassicOddC2Even (K := K) pairs omega omega omegaSharp)
      (heClassicOddC2Even_adjacentAdmissible pairs omega omega omegaSharp
        homega homega homegaSharp)
      (heClassicOddC2Even_weakTwoStep pairs omega omega omegaSharp
        homega homega homegaSharp)).lattice
    Lattice.Represents
        (BONG.coefficientDiagonalSpace
          (heClassicOddC1 (K := K) pairs omega))
        (BONG.coefficientDiagonalSpace w) L1 M ∨
      Lattice.Represents
        (BONG.coefficientDiagonalSpace
          (heClassicOddC2Even (K := K) pairs omega omega omegaSharp))
        (BONG.coefficientDiagonalSpace w) L2 M := by
  dsimp only
  let omega := heClassicOmega (K := K)
  let omegaSharp := heClassicOmegaSharp (K := K)
  let L1 := (heHuExactRealization
    (heClassicOddC1 (K := K) pairs omega)
    (heClassicOddC1_adjacentAdmissible pairs omega homegaNonnegative)
    (heClassicOddC1_weakTwoStep pairs omega homegaNonnegative)).lattice
  let L2 := (heHuExactRealization
    (heClassicOddC2Even (K := K) pairs omega omega omegaSharp)
    (heClassicOddC2Even_adjacentAdmissible pairs omega omega omegaSharp
      homega homega homegaSharp)
    (heClassicOddC2Even_weakTwoStep pairs omega omega omegaSharp
      homega homega homegaSharp)).lattice
  let a1 := heClassicOddC1GoodBONG (K := K) pairs omega
    homegaNonnegative
  let a2 := heClassicOddC2EvenGoodBONG (K := K) pairs omega omega
    omegaSharp homega homega homegaSharp
  have hSource1Zero : forall k : Fin (2 * pairs + 3), a1.order k = 0 := by
    intro k
    simp only [a1, heClassicOddC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicOddC1_order, homega]
    simp
  have hSource2Zero : forall k : Fin (2 * pairs + 3), a2.order k = 0 := by
    intro k
    simp only [a2, heClassicOddC2EvenGoodBONG, heHuExactGoodBONG_order]
    exact heClassicOddC2Even_order_zero pairs omega omega omegaSharp
      homega homega homegaSharp k
  have hSource1Alpha : forall k : Fin (2 * pairs + 2),
      a1.alphaValue k = 1 := by
    intro k
    exact heClassicOddC1_alpha_eq_one (K := K) pairs omega 1
      homegaNonnegative (Or.inr rfl) (by
        have h : ordUnit K omega = 0 := by simpa only [omega] using homega
        omega)
        (by rw [heClassicOmega_defect (K := K)]; norm_num) k
  have hSource2Alpha : forall k : Fin (2 * pairs + 2),
      a2.alphaValue k = 1 := by
    intro k
    exact heClassicOddC2Even_alpha_eq_one (K := K) pairs omega omega
      omegaSharp homega homega homegaSharp
        (by rw [heClassicOmega_defect (K := K)]; norm_num) k
  have hSource1Classic : Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicOddC1 (K := K) pairs omega)) L1 := by
    exact heClassicOddC1_isClassicIntegral (K := K) pairs omega
      homegaNonnegative
  have hSource2Classic : Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicOddC2Even (K := K) pairs omega omega omegaSharp)) L2 := by
    exact heClassicOddC2Even_isClassicIntegral (K := K) pairs omega omega
      omegaSharp homega homega homegaSharp
  rcases he2022ClassicLemma71v5_ambient_dichotomy
      (K := K) pairs w with hfirst | hsecond
  · left
    have hambient :
        (BONG.coefficientDiagonalSpace
          (heClassicOddC1 (K := K) pairs omega)).Represents
            (BONG.coefficientDiagonalSpace w) := by
      change
        (QuadraticSpace.finiteDiagonal
          (fun i => ((heClassicOddC1 (K := K) pairs omega i) : K))
          (fun i => Units.ne_zero
            (heClassicOddC1 (K := K) pairs omega i))).Represents
        (QuadraticSpace.finiteDiagonal (fun i => ((w i) : K))
          (fun i => Units.ne_zero (w i)))
      rw [QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents]
      change DiagonalRepresents (diagonalUnitCoefficients w)
        (diagonalUnitCoefficients
          (heClassicOddC1 (K := K) pairs omega))
      simpa only [omega] using hfirst
    exact a1.he2022ClassicLemma71v5_ramificationOne_represents pairs b
      heOne hSource1Classic hBClassic hSource1Zero hSource1Alpha hambient
  · right
    have hambient :
        (BONG.coefficientDiagonalSpace
          (heClassicOddC2Even (K := K) pairs omega omega omegaSharp)).Represents
            (BONG.coefficientDiagonalSpace w) := by
      change
        (QuadraticSpace.finiteDiagonal
          (fun i => ((heClassicOddC2Even (K := K) pairs omega omega
            omegaSharp i) : K))
          (fun i => Units.ne_zero
            (heClassicOddC2Even (K := K) pairs omega omega
              omegaSharp i))).Represents
        (QuadraticSpace.finiteDiagonal (fun i => ((w i) : K))
          (fun i => Units.ne_zero (w i)))
      rw [QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents]
      change DiagonalRepresents (diagonalUnitCoefficients w)
        (diagonalUnitCoefficients
          (heClassicOddC2Even (K := K) pairs omega omega omegaSharp))
      simpa only [omega, omegaSharp] using hsecond
    exact a2.he2022ClassicLemma71v5_ramificationOne_represents pairs b
      heOne hSource2Classic hBClassic hSource2Zero hSource2Alpha hambient

/-- The low-defect branch of corrected Lemma 7.1(ii), specialized to the
literal even first-column model. -/
theorem he2022ClassicLemma71v5_oddOmega_represents_evenC1_dichotomy
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    (pairs : Nat) (c : Kˣ) (d : Int)
    (hc : 0 <= ordUnit K c) (hd : d = 0 ∨ d = 1)
    (hcOrder : ordUnit K c = 1 - d)
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    (heClassicOddC1Model (K := K) pairs (heClassicOmega (K := K))
      (by rw [heClassicOmega_order (K := K)])).Represents
        (heClassicEvenC1Model (K := K) pairs c hc) ∨
      (heClassicOddC2EvenModel (K := K) pairs
        (heClassicOmega (K := K)) (heClassicOmega (K := K))
        (heClassicOmegaSharp (K := K))
        (heClassicOmega_order (K := K))
        (heClassicOmega_order (K := K))
        (heClassicOmegaSharp_order (K := K))).Represents
          (heClassicEvenC1Model (K := K) pairs c hc) := by
  let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
  have hTargetZero : forall k : Fin (2 * pairs + 2),
      k.val < 2 * pairs + 1 -> b.order k = 0 := by
    intro k hk
    simp only [b, heClassicEvenC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC1_order]
    simp [show k.val ≠ 2 * pairs + 1 by omega]
  have hTargetAlpha : forall k : Fin (2 * pairs + 1),
      b.alphaValue k = 1 := by
    exact heClassicEvenC1_alpha_eq_one (K := K) pairs c d hc hd
      hcOrder hcDefect
  have hTargetLast : b.order ⟨2 * pairs + 1, by omega⟩ = 1 - d := by
    simp only [b, heClassicEvenC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC1_order]
    simp [hcOrder]
  exact he2022ClassicLemma71v5_lowDefect_coefficient_dichotomy
    (K := K) pairs (heClassicOmega_order (K := K))
      (heClassicOmegaSharp_order (K := K)) (by
        rw [heClassicOmega_order (K := K)])
      (heClassicEvenC1 (K := K) pairs c) b d hd
      (heClassicEvenC1_isClassicIntegral (K := K) pairs c hc)
      hTargetZero hTargetAlpha hTargetLast

/-- The low-defect branch of corrected Lemma 7.1(ii), specialized to the
literal even second-column model. -/
theorem he2022ClassicLemma71v5_oddOmega_represents_evenC2_dichotomy
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    (pairs : Nat) (c cSharp : Kˣ) (d : Int)
    (hc : 0 <= ordUnit K c) (hcSharp : ordUnit K cSharp = 0)
    (hd : d = 0 ∨ d = 1) (hcOrder : ordUnit K c = 1 - d)
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    (heClassicOddC1Model (K := K) pairs (heClassicOmega (K := K))
      (by rw [heClassicOmega_order (K := K)])).Represents
        (heClassicEvenC2Model (K := K) pairs c cSharp hc hcSharp) ∨
      (heClassicOddC2EvenModel (K := K) pairs
        (heClassicOmega (K := K)) (heClassicOmega (K := K))
        (heClassicOmegaSharp (K := K))
        (heClassicOmega_order (K := K))
        (heClassicOmega_order (K := K))
        (heClassicOmegaSharp_order (K := K))).Represents
          (heClassicEvenC2Model (K := K) pairs c cSharp hc hcSharp) := by
  let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
  have hTargetZero : forall k : Fin (2 * pairs + 2),
      k.val < 2 * pairs + 1 -> b.order k = 0 := by
    intro k hk
    simp only [b, heClassicEvenC2GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC2_order pairs c cSharp hcSharp]
    simp [show k.val ≠ 2 * pairs + 1 by omega]
  have hTargetAlpha : forall k : Fin (2 * pairs + 1),
      b.alphaValue k = 1 := by
    exact heClassicEvenC2_alpha_eq_one (K := K) pairs c cSharp d hc
      hcSharp hd hcOrder hcDefect
  have hTargetLast : b.order ⟨2 * pairs + 1, by omega⟩ = 1 - d := by
    simp only [b, heClassicEvenC2GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC2_order pairs c cSharp hcSharp]
    simp [hcOrder]
  exact he2022ClassicLemma71v5_lowDefect_coefficient_dichotomy
    (K := K) pairs (heClassicOmega_order (K := K))
      (heClassicOmegaSharp_order (K := K)) (by
        rw [heClassicOmega_order (K := K)])
      (heClassicEvenC2 (K := K) pairs c cSharp) b d hd
      (heClassicEvenC2_isClassicIntegral (K := K) pairs c cSharp hc hcSharp)
      hTargetZero hTargetAlpha hTargetLast

/-- At ramification index one, the two odd `omega` rows cover either
exceptional even `H` model. -/
theorem he2022ClassicLemma71v5_oddOmega_represents_evenH_dichotomy
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    (pairs : Nat) (heOne : ramificationIndex K = 1)
    (c : Kˣ)
    (hcClass : c = 1 ∨
      c = (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit)
    (hcOrder : ordUnit K c = 0) :
    (heClassicOddC1Model (K := K) pairs (heClassicOmega (K := K))
      (by rw [heClassicOmega_order (K := K)])).Represents
        (heClassicEvenHModel (K := K) pairs c hcClass hcOrder) ∨
      (heClassicOddC2EvenModel (K := K) pairs
        (heClassicOmega (K := K)) (heClassicOmega (K := K))
        (heClassicOmegaSharp (K := K))
        (heClassicOmega_order (K := K))
        (heClassicOmega_order (K := K))
        (heClassicOmegaSharp_order (K := K))).Represents
          (heClassicEvenHModel (K := K) pairs c hcClass hcOrder) := by
  let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
  exact he2022ClassicLemma71v5_ramificationOne_coefficient_dichotomy
    (K := K) pairs (heClassicOmega_order (K := K))
      (heClassicOmegaSharp_order (K := K)) (by
        rw [heClassicOmega_order (K := K)]) heOne
      (heClassicEvenH (K := K) pairs c) b
      (heClassicEvenH_isClassicIntegral (K := K) pairs c hcClass hcOrder)

end BONG.GoodBONG

end Bong
