/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma75
import Bong.Bong.He2022ClassicLemma314
import Bong.Bong.Beli2019EvenClassMultiplier

/-!
# He (2024), Lemmas 7.6(i) and 7.7

The publisher's `P₂^(n+2)(Delta)` row has source orders
`0,...,0,1,1` and alpha invariants one through the last zero coordinate.
This file packages that literal source and verifies the four pointwise parts
of Theorem 2.5 against both published `C` columns.
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

/-- Odd valuation makes the embedded relative defect zero. -/
theorem he2022Classic_defectOrder_eq_zero_of_odd_ordUnit
    (x : Kˣ) (hx : Odd (ordUnit K x)) :
    defectOrder (K := K) x = 0 := by
  unfold defectOrder
  rw [quadraticDefect_eq_zero_of_odd_ordUnit x hx]
  rfl

/-- Even valuation makes the embedded relative defect at least one. -/
theorem he2022Classic_one_le_defectOrder_of_even_ordUnit
    (x : Kˣ) (hx : Even (ordUnit K x)) :
    (1 : WithTop ℚ) <= defectOrder (K := K) x :=
  defectOrder_one_le_of_even x hx

private theorem he2022Classic77_prefixSum_zero {s : Nat}
    (a : GoodBONG q L s) (k : Nat) (hk : k ≤ s)
    (hzero : ∀ i : Fin s, i.val < k → a.order i = 0) :
    a.orderSequence.prefixSum k = 0 := by
  unfold BeliOrderSequence.prefixSum
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
  exact hzero ⟨i, by omega⟩ hi

private theorem he2022Classic77_negOne_order :
    ordUnit K (-1 : Kˣ) = 0 := by
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  rw [ordUnit_neg, hone]

/-- Lemma 7.7(i)--(ii), isolated at the three boundary indices occurring in
the published proof.  The hypotheses are precisely its displayed source and
target profiles and the domination-principle estimate in formula (7.5). -/
theorem he2022ClassicLemma77_boundary_conditions
    (pairs : Nat) (a : GoodBONG q L (2 * pairs + 4))
    (b : GoodBONG r M (2 * pairs + 2)) (d : Int)
    (hd : d = 0 ∨ d = 1)
    (hSourceZero : ∀ k : Fin (2 * pairs + 4),
      k.val < 2 * pairs + 2 → a.order k = 0)
    (hSourceAlpha : ∀ k : Fin (2 * pairs + 3),
      k.val < 2 * pairs + 2 → a.alphaValue k = 1)
    (hSourceNext : a.order ⟨2 * pairs + 2, by omega⟩ = 1)
    (hSourceLast : a.order ⟨2 * pairs + 3, by omega⟩ = 1)
    (hTargetZero : ∀ k : Fin (2 * pairs + 2),
      k.val < 2 * pairs + 1 → b.order k = 0)
    (hTargetAlpha : ∀ k : Fin (2 * pairs + 1),
      k.val < 2 * pairs + 1 → b.alphaValue k = 1)
    (hTargetLast : b.order ⟨2 * pairs + 1, by omega⟩ = 1 - d)
    (hFullMixed : a.truncatedPrefixDefect b (-1)
      (2 * pairs + 4) (2 * pairs + 2) ≤ 1) :
    (∀ i : RepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      2 * pairs ≤ i.val → a.HeClassicDefectConditionAt b i) ∧
    (∀ i : CentralRepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      2 * pairs + 1 ≤ i.val →
        a.HeClassicPublishedCentralConditionAt b i) := by
  have hSourcePrefixZero : ∀ k : Nat, k ≤ 2 * pairs + 2 →
      ordUnit K (a.prefixProduct k) = 0 := by
    intro k hk
    rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum k (by omega)]
    exact he2022Classic77_prefixSum_zero a k (by omega) (fun i hi ↦
      hSourceZero i (by omega))
  have hTargetPrefixZero : ∀ k : Nat, k ≤ 2 * pairs + 1 →
      ordUnit K (b.prefixProduct k) = 0 := by
    intro k hk
    rw [b.ordUnit_prefixProduct_eq_orderSequence_prefixSum k (by omega)]
    exact he2022Classic77_prefixSum_zero b k (by omega) (fun i hi ↦
      hTargetZero i (by omega))
  have hSourcePrefixNext :
      ordUnit K (a.prefixProduct (2 * pairs + 3)) = 1 := by
    rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (2 * pairs + 3) (by omega),
      a.orderSequence.prefixSum_succ,
      a.orderSequence_entryOrZero_eq_order
        (⟨2 * pairs + 2, by omega⟩ : Fin (2 * pairs + 4)),
      hSourceNext]
    have hzero := he2022Classic77_prefixSum_zero a (2 * pairs + 2)
      (by omega) (fun i hi ↦ hSourceZero i (by omega))
    rw [hzero]
    omega
  have hOddMixed : Odd (ordUnit K
      ((-1 : Kˣ) * a.prefixProduct (2 * pairs + 3) *
        b.prefixProduct (2 * pairs + 1))) := by
    rw [ordUnit_mul, ordUnit_mul,
      he2022Classic77_negOne_order (K := K), hSourcePrefixNext,
      hTargetPrefixZero (2 * pairs + 1) (by omega)]
    exact odd_one
  have hMixedZero : a.truncatedPrefixDefect b (-1)
      (2 * pairs + 3) (2 * pairs + 1) = 0 :=
    a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed
      (alphaV := beliUniversalAlphaLaws)
      (alphaW := beliUniversalAlphaLaws)
      b (-1) (2 * pairs + 3) (2 * pairs + 1) hOddMixed
  have hTargetPrefixFull :
      ordUnit K (b.prefixProduct (2 * pairs + 2)) = 1 - d := by
    rw [b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (2 * pairs + 2) (by omega),
      b.orderSequence.prefixSum_succ,
      b.orderSequence_entryOrZero_eq_order
        (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)),
      hTargetLast]
    have hzero := he2022Classic77_prefixSum_zero b (2 * pairs + 1)
      (by omega) (fun i hi ↦ hTargetZero i (by omega))
    rw [hzero]
    omega
  have hDefectEarly : ∀
      (i : RepresentationIndex (2 * pairs + 4) (2 * pairs + 2)),
      2 * pairs ≤ i.val → i.val ≤ 2 * pairs + 1 →
        a.HeClassicDefectConditionAt b i := by
    intro i hiLower hiUpper
    have hiPos := i.pos
    have hiSource : i.val < 2 * pairs + 2 := by omega
    have hiPrevious : i.val - 1 < 2 * pairs + 1 := by omega
    have hiSourceGap : i.val - 1 < 2 * pairs + 2 := by omega
    have hSourceSelfEven : Even (ordUnit K
        (a.prefixProduct i.val * b.prefixProduct i.val)) := by
      rw [ordUnit_mul, hSourcePrefixZero i.val (by omega),
        hTargetPrefixZero i.val (by omega)]
      exact Even.zero
    have hRaw : (1 : WithTop ℚ) ≤ defectOrder (K := K)
        ((1 : Kˣ) * a.prefixProduct i.val * b.prefixProduct i.val) := by
      simpa only [one_mul] using
        he2022Classic_one_le_defectOrder_of_even_ordUnit
          (a.prefixProduct i.val * b.prefixProduct i.val) hSourceSelfEven
    have hSourceCap : a.prefixAlphaCap i.val = 1 := by
      rw [a.prefixAlphaCap_of_internal i.pos (by omega),
        hSourceAlpha ⟨i.val - 1, by omega⟩ hiSourceGap]
      norm_num
    have hTargetCap : b.prefixAlphaCap i.val = 1 := by
      rw [b.prefixAlphaCap_of_internal i.pos (by omega),
        hTargetAlpha ⟨i.val - 1, by omega⟩ hiPrevious]
      norm_num
    have hSelfLower : (1 : WithTop ℚ) ≤
        a.truncatedPrefixDefect b 1 i.val i.val := by
      unfold truncatedPrefixDefect
      rw [hSourceCap, hTargetCap]
      exact le_min hRaw (by simp)
    unfold HeClassicDefectConditionAt
    rw [a.coe_representationAlphaValue b i]
    calc
      a.representationAlpha b i ≤ a.representationPrimaryDefect b i :=
        a.representationAlpha_le_primary b i
      _ ≤ (((a.order ⟨i.val, i.lt_large⟩ -
            b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
            a.prefixAlphaCap (i.val + 1) := by
          unfold representationPrimaryDefect
          exact add_le_add_right
            (a.truncatedPrefixDefect_le_leftCap b (-1)
              (i.val + 1) (i.val - 1)) _
      _ = 1 := by
        rw [hSourceZero ⟨i.val, i.lt_large⟩ hiSource,
          hTargetZero ⟨i.val - 1, by omega⟩ hiPrevious,
          a.prefixAlphaCap_of_internal (by omega) (by omega)]
        have hindex : (⟨i.val + 1 - 1, by omega⟩ : Fin (2 * pairs + 3)) =
            ⟨i.val, by omega⟩ := by
          apply Fin.ext
          change i.val + 1 - 1 = i.val
          omega
        rw [hindex, hSourceAlpha ⟨i.val, by omega⟩ hiSource]
        norm_num
      _ ≤ a.truncatedPrefixDefect b 1 i.val i.val := hSelfLower
  constructor
  · intro i hi
    have hiCases : i.val = 2 * pairs ∨ i.val = 2 * pairs + 1 ∨
        i.val = 2 * pairs + 2 := by
      have := i.le_small
      omega
    rcases hiCases with hfirst | hsecond | hlast
    · exact hDefectEarly i hi (by omega)
    · exact hDefectEarly i hi (by omega)
    · have hPrimaryMixed : a.truncatedPrefixDefect b (-1)
          (i.val + 1) (i.val - 1) = 0 := by
        have hplus : i.val + 1 = 2 * pairs + 3 := by omega
        have hminus : i.val - 1 = 2 * pairs + 1 := by
          rw [hlast]
          omega
        rw [hplus, hminus]
        exact hMixedZero
      unfold HeClassicDefectConditionAt
      rw [a.coe_representationAlphaValue b i]
      have hAlphaUpper : a.representationAlpha b i ≤
          ((d : ℚ) : WithTop ℚ) := by
        calc
          a.representationAlpha b i ≤ a.representationPrimaryDefect b i :=
            a.representationAlpha_le_primary b i
          _ = ((d : ℚ) : WithTop ℚ) := by
            unfold representationPrimaryDefect
            rw [hPrimaryMixed]
            have hSourceIndex :
                (⟨i.val, i.lt_large⟩ : Fin (2 * pairs + 4)) =
                  ⟨2 * pairs + 2, by omega⟩ := Fin.ext hlast
            have hTargetIndex :
                (⟨i.val - 1, by omega⟩ : Fin (2 * pairs + 2)) =
                  ⟨2 * pairs + 1, by omega⟩ := by
              apply Fin.ext
              change i.val - 1 = 2 * pairs + 1
              omega
            rw [hSourceIndex, hSourceNext, hTargetIndex, hTargetLast]
            norm_num
      rcases hd with rfl | rfl
      · have hTargetFullOdd : Odd (ordUnit K
            (a.prefixProduct (2 * pairs + 2) *
              b.prefixProduct (2 * pairs + 2))) := by
          rw [ordUnit_mul,
            hSourcePrefixZero (2 * pairs + 2) (by omega),
            hTargetPrefixFull]
          exact odd_one
        have hSelfZero : a.truncatedPrefixDefect b 1 i.val i.val = 0 := by
          apply a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed
            (alphaV := beliUniversalAlphaLaws)
            (alphaW := beliUniversalAlphaLaws)
          simpa only [one_mul, hlast] using hTargetFullOdd
        rw [hSelfZero]
        simpa using hAlphaUpper
      · have hTargetFullZero :
            ordUnit K (b.prefixProduct (2 * pairs + 2)) = 0 := by
          simpa using hTargetPrefixFull
        have hSelfEven : Even (ordUnit K
            (a.prefixProduct (2 * pairs + 2) *
              b.prefixProduct (2 * pairs + 2))) := by
          rw [ordUnit_mul,
            hSourcePrefixZero (2 * pairs + 2) (by omega),
            hTargetFullZero]
          exact Even.zero
        have hRaw : (1 : WithTop ℚ) ≤ defectOrder (K := K)
            ((1 : Kˣ) * a.prefixProduct i.val *
              b.prefixProduct i.val) := by
          simpa only [one_mul, hlast] using
            he2022Classic_one_le_defectOrder_of_even_ordUnit
              (a.prefixProduct (2 * pairs + 2) *
                b.prefixProduct (2 * pairs + 2)) hSelfEven
        have hSourceCap : a.prefixAlphaCap i.val = 1 := by
          rw [a.prefixAlphaCap_of_internal i.pos (by omega)]
          have hindex :
              (⟨i.val - 1, by omega⟩ : Fin (2 * pairs + 3)) =
                ⟨2 * pairs + 1, by omega⟩ := by
            apply Fin.ext
            change i.val - 1 = 2 * pairs + 1
            omega
          have hgap : 2 * pairs + 1 < 2 * pairs + 2 := by omega
          rw [hindex, hSourceAlpha ⟨2 * pairs + 1, by omega⟩ hgap]
          norm_num
        have hTargetCap : b.prefixAlphaCap i.val = ⊤ := by
          rw [hlast]
          exact b.prefixAlphaCap_last
        have hSelfLower : (1 : WithTop ℚ) ≤
            a.truncatedPrefixDefect b 1 i.val i.val := by
          unfold truncatedPrefixDefect
          rw [hSourceCap, hTargetCap]
          exact le_min hRaw (by simp)
        exact hAlphaUpper.trans hSelfLower
  · intro i hi
    have hiCases : i.val = 2 * pairs + 1 ∨
        i.val = 2 * pairs + 2 ∨ i.val = 2 * pairs + 3 := by
      have := i.le_small_succ
      omega
    unfold HeClassicPublishedCentralConditionAt
    intro hTrigger
    rcases hiCases with hfirst | hsecond | hlast
    · unfold centralDefectTrigger at hTrigger
      have hiOneLt := i.one_lt
      have hSourceLt : i.val < 2 * pairs + 2 := by
        rw [hfirst]
        omega
      have hTargetLt : i.val - 2 < 2 * pairs + 1 := by
        rw [hfirst]
        omega
      have hSourceOrder : a.order ⟨i.val, by omega⟩ = 0 :=
        hSourceZero _ hSourceLt
      have hTargetOrder : b.order ⟨i.val - 2, by omega⟩ = 0 :=
        hTargetZero _ hTargetLt
      rw [hTargetOrder, hSourceOrder] at hTrigger
      exact (lt_irrefl (0 : Int) hTrigger.1).elim
    · unfold centralDefectTrigger at hTrigger
      have hiOneLt := i.one_lt
      have hPrevious : a.centralPreviousDefect b i ≤ 1 := by
        calc
          a.centralPreviousDefect b i ≤ a.prefixAlphaCap i.val := by
            unfold centralPreviousDefect
            exact a.truncatedPrefixDefect_le_leftCap b (-1)
              i.val (i.val - 2)
          _ = 1 := by
            rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
            have hgap : i.val - 1 < 2 * pairs + 2 := by
              rw [hsecond]
              omega
            rw [hSourceAlpha ⟨i.val - 1, by omega⟩ hgap]
            norm_num
      have hCurrent : a.centralCurrentDefect b i = 0 := by
        unfold centralCurrentDefect
        have hplus : i.val + 1 = 2 * pairs + 3 := by omega
        have hminus : i.val - 1 = 2 * pairs + 1 := by
          rw [hsecond]
          omega
        rw [hplus, hminus]
        exact hMixedZero
      have hSum : a.centralPreviousDefect b i +
          a.centralCurrentDefect b i ≤ 1 := by
        rw [hCurrent, add_zero]
        exact hPrevious
      have hThreshold : (1 : WithTop ℚ) ≤
          (((2 * (ramificationIndex K : ℚ) +
            (b.order ⟨i.val - 2, by omega⟩ : ℚ) -
            (a.order ⟨i.val, by omega⟩ : ℚ) : ℚ) : WithTop ℚ)) := by
        have hSourceIndex : (⟨i.val, by omega⟩ : Fin (2 * pairs + 4)) =
            ⟨2 * pairs + 2, by omega⟩ := Fin.ext hsecond
        have hTargetVal : i.val - 2 = 2 * pairs := by
          calc
            i.val - 2 = (2 * pairs + 2) - 2 :=
              congrArg (fun k ↦ k - 2) hsecond
            _ = 2 * pairs := by omega
        have hTargetLt : i.val - 2 < 2 * pairs + 1 := by
          calc
            i.val - 2 = 2 * pairs := hTargetVal
            _ < 2 * pairs + 1 := Nat.lt_succ_self _
        have hTargetOrder : b.order ⟨i.val - 2, by omega⟩ = 0 :=
          hTargetZero _ hTargetLt
        rw [hTargetOrder, hSourceIndex, hSourceNext]
        have heQ : (1 : ℚ) ≤ (ramificationIndex K : ℚ) := by
          exact_mod_cast (Nat.succ_le_iff.mpr
            (ramificationIndex_pos (K := K)))
        have hq : (1 : ℚ) ≤ 2 * (ramificationIndex K : ℚ) - 1 := by
          linarith
        exact_mod_cast hq
      exfalso
      exact (not_lt_of_ge (hSum.trans hThreshold)) hTrigger.2
    · unfold centralDefectTrigger at hTrigger
      have hiOneLt := i.one_lt
      have hPrevious : a.centralPreviousDefect b i = 0 := by
        unfold centralPreviousDefect
        rw [hlast]
        have hsub : (2 * pairs + 3) - 2 = 2 * pairs + 1 := by omega
        rw [hsub]
        exact hMixedZero
      have hSum : a.centralPreviousDefect b i +
          a.centralCurrentDefect b i ≤ 1 := by
        rw [hPrevious, zero_add]
        unfold centralCurrentDefect
        rw [hlast]
        have hplus : 2 * pairs + 3 + 1 = 2 * pairs + 4 := by omega
        have hsub : (2 * pairs + 3) - 1 = 2 * pairs + 2 := by omega
        rw [hplus, hsub]
        exact hFullMixed
      have hTargetLastNonnegative :
          0 ≤ b.order ⟨2 * pairs + 1, by omega⟩ := by
        rw [hTargetLast]
        rcases hd with rfl | rfl <;> omega
      have hThreshold : (1 : WithTop ℚ) ≤
          (((2 * (ramificationIndex K : ℚ) +
            (b.order ⟨i.val - 2, by omega⟩ : ℚ) -
            (a.order ⟨i.val, by omega⟩ : ℚ) : ℚ) : WithTop ℚ)) := by
        have hTargetIndex :
            (⟨i.val - 2, by omega⟩ : Fin (2 * pairs + 2)) =
              ⟨2 * pairs + 1, by omega⟩ := by
          apply Fin.ext
          change i.val - 2 = 2 * pairs + 1
          omega
        have hSourceIndex :
            (⟨i.val, by omega⟩ : Fin (2 * pairs + 4)) =
              ⟨2 * pairs + 3, by omega⟩ := Fin.ext hlast
        rw [hTargetIndex, hSourceIndex, hSourceLast]
        have heQ : (1 : ℚ) ≤ (ramificationIndex K : ℚ) := by
          exact_mod_cast (Nat.succ_le_iff.mpr
            (ramificationIndex_pos (K := K)))
        have hlastQ : (0 : ℚ) ≤
            (b.order ⟨2 * pairs + 1, by omega⟩ : ℚ) := by
          exact_mod_cast hTargetLastNonnegative
        have hq : (1 : ℚ) ≤ 2 * (ramificationIndex K : ℚ) +
            (b.order ⟨2 * pairs + 1, by omega⟩ : ℚ) - 1 := by
          linarith
        exact_mod_cast hq
      exfalso
      exact (not_lt_of_ge (hSum.trans hThreshold)) hTrigger.2

end BONG.GoodBONG

private theorem he2022Classic77_discriminant_order :
    ordUnit K
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit = 0 :=
  (isValuationUnit_iff_ordUnit_eq_zero K _).1
    (inferInstance : DyadicDiscriminantClassLaws K).discriminant_isValuationUnit

private theorem he2022Classic77_uniformizer_order :
    ordUnit K (uniformizerPowerUnit K (1 : Int)) = 1 := by
  rw [ordUnit_uniformizerPowerUnit]

/-- The exact good BONG on `P₂^(2*pairs+4)(Delta)`. -/
noncomputable def heClassicEvenP2DiscriminantGoodBONG (pairs : Nat) :=
  heClassicEvenP2GoodBONG (K := K) pairs
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    (uniformizerPowerUnit K (1 : Int))
    (he2022Classic77_discriminant_order (K := K)) (by
      rw [he2022Classic77_uniformizer_order (K := K)]
      omega)

/-- The exact bundled lattice `P₂^(2*pairs+4)(Delta)`. -/
noncomputable def heClassicEvenP2DiscriminantModel (pairs : Nat) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuExactModel
    (heClassicEvenP2 (K := K) pairs
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
      (uniformizerPowerUnit K (1 : Int)))
    (heClassicEvenP2_adjacentAdmissible pairs _ _
      (he2022Classic77_discriminant_order (K := K)) (by
        rw [he2022Classic77_uniformizer_order (K := K)]
        omega))
    (heClassicEvenP2_weakTwoStep pairs _ _
      (he2022Classic77_discriminant_order (K := K)) (by
        rw [he2022Classic77_uniformizer_order (K := K)]
        omega))

/-- Lemma 7.6(i), source-order profile. -/
theorem heClassicEvenP2Discriminant_order (pairs : Nat)
    (i : Fin (2 * pairs + 4)) :
    (heClassicEvenP2DiscriminantGoodBONG (K := K) pairs).order i =
      if i.val < 2 * pairs + 2 then 0 else 1 := by
  simp only [heClassicEvenP2DiscriminantGoodBONG,
    heClassicEvenP2GoodBONG, heHuExactGoodBONG_order]
  rw [heClassicEvenP2_order pairs _ _
    (he2022Classic77_discriminant_order (K := K)),
    he2022Classic77_uniformizer_order (K := K)]

/-- Lemma 7.6(i), alpha profile through paper index `n`. -/
theorem heClassicEvenP2Discriminant_alpha_eq_one
    (pairs : Nat) (i : Fin (2 * pairs + 3))
    (hi : i.val <= 2 * pairs + 1) :
    (heClassicEvenP2DiscriminantGoodBONG (K := K) pairs).alphaValue i = 1 := by
  exact heClassicEvenP2_alpha_eq_one_through_boundary
    (K := K) pairs
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
      (uniformizerPowerUnit K (1 : Int))
      (he2022Classic77_discriminant_order (K := K))
      (he2022Classic77_uniformizer_order (K := K)) i hi

/-- The literal `P₂(Delta)` model is classic integral. -/
@[simp] theorem heClassicEvenP2DiscriminantModel_isClassicIntegral
    (pairs : Nat) :
    (heClassicEvenP2DiscriminantModel (K := K) pairs).IsClassicIntegral := by
  change Lattice.IsClassicIntegral
    (BONG.coefficientDiagonalSpace
      (heClassicEvenP2 (K := K) pairs
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
        (uniformizerPowerUnit K (1 : Int))))
    (heHuExactRealization
      (heClassicEvenP2 (K := K) pairs
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
        (uniformizerPowerUnit K (1 : Int)))
      (heClassicEvenP2_adjacentAdmissible pairs _ _
        (he2022Classic77_discriminant_order (K := K)) (by
          rw [he2022Classic77_uniformizer_order (K := K)]
          omega))
      (heClassicEvenP2_weakTwoStep pairs _ _
        (he2022Classic77_discriminant_order (K := K)) (by
          rw [he2022Classic77_uniformizer_order (K := K)]
          omega))).lattice
  exact heClassicEvenP2_isClassicIntegral (K := K) pairs _ _
    (he2022Classic77_discriminant_order (K := K)) (by
      rw [he2022Classic77_uniformizer_order (K := K)]
      omega)

namespace BONG.GoodBONG

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
private theorem he2022Classic77_signedFullProduct_factor
    (pairs : Nat) (x y c : Kˣ) :
    (-1 : Kˣ) * ((-1 : Kˣ) ^ pairs * x ^ 2) *
        ((-1 : Kˣ) ^ (pairs + 1) * (y ^ 2 * c)) =
      c * (x * y) ^ 2 := by
  have hsign : (-1 : Kˣ) * (-1 : Kˣ) ^ pairs *
      (-1 : Kˣ) ^ (pairs + 1) = 1 := by
    rcases Nat.even_or_odd pairs with hp | hp
    · have hpNext : Odd (pairs + 1) := Even.add_one hp
      rw [hp.neg_one_pow, hpNext.neg_one_pow]
      simp
    · have hpNext : Even (pairs + 1) := Odd.add_one hp
      rw [hp.neg_one_pow, hpNext.neg_one_pow]
      simp
  calc
    (-1 : Kˣ) * ((-1 : Kˣ) ^ pairs * x ^ 2) *
        ((-1 : Kˣ) ^ (pairs + 1) * (y ^ 2 * c)) =
        ((-1 : Kˣ) * (-1 : Kˣ) ^ pairs *
          (-1 : Kˣ) ^ (pairs + 1)) * (c * (x * y) ^ 2) := by
      rw [mul_pow]
      ac_rfl
    _ = c * (x * y) ^ 2 := by rw [hsign, one_mul]

/-- Formula (7.5) for the first published `C` column. -/
theorem he2022ClassicLemma77_C1_fullMixed_le_one
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) (d : Int)
    (hd : d = 0 ∨ d = 1)
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    (heClassicEvenP2DiscriminantGoodBONG (K := K) pairs).truncatedPrefixDefect
          (heClassicEvenC1GoodBONG (K := K) pairs c hc) (-1)
          (2 * pairs + 4) (2 * pairs + 2) ≤ 1 := by
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let pi := uniformizerPowerUnit K (1 : Int)
  let a := heClassicEvenP2DiscriminantGoodBONG (K := K) pairs
  let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
  have hSource : a.prefixProduct (2 * pairs + 4) =
      (-1 : Kˣ) ^ pairs * (delta * pi) ^ 2 := by
    simpa only [a, delta, pi, heClassicEvenP2DiscriminantGoodBONG] using
      (heClassicEvenP2_prefixProduct_full (K := K) pairs delta pi
        (he2022Classic77_discriminant_order (K := K)) (by
          rw [he2022Classic77_uniformizer_order (K := K)]
          omega))
  have hTarget : b.prefixProduct (2 * pairs + 2) =
      (-1 : Kˣ) ^ (pairs + 1) * c := by
    simpa only [b] using
      (heClassicEvenC1_prefixProduct_full (K := K) pairs c hc)
  have hFactor :
      (-1 : Kˣ) * ((-1 : Kˣ) ^ pairs * (delta * pi) ^ 2) *
          ((-1 : Kˣ) ^ (pairs + 1) * c) =
        c * (delta * pi) ^ 2 := by
    simpa using he2022Classic77_signedFullProduct_factor
      (K := K) pairs (delta * pi) 1 c
  calc
    a.truncatedPrefixDefect b (-1) (2 * pairs + 4) (2 * pairs + 2) ≤
        defectOrder (K := K)
          ((-1 : Kˣ) * a.prefixProduct (2 * pairs + 4) *
            b.prefixProduct (2 * pairs + 2)) :=
      a.truncatedPrefixDefect_le_defect b (-1)
        (2 * pairs + 4) (2 * pairs + 2)
    _ = defectOrder (K := K) c := by
      rw [hSource, hTarget, hFactor, defectOrder_mul_square]
    _ = (((d : Int) : ℚ) : WithTop ℚ) := hcDefect
    _ ≤ 1 := by rcases hd with rfl | rfl <;> norm_num

/-- Formula (7.5) for the second published `C` column. -/
theorem he2022ClassicLemma77_C2_fullMixed_le_one
    (pairs : Nat) (c cSharp : Kˣ) (hc : 0 ≤ ordUnit K c)
    (hcSharp : ordUnit K cSharp = 0) (d : Int)
    (hd : d = 0 ∨ d = 1)
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    (heClassicEvenP2DiscriminantGoodBONG (K := K) pairs).truncatedPrefixDefect
          (heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp) (-1)
          (2 * pairs + 4) (2 * pairs + 2) ≤ 1 := by
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let pi := uniformizerPowerUnit K (1 : Int)
  let a := heClassicEvenP2DiscriminantGoodBONG (K := K) pairs
  let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
  have hSource : a.prefixProduct (2 * pairs + 4) =
      (-1 : Kˣ) ^ pairs * (delta * pi) ^ 2 := by
    simpa only [a, delta, pi, heClassicEvenP2DiscriminantGoodBONG] using
      (heClassicEvenP2_prefixProduct_full (K := K) pairs delta pi
        (he2022Classic77_discriminant_order (K := K)) (by
          rw [he2022Classic77_uniformizer_order (K := K)]
          omega))
  have hTarget : b.prefixProduct (2 * pairs + 2) =
      (-1 : Kˣ) ^ (pairs + 1) * (cSharp ^ 2 * c) := by
    simpa only [b] using
      (heClassicEvenC2_prefixProduct_full (K := K)
        pairs c cSharp hc hcSharp)
  have hFactor :
      (-1 : Kˣ) * ((-1 : Kˣ) ^ pairs * (delta * pi) ^ 2) *
          ((-1 : Kˣ) ^ (pairs + 1) * (cSharp ^ 2 * c)) =
        c * ((delta * pi) * cSharp) ^ 2 :=
    he2022Classic77_signedFullProduct_factor
      (K := K) pairs (delta * pi) cSharp c
  calc
    a.truncatedPrefixDefect b (-1) (2 * pairs + 4) (2 * pairs + 2) ≤
        defectOrder (K := K)
          ((-1 : Kˣ) * a.prefixProduct (2 * pairs + 4) *
            b.prefixProduct (2 * pairs + 2)) :=
      a.truncatedPrefixDefect_le_defect b (-1)
        (2 * pairs + 4) (2 * pairs + 2)
    _ = defectOrder (K := K) c := by
      rw [hSource, hTarget, hFactor, defectOrder_mul_square]
    _ = (((d : Int) : ℚ) : WithTop ℚ) := hcDefect
    _ ≤ 1 := by rcases hd with rfl | rfl <;> norm_num

/-- Lemma 7.7(iii), separated exactly along the proof in the published
paper: Corollaries 3.10--3.13 handle the stable ranges, while parts (i) and
(ii) supply the final three defect and central indices. -/
theorem he2022ClassicLemma77iii_of_boundary_conditions
    (pairs : Nat) (a : GoodBONG q L (2 * pairs + 4))
    (b : GoodBONG r M (2 * pairs + 2))
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hSourceZero : ∀ k : Fin (2 * pairs + 4),
      k.val < 2 * pairs + 2 → a.order k = 0)
    (hSourceAlpha : ∀ k : Fin (2 * pairs + 3),
      k.val < 2 * pairs + 2 → a.alphaValue k = 1)
    (hSourceNext : a.order ⟨2 * pairs + 2, by omega⟩ = 1)
    (hSourceLast : a.order ⟨2 * pairs + 3, by omega⟩ = 1)
    (hTargetLast : 0 ≤ b.order ⟨2 * pairs + 1, by omega⟩)
    (hDefectBoundary : ∀ i :
      RepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      2 * pairs ≤ i.val → a.HeClassicDefectConditionAt b i)
    (hCentralBoundary : ∀ i :
      CentralRepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      2 * pairs + 1 ≤ i.val →
        a.HeClassicPublishedCentralConditionAt b i) :
    (∀ i : Fin (2 * pairs + 2),
      a.HeClassicOrderConditionAt b (by omega) i) ∧
    (∀ i : RepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      a.HeClassicDefectConditionAt b i) ∧
    (∀ i : CentralRepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      a.HeClassicPublishedCentralConditionAt b i) ∧
    (∀ i : LongRepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      a.HeClassicLongConditionAt b i) := by
  constructor
  · exact a.he2022ClassicCorollary310i_of_targetLastNonnegative
      (m := 2 * pairs + 2) pairs b (by omega) hBClassic
        hSourceZero hTargetLast
  constructor
  · intro i
    by_cases hi : i.val + 3 ≤ 2 * pairs + 2
    · exact a.he2022ClassicCorollary311iEven
        (m := 2 * pairs + 1) pairs b (by omega)
          hAClassic hBClassic hSourceZero hSourceAlpha i hi
    · exact hDefectBoundary i (by omega)
  constructor
  · intro i
    by_cases hi : i.val + 2 ≤ 2 * pairs + 2
    · exact a.he2022ClassicCorollary312iEven
        (m := 2 * pairs + 1) pairs b (by omega)
          hBClassic hSourceZero i hi
    · exact hCentralBoundary i (by omega)
  · intro i
    apply a.he2022ClassicCorollary313ii (2 * pairs) b hSourceZero
      (Or.inr hSourceNext)
    · rw [hSourceLast, hSourceNext]
      have hePositive := ramificationIndex_pos (K := K)
      omega
    · have := i.succ_lt_large
      omega

/-- Lemma 7.7(iii) for the literal first published `C` column. -/
theorem he2022ClassicLemma77iii_C1_conditions
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) (d : Int)
    (hd : d = 0 ∨ d = 1) (hcOrder : ordUnit K c = 1 - d)
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    let a := heClassicEvenP2DiscriminantGoodBONG (K := K) pairs
    let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
    (∀ i : Fin (2 * pairs + 2),
      a.HeClassicOrderConditionAt b (by omega) i) ∧
    (∀ i : RepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      a.HeClassicDefectConditionAt b i) ∧
    (∀ i : CentralRepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      a.HeClassicPublishedCentralConditionAt b i) ∧
    (∀ i : LongRepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      a.HeClassicLongConditionAt b i) := by
  dsimp only
  let a := heClassicEvenP2DiscriminantGoodBONG (K := K) pairs
  let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
  have hSourceZero : ∀ k : Fin (2 * pairs + 4),
      k.val < 2 * pairs + 2 → a.order k = 0 := by
    intro k hk
    simp only [a, heClassicEvenP2Discriminant_order]
    simp [hk]
  have hSourceAlpha : ∀ k : Fin (2 * pairs + 3),
      k.val < 2 * pairs + 2 → a.alphaValue k = 1 := by
    intro k hk
    exact heClassicEvenP2Discriminant_alpha_eq_one
      (K := K) pairs k (by omega)
  have hSourceNext : a.order ⟨2 * pairs + 2, by omega⟩ = 1 := by
    simp [a, heClassicEvenP2Discriminant_order]
  have hSourceLast : a.order ⟨2 * pairs + 3, by omega⟩ = 1 := by
    simp [a, heClassicEvenP2Discriminant_order]
  have hTargetZero : ∀ k : Fin (2 * pairs + 2),
      k.val < 2 * pairs + 1 → b.order k = 0 := by
    intro k hk
    simp only [b, heClassicEvenC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC1_order]
    simp [show k.val ≠ 2 * pairs + 1 by omega]
  have hTargetAlpha : ∀ k : Fin (2 * pairs + 1),
      k.val < 2 * pairs + 1 → b.alphaValue k = 1 := by
    intro k _hk
    simpa only [b] using
      (heClassicEvenC1_alpha_eq_one (K := K) pairs c d hc hd
        hcOrder hcDefect k)
  have hTargetLast : b.order ⟨2 * pairs + 1, by omega⟩ = 1 - d := by
    simp only [b, heClassicEvenC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC1_order]
    simp [hcOrder]
  have hFullMixed : a.truncatedPrefixDefect b (-1)
      (2 * pairs + 4) (2 * pairs + 2) ≤ 1 := by
    simpa only [a, b] using
      (he2022ClassicLemma77_C1_fullMixed_le_one
        (K := K) pairs c hc d hd hcDefect)
  have hBoundary := he2022ClassicLemma77_boundary_conditions pairs a b d hd
    hSourceZero hSourceAlpha hSourceNext hSourceLast hTargetZero
      hTargetAlpha hTargetLast hFullMixed
  have hTargetLastNonnegative :
      0 ≤ b.order ⟨2 * pairs + 1, by omega⟩ := by
    rw [hTargetLast]
    rcases hd with rfl | rfl <;> omega
  have hAClassic := heClassicEvenP2_isClassicIntegral (K := K) pairs
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    (uniformizerPowerUnit K (1 : Int))
    (he2022Classic77_discriminant_order (K := K)) (by
      rw [he2022Classic77_uniformizer_order (K := K)]
      omega)
  have hBClassic := heClassicEvenC1_isClassicIntegral (K := K) pairs c hc
  exact he2022ClassicLemma77iii_of_boundary_conditions pairs a b hAClassic
    hBClassic hSourceZero hSourceAlpha hSourceNext hSourceLast
      hTargetLastNonnegative hBoundary.1 hBoundary.2

/-- Lemma 7.7(iii) for the literal second published `C` column. -/
theorem he2022ClassicLemma77iii_C2_conditions
    (pairs : Nat) (c cSharp : Kˣ) (hc : 0 ≤ ordUnit K c)
    (hcSharp : ordUnit K cSharp = 0) (d : Int)
    (hd : d = 0 ∨ d = 1) (hcOrder : ordUnit K c = 1 - d)
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    let a := heClassicEvenP2DiscriminantGoodBONG (K := K) pairs
    let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
    (∀ i : Fin (2 * pairs + 2),
      a.HeClassicOrderConditionAt b (by omega) i) ∧
    (∀ i : RepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      a.HeClassicDefectConditionAt b i) ∧
    (∀ i : CentralRepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      a.HeClassicPublishedCentralConditionAt b i) ∧
    (∀ i : LongRepresentationIndex (2 * pairs + 4) (2 * pairs + 2),
      a.HeClassicLongConditionAt b i) := by
  dsimp only
  let a := heClassicEvenP2DiscriminantGoodBONG (K := K) pairs
  let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
  have hSourceZero : ∀ k : Fin (2 * pairs + 4),
      k.val < 2 * pairs + 2 → a.order k = 0 := by
    intro k hk
    simp only [a, heClassicEvenP2Discriminant_order]
    simp [hk]
  have hSourceAlpha : ∀ k : Fin (2 * pairs + 3),
      k.val < 2 * pairs + 2 → a.alphaValue k = 1 := by
    intro k hk
    exact heClassicEvenP2Discriminant_alpha_eq_one
      (K := K) pairs k (by omega)
  have hSourceNext : a.order ⟨2 * pairs + 2, by omega⟩ = 1 := by
    simp [a, heClassicEvenP2Discriminant_order]
  have hSourceLast : a.order ⟨2 * pairs + 3, by omega⟩ = 1 := by
    simp [a, heClassicEvenP2Discriminant_order]
  have hTargetZero : ∀ k : Fin (2 * pairs + 2),
      k.val < 2 * pairs + 1 → b.order k = 0 := by
    intro k hk
    simp only [b, heClassicEvenC2GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC2_order pairs c cSharp hcSharp]
    simp [show k.val ≠ 2 * pairs + 1 by omega]
  have hTargetAlpha : ∀ k : Fin (2 * pairs + 1),
      k.val < 2 * pairs + 1 → b.alphaValue k = 1 := by
    intro k _hk
    simpa only [b] using
      (heClassicEvenC2_alpha_eq_one (K := K) pairs c cSharp d hc
        hcSharp hd hcOrder hcDefect k)
  have hTargetLast : b.order ⟨2 * pairs + 1, by omega⟩ = 1 - d := by
    simp only [b, heClassicEvenC2GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC2_order pairs c cSharp hcSharp]
    simp [hcOrder]
  have hFullMixed : a.truncatedPrefixDefect b (-1)
      (2 * pairs + 4) (2 * pairs + 2) ≤ 1 := by
    simpa only [a, b] using
      (he2022ClassicLemma77_C2_fullMixed_le_one
        (K := K) pairs c cSharp hc hcSharp d hd hcDefect)
  have hBoundary := he2022ClassicLemma77_boundary_conditions pairs a b d hd
    hSourceZero hSourceAlpha hSourceNext hSourceLast hTargetZero
      hTargetAlpha hTargetLast hFullMixed
  have hTargetLastNonnegative :
      0 ≤ b.order ⟨2 * pairs + 1, by omega⟩ := by
    rw [hTargetLast]
    rcases hd with rfl | rfl <;> omega
  have hAClassic := heClassicEvenP2_isClassicIntegral (K := K) pairs
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    (uniformizerPowerUnit K (1 : Int))
    (he2022Classic77_discriminant_order (K := K)) (by
      rw [he2022Classic77_uniformizer_order (K := K)]
      omega)
  have hBClassic := heClassicEvenC2_isClassicIntegral (K := K)
    pairs c cSharp hc hcSharp
  exact he2022ClassicLemma77iii_of_boundary_conditions pairs a b hAClassic
    hBClassic hSourceZero hSourceAlpha hSourceNext hSourceLast
      hTargetLastNonnegative hBoundary.1 hBoundary.2

end BONG.GoodBONG

/-- Lemma 7.7 and Theorem 2.5, first published `C` column. -/
theorem he2022ClassicLemma77_C1_represents
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) (d : Int)
    (hd : d = 0 ∨ d = 1) (hcOrder : ordUnit K c = 1 - d)
    (hcDefect : BONG.GoodBONG.defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    (heClassicEvenP2DiscriminantModel (K := K) pairs).Represents
      (heClassicEvenC1Model (K := K) pairs c hc) := by
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let pi := uniformizerPowerUnit K (1 : Int)
  let a := heClassicEvenP2DiscriminantGoodBONG (K := K) pairs
  let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
  have hcDefectCases : BONG.GoodBONG.defectOrder (K := K) c = 0 ∨
      BONG.GoodBONG.defectOrder (K := K) c = 1 := by
    rcases hd with rfl | rfl
    · left
      simpa using hcDefect
    · right
      simpa using hcDefect
  have hAmbient :
      (BONG.coefficientDiagonalSpace
        (heClassicEvenP2 (K := K) pairs delta pi)).Represents
        (BONG.coefficientDiagonalSpace
          (heClassicEvenC1 (K := K) pairs c)) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenP2 (K := K) pairs delta pi)).2
        (he2022ClassicLemma75i_C1_represents_P2
          (K := K) pairs delta pi c hcDefectCases)
  have hconditions :=
    BONG.GoodBONG.he2022ClassicLemma77iii_C1_conditions
      (K := K) pairs c hc d hd hcOrder hcDefect
  apply a.he2022ClassicRepresents_of_pointwisePrime b (by omega) hAmbient
  · exact hconditions.1
  · exact hconditions.2.1
  · exact hconditions.2.2.1
  · exact hconditions.2.2.2

/-- Lemma 7.7 and Theorem 2.5, second published `C` column. -/
theorem he2022ClassicLemma77_C2_represents
    (pairs : Nat) (c cSharp : Kˣ) (hc : 0 ≤ ordUnit K c)
    (hcSharp : ordUnit K cSharp = 0) (d : Int)
    (hd : d = 0 ∨ d = 1) (hcOrder : ordUnit K c = 1 - d)
    (hcDefect : BONG.GoodBONG.defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    (heClassicEvenP2DiscriminantModel (K := K) pairs).Represents
      (heClassicEvenC2Model (K := K) pairs c cSharp hc hcSharp) := by
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let pi := uniformizerPowerUnit K (1 : Int)
  let a := heClassicEvenP2DiscriminantGoodBONG (K := K) pairs
  let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
  have hcDefectCases : BONG.GoodBONG.defectOrder (K := K) c = 0 ∨
      BONG.GoodBONG.defectOrder (K := K) c = 1 := by
    rcases hd with rfl | rfl
    · left
      simpa using hcDefect
    · right
      simpa using hcDefect
  have hAmbient :
      (BONG.coefficientDiagonalSpace
        (heClassicEvenP2 (K := K) pairs delta pi)).Represents
        (BONG.coefficientDiagonalSpace
          (heClassicEvenC2 (K := K) pairs c cSharp)) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (heClassicEvenC2 (K := K) pairs c cSharp)
      (heClassicEvenP2 (K := K) pairs delta pi)).2
        (he2022ClassicLemma75i_C2_represents_P2
          (K := K) pairs delta pi c cSharp hcDefectCases)
  have hconditions :=
    BONG.GoodBONG.he2022ClassicLemma77iii_C2_conditions
      (K := K) pairs c cSharp hc hcSharp d hd hcOrder hcDefect
  apply a.he2022ClassicRepresents_of_pointwisePrime b (by omega) hAmbient
  · exact hconditions.1
  · exact hconditions.2.1
  · exact hconditions.2.2.1
  · exact hconditions.2.2.2

end Bong
