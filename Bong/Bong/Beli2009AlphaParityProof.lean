/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009AlphaArithmetic
import Bong.Bong.Beli2009AlphaLocalizationProof
import Bong.Bong.Beli2019EvenClassMultiplier
import Bong.Bong.Beli2006AlphaP3OddProof

/-!
# A proof of Beli (2009/2010), Lemma 2.7(iv)

The proof follows Beli's induction on the BONG length.  Corollary 2.5(ii)
reduces the defining minimum to the half-gap, the local quadratic defect, and
the alpha values of the two proper consecutive segments.  The only field
input in the local-defect branch is the parity theorem for the defect of an
even-order square class below the dyadic endpoint.

Consequently `Beli2009AlphaParityLaws` is derived from the earlier alpha and
quadratic-defect laws and is no longer an independent trust-boundary input.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

theorem oddRationalInteger_add_evenInteger
    {x : ℚ} (hx : IsOddRationalInteger x) {z : Int} (hz : Even z) :
    IsOddRationalInteger ((z : ℚ) + x) := by
  rcases hx with ⟨k, hkOdd, rfl⟩
  refine ⟨z + k, hz.add_odd hkOdd, ?_⟩
  push_cast
  ring

namespace BONG.GoodBONG

theorem orderGap_ge_neg_two_mul_e_for_parity
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    -(2 * (ramificationIndex K : Int)) ≤ b.orderGap i := by
  have hadmissible := b.toBONG.adjacentParameter_isBinaryParameterAdmissible
    i.castSucc (Nat.add_lt_add_right i.isLt 1)
  have hlower := hadmissible.ordUnit_ge_neg_two_mul_e
  rw [b.toBONG.ordUnit_adjacentParameter i.castSucc
    (Nat.add_lt_add_right i.isLt 1)] at hlower
  exact hlower

theorem ordUnit_adjacentProduct_eq_adjacentOrderSum
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    ordUnit K (b.adjacentProduct i) =
      b.order i.castSucc + b.order i.succ := by
  unfold adjacentProduct
  rw [ordUnit_neg, ordUnit_mul]
  change ordUnit K (b.toBONG.valueUnit i.castSucc) +
      ordUnit K (b.toBONG.valueUnit i.succ) = _
  rw [← b.toBONG.order_eq_ordUnit, ← b.toBONG.order_eq_ordUnit]
  rfl

theorem even_ordUnit_adjacentProduct_of_even_orderGap
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hgap : Even (b.orderGap i)) :
    Even (ordUnit K (b.adjacentProduct i)) := by
  rw [b.ordUnit_adjacentProduct_eq_adjacentOrderSum i]
  rcases hgap with ⟨z, hz⟩
  refine ⟨b.order i.castSucc + z, ?_⟩
  unfold orderGap at hz
  omega

theorem prefixSegmentAlphaCandidate_eq_gap_add_alpha
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1)) (hi : 0 < i.1) :
    b.prefixSegmentAlphaCandidate i hi =
      ((b.orderGap i : ℚ) +
        ((b.prefixAlphaSegmentWitness i hi).toGoodBONG b.good).alphaValue
          (prefixAlphaLocalizationIndex i hi).localPivot : ℚ) := by
  have hidx :
      (prefixAlphaLocalizationIndex i hi).pivotFin.succ = i.castSucc := by
    apply Fin.ext
    change i.1 - 1 + 1 = i.1
    omega
  unfold prefixSegmentAlphaCandidate leftCompressionValue orderGap
  rw [hidx]

theorem suffixSegmentAlphaCandidate_eq_gap_add_alpha
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hi : i.1 + 1 < n + 1) :
    b.suffixSegmentAlphaCandidate i hi =
      ((b.orderGap i : ℚ) +
        ((b.suffixAlphaSegmentWitness i hi).toGoodBONG b.good).alphaValue
          (suffixAlphaLocalizationIndex i hi).localPivot : ℚ) := by
  unfold suffixSegmentAlphaCandidate rightCompressionValue orderGap
  simp only [WithTop.coe_eq_coe]
  rfl

theorem halfGapValue_le_gap_add_prefixSegmentHalfGap
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1)) (hi : 0 < i.1) :
    b.halfGapValue i ≤
      (b.orderGap i : ℚ) +
        ((b.prefixAlphaSegmentWitness i hi).toGoodBONG b.good).halfGapValue
          (prefixAlphaLocalizationIndex i hi).localPivot := by
  let s := prefixAlphaLocalizationIndex i hi
  let w := b.prefixAlphaSegmentWitness i hi
  let c := w.toGoodBONG b.good
  have hlocalTop := b.segment_halfGapCandidate_local s w
  have hlocal : c.halfGapValue s.localPivot =
      b.halfGapValue s.pivotFin := by
    apply WithTop.coe_injective
    rw [c.coe_halfGapValue, b.coe_halfGapValue]
    exact hlocalTop
  rw [hlocal]
  have hpivotSucc : s.pivotFin.succ = i.castSucc := by
    apply Fin.ext
    change i.1 - 1 + 1 = i.1
    omega
  have htwo : s.pivotFin.1 + 2 < n + 2 := by
    change i.1 - 1 + 2 < n + 2
    omega
  have hright :
      (⟨s.pivotFin.castSucc.1 + 2, htwo⟩ : Fin (n + 2)) = i.succ := by
    apply Fin.ext
    change i.1 - 1 + 2 = i.1 + 1
    omega
  have hgood := b.good s.pivotFin.castSucc htwo
  change b.order s.pivotFin.castSucc ≤
      b.order ⟨s.pivotFin.castSucc.1 + 2, htwo⟩ at hgood
  rw [hright] at hgood
  unfold halfGapValue orderGap
  rw [hpivotSucc]
  push_cast
  have hgoodQ : (b.order s.pivotFin.castSucc : ℚ) ≤
      (b.order i.succ : ℚ) := by exact_mod_cast hgood
  linarith [hgoodQ]

theorem halfGapValue_le_gap_add_suffixSegmentHalfGap
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hi : i.1 + 1 < n + 1) :
    b.halfGapValue i ≤
      (b.orderGap i : ℚ) +
        ((b.suffixAlphaSegmentWitness i hi).toGoodBONG b.good).halfGapValue
          (suffixAlphaLocalizationIndex i hi).localPivot := by
  let s := suffixAlphaLocalizationIndex i hi
  let w := b.suffixAlphaSegmentWitness i hi
  let c := w.toGoodBONG b.good
  have hlocalTop := b.segment_halfGapCandidate_local s w
  have hlocal : c.halfGapValue s.localPivot =
      b.halfGapValue s.pivotFin := by
    apply WithTop.coe_injective
    rw [c.coe_halfGapValue, b.coe_halfGapValue]
    exact hlocalTop
  rw [hlocal]
  have hpivotCast : s.pivotFin.castSucc = i.succ := by
    apply Fin.ext
    rfl
  let k : Fin (n + 2) := ⟨i.1 + 2, by omega⟩
  have hpivotSucc : s.pivotFin.succ = k := by
    apply Fin.ext
    rfl
  have htwo : i.castSucc.1 + 2 < n + 2 := by
    change i.1 + 2 < n + 2
    omega
  have hgood := b.good i.castSucc htwo
  have hright :
      (⟨i.castSucc.1 + 2, htwo⟩ : Fin (n + 2)) = k := by
    apply Fin.ext
    rfl
  change b.order i.castSucc ≤
      b.order ⟨i.castSucc.1 + 2, htwo⟩ at hgood
  rw [hright] at hgood
  unfold halfGapValue orderGap
  rw [hpivotCast, hpivotSucc]
  push_cast
  have hgoodQ : (b.order i.castSucc : ℚ) ≤ (b.order k : ℚ) := by
    exact_mod_cast hgood
  linarith [hgoodQ]

theorem odd_alphaValue_of_eq_localDefectCandidate
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hgapEven : Even (b.orderGap i))
    (hstrict : b.alphaValue i < b.halfGapValue i)
    (hcandidate : (b.alphaValue i : WithTop ℚ) =
      b.leftDefectCandidate i i) :
    IsOddRationalInteger (b.alphaValue i) := by
  rw [show b.leftDefectCandidate i i =
      ((b.orderGap i : ℚ) : WithTop ℚ) + b.adjacentDefect i by rfl]
      at hcandidate
  cases hdefect : b.adjacentDefect i with
  | top =>
      rw [hdefect, add_top] at hcandidate
      exact (WithTop.coe_ne_top hcandidate).elim
  | coe d =>
      rw [hdefect, ← WithTop.coe_add] at hcandidate
      have hvalue : b.alphaValue i = (b.orderGap i : ℚ) + d :=
        WithTop.coe_eq_coe.mp hcandidate
      have hlower := b.orderGap_ge_neg_two_mul_e_for_parity i
      have hlowerQ :
          -(2 * (ramificationIndex K : ℚ)) ≤ (b.orderGap i : ℚ) := by
        exact_mod_cast hlower
      have hdLt : d < 2 * (ramificationIndex K : ℚ) := by
        rw [hvalue] at hstrict
        unfold halfGapValue at hstrict
        linarith
      have hproductEven :=
        b.even_ordUnit_adjacentProduct_of_even_orderGap i hgapEven
      have hdefect' : defectOrder (K := K) (b.adjacentProduct i) =
          (d : WithTop ℚ) := by
        simpa only [adjacentDefect] using hdefect
      have hdOdd := isOddRationalInteger_of_even_ordUnit_of_defectOrder_eq
        (b.adjacentProduct i) d hproductEven hdefect' hdLt
      rw [hvalue]
      exact oddRationalInteger_add_evenInteger hdOdd hgapEven

theorem beli2009Lemma27_iv_proved
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hne : b.alphaValue i ≠ b.halfGapValue i) :
    IsOddRationalInteger (b.alphaValue i) := by
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      cases n with
      | zero => exact Fin.elim0 i
      | succ k =>
          have hstrict : b.alphaValue i < b.halfGapValue i :=
            lt_of_le_of_ne (b.alphaValue_le_halfGapValue i) hne
          have hgapLt :
              b.orderGap i < 2 * (ramificationIndex K : Int) := by
            by_contra hnot
            have hge : 2 * (ramificationIndex K : Int) ≤ b.orderGap i :=
              le_of_not_gt hnot
            exact hne (b.alpha_p4 i hge)
          rcases Int.even_or_odd (b.orderGap i) with hgapEven | hgapOdd
          · have halphaMem :
                (b.alphaValue i : WithTop ℚ) ∈
                  b.segmentRecursiveAlphaCandidates i := by
              rw [b.coe_alphaValue, b.beli2009Corollary25_ii i]
              exact Finset.min'_mem _ _
            simp only [segmentRecursiveAlphaCandidates, Finset.mem_insert,
              Finset.mem_union] at halphaMem
            rcases halphaMem with hhalf | hlocal | hprefix | hsuffix
            · have hvalue : b.alphaValue i = b.halfGapValue i := by
                apply WithTop.coe_injective
                rw [b.coe_halfGapValue]
                exact hhalf
              exact (hne hvalue).elim
            · exact b.odd_alphaValue_of_eq_localDefectCandidate i hgapEven
                hstrict hlocal
            · unfold prefixSegmentAlphaCandidates at hprefix
              split at hprefix
              next hi =>
                have hcandidate := Finset.mem_singleton.mp hprefix
                let s := prefixAlphaLocalizationIndex i hi
                let w := b.prefixAlphaSegmentWitness i hi
                let c := w.toGoodBONG b.good
                have hvalue : b.alphaValue i =
                    (b.orderGap i : ℚ) + c.alphaValue s.localPivot := by
                  apply WithTop.coe_eq_coe.mp
                  calc
                    (b.alphaValue i : WithTop ℚ) =
                        b.prefixSegmentAlphaCandidate i hi := hcandidate
                    _ = (((b.orderGap i : ℚ) +
                          c.alphaValue s.localPivot : ℚ) : WithTop ℚ) := by
                      exact b.prefixSegmentAlphaCandidate_eq_gap_add_alpha i hi
                have hsmall : s.stop - s.start < k + 1 := by
                  change i.1 - 0 < k + 1
                  omega
                by_cases hsegmentHalf :
                    c.alphaValue s.localPivot = c.halfGapValue s.localPivot
                · have hlower :=
                    b.halfGapValue_le_gap_add_prefixSegmentHalfGap i hi
                  have hlower' : b.halfGapValue i ≤
                      (b.orderGap i : ℚ) + c.alphaValue s.localPivot := by
                    rw [hsegmentHalf]
                    exact hlower
                  have hcontra :
                      (b.orderGap i : ℚ) + c.alphaValue s.localPivot <
                        b.halfGapValue i := by
                    rw [← hvalue]
                    exact hstrict
                  exact (not_lt_of_ge hlower' hcontra).elim
                · have hsegmentOdd :=
                    ih (s.stop - s.start) hsmall c s.localPivot hsegmentHalf
                  rw [hvalue]
                  exact oddRationalInteger_add_evenInteger hsegmentOdd hgapEven
              next hnot => simp at hprefix
            · unfold suffixSegmentAlphaCandidates at hsuffix
              split at hsuffix
              next hi =>
                have hcandidate := Finset.mem_singleton.mp hsuffix
                let s := suffixAlphaLocalizationIndex i hi
                let w := b.suffixAlphaSegmentWitness i hi
                let c := w.toGoodBONG b.good
                have hvalue : b.alphaValue i =
                    (b.orderGap i : ℚ) + c.alphaValue s.localPivot := by
                  apply WithTop.coe_eq_coe.mp
                  calc
                    (b.alphaValue i : WithTop ℚ) =
                        b.suffixSegmentAlphaCandidate i hi := hcandidate
                    _ = (((b.orderGap i : ℚ) +
                          c.alphaValue s.localPivot : ℚ) : WithTop ℚ) := by
                      exact b.suffixSegmentAlphaCandidate_eq_gap_add_alpha i hi
                have hsmall : s.stop - s.start < k + 1 := by
                  change k + 1 - (i.1 + 1) < k + 1
                  omega
                by_cases hsegmentHalf :
                    c.alphaValue s.localPivot = c.halfGapValue s.localPivot
                · have hlower :=
                    b.halfGapValue_le_gap_add_suffixSegmentHalfGap i hi
                  have hlower' : b.halfGapValue i ≤
                      (b.orderGap i : ℚ) + c.alphaValue s.localPivot := by
                    rw [hsegmentHalf]
                    exact hlower
                  have hcontra :
                      (b.orderGap i : ℚ) + c.alphaValue s.localPivot <
                        b.halfGapValue i := by
                    rw [← hvalue]
                    exact hstrict
                  exact (not_lt_of_ge hlower' hcontra).elim
                · have hsegmentOdd :=
                    ih (s.stop - s.start) hsmall c s.localPivot hsegmentHalf
                  rw [hvalue]
                  exact oddRationalInteger_add_evenInteger hsegmentOdd hgapEven
              next hnot => simp at hsuffix
          · have halphaGap :=
              b.alphaValue_eq_orderGap_of_odd_of_le_twoE
                i hgapLt.le hgapOdd
            exact ⟨b.orderGap i, hgapOdd, halphaGap⟩

end BONG.GoodBONG

/-- Beli (2009/2010), Lemma 2.7(iv), discharged by the concrete induction
above. -/
noncomputable instance beli2009AlphaParityLaws_proved
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K] :
    Beli2009AlphaParityLaws.{u, v} K where
  odd_integer_unless_half := fun b i hne ↦
    BONG.GoodBONG.beli2009Lemma27_iv_proved b i hne

end Bong
