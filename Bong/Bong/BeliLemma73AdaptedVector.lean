/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma73EndpointVector
import Bong.Bong.BinaryAdaptedShearVector

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

theorem exists_lemma73AdaptedShearCoefficient
    (b : BONG V q L 2)
    (hcriterion : SatisfiesLemma72UnitCriterion
      (K := K) b.binaryParameter)
    (hupper : b.binaryOrderGap ≤ 0) :
    ∃ c : K,
      (2 : K) * c ∈ IntegerRing K ∧
      c ^ 2 + (b.binaryParameter : K) ∈ IntegerRing K ∧
      c ≠ 0 ∧
      ord K c = ((b.binaryOrderGap / 2 : Int) : WithTop Int) ∧
      (((lemma73CentralDepth (K := K) b.binaryOrderGap : Nat) : Int) :
          WithTop Int) ≤
        ord K (c ^ 2 + (b.binaryParameter : K)) ∧
      (b.binaryOrderGap = 0 →
        (((lemma73CentralDepth (K := K) b.binaryOrderGap : Nat) : Int) :
            WithTop Int) <
          ord K (c ^ 2 + (b.binaryParameter : K))) := by
  have hparameterOrder :
      ordUnit K b.binaryParameter = b.binaryOrderGap := by
    change b.binaryParameterOrder = b.binaryOrderGap
    exact b.binaryParameterOrder_eq_orderGap
  have hEvenParameter : Even (ordUnit K b.binaryParameter) := by
    exact hcriterion.1
  rcases exists_defectAdaptedShear b.binaryParameter
      b.binaryParameter_isBinaryParameterAdmissible hEvenParameter with
    ⟨c, htwo, hdiagIntegral, hcrossEq, hsecond⟩
  rw [hparameterOrder] at hcrossEq hsecond
  have hcNe : c ≠ 0 := by
    intro hc
    rw [hc, mul_zero, ord_zero] at hcrossEq
    exact WithTop.top_ne_coe hcrossEq
  let cu : Kˣ := Units.mk0 c hcNe
  have hcUnitOrder : ordUnit K cu = b.binaryOrderGap / 2 := by
    rw [ord_mul, ← ramificationIndex_spec,
      ← show (cu : K) = c by rfl, ← coe_ordUnit] at hcrossEq
    norm_cast at hcrossEq
    omega
  have hcOrder : ord K c =
      ((b.binaryOrderGap / 2 : Int) : WithTop Int) := by
    rw [← show (cu : K) = c by rfl, ← coe_ordUnit, hcUnitOrder]
  have hlower := b.binaryOrderGap_ge_neg_two_mul_e
  have hkCast := lemma73CentralDepth_cast
    (K := K) b.binaryOrderGap hlower
  have hcut : 0 ≤ (ramificationIndex K : Int) -
      ordUnit K b.binaryParameter / 2 := by
    rw [hparameterOrder]
    omega
  have hdCut := beliParameterDefect_cutoff_le_of_unitCriterion
    (K := K) b.binaryParameter hcriterion hcut
  have hweak :
      (((lemma73CentralDepth (K := K) b.binaryOrderGap : Nat) : Int) :
          WithTop Int) ≤
        ord K (c ^ 2 + (b.binaryParameter : K)) := by
    rcases hsecond with htop | hfinite
    · rw [htop.2, ord_zero]
      exact le_top
    · have hdNat :
          ((ramificationIndex K : Int) -
              ordUnit K b.binaryParameter / 2).toNat ≤
            beliParameterDefectNat K b.binaryParameter := by
        have hnat := ENat.toNat_le_toNat hdCut hfinite.1
        simpa [beliParameterDefectNat] using hnat
      rw [hfinite.2]
      apply WithTop.coe_le_coe.mpr
      rw [hkCast]
      have hdInt :
          (ramificationIndex K : Int) - b.binaryOrderGap / 2 ≤
            (beliParameterDefectNat K b.binaryParameter : Int) := by
        have hcast :
            (((ramificationIndex K : Int) -
                b.binaryOrderGap / 2).toNat : Nat) ≤
              beliParameterDefectNat K b.binaryParameter := by
          simpa [hparameterOrder] using hdNat
        have hcastInt :
            ((((ramificationIndex K : Int) -
                b.binaryOrderGap / 2).toNat : Nat) : Int) ≤
              (beliParameterDefectNat K b.binaryParameter : Int) := by
          exact_mod_cast hcast
        rw [Int.toNat_of_nonneg (by omega)] at hcastInt
        exact hcastInt
      omega
  have hstrict : b.binaryOrderGap = 0 →
      (((lemma73CentralDepth (K := K) b.binaryOrderGap : Nat) : Int) :
          WithTop Int) <
        ord K (c ^ 2 + (b.binaryParameter : K)) := by
    intro hGzero
    rcases hsecond with htop | hfinite
    · rw [htop.2, ord_zero]
      exact WithTop.coe_lt_top _
    · have hnotEndpoint :
          ¬IsNegativeDiscriminantQuarterParameter
            (K := K) b.binaryParameter := by
        intro hendpoint
        have hePos := ramificationIndex_pos K
        have hendpointOrder := hendpoint.1
        rw [hparameterOrder, hGzero] at hendpointOrder
        omega
      have hdStrict :=
        beliParameterDefect_cutoff_lt_of_unitCriterion_of_not_endpoint
          (K := K) b.binaryParameter hcriterion hnotEndpoint hcut
      have hdefectEq :
          ((beliParameterDefectNat K b.binaryParameter : Nat) : ℕ∞) =
            beliParameterDefect K b.binaryParameter := by
        simpa [beliParameterDefectNat] using
          (ENat.coe_toNat hfinite.1)
      rw [← hdefectEq] at hdStrict
      have hdNat :
          ((ramificationIndex K : Int) -
              ordUnit K b.binaryParameter / 2).toNat <
            beliParameterDefectNat K b.binaryParameter := by
        exact_mod_cast hdStrict
      rw [hfinite.2]
      apply WithTop.coe_lt_coe.mpr
      rw [hkCast, hGzero]
      have hparameterZero : ordUnit K b.binaryParameter = 0 := by
        rw [hparameterOrder, hGzero]
      rw [hparameterZero] at hdNat
      norm_num at hdNat ⊢
      exact_mod_cast hdNat
  exact ⟨c, htwo, hdiagIntegral, hcNe, hcOrder, hweak, hstrict⟩

/-- The integral defect-adapted vector and the exact order information needed
for the asymmetric form of Lemma 3.19. -/
structure Lemma73AdaptedBinaryVectorData (b : BONG V q L 2) where
  coefficient : K
  two_mul_coefficient_mem :
    (2 : K) * coefficient ∈ IntegerRing K
  diagonal_coefficient_mem :
    coefficient ^ 2 + (b.binaryParameter : K) ∈ IntegerRing K
  coefficient_ne : coefficient ≠ 0
  vector_mem :
    b.binaryAdaptedShearAmbientVector coefficient ∈ L
  mixed_ne :
    q.bilin b.head (b.binaryAdaptedShearAmbientVector coefficient) ≠ 0
  mixed_order :
    ordUnit K (Units.mk0
      (q.bilin b.head (b.binaryAdaptedShearAmbientVector coefficient))
      mixed_ne) =
      b.order 0 + b.binaryOrderGap / 2
  norm_order_ge :
    (((b.order 0 +
        (lemma73CentralDepth (K := K) b.binaryOrderGap : Nat) : Int)) :
          WithTop Int) ≤
      ord K (q.quadratic
        (b.binaryAdaptedShearAmbientVector coefficient))
  norm_order_gt_of_gap_zero : b.binaryOrderGap = 0 →
    (((b.order 0 +
        (lemma73CentralDepth (K := K) b.binaryOrderGap : Nat) : Int)) :
          WithTop Int) <
      ord K (q.quadratic
        (b.binaryAdaptedShearAmbientVector coefficient))

/-- The first two vectors of the ternary argument admit an integral adapted
vector with the required mixed and diagonal orders. -/
theorem exists_lemma73AdaptedBinaryVectorData
    (b : BONG V q L 2)
    (hcriterion : SatisfiesLemma72UnitCriterion
      (K := K) b.binaryParameter)
    (hupper : b.binaryOrderGap ≤ 0) :
    Nonempty (Lemma73AdaptedBinaryVectorData b) := by
  rcases b.exists_lemma73AdaptedShearCoefficient hcriterion hupper with
    ⟨c, htwo, hdiag, hcNe, hcOrder, hnorm, hnormStrict⟩
  have hvectorMem :=
    b.binaryAdaptedShearAmbientVector_mem c htwo hdiag
  have hmixedNe :
      q.bilin b.head (b.binaryAdaptedShearAmbientVector c) ≠ 0 := by
    rw [b.bilin_head_binaryAdaptedShearAmbientVector]
    exact mul_ne_zero (Units.ne_zero (b.valueUnit 0)) hcNe
  have hmixedOrder :
      ordUnit K (Units.mk0
        (q.bilin b.head (b.binaryAdaptedShearAmbientVector c))
        hmixedNe) =
        b.order 0 + b.binaryOrderGap / 2 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    change ord K
      (q.bilin b.head (b.binaryAdaptedShearAmbientVector c)) = _
    rw [b.bilin_head_binaryAdaptedShearAmbientVector,
      ord_mul, ← coe_ordUnit, ← b.order_eq_ordUnit, hcOrder]
    norm_cast
  have hnormScaled :
      (((b.order 0 +
          (lemma73CentralDepth (K := K) b.binaryOrderGap : Nat) : Int)) :
            WithTop Int) ≤
        ord K (q.quadratic
          (b.binaryAdaptedShearAmbientVector c)) := by
    rw [b.quadratic_binaryAdaptedShearAmbientVector,
      ord_mul, ← coe_ordUnit, ← b.order_eq_ordUnit]
    simpa only [WithTop.coe_add, add_comm] using
      (add_le_add_left hnorm (b.order 0 : WithTop Int))
  have hnormScaledStrict : b.binaryOrderGap = 0 →
      (((b.order 0 +
          (lemma73CentralDepth (K := K) b.binaryOrderGap : Nat) : Int)) :
            WithTop Int) <
        ord K (q.quadratic
          (b.binaryAdaptedShearAmbientVector c)) := by
    intro hzero
    rw [b.quadratic_binaryAdaptedShearAmbientVector,
      ord_mul, ← coe_ordUnit, ← b.order_eq_ordUnit]
    simpa only [WithTop.coe_add] using
      (WithTop.add_lt_add_left
        (show (b.order 0 : WithTop Int) ≠ ⊤ from WithTop.coe_ne_top)
        (hnormStrict hzero))
  exact ⟨{
    coefficient := c
    two_mul_coefficient_mem := htwo
    diagonal_coefficient_mem := hdiag
    coefficient_ne := hcNe
    vector_mem := hvectorMem
    mixed_ne := hmixedNe
    mixed_order := hmixedOrder
    norm_order_ge := hnormScaled
    norm_order_gt_of_gap_zero := hnormScaledStrict }⟩

end BONG

end Bong
