/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliCorollary44ThreeBlockProof
import Bong.Bong.BinaryStrictModular
import Bong.Bong.GoodExistence
import Bong.Lattice.OrthogonalSupScale
import Bong.Lattice.RankOneNormScale

/-!
# The scale formula in Beli (2003), Corollary 4.4(iv)

The proof follows the first block of a good BONG.  A nondecreasing first
pair splits off a unary component.  A strictly decreasing first pair forms
an improper modular binary component.  In either case goodness forces every
remaining component scale to have no smaller valuation, so the first block
generates the scale of the whole lattice.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG

/-- The value of a unary BONG generates its scale ideal. -/
theorem scaleIdeal_eq_principal_valueUnit_zero_unary
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 1) :
    Lattice.scaleIdeal q L =
      Lattice.principalIdeal (K := K) (b.valueUnit 0 : K) := by
  have hfin : finrank K V = 1 := b.length_eq_finrank.symm
  calc
    Lattice.scaleIdeal q L = Lattice.normIdeal q L :=
      (Lattice.normIdeal_eq_scaleIdeal_of_finrank_eq_one q L hfin).symm
    _ = Lattice.principalIdeal (K := K) (q.quadratic b.head) :=
      b.head_isNormGenerator.normIdeal_eq
    _ = Lattice.principalIdeal (K := K) (b.valueUnit 0 : K) := by
      rw [← b.value_zero_eq_quadratic_head]
      rfl

/-- Principal ideals reverse the valuation order of nonzero generators. -/
theorem principalIdeal_le_principalIdeal_of_ordUnit_le
    (a b : Kˣ) (h : ordUnit K a ≤ ordUnit K b) :
    Lattice.principalIdeal (K := K) (b : K) ≤
      Lattice.principalIdeal (K := K) (a : K) := by
  apply (Lattice.principalIdeal_le_iff_ord_ge
    (Units.ne_zero b) (Units.ne_zero a)).2
  rw [← coe_ordUnit, ← coe_ordUnit]
  exact WithTop.coe_le_coe.mpr h

/-- A two-block split computes the ambient scale as the supremum of its
segment scales. -/
theorem TwoBlockSplitWitness.scaleIdeal_eq_sup
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n cut : Nat}
    {b : BONG V q L n} {hcut : cut ≤ n}
    (S : TwoBlockSplitWitness b cut hcut) :
    Lattice.scaleIdeal q L =
      Lattice.scaleIdeal
          (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice ⊔
        Lattice.scaleIdeal
          (q.restrict S.right.carrier S.right.nondegenerate)
          S.right.lattice := by
  rw [S.decomposition.scaleIdeal_eq_sup_components_fin_two,
    S.component_zero, S.component_one]
  rfl

/-- A three-block split computes the ambient scale as the iterated supremum
of its segment scales. -/
theorem ThreeBlockSplitWitness.scaleIdeal_eq_sup
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    {b : BONG V q L n} {i : Fin n} {hi : i.val + 1 < n}
    (S : ThreeBlockSplitWitness b i hi) :
    Lattice.scaleIdeal q L =
      (Lattice.scaleIdeal
          (q.restrict S.leftBlock.carrier S.leftBlock.nondegenerate)
          S.leftBlock.lattice ⊔
        Lattice.scaleIdeal
          (q.restrict S.pairBlock.carrier S.pairBlock.nondegenerate)
          S.pairBlock.lattice) ⊔
        Lattice.scaleIdeal
          (q.restrict S.rightBlock.carrier S.rightBlock.nondegenerate)
          S.rightBlock.lattice := by
  rw [S.decomposition.scaleIdeal_eq_sup_components_fin_three,
    S.component_zero, S.component_one, S.component_two]
  rfl

/-- A zero-length BONG segment has zero scale ideal. -/
theorem SegmentWitness.scaleIdeal_eq_bot_of_length_zero
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n start : Nat}
    {b : BONG V q L n} {bound : start ≤ n}
    (S : SegmentWitness b start 0 (by omega)) :
    Lattice.scaleIdeal
        (q.restrict S.carrier S.nondegenerate) S.lattice = ⊥ := by
  apply le_antisymm
  · apply Lattice.scaleIdeal_le_of_bilin_mem
      (q.restrict S.carrier S.nondegenerate) S.lattice
    intro x y _ _
    have hsub : Subsingleton S.carrier := by
      constructor
      intro z w
      apply Subtype.ext
      have hz : (z : V) = 0 := by
        have hzmem : (z : V) ∈ b.segmentCarrier start 0 (by omega) := by
          rw [← S.carrier_eq_segmentCarrier]
          exact z.property
        simpa [BONG.segmentCarrier] using hzmem
      have hw : (w : V) = 0 := by
        have hwmem : (w : V) ∈ b.segmentCarrier start 0 (by omega) := by
          rw [← S.carrier_eq_segmentCarrier]
          exact w.property
        simpa [BONG.segmentCarrier] using hwmem
      rw [hz, hw]
    have hxzero : x = 0 := hsub.elim x 0
    rw [hxzero]
    simp
  · exact bot_le

/-- Reindexing a good segment changes only its finite length index; its
orders remain the corresponding ambient BONG orders. -/
@[simp]
theorem SegmentWitness.order_toGoodBONG_castLength
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n start length m : Nat}
    {b : BONG V q L n} {bound : start + length ≤ n}
    (S : SegmentWitness b start length bound) (hgood : b.IsGood)
    (hlength : length = m) (i : Fin m) :
    ((S.toGoodBONG hgood).castLength hlength).order i =
      b.order ⟨start + i.val, by omega⟩ := by
  calc
    ((S.toGoodBONG hgood).castLength hlength).order i =
        (S.toGoodBONG hgood).order ⟨i.val, by omega⟩ :=
      GoodBONG.order_castLength _ _ i
    _ = S.bong.order ⟨i.val, by omega⟩ := rfl
    _ = b.order (S.sourceIndex ⟨i.val, by omega⟩) :=
      S.order_eq ⟨i.val, by omega⟩
    _ = b.order ⟨start + i.val, by omega⟩ := by
      congr 1

/-- Beli (2003), Corollary 4.4(iv), proved without a
`BeliCorollary44Laws` instance. -/
theorem beliCorollary44_iv_unconditional {n : Nat}
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L (n + 2)) (hgood : b.IsGood) :
    Lattice.HasDoubledScaleOrder q L
      (min (2 * b.order 0) (b.order 0 + b.order 1)) := by
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases hnondecreasing : b.order 0 ≤ b.order 1
      · rcases b.beliCorollary44_i_unconditional hgood
          (0 : Fin (n + 2)) (by simp)
          hnondecreasing with ⟨S⟩
        let left := S.left.bong
        have hleftOrder : left.order 0 = b.order 0 := by
          change S.left.bong.order 0 = b.order 0
          simpa [SegmentWitness.sourceIndex] using S.left.order_eq (0 : Fin 1)
        have hleftScale :
            Lattice.scaleIdeal
                (q.restrict S.left.carrier S.left.nondegenerate)
                S.left.lattice =
              Lattice.principalIdeal (K := K) (left.valueUnit 0 : K) :=
          left.scaleIdeal_eq_principal_valueUnit_zero_unary
        let rightRaw := S.right.toGoodBONG hgood
        by_cases hnzero : n = 0
        · subst n
          let right := rightRaw.castLength (by omega : (0 + 2 - 1 = 1))
          have hrightScale :
              Lattice.scaleIdeal
                  (q.restrict S.right.carrier S.right.nondegenerate)
                  S.right.lattice =
                Lattice.principalIdeal (K := K)
                  (right.toBONG.valueUnit 0 : K) :=
            right.toBONG.scaleIdeal_eq_principal_valueUnit_zero_unary
          have horders :
              ordUnit K (left.valueUnit 0) ≤
                ordUnit K (right.toBONG.valueUnit 0) := by
            rw [← left.order_eq_ordUnit, ← right.toBONG.order_eq_ordUnit,
              hleftOrder]
            change b.order 0 ≤ right.order 0
            rw [show right.order 0 = b.order 1 by
              simpa [right, rightRaw] using
                S.right.order_toGoodBONG_castLength hgood
                  (by omega : (0 + 2 - 1 = 1)) (0 : Fin 1)]
            exact hnondecreasing
          have hscale := S.scaleIdeal_eq_sup
          rw [hleftScale, hrightScale,
            sup_eq_left.mpr
              (principalIdeal_le_principalIdeal_of_ordUnit_le
                (left.valueUnit 0) (right.toBONG.valueUnit 0) horders)] at hscale
          refine ⟨left.valueUnit 0, hscale, ?_⟩
          rw [← left.order_eq_ordUnit, hleftOrder]
          change 2 * b.order 0 =
            min (2 * b.order 0) (b.order 0 + b.order 1)
          rw [min_eq_left]
          omega
        · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
            exact ⟨n - 1, by omega⟩
          let right := rightRaw.castLength
            (by omega : ((k + 1) + 2 - 1 = k + 2))
          rcases ih k (by omega) right.toBONG right.good with
            ⟨s, hrightScale, hsOrder⟩
          have hzeroTwo : b.order 0 ≤ b.order 2 :=
            hgood (0 : Fin (k + 1 + 2)) (by simp)
          have hrightOrderZero : right.order 0 = b.order 1 := by
            change ((S.right.toGoodBONG hgood).castLength _).order 0 =
              b.order 1
            exact S.right.order_toGoodBONG_castLength hgood
              (by omega : ((k + 1) + 2 - 1 = k + 2))
              (0 : Fin (k + 2))
          have hrightOrderOne : right.order 1 = b.order 2 := by
            change ((S.right.toGoodBONG hgood).castLength _).order 1 =
              b.order 2
            exact S.right.order_toGoodBONG_castLength hgood
              (by omega : ((k + 1) + 2 - 1 = k + 2))
              (1 : Fin (k + 2))
          have hminBound :
              2 * b.order 0 ≤
                min (2 * right.order 0)
                  (right.order 0 + right.order 1) := by
            apply le_min
            · rw [hrightOrderZero]
              omega
            · rw [hrightOrderZero, hrightOrderOne]
              omega
          have horders : ordUnit K (left.valueUnit 0) ≤ ordUnit K s := by
            rw [← left.order_eq_ordUnit, hleftOrder]
            have hs : 2 * b.order 0 ≤ 2 * ordUnit K s := by
              rw [hsOrder]
              exact hminBound
            omega
          have hscale := S.scaleIdeal_eq_sup
          rw [hleftScale, hrightScale,
            sup_eq_left.mpr
              (principalIdeal_le_principalIdeal_of_ordUnit_le
                (left.valueUnit 0) s horders)] at hscale
          refine ⟨left.valueUnit 0, hscale, ?_⟩
          rw [← left.order_eq_ordUnit, hleftOrder]
          change 2 * b.order 0 =
            min (2 * b.order 0) (b.order 0 + b.order 1)
          rw [min_eq_left]
          omega
      · have hstrict : b.order 1 < b.order 0 := lt_of_not_ge hnondecreasing
        by_cases hnzero : n = 0
        · subst n
          have hscale := b.scaleIdeal_eq_principal_binaryMixedPairing hstrict
          refine ⟨b.binaryMixedPairingUnit hstrict, ?_, ?_⟩
          · simpa using hscale
          · rw [b.two_mul_ordUnit_binaryMixedPairing_eq_order_add hstrict,
              min_eq_right]
            omega
        · rcases b.beliCorollary44_ii_unconditional hgood
            (0 : Fin (n + 2)) (by simp)
            hstrict with ⟨S⟩
          let pair := S.pairBlock.bong
          have hpairOrderZero : pair.order 0 = b.order 0 := by
            change S.pairBlock.bong.order 0 = b.order 0
            simpa [SegmentWitness.sourceIndex] using
              S.pairBlock.order_eq (0 : Fin 2)
          have hpairOrderOne : pair.order 1 = b.order 1 := by
            change S.pairBlock.bong.order 1 = b.order 1
            simpa [SegmentWitness.sourceIndex] using
              S.pairBlock.order_eq (1 : Fin 2)
          have hpairStrict : pair.order 1 < pair.order 0 := by
            rw [hpairOrderOne, hpairOrderZero]
            exact hstrict
          let c := pair.binaryMixedPairingUnit hpairStrict
          have hpairScale :
              Lattice.scaleIdeal
                  (q.restrict S.pairBlock.carrier S.pairBlock.nondegenerate)
                  S.pairBlock.lattice =
                Lattice.principalIdeal (K := K) (c : K) := by
            simpa [c] using
              pair.scaleIdeal_eq_principal_binaryMixedPairing hpairStrict
          have hleftScale :
              Lattice.scaleIdeal
                  (q.restrict S.leftBlock.carrier S.leftBlock.nondegenerate)
                  S.leftBlock.lattice = ⊥ :=
            S.leftBlock.scaleIdeal_eq_bot_of_length_zero
          let rightRaw := S.rightBlock.toGoodBONG hgood
          by_cases hnone : n = 1
          · subst n
            let right := rightRaw.castLength
              (by omega : (1 + 2 - (0 + 2) = 1))
            have hrightScale :
                Lattice.scaleIdeal
                    (q.restrict S.rightBlock.carrier S.rightBlock.nondegenerate)
                    S.rightBlock.lattice =
                  Lattice.principalIdeal (K := K)
                    (right.toBONG.valueUnit 0 : K) :=
              right.toBONG.scaleIdeal_eq_principal_valueUnit_zero_unary
            have hzeroTwo : b.order 0 ≤ b.order 2 :=
              hgood (0 : Fin 3) (by simp)
            have horders :
                ordUnit K c ≤ ordUnit K (right.toBONG.valueUnit 0) := by
              have hc := pair.two_mul_ordUnit_binaryMixedPairing_eq_order_add
                hpairStrict
              have hrightOrder :
                  right.order 0 = b.order 2 := by
                change ((S.rightBlock.toGoodBONG hgood).castLength _).order 0 =
                  b.order 2
                exact S.rightBlock.order_toGoodBONG_castLength hgood
                  (by omega : (1 + 2 - (0 + 2) = 1)) (0 : Fin 1)
              rw [← right.toBONG.order_eq_ordUnit]
              change ordUnit K c ≤ right.order 0
              rw [hrightOrder]
              change ordUnit K c ≤ b.order 2
              have hcOrder : 2 * ordUnit K c =
                  b.order 0 + b.order 1 := by
                change 2 * ordUnit K
                    (pair.binaryMixedPairingUnit hpairStrict) = _
                rw [pair.two_mul_ordUnit_binaryMixedPairing_eq_order_add,
                  hpairOrderZero, hpairOrderOne]
              have hdouble : 2 * ordUnit K c ≤ 2 * b.order 2 := by
                omega
              omega
            have hscale := S.scaleIdeal_eq_sup
            rw [hleftScale, hpairScale, hrightScale, bot_sup_eq,
              sup_eq_left.mpr
                (principalIdeal_le_principalIdeal_of_ordUnit_le c
                  (right.toBONG.valueUnit 0) horders)] at hscale
            refine ⟨c, hscale, ?_⟩
            rw [show 2 * ordUnit K c = b.order 0 + b.order 1 by
              change 2 * ordUnit K
                  (pair.binaryMixedPairingUnit hpairStrict) = _
              rw [pair.two_mul_ordUnit_binaryMixedPairing_eq_order_add,
                hpairOrderZero, hpairOrderOne],
              min_eq_right]
            omega
          · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := by
              exact ⟨n - 2, by omega⟩
            let right := rightRaw.castLength
              (by omega : ((k + 2) + 2 - (0 + 2) = k + 2))
            rcases ih k (by omega) right.toBONG right.good with
              ⟨s, hrightScale, hsOrder⟩
            have hzeroTwo : b.order 0 ≤ b.order 2 :=
              hgood (0 : Fin (k + 2 + 2)) (by simp)
            have honeThree : b.order 1 ≤ b.order 3 :=
              hgood (1 : Fin (k + 2 + 2)) (by simp)
            have hrightOrderZero : right.order 0 = b.order 2 := by
              change ((S.rightBlock.toGoodBONG hgood).castLength _).order 0 =
                b.order 2
              exact S.rightBlock.order_toGoodBONG_castLength hgood
                (by omega : ((k + 2) + 2 - (0 + 2) = k + 2))
                (0 : Fin (k + 2))
            have hrightOrderOne : right.order 1 = b.order 3 := by
              change ((S.rightBlock.toGoodBONG hgood).castLength _).order 1 =
                b.order 3
              exact S.rightBlock.order_toGoodBONG_castLength hgood
                (by omega : ((k + 2) + 2 - (0 + 2) = k + 2))
                (1 : Fin (k + 2))
            have htailBound :
                b.order 0 + b.order 1 ≤
                  min (2 * right.order 0)
                    (right.order 0 + right.order 1) := by
              apply le_min
              · rw [hrightOrderZero]
                omega
              · rw [hrightOrderZero, hrightOrderOne]
                omega
            have hcOrder : 2 * ordUnit K c = b.order 0 + b.order 1 := by
              change 2 * ordUnit K
                  (pair.binaryMixedPairingUnit hpairStrict) = _
              rw [pair.two_mul_ordUnit_binaryMixedPairing_eq_order_add,
                hpairOrderZero, hpairOrderOne]
            have horders : ordUnit K c ≤ ordUnit K s := by
              have hdouble : 2 * ordUnit K c ≤ 2 * ordUnit K s := by
                rw [hcOrder, hsOrder]
                exact htailBound
              omega
            have hscale := S.scaleIdeal_eq_sup
            rw [hleftScale, hpairScale, hrightScale, bot_sup_eq,
              sup_eq_left.mpr
                (principalIdeal_le_principalIdeal_of_ordUnit_le c s horders)]
                at hscale
            refine ⟨c, hscale, ?_⟩
            rw [hcOrder, min_eq_right]
            omega

end BONG

end Bong
