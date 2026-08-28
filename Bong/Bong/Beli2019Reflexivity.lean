/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019RepresentationTransitivity
import Bong.Bong.Beli2009AlphaCompression

/-!
# Beli (2019), the identity case of Theorem 2.1

The zero-length prime-index chain starts with a lattice represented by itself.
This file proves the four representation conditions when the same good BONG
is used on both sides.  In particular, condition (ii) is reduced directly to
the finite candidate set defining `alpha`; no additional local-law interface
is required.
-/

namespace Bong

universe u v w

open Dyadic

/-- Beli (2019), Corollary 3.11: the four conditions are independent of the
chosen good BONGs on the two fixed lattices.  The approximation proof of this
transport is kept as the remaining Section 3 interface. -/
class Beli2019Corollary311Laws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  conditions_iff
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (a a' : BONG.GoodBONG q L (m + 1))
    (b b' : BONG.GoodBONG r M (n + 1)) (hRank : n ≤ m) :
    RepresentationConditions a b hRank ↔
      RepresentationConditions a' b' hRank

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- A good-BONG value prefix represents the prefix obtained by deleting its
last coefficient. -/
theorem prefixValues_represents_succ (a : GoodBONG q L (n + 1))
    (k : Nat) (hk : k + 1 ≤ n + 1) :
    DiagonalRepresents
      (a.prefixValues k (by omega))
      (a.prefixValues (k + 1) hk) := by
  convert DiagonalRepresents.prefixSucc
    (a.prefixValues (k + 1) hk) using 1
  funext i
  rfl

/-- Any shorter good-BONG value prefix is represented by a longer prefix. -/
theorem prefixValues_represents_of_le (a : GoodBONG q L (n + 1))
    (k l : Nat) (hkl : k ≤ l) (hl : l ≤ n + 1) :
    DiagonalRepresents
      (a.prefixValues k (hkl.trans hl))
      (a.prefixValues l hl) := by
  convert DiagonalRepresents.prefixOfLE (a.prefixValues l hl) hkl using 1
  funext i
  rfl

/-- Condition (i) holds identically for one good BONG. -/
theorem representationOrderCondition_self (a : GoodBONG q L (n + 1)) :
    a.RepresentationOrderCondition a (Nat.le_refl n) := by
  intro i
  exact Or.inl le_rfl

/-- The capped comparison defect of identical prefixes is their common alpha
cap, since the comparison product is a square. -/
theorem truncatedPrefixDefect_self_one
    (a : GoodBONG q L (n + 1)) (i : Nat) :
    a.truncatedPrefixDefect a 1 i i = a.prefixAlphaCap i := by
  unfold truncatedPrefixDefect
  rw [defectOrder_eq_top_of_isSquare]
  · simp
  · refine ⟨a.prefixProduct i, ?_⟩
    simp only [one_mul]

/-- Translate an ordinary representation boundary `i` to the corresponding
zero-based alpha index `i - 1`. -/
def representationAlphaIndex
    (i : RepresentationIndex (n + 1) (n + 1)) : Fin n :=
  ⟨i.val - 1, by have := i.pos; have := i.lt_large; omega⟩

/-- In the identity case, the half-gap candidate for `A_i` is the half-gap
candidate defining `alpha_(i-1)`. -/
theorem representationHalfGap_self_eq
    (a : GoodBONG q L (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1)) :
    a.representationHalfGap a i =
      a.halfGapCandidate (representationAlphaIndex i) := by
  have hsub : i.val - 1 + 1 = i.val :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt i.pos))
  have hsucc : (representationAlphaIndex i).succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [representationAlphaIndex, Fin.succ]
    exact hsub
  have hcast : (representationAlphaIndex i).castSucc =
      (⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ :
        Fin (n + 1)) := by
    apply Fin.ext
    rfl
  unfold representationHalfGap halfGapCandidate
  rw [hsucc, hcast]

/-- The primary truncated defect in the identity case is bounded by the
adjacent defect at the matching alpha index. -/
theorem truncatedPrefixDefect_neg_succ_pred_le_adjacent
    (a : GoodBONG q L (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1)) :
    a.truncatedPrefixDefect a (-1) (i.val + 1) (i.val - 1) ≤
      a.adjacentDefect (representationAlphaIndex i) := by
  have hil := i.lt_large
  have hipos := i.pos
  have hsub : i.val - 1 + 1 = i.val :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt i.pos))
  apply (a.truncatedPrefixDefect_le_defect a (-1)
    (i.val + 1) (i.val - 1)).trans_eq
  unfold adjacentDefect
  have hi : (i.val - 1) + 1 < n + 1 := by omega
  have hproduct := a.prefixProduct_add_two (i.val - 1) hi
  have hindex : i.val + 1 = (i.val - 1) + 2 := by omega
  rw [hindex, hproduct]
  have hzero :
      (⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Fin (n + 1)) =
        (representationAlphaIndex i).castSucc := by
    apply Fin.ext
    rfl
  have hone :
      (⟨i.val - 1 + 1, hi⟩ : Fin (n + 1)) =
        (representationAlphaIndex i).succ := by
    apply Fin.ext
    simp only [representationAlphaIndex, Fin.succ]
  rw [hzero, hone]
  rw [show (-1 : Kˣ) *
      (a.prefixProduct (i.val - 1) *
        a.valueUnit (representationAlphaIndex i).castSucc *
        a.valueUnit (representationAlphaIndex i).succ) *
      a.prefixProduct (i.val - 1) =
      a.adjacentProduct (representationAlphaIndex i) *
        a.prefixProduct (i.val - 1) ^ 2 by
    unfold adjacentProduct representationAlphaIndex
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_one, pow_two]
    ring]
  exact defectOrder_mul_square _ _

/-- The identity primary candidate is bounded by the local left-defect
candidate in the definition of `alpha`. -/
theorem representationPrimaryDefect_self_le_leftDefect
    (a : GoodBONG q L (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1)) :
    a.representationPrimaryDefect a i ≤
      a.leftDefectCandidate (representationAlphaIndex i)
        (representationAlphaIndex i) := by
  have hsub : i.val - 1 + 1 = i.val :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt i.pos))
  have hsucc : (representationAlphaIndex i).succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [representationAlphaIndex, Fin.succ]
    exact hsub
  have hcast : (representationAlphaIndex i).castSucc =
      (⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ :
        Fin (n + 1)) := by
    apply Fin.ext
    rfl
  unfold representationPrimaryDefect leftDefectCandidate
  rw [hsucc, hcast]
  gcongr
  exact a.truncatedPrefixDefect_neg_succ_pred_le_adjacent i

/-- The same primary candidate is bounded by either neighboring-alpha term,
when that neighbor exists. -/
theorem representationPrimaryDefect_self_le_neighborAlphaCandidate
    (a : GoodBONG q L (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (j : Fin n)
    (hadjacent : j.val + 1 = (representationAlphaIndex i).val ∨
      (representationAlphaIndex i).val + 1 = j.val) :
    a.representationPrimaryDefect a i ≤
      a.neighborAlphaCandidate (representationAlphaIndex i) j := by
  have hsub : i.val - 1 + 1 = i.val :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt i.pos))
  have hsucc : (representationAlphaIndex i).succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [representationAlphaIndex, Fin.succ]
    exact hsub
  have hcast : (representationAlphaIndex i).castSucc =
      (⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ :
        Fin (n + 1)) := by
    apply Fin.ext
    rfl
  rcases hadjacent with hprev | hnext
  · change j.val + 1 = i.val - 1 at hprev
    have hiTwo : 2 ≤ i.val := by omega
    have hcap := a.truncatedPrefixDefect_le_rightCap a (-1)
      (i.val + 1) (i.val - 1)
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    have hj : j = ⟨(i.val - 1) - 1, by omega⟩ := by
      apply Fin.ext
      change j.val = (i.val - 1) - 1
      omega
    unfold representationPrimaryDefect neighborAlphaCandidate alphaGapValue
    rw [hsucc, hcast, hj]
    simpa only [WithTop.coe_add] using add_le_add_right hcap
      (((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ)
  · have hcap := a.truncatedPrefixDefect_le_leftCap a (-1)
      (i.val + 1) (i.val - 1)
    change i.val - 1 + 1 = j.val at hnext
    have hiN : i.val < n := by
      have := j.isLt
      omega
    have hright : i.val + 1 < n + 1 := by
      omega
    rw [a.prefixAlphaCap_of_internal (by omega) hright] at hcap
    have hj : j = ⟨(i.val + 1) - 1, by omega⟩ := by
      apply Fin.ext
      change j.val = (i.val + 1) - 1
      omega
    unfold representationPrimaryDefect neighborAlphaCandidate alphaGapValue
    rw [hsucc, hcast, hj]
    simpa only [WithTop.coe_add] using add_le_add_right hcap
      (((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ)

/-- In the identity case, the representation invariant `A_i` is bounded by
the corresponding lattice invariant `alpha_(i-1)`. -/
theorem representationAlpha_self_le_alpha
    (a : GoodBONG q L (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1)) :
    a.representationAlpha a i ≤
      a.alpha (representationAlphaIndex i) := by
  cases n with
  | zero =>
      have := i.pos
      have := i.lt_large
      omega
  | succ n =>
      unfold alpha
      apply Finset.le_min'
      intro x hx
      simp only [alphaCandidates, Finset.mem_insert,
        Finset.mem_union] at hx
      rcases hx with rfl | hx | hx
      · rw [← a.representationHalfGap_self_eq i]
        exact a.representationAlpha_le_halfGap a i
      · rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
        have hjle := (Finset.mem_filter.mp hj).2
        by_cases hjeq : j = representationAlphaIndex i
        · subst j
          exact (a.representationAlpha_le_primary a i).trans
            (a.representationPrimaryDefect_self_le_leftDefect i)
        · have hjlt : j < representationAlphaIndex i :=
            lt_of_le_of_ne hjle hjeq
          let p : Fin (n + 1) :=
            ⟨(representationAlphaIndex i).val - 1, by omega⟩
          have hp : p.val + 1 = (representationAlphaIndex i).val := by
            dsimp only [p]
            omega
          have hjp : j ≤ p := by
            change j.val ≤ p.val
            dsimp only [p]
            omega
          exact ((a.representationAlpha_le_primary a i).trans
            (a.representationPrimaryDefect_self_le_neighborAlphaCandidate
              i p (Or.inl hp))).trans
                (a.predecessorNeighbor_le_leftDefectCandidate
                  (representationAlphaIndex i) p j hp hjp)
      · rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
        have hle := (Finset.mem_filter.mp hj).2
        by_cases hjeq : j = representationAlphaIndex i
        · subst j
          calc
            a.representationAlpha a i ≤
                a.representationPrimaryDefect a i :=
              a.representationAlpha_le_primary a i
            _ ≤ a.leftDefectCandidate (representationAlphaIndex i)
                (representationAlphaIndex i) :=
              a.representationPrimaryDefect_self_le_leftDefect i
            _ = a.rightDefectCandidate (representationAlphaIndex i)
                (representationAlphaIndex i) := by
              rfl
        · have hlt : representationAlphaIndex i < j :=
            lt_of_le_of_ne hle (Ne.symm hjeq)
          let s : Fin (n + 1) :=
            ⟨(representationAlphaIndex i).val + 1, by omega⟩
          have hs : (representationAlphaIndex i).val + 1 = s.val := by
            rfl
          have hsj : s ≤ j := by
            change s.val ≤ j.val
            dsimp only [s]
            omega
          exact ((a.representationAlpha_le_primary a i).trans
            (a.representationPrimaryDefect_self_le_neighborAlphaCandidate
              i s (Or.inr hs))).trans
                (a.successorNeighbor_le_rightDefectCandidate
                  (representationAlphaIndex i) s j hs hsj)

/-- Condition (iii) is automatic for identical BONGs because the required
shorter diagonal prefix embeds into the longer one. -/
theorem centralRepresentationConditions_self
    (a : GoodBONG q L (n + 1)) :
    a.CentralRepresentationConditions a := by
  intro i _
  have hi := i.one_lt
  have hil := i.lt_large
  exact a.prefixValues_represents_of_le (i.val - 1) i.val
    (by omega) (by omega)

/-- Condition (iv) is automatic for identical BONGs by the two-coordinate
prefix inclusion. -/
theorem longRepresentationConditions_self
    (a : GoodBONG q L (n + 1)) :
    a.LongRepresentationConditions a := by
  intro i _
  have hi := i.one_lt
  have hil := i.succ_lt_large
  exact a.prefixValues_represents_of_le (i.val - 1) (i.val + 1)
    (by omega) (by omega)

/-- Condition (ii) holds identically for one good BONG. -/
theorem representationDefectCondition_self
    (a : GoodBONG q L (n + 1)) :
    a.RepresentationDefectCondition a := by
  intro i
  rw [a.coe_representationAlphaValue a i,
    a.truncatedPrefixDefect_self_one i.val,
    a.prefixAlphaCap_of_internal i.pos i.lt_large]
  change a.representationAlpha a i ≤
    (a.alphaValue (representationAlphaIndex i) : WithTop ℚ)
  rw [a.coe_alphaValue (representationAlphaIndex i)]
  exact a.representationAlpha_self_le_alpha i

/-- The four conditions of Theorem 2.1 for one fixed good BONG on both sides. -/
theorem representationConditions_self
    (a : GoodBONG q L (n + 1)) :
    RepresentationConditions a a (Nat.le_refl n) where
  orderCondition := a.representationOrderCondition_self
  defectCondition := a.representationDefectCondition_self
  centralRepresentations := a.centralRepresentationConditions_self
  longRepresentations := a.longRepresentationConditions_self

/-- The identity case for arbitrary choices of good BONG on the same lattice,
obtained by transporting the concrete self case through Corollary 3.11. -/
theorem representationConditions_sameLattice
    [Beli2019Corollary311Laws.{u, v, v} K]
    (a b : GoodBONG q L (n + 1)) :
    RepresentationConditions a b (Nat.le_refl n) := by
  exact (Beli2019Corollary311Laws.conditions_iff
    a a a b (Nat.le_refl n)).mp a.representationConditions_self

end BONG.GoodBONG

end Bong
