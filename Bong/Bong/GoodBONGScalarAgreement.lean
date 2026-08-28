/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Representation

/-!
# Scalar agreement between good BONGs

The numerical invariants of a good BONG depend only on its sequence of
nonzero quadratic values.  This file records that fact across different
ambient quadratic spaces.  It is useful when an isometric embedding is
replaced by a literal lattice inclusion.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- The initial numerical invariants of a longer good BONG agree with those
of a shorter good BONG.  The alpha-cap clause is separate from scalar-value
agreement because an alpha invariant can see values beyond the boundary. -/
structure PrefixAgreement
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hRank : n ≤ m) : Prop where
  valueUnit_eq (i : Fin (n + 1)) :
    a.valueUnit ⟨i.val, by omega⟩ = b.valueUnit i
  prefixAlphaCap_eq (i : Nat) (hi : i ≤ n) :
    a.prefixAlphaCap i = b.prefixAlphaCap i

namespace PrefixAgreement

variable {a : GoodBONG q L (m + 1)} {b : GoodBONG r M (n + 1)}
  {hRank : n ≤ m}

/-- Prefix agreement identifies the underlying field values. -/
theorem value_eq (h : PrefixAgreement a b hRank) (i : Fin (n + 1)) :
    a.value ⟨i.val, by omega⟩ = b.value i := by
  simpa only [coe_valueUnit] using congrArg Units.val (h.valueUnit_eq i)

/-- Prefix agreement identifies the valuation orders in the shorter range. -/
theorem order_eq (h : PrefixAgreement a b hRank) (i : Fin (n + 1)) :
    a.order ⟨i.val, by omega⟩ = b.order i := by
  unfold GoodBONG.order
  rw [a.toBONG.order_eq_ordUnit, b.toBONG.order_eq_ordUnit]
  exact congrArg (ordUnit K) (h.valueUnit_eq i)

/-- Nat-indexed form of prefix order agreement. -/
theorem order_eq_nat (h : PrefixAgreement a b hRank) {i : Nat}
    (hi : i < n + 1) :
    a.order ⟨i, by omega⟩ = b.order ⟨i, hi⟩ := by
  simpa only using h.order_eq ⟨i, hi⟩

/-- Prefix agreement identifies every product lying in the shorter range. -/
theorem prefixProduct_eq (h : PrefixAgreement a b hRank) (i : Nat)
    (hi : i ≤ n + 1) :
    a.prefixProduct i = b.prefixProduct i := by
  unfold prefixProduct BONG.prefixProduct
  apply Finset.prod_bij (fun j hj ↦ ⟨j.val, by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    omega⟩)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hj
  · intro j₁ hj₁ j₂ hj₂ heq
    apply Fin.ext
    exact congrArg (fun j : Fin (n + 1) ↦ j.val) heq
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨⟨j.val, by omega⟩, ?_, Fin.ext rfl⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
  · intro j hj
    have hv := h.valueUnit_eq ⟨j.val, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      omega⟩
    simpa only [GoodBONG.valueUnit] using hv

/-- Prefix agreement identifies every finite family of prefix values. -/
theorem prefixValues_eq (h : PrefixAgreement a b hRank) (i : Nat)
    (hi : i ≤ n + 1) :
    a.prefixValues i (hi.trans (by omega)) = b.prefixValues i hi := by
  funext j
  exact h.value_eq ⟨j.val, j.isLt.trans_le hi⟩

end PrefixAgreement

/-- Two equally long good BONGs have the same scalar sequence. -/
structure ScalarAgreement
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1)) : Prop where
  valueUnit_eq (i : Fin (n + 1)) : a.valueUnit i = b.valueUnit i

namespace ScalarAgreement

variable {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)}

/-- Scalar agreement is reflexive. -/
theorem refl (a : GoodBONG q L (n + 1)) : ScalarAgreement a a where
  valueUnit_eq _ := rfl

/-- Scalar agreement is symmetric. -/
theorem symm (h : ScalarAgreement a b) : ScalarAgreement b a where
  valueUnit_eq i := (h.valueUnit_eq i).symm

/-- Scalar agreement is transitive, also across a third ambient space. -/
theorem trans
    {U : Type*} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {N : Lattice K U}
    {c : GoodBONG s N (n + 1)}
    (hab : ScalarAgreement a b) (hbc : ScalarAgreement b c) :
    ScalarAgreement a c where
  valueUnit_eq i := (hab.valueUnit_eq i).trans (hbc.valueUnit_eq i)

/-- Scalar agreement also identifies the underlying field values. -/
theorem value_eq (h : ScalarAgreement a b) (i : Fin (n + 1)) :
    a.value i = b.value i := by
  simpa only [coe_valueUnit] using congrArg Units.val (h.valueUnit_eq i)

/-- Scalar agreement identifies all valuation orders. -/
theorem order_eq (h : ScalarAgreement a b) (i : Fin (n + 1)) :
    a.order i = b.order i := by
  unfold GoodBONG.order
  rw [a.toBONG.order_eq_ordUnit, b.toBONG.order_eq_ordUnit]
  exact congrArg (ordUnit K) (h.valueUnit_eq i)

/-- Scalar agreement identifies adjacent products. -/
theorem adjacentProduct_eq (h : ScalarAgreement a b) (i : Fin n) :
    a.adjacentProduct i = b.adjacentProduct i := by
  unfold adjacentProduct
  rw [h.valueUnit_eq, h.valueUnit_eq]

/-- Scalar agreement identifies adjacent defect orders. -/
theorem adjacentDefect_eq (h : ScalarAgreement a b) (i : Fin n) :
    a.adjacentDefect i = b.adjacentDefect i := by
  unfold adjacentDefect
  rw [h.adjacentProduct_eq]

/-- Scalar agreement identifies the half-gap candidates. -/
theorem halfGapCandidate_eq (h : ScalarAgreement a b) (i : Fin n) :
    a.halfGapCandidate i = b.halfGapCandidate i := by
  unfold halfGapCandidate
  rw [h.order_eq, h.order_eq]

/-- Scalar agreement identifies the left defect candidates. -/
theorem leftDefectCandidate_eq (h : ScalarAgreement a b) (i j : Fin n) :
    a.leftDefectCandidate i j = b.leftDefectCandidate i j := by
  unfold leftDefectCandidate
  rw [h.order_eq, h.order_eq, h.adjacentDefect_eq]

/-- Scalar agreement identifies the right defect candidates. -/
theorem rightDefectCandidate_eq (h : ScalarAgreement a b) (i j : Fin n) :
    a.rightDefectCandidate i j = b.rightDefectCandidate i j := by
  unfold rightDefectCandidate
  rw [h.order_eq, h.order_eq, h.adjacentDefect_eq]

/-- Scalar agreement identifies the finite candidate set defining alpha. -/
theorem alphaCandidates_eq (h : ScalarAgreement a b) (i : Fin n) :
    a.alphaCandidates i = b.alphaCandidates i := by
  unfold alphaCandidates
  rw [h.halfGapCandidate_eq]
  congr 2
  · apply Finset.image_congr
    intro j _
    exact h.leftDefectCandidate_eq i j
  · apply Finset.image_congr
    intro j _
    exact h.rightDefectCandidate_eq i j

/-- Scalar agreement identifies alpha as a `WithTop` value. -/
theorem alpha_eq (h : ScalarAgreement a b) (i : Fin n) :
    a.alpha i = b.alpha i := by
  unfold alpha
  apply le_antisymm
  · apply Finset.le_min'
    intro x hx
    apply Finset.min'_le
    simpa only [h.alphaCandidates_eq i] using hx
  · apply Finset.le_min'
    intro x hx
    apply Finset.min'_le
    simpa only [h.alphaCandidates_eq i] using hx

/-- Scalar agreement identifies the rational alpha values. -/
theorem alphaValue_eq (h : ScalarAgreement a b) (i : Fin n) :
    a.alphaValue i = b.alphaValue i := by
  apply WithTop.coe_injective
  rw [coe_alphaValue, coe_alphaValue, h.alpha_eq]

/-- Scalar agreement identifies every prefix product. -/
theorem prefixProduct_eq (h : ScalarAgreement a b) (i : Nat) :
    a.prefixProduct i = b.prefixProduct i := by
  unfold prefixProduct BONG.prefixProduct
  apply Finset.prod_congr rfl
  intro j hj
  rw [Finset.mem_filter] at hj
  exact h.valueUnit_eq j

/-- Scalar agreement identifies every capped alpha boundary. -/
theorem prefixAlphaCap_eq (h : ScalarAgreement a b) (i : Nat) :
    a.prefixAlphaCap i = b.prefixAlphaCap i := by
  unfold prefixAlphaCap
  split_ifs with hi
  · rw [h.alphaValue_eq]
  · rfl

/-- Full scalar agreement gives prefix agreement at the reflexive rank bound. -/
theorem toPrefixAgreement (h : ScalarAgreement a b) :
    PrefixAgreement a b (Nat.le_refl n) where
  valueUnit_eq i := h.valueUnit_eq i
  prefixAlphaCap_eq i _ := h.prefixAlphaCap_eq i

/-- Scalar agreement identifies every finite family of prefix values. -/
theorem prefixValues_eq (h : ScalarAgreement a b) (i : Nat)
    (hi : i ≤ n + 1) :
    a.prefixValues i hi = b.prefixValues i hi := by
  funext j
  exact h.value_eq ⟨j.val, j.isLt.trans_le hi⟩

end ScalarAgreement

end BONG.GoodBONG

end Bong
