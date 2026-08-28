/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009FinalRemarksProof
import Bong.Bong.AdjacentNormGeneratorChange
import Bong.Bong.DefectArithmetic
import Bong.Bong.BeliLemma63
import Bong.Bong.BeliLemma63Proof
import Bong.Bong.BeliLemma66Proof
import Bong.Bong.Beli2019Lemma88Sufficiency
import Bong.Bong.Beli2019Lemma88Necessity
import Bong.Bong.Beli2019Corollary810
import Bong.Bong.Beli2019Corollary811
import Bong.Bong.Beli2019Lemma93Ordinary
import Bong.Bong.EqualRankRepresentationRigidity
import Bong.Bong.Beli2019MainTheorem

namespace Bong

open Dyadic
open BONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Beli2009FinalRemarksProof.LargeResidueConnectivity

private theorem unitSquareClass_inv_local (x : Kˣ) :
    unitSquareClass K x⁻¹ = (unitSquareClass K x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← unitSquareClass_mul, inv_mul_cancel, unitSquareClass_one]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
theorem binaryTransformAt_inv
    {N : Nat} (a : Fin (N + 1) → Kˣ) (i : Fin N)
    (eta : Kˣ) :
    beli2009BinaryTransformAt
        (beli2009BinaryTransformAt a i eta) i eta⁻¹ = a := by
  funext j
  by_cases hleft : j = i.castSucc
  · subst j
    simp
  by_cases hright : j = i.succ
  · subst j
    simp
  rw [beli2009BinaryTransformAt_of_ne _ _ _ _ hleft hright,
    beli2009BinaryTransformAt_of_ne _ _ _ _ hleft hright]

theorem IsBeli2009BinaryTransformation.symm
    {N : Nat} {a b : Fin (N + 1) → Kˣ}
    (h : IsBeli2009BinaryTransformation (K := K) a b) :
    IsBeli2009BinaryTransformation (K := K) b a := by
  rcases h with ⟨i, eta, heta, rfl⟩
  refine ⟨i, eta⁻¹, ?_, ?_⟩
  · have hparameter :
        beli2009BinaryTransformAt a i (eta : Kˣ) i.succ /
            beli2009BinaryTransformAt a i (eta : Kˣ) i.castSucc =
          a i.succ / a i.castSucc := by
      simp only [beli2009BinaryTransformAt_succ,
        beli2009BinaryTransformAt_castSucc]
      simp only [div_eq_mul_inv, mul_inv_rev]
      calc
        (eta : Kˣ) * a i.succ *
              ((a i.castSucc)⁻¹ * (eta : Kˣ)⁻¹) =
            ((eta : Kˣ) * (eta : Kˣ)⁻¹) *
              (a i.succ * (a i.castSucc)⁻¹) := by ac_rfl
        _ = a i.succ * (a i.castSucc)⁻¹ := by simp
    rw [hparameter, map_inv]
    exact (beliNormGeneratorGroup K (a i.succ / a i.castSucc)).inv_mem heta
  · exact (binaryTransformAt_inv a i (eta : Kˣ)).symm

theorem IsBeli2009BinaryStep.symm
    {N : Nat} {a b : Fin (N + 1) → Kˣ}
    (h : IsBeli2009BinaryStep (K := K) a b) :
    IsBeli2009BinaryStep (K := K) b a := by
  rcases h with h | h
  · exact Or.inl (Beli2009ValueSequenceEquivalent.symm h)
  · exact Or.inr (IsBeli2009BinaryTransformation.symm h)

theorem Beli2009BinaryReachable.symm
    {N : Nat} {a b : Fin (N + 1) → Kˣ}
    (h : Beli2009BinaryReachable (K := K) a b) :
    Beli2009BinaryReachable (K := K) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hreach hstep ih =>
      exact (Relation.ReflTransGen.single
        (IsBeli2009BinaryStep.symm hstep)).trans ih

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
theorem binaryTransformAt_cons
    {N : Nat} (x : Kˣ) (a : Fin (N + 1) → Kˣ)
    (i : Fin N) (eta : Kˣ) :
    beli2009BinaryTransformAt (Fin.cons x a) i.succ eta =
      Fin.cons x (beli2009BinaryTransformAt a i eta) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · have hleft : (0 : Fin (N + 2)) ≠ i.succ.castSucc := by
      intro h
      have := congrArg Fin.val h
      simp at this
    have hright : (0 : Fin (N + 2)) ≠ i.succ.succ := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp only [beli2009BinaryTransformAt, Function.update_apply,
      if_neg hright, if_neg hleft, Fin.cons_zero]
  · simp [beli2009BinaryTransformAt, Function.update, Fin.cons]

theorem Beli2009ValueSequenceEquivalent.cons
    {N : Nat} (x : Kˣ) {a b : Fin (N + 1) → Kˣ}
    (h : Beli2009ValueSequenceEquivalent (K := K) a b) :
    Beli2009ValueSequenceEquivalent (K := K) (Fin.cons x a) (Fin.cons x b) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simpa using h j

theorem IsBeli2009BinaryTransformation.cons
    {N : Nat} (x : Kˣ) {a b : Fin (N + 1) → Kˣ}
    (h : IsBeli2009BinaryTransformation (K := K) a b) :
    IsBeli2009BinaryTransformation (K := K) (Fin.cons x a) (Fin.cons x b) := by
  rcases h with ⟨i, eta, heta, rfl⟩
  refine ⟨i.succ, eta, ?_, ?_⟩
  · simpa using heta
  · exact (binaryTransformAt_cons x a i (eta : Kˣ)).symm

theorem IsBeli2009BinaryStep.cons
    {N : Nat} (x : Kˣ) {a b : Fin (N + 1) → Kˣ}
    (h : IsBeli2009BinaryStep (K := K) a b) :
    IsBeli2009BinaryStep (K := K) (Fin.cons x a) (Fin.cons x b) := by
  rcases h with h | h
  · exact Or.inl (Beli2009ValueSequenceEquivalent.cons x h)
  · exact Or.inr (IsBeli2009BinaryTransformation.cons x h)

theorem Beli2009BinaryReachable.cons
    {N : Nat} (x : Kˣ) {a b : Fin (N + 1) → Kˣ}
    (h : Beli2009BinaryReachable (K := K) a b) :
    Beli2009BinaryReachable (K := K) (Fin.cons x a) (Fin.cons x b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hreach hstep ih =>
      exact ih.tail (IsBeli2009BinaryStep.cons x hstep)

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
theorem binaryTransformAt_snoc
    {N : Nat} (a : Fin (N + 1) → Kˣ) (x : Kˣ)
    (i : Fin N) (eta : Kˣ) :
    beli2009BinaryTransformAt (Fin.snoc a x) i.castSucc eta =
      Fin.snoc (beli2009BinaryTransformAt a i eta) x := by
  unfold beli2009BinaryTransformAt
  simp only [Fin.snoc_update, Fin.snoc_castSucc, Fin.castSucc_succ]
  rw [← Fin.castSucc_succ, Fin.snoc_castSucc]

theorem Beli2009ValueSequenceEquivalent.snoc
    {N : Nat} (x : Kˣ) {a b : Fin (N + 1) → Kˣ}
    (h : Beli2009ValueSequenceEquivalent (K := K) a b) :
    Beli2009ValueSequenceEquivalent (K := K) (Fin.snoc a x) (Fin.snoc b x) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
  · simpa using h j

theorem IsBeli2009BinaryTransformation.snoc
    {N : Nat} (x : Kˣ) {a b : Fin (N + 1) → Kˣ}
    (h : IsBeli2009BinaryTransformation (K := K) a b) :
    IsBeli2009BinaryTransformation (K := K) (Fin.snoc a x) (Fin.snoc b x) := by
  rcases h with ⟨i, eta, heta, rfl⟩
  refine ⟨i.castSucc, eta, ?_, ?_⟩
  · simpa only [← Fin.castSucc_succ, Fin.snoc_castSucc] using heta
  · exact (binaryTransformAt_snoc a x i (eta : Kˣ)).symm

theorem IsBeli2009BinaryStep.snoc
    {N : Nat} (x : Kˣ) {a b : Fin (N + 1) → Kˣ}
    (h : IsBeli2009BinaryStep (K := K) a b) :
    IsBeli2009BinaryStep (K := K) (Fin.snoc a x) (Fin.snoc b x) := by
  rcases h with h | h
  · exact Or.inl (Beli2009ValueSequenceEquivalent.snoc x h)
  · exact Or.inr (IsBeli2009BinaryTransformation.snoc x h)

theorem Beli2009BinaryReachable.snoc
    {N : Nat} (x : Kˣ) {a b : Fin (N + 1) → Kˣ}
    (h : Beli2009BinaryReachable (K := K) a b) :
    Beli2009BinaryReachable (K := K) (Fin.snoc a x) (Fin.snoc b x) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hreach hstep ih =>
      exact ih.tail (IsBeli2009BinaryStep.snoc x hstep)

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
def prefixTwoAppend {N : Nat} (a : Fin 2 → Kˣ) (tail : Fin N → Kˣ) :
    Fin (N + 2) → Kˣ :=
  Fin.append a tail ∘ Fin.cast (Nat.add_comm N 2)

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
@[simp] theorem prefixTwoAppend_zero
    {N : Nat} (a : Fin 2 → Kˣ) (tail : Fin N → Kˣ) :
    prefixTwoAppend a tail (0 : Fin (N + 2)) = a 0 := by
  change Fin.append a tail (Fin.cast (Nat.add_comm N 2) 0) = a 0
  rw [show Fin.cast (Nat.add_comm N 2) (0 : Fin (N + 2)) =
      Fin.castAdd N (0 : Fin 2) by apply Fin.ext; rfl,
    Fin.append_left]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
@[simp] theorem prefixTwoAppend_one
    {N : Nat} (a : Fin 2 → Kˣ) (tail : Fin N → Kˣ) :
    prefixTwoAppend a tail (1 : Fin (N + 2)) = a 1 := by
  change Fin.append a tail (Fin.cast (Nat.add_comm N 2) 1) = a 1
  rw [show Fin.cast (Nat.add_comm N 2) (1 : Fin (N + 2)) =
      Fin.castAdd N (1 : Fin 2) by apply Fin.ext; rfl,
    Fin.append_left]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
@[simp] theorem prefixTwoAppend_succ_succ
    {N : Nat} (a : Fin 2 → Kˣ) (tail : Fin N → Kˣ) (j : Fin N) :
    prefixTwoAppend a tail j.succ.succ = tail j := by
  change Fin.append a tail
      (Fin.cast (Nat.add_comm N 2) j.succ.succ) = tail j
  rw [show Fin.cast (Nat.add_comm N 2) j.succ.succ =
      Fin.natAdd 2 j by apply Fin.ext; simp; omega,
    Fin.append_right]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
theorem binaryTransformAt_prefixTwoAppend
    {N : Nat} (a : Fin 2 → Kˣ) (tail : Fin N → Kˣ) (eta : Kˣ) :
    beli2009BinaryTransformAt (prefixTwoAppend a tail)
        (0 : Fin (N + 1)) eta =
      prefixTwoAppend
        (beli2009BinaryTransformAt a (0 : Fin 1) eta) tail := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [beli2009BinaryTransformAt]
  · refine Fin.cases ?_ (fun l => ?_) k
    · simp [beli2009BinaryTransformAt]
    · rw [beli2009BinaryTransformAt_of_ne]
      · simp
      · intro h
        have := congrArg Fin.val h
        simp at this
      · intro h
        have := congrArg Fin.val h
        simp at this

theorem Beli2009ValueSequenceEquivalent.prefixTwoAppend
    {N : Nat} (tail : Fin N → Kˣ) {a b : Fin 2 → Kˣ}
    (h : Beli2009ValueSequenceEquivalent (K := K) a b) :
    Beli2009ValueSequenceEquivalent (K := K)
      (prefixTwoAppend a tail) (prefixTwoAppend b tail) := by
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · simpa using h 0
  · refine Fin.cases ?_ (fun j => ?_) k
    · simpa using h 1
    · simp

theorem IsBeli2009BinaryTransformation.prefixTwoAppend
    {N : Nat} (tail : Fin N → Kˣ) {a b : Fin 2 → Kˣ}
    (h : IsBeli2009BinaryTransformation (K := K) a b) :
    IsBeli2009BinaryTransformation (K := K)
      (prefixTwoAppend a tail) (prefixTwoAppend b tail) := by
  rcases h with ⟨i, eta, heta, rfl⟩
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  refine ⟨0, eta, ?_, ?_⟩
  · simpa using heta
  · exact (binaryTransformAt_prefixTwoAppend a tail (eta : Kˣ)).symm

theorem IsBeli2009BinaryStep.prefixTwoAppend
    {N : Nat} (tail : Fin N → Kˣ) {a b : Fin 2 → Kˣ}
    (h : IsBeli2009BinaryStep (K := K) a b) :
    IsBeli2009BinaryStep (K := K)
      (prefixTwoAppend a tail) (prefixTwoAppend b tail) := by
  rcases h with h | h
  · exact Or.inl (Beli2009ValueSequenceEquivalent.prefixTwoAppend tail h)
  · exact Or.inr (IsBeli2009BinaryTransformation.prefixTwoAppend tail h)

theorem Beli2009BinaryReachable.prefixTwoAppend
    {N : Nat} (tail : Fin N → Kˣ) {a b : Fin 2 → Kˣ}
    (h : Beli2009BinaryReachable (K := K) a b) :
    Beli2009BinaryReachable (K := K)
      (prefixTwoAppend a tail) (prefixTwoAppend b tail) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hreach hstep ih =>
      exact ih.tail (IsBeli2009BinaryStep.prefixTwoAppend tail hstep)

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
def firstTwoValues {N : Nat} (a : Fin (N + 2) → Kˣ) : Fin 2 → Kˣ :=
  fun i => a ⟨i.val, by omega⟩

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
def afterTwoValues {N : Nat} (a : Fin (N + 2) → Kˣ) : Fin N → Kˣ :=
  fun i => a i.succ.succ

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
theorem prefixTwoAppend_firstTwoValues_afterTwoValues
    {N : Nat} (a : Fin (N + 2) → Kˣ) :
    prefixTwoAppend (firstTwoValues a) (afterTwoValues a) = a := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · simp [afterTwoValues]

theorem cons_tailValues_eq
    {N : Nat} (b : BONG.GoodBONG q L (N + 2)) :
    Fin.cons (b.valueUnit (0 : Fin (N + 2)))
        (fun i => b.tail.valueUnit i) =
      (fun i => b.valueUnit i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · apply Units.ext
    change b.toBONG.tail.value j = b.toBONG.value j.succ
    exact b.toBONG.value_tail j

theorem exists_goodBONG_binaryTransformation_exact
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 1))
    (i : Fin N) (eta : valuationUnitSubgroup K)
    (heta : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K (a.valueUnit i.succ / a.valueUnit i.castSucc)) :
    ∃ b : BONG.GoodBONG q L (N + 1),
      (fun j => b.valueUnit j) =
        beli2009BinaryTransformAt (fun j => a.valueUnit j) i eta := by
  let ii : Fin (N + 1) := i.castSucc
  have hii : ii.val + 1 < N + 1 := by
    dsimp only [ii]
    exact Nat.succ_lt_succ i.isLt
  have hparameter : a.toBONG.adjacentParameter ii hii =
      a.valueUnit i.succ / a.valueUnit i.castSucc := by
    unfold BONG.adjacentParameter
    congr 2
  have heta' : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K (a.toBONG.adjacentParameter ii hii) := by
    rwa [hparameter]
  rcases BONG.exists_adjacentMultiplierData a ii hii eta heta' with ⟨D⟩
  refine ⟨D.bong, ?_⟩
  funext j
  by_cases hleft : j = i.castSucc
  · subst j
    simpa only [beli2009BinaryTransformAt_castSucc, ii] using D.valueUnit_left
  by_cases hright : j = i.succ
  · subst j
    have hindex : (⟨ii.val + 1, hii⟩ : Fin (N + 1)) = i.succ := by
      apply Fin.ext
      rfl
    simpa only [beli2009BinaryTransformAt_succ, hindex] using D.valueUnit_right
  have hleftVal : j.val ≠ i.val := by
    intro h
    exact hleft (Fin.ext h)
  have hrightVal : j.val ≠ i.val + 1 := by
    intro h
    exact hright (Fin.ext h)
  have houtside : j.val < ii.val ∨ ii.val + 2 ≤ j.val := by
    by_cases hbefore : j.val < ii.val
    · exact Or.inl hbefore
    · right
      change ¬j.val < i.val at hbefore
      change i.val + 2 ≤ j.val
      omega
  rw [beli2009BinaryTransformAt_of_ne _ _ _ _ hleft hright]
  rcases houtside with hbefore | hafter
  · exact D.valueUnit_before j hbefore
  · exact D.valueUnit_after j hafter

/-- Exact adjacent realization packaged as a Beli (2009) binary
transformation. -/
theorem exists_goodBONG_binaryTransformation
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 1))
    (i : Fin N) (eta : valuationUnitSubgroup K)
    (heta : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K (a.valueUnit i.succ / a.valueUnit i.castSucc)) :
    ∃ b : BONG.GoodBONG q L (N + 1),
      IsBeli2009BinaryTransformation (K := K)
        (fun j => a.valueUnit j) (fun j => b.valueUnit j) := by
  rcases exists_goodBONG_binaryTransformation_exact a i eta heta with
    ⟨b, hb⟩
  exact ⟨b, i, eta, heta, hb⟩

theorem reachable_rankOne
    (a b : BONG.GoodBONG q L 1) :
    Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => b.valueUnit i) := by
  have horders : a.SameOrders b :=
    (BONG.GoodBONG.beli2009Theorem31_concrete
      (QuadraticSpace.isIsometric_refl q) a b).mp
        (Lattice.isIsometric_refl q L) |>.sameOrders
  rcases BONG.exists_valueProduct_eq_mul_square a.toBONG b.toBONG with
    ⟨p, hp⟩
  have hpOrder : ordUnit K p = 0 := by
    have h := congrArg (ordUnit K) hp
    have hproductA : a.toBONG.valueProduct = a.valueUnit 0 := by
      change a.toBONG.valueProduct = a.toBONG.valueUnit 0
      apply Units.ext
      simp only [BONG.coe_valueProduct, Fin.prod_univ_one,
        BONG.coe_valueUnit]
    have hproductB : b.toBONG.valueProduct = b.valueUnit 0 := by
      change b.toBONG.valueProduct = b.toBONG.valueUnit 0
      apply Units.ext
      simp only [BONG.coe_valueProduct, Fin.prod_univ_one,
        BONG.coe_valueUnit]
    rw [hproductA, hproductB, ordUnit_mul, ordUnit_pow] at h
    change b.order 0 = a.order 0 + 2 * ordUnit K p at h
    rw [horders 0] at h
    omega
  have hpUnit : IsValuationUnit K (p : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K p).2 hpOrder
  apply Beli2009ValueSequenceEquivalent.reachable
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  have hproductA : a.toBONG.valueProduct = a.valueUnit 0 := by
    change a.toBONG.valueProduct = a.toBONG.valueUnit 0
    apply Units.ext
    simp only [BONG.coe_valueProduct, Fin.prod_univ_one,
      BONG.coe_valueUnit]
  have hproductB : b.toBONG.valueProduct = b.valueUnit 0 := by
    change b.toBONG.valueProduct = b.toBONG.valueUnit 0
    apply Units.ext
    simp only [BONG.coe_valueProduct, Fin.prod_univ_one,
      BONG.coe_valueUnit]
  rw [hproductA, hproductB] at hp
  change unitSquareClass K (a.valueUnit 0) =
    unitSquareClass K (b.valueUnit 0)
  rw [hp]
  exact (unitSquareClass_mul_unit_square K (a.valueUnit 0) p hpUnit).symm

theorem reachable_rankTwo
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    (a b : BONG.GoodBONG q L 2) :
    Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => b.valueUnit i) := by
  have horders : a.SameOrders b :=
    (BONG.GoodBONG.beli2009Theorem31_concrete
      (QuadraticSpace.isIsometric_refl q) a b).mp
        (Lattice.isIsometric_refl q L) |>.sameOrders
  let raw : Kˣ := b.valueUnit 0 / a.valueUnit 0
  have hrawOrder : ordUnit K raw = 0 := by
    dsimp only [raw]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv]
    change b.order 0 + -a.order 0 = 0
    rw [horders 0]
    simp
  have hrawUnit : IsValuationUnit K (raw : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K raw).2 hrawOrder
  let eta : valuationUnitSubgroup K := ⟨raw, hrawUnit⟩
  have hetaGroup : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K a.toBONG.binaryParameter := by
    change valuationUnitClassHom K eta ∈
      (beliNormGeneratorGroup K a.toBONG.binaryParameter :
        Set (ValuationUnitClass K))
    rw [← a.toBONG.normGeneratorValueRatioClassSet_eq_beliNormGeneratorGroup]
    refine ⟨b.toBONG.head, b.toBONG.head_isNormGenerator, ?_⟩
    unfold BONG.normGeneratorValueRatioClass
      BONG.normGeneratorValueRatioValuationUnit
      BONG.normGeneratorValueRatioUnit
    apply congrArg (valuationUnitClassHom K)
    apply Subtype.ext
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mk0,
      BONG.coe_valueUnit]
    rw [← b.toBONG.value_zero_eq_quadratic_head]
    change b.toBONG.value 0 / a.toBONG.value 0 = (raw : K)
    dsimp only [raw, BONG.GoodBONG.valueUnit]
    simp only [Units.val_div_eq_div_val, BONG.coe_valueUnit]
  let changed : Fin 2 → Kˣ :=
    beli2009BinaryTransformAt (fun i => a.valueUnit i)
      (0 : Fin 1) (eta : Kˣ)
  have htrans : IsBeli2009BinaryTransformation (K := K)
      (fun i => a.valueUnit i) changed := by
    exact ⟨0, eta, hetaGroup, rfl⟩
  have hequiv : Beli2009ValueSequenceEquivalent (K := K)
      changed (fun i => b.valueUnit i) := by
    intro i
    fin_cases i
    · change unitSquareClass K ((eta : Kˣ) * a.valueUnit 0) =
        unitSquareClass K (b.valueUnit 0)
      have hraw : (eta : Kˣ) = b.valueUnit 0 / a.valueUnit 0 := rfl
      rw [hraw]
      simp
    · change unitSquareClass K ((eta : Kˣ) * a.valueUnit 1) =
        unitSquareClass K (b.valueUnit 1)
      have hparameter := a.toBONG.binaryUnitSquareClass_eq b.toBONG
      have hraw : (eta : Kˣ) = b.valueUnit 0 / a.valueUnit 0 := rfl
      have hparameter' :
          (unitSquareClass K (a.valueUnit 0))⁻¹ *
              unitSquareClass K (a.valueUnit 1) =
            (unitSquareClass K (b.valueUnit 0))⁻¹ *
              unitSquareClass K (b.valueUnit 1) := by
        simpa only [BONG.binaryUnitSquareClass, BONG.binaryParameter,
          BONG.GoodBONG.valueUnit, unitSquareClass_mul,
          unitSquareClass_inv_local, div_eq_mul_inv,
          mul_comm] using hparameter
      calc
        unitSquareClass K ((eta : Kˣ) * a.valueUnit 1) =
            (unitSquareClass K (b.valueUnit 0) *
                (unitSquareClass K (a.valueUnit 0))⁻¹) *
              unitSquareClass K (a.valueUnit 1) := by
                rw [unitSquareClass_mul, hraw]
                simp only [div_eq_mul_inv, unitSquareClass_mul,
                  unitSquareClass_inv_local]
        _ = unitSquareClass K (b.valueUnit 0) *
              ((unitSquareClass K (a.valueUnit 0))⁻¹ *
                unitSquareClass K (a.valueUnit 1)) := by group
        _ = unitSquareClass K (b.valueUnit 0) *
              ((unitSquareClass K (b.valueUnit 0))⁻¹ *
                unitSquareClass K (b.valueUnit 1)) := by rw [hparameter']
        _ = unitSquareClass K (b.valueUnit 1) := by group
  exact htrans.reachable.trans hequiv.reachable

/-- If the current full BONG has Property B, every norm-generator value of
the same lattice can be moved into its first coordinate by one adjacent
binary transformation.  This is the path form of Beli (2003), Lemma 6.3(ii).
-/
theorem reachable_headAlignment_of_propertyB
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [lemma63 : BeliLemma63Laws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    {N : Nat} (a b : BONG.GoodBONG q L (N + 2))
    (hB : a.toBONG.HasPropertyB) :
    ∃ c : BONG.GoodBONG q L (N + 2),
      c.valueUnit (0 : Fin (N + 2)) = b.valueUnit (0 : Fin (N + 2)) ∧
        Beli2009BinaryReachable (K := K)
          (fun i ↦ a.valueUnit i) (fun i ↦ c.valueUnit i) := by
  let eta : valuationUnitSubgroup K :=
    a.toBONG.normGeneratorValueRatioValuationUnit
      b.toBONG.head b.toBONG.head_isNormGenerator
  have hetaSet : a.toBONG.normGeneratorValueRatioClass
        b.toBONG.head b.toBONG.head_isNormGenerator ∈
      a.toBONG.normGeneratorValueRatioClassSet := by
    exact ⟨b.toBONG.head, b.toBONG.head_isNormGenerator, rfl⟩
  have hetaGroup : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K
        (a.valueUnit (1 : Fin (N + 2)) /
          a.valueUnit (0 : Fin (N + 2))) := by
    have hmem :=
      (BeliLemma63Laws.valueRatioClassSet_subset_group_of_propertyB
        a.toBONG hB) hetaSet
    change a.toBONG.normGeneratorValueRatioClass
        b.toBONG.head b.toBONG.head_isNormGenerator ∈
      beliNormGeneratorGroup K
        (a.valueUnit (1 : Fin (N + 2)) /
          a.valueUnit (0 : Fin (N + 2)))
    convert hmem using 1 <;>
      simp [BONG.adjacentParameter, BONG.GoodBONG.valueUnit]
  rcases exists_goodBONG_binaryTransformation_exact a
      (0 : Fin (N + 1)) eta hetaGroup with ⟨c, hvalues⟩
  have htrans : IsBeli2009BinaryTransformation (K := K)
      (fun j ↦ a.valueUnit j) (fun j ↦ c.valueUnit j) :=
    ⟨(0 : Fin (N + 1)), eta, hetaGroup, hvalues⟩
  have hfirst : c.valueUnit (0 : Fin (N + 2)) =
      b.valueUnit (0 : Fin (N + 2)) := by
    rw [congrFun hvalues (0 : Fin (N + 2))]
    change (eta : Kˣ) * a.valueUnit 0 = b.valueUnit 0
    dsimp only [eta, BONG.normGeneratorValueRatioValuationUnit,
      BONG.normGeneratorValueRatioUnit]
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0, Units.val_div_eq_div_val,
      BONG.coe_valueUnit]
    rw [← b.toBONG.value_zero_eq_quadratic_head]
    field_simp [a.toBONG.value_ne_zero (0 : Fin (N + 2))]
    simpa only [BONG.GoodBONG.coe_valueUnit, BONG.GoodBONG.value] using
      (mul_comm (b.toBONG.value (0 : Fin (N + 2)))
        (a.toBONG.value (0 : Fin (N + 2))))
  exact ⟨c, hfirst, htrans.reachable⟩

theorem reachable_of_firstBinarySegmentReplacement
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    {N : Nat} {bound : 0 + 2 ≤ N + 2}
    (b : BONG.GoodBONG q L (N + 2))
    (w : BONG.SegmentWitness b.toBONG 0 2 bound)
    (c : BONG.GoodBONG
      (q.restrict w.carrier w.nondegenerate) w.lattice 2)
    (R : BONG.SegmentReplacementWitness b.toBONG w c.toBONG) :
    Beli2009BinaryReachable (K := K)
      (fun i => b.valueUnit i) (fun i => R.bong.valueUnit i) := by
  let s := w.toGoodBONG b.good
  have hlocal : Beli2009BinaryReachable (K := K)
      (fun i => s.valueUnit i) (fun i => c.valueUnit i) :=
    reachable_rankTwo s c
  let tail : Fin N → Kˣ := afterTwoValues (fun i => b.valueUnit i)
  have hlift := Beli2009BinaryReachable.prefixTwoAppend tail hlocal
  have hsource :
      prefixTwoAppend (fun i => s.valueUnit i) tail =
        (fun i => b.valueUnit i) := by
    rw [show (fun i => s.valueUnit i) =
        firstTwoValues (fun i => b.valueUnit i) by
      funext i
      change w.bong.valueUnit i = b.toBONG.valueUnit ⟨i.val, by omega⟩
      simpa [BONG.SegmentWitness.sourceIndex] using w.valueUnit_eq i]
    exact prefixTwoAppend_firstTwoValues_afterTwoValues _
  have htarget :
      prefixTwoAppend (fun i => c.valueUnit i) tail =
        (fun i => R.bong.valueUnit i) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · apply Units.ext
      change c.toBONG.value 0 = R.bong.value 0
      rw [← c.toBONG.quadratic_ambientVector,
        ← R.bong.quadratic_ambientVector]
      exact (congrArg q.quadratic (R.inside_eq (0 : Fin 2))).symm
    · refine Fin.cases ?_ (fun j => ?_) k
      · apply Units.ext
        change c.toBONG.value 1 = R.bong.value 1
        rw [← c.toBONG.quadratic_ambientVector,
          ← R.bong.quadratic_ambientVector]
        exact (congrArg q.quadratic (R.inside_eq (1 : Fin 2))).symm
      · rw [prefixTwoAppend_succ_succ]
        dsimp only [tail, afterTwoValues]
        apply Units.ext
        change b.toBONG.value j.succ.succ = R.bong.value j.succ.succ
        rw [← b.toBONG.quadratic_ambientVector,
          ← R.bong.quadratic_ambientVector]
        exact (congrArg q.quadratic
          (R.after_eq j.succ.succ (by simp))).symm
  rw [hsource] at hlift
  rwa [htarget] at hlift

/-- A Lemma 8.8 first-value transform together with the binary path that
constructs it. -/
structure ReachableFirstValueTransform
    {N : Nat} (b : BONG.GoodBONG q L (N + 2)) where
  transform : b.Beli2019FirstValueTransform
  reachable : Beli2009BinaryReachable (K := K)
    (fun i => b.valueUnit i) (fun i => transform.transformed.valueUnit i)

/-- A prescribed-first-value transform from Lemma 8.14 together with the
adjacent-binary path that realizes it. -/
structure ReachablePrescribedFirstValueTransform
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    {N : Nat} (a : BONG.GoodBONG q L (N + 3))
    (b : BONG.GoodBONG r M 1) where
  transform : a.Beli2019PrescribedFirstValueTransform b
  reachable : Beli2009BinaryReachable (K := K)
    (fun i => a.valueUnit i) (fun i => transform.transformed.valueUnit i)

/-- Reduction (I) of Lemma 8.14 together with the binary path producing the
first normal form. -/
structure ReachableLemma814FirstNormalForm
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    {N : Nat} (a : BONG.GoodBONG q L (N + 3))
    (b : BONG.GoodBONG r M 1) where
  data : a.Beli2019Lemma814FirstNormalForm b
  reachable : Beli2009BinaryReachable (K := K)
    (fun i => a.valueUnit i) (fun i => data.transformed.valueUnit i)

/-- A tail replacement together with the adjacent-binary path that realizes
it.  Keeping the path in the structure makes the transformed first binary
cut available to the next local move without hiding it behind an existential.
-/
structure ReachableTailReplacementData
    {N : Nat} (b : BONG.GoodBONG q L (N + 3)) where
  data : b.Beli2019TailReplacementData
  reachable : Beli2009BinaryReachable (K := K)
    (fun i => b.valueUnit i) (fun i => data.transformed.valueUnit i)

theorem reachableTailReplacementData_of_firstValueTransform
    [GoodBONGClassificationLaws.{u, v, v} K]
    [BeliLemma47Laws.{u, v} K]
    {N : Nat} (b : BONG.GoodBONG q L (N + 3))
    (T : ReachableFirstValueTransform b.tail) :
    ∃ D : b.Beli2019TailReplacementData,
      Beli2009BinaryReachable (K := K)
        (fun i => b.valueUnit i) (fun i => D.transformed.valueUnit i) := by
  let c := b.replaceTailGood T.transform.transformed
  have hfirst : c.valueUnit (0 : Fin (N + 3)) =
      b.valueUnit (0 : Fin (N + 3)) := by
    apply Units.ext
    change (b.replaceTailGood T.transform.transformed).toBONG.value 0 =
      b.toBONG.value 0
    rw [(b.replaceTailGood T.transform.transformed).toBONG.value_zero_eq_quadratic_head,
      b.toBONG.value_zero_eq_quadratic_head,
      b.replaceTailGood_head]
  have htailValue : b.tail.valueUnit (0 : Fin (N + 2)) =
      b.valueUnit (1 : Fin (N + 3)) := by
    apply Units.ext
    change b.toBONG.tail.value 0 = b.toBONG.value 1
    rw [b.toBONG.value_tail]
    congr 1
  have hsecond : c.valueUnit (1 : Fin (N + 3)) =
      T.transform.epsilon * b.valueUnit (1 : Fin (N + 3)) := by
    calc
      c.valueUnit (1 : Fin (N + 3)) =
          T.transform.transformed.valueUnit (0 : Fin (N + 2)) := by
        apply Units.ext
        rw [c.coe_valueUnit, T.transform.transformed.coe_valueUnit]
        change c.toBONG.value (1 : Fin (N + 3)) =
          T.transform.transformed.toBONG.value (0 : Fin (N + 2))
        have hindex : (1 : Fin (N + 3)) =
            (0 : Fin (N + 2)).succ := by
          apply Fin.ext
          simp
        rw [hindex, ← c.toBONG.value_tail (0 : Fin (N + 2))]
        rfl
      _ = T.transform.epsilon * b.tail.valueUnit (0 : Fin (N + 2)) :=
        T.transform.firstValue_eq
      _ = T.transform.epsilon * b.valueUnit (1 : Fin (N + 3)) :=
        congrArg (T.transform.epsilon * ·) htailValue
  let D : b.Beli2019TailReplacementData := {
    epsilon := T.transform.epsilon
    epsilon_isValuationUnit := T.transform.epsilon_isValuationUnit
    epsilon_defect := T.transform.epsilon_defect
    transformed := c
    firstValue_eq := hfirst
    secondValue_eq := hsecond
  }
  refine ⟨D, ?_⟩
  have hlift := Beli2009BinaryReachable.cons
    (b.valueUnit (0 : Fin (N + 3))) T.reachable
  rw [cons_tailValues_eq b] at hlift
  have htarget :
      Fin.cons (b.valueUnit (0 : Fin (N + 3)))
          (fun i => T.transform.transformed.valueUnit i) =
        (fun i => c.valueUnit i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hfirst.symm
    · apply Units.ext
      change T.transform.transformed.toBONG.value j = c.toBONG.value j.succ
      rw [← c.toBONG.value_tail j]
      rfl
  rw [htarget] at hlift
  exact hlift

/-- Package the path-refined tail replacement so that later binary-prefix
arguments may state their hypotheses directly on the concrete replacement.
-/
theorem nonempty_reachableTailReplacementData_of_firstValueTransform
    [GoodBONGClassificationLaws.{u, v, v} K]
    [BeliLemma47Laws.{u, v} K]
    {N : Nat} (b : BONG.GoodBONG q L (N + 3))
    (T : ReachableFirstValueTransform b.tail) :
    Nonempty (ReachableTailReplacementData b) := by
  rcases reachableTailReplacementData_of_firstValueTransform b T with
    ⟨D, hD⟩
  exact ⟨⟨D, hD⟩⟩

theorem exists_reachable_firstValueScaling_of_firstBinaryAlpha
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    {N : Nat} (b : BONG.GoodBONG q L (N + 2)) (epsilon : Kˣ)
    (hunit : IsValuationUnit K (epsilon : K))
    (hdefect : (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) epsilon)
    (hbinary : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hhilbert : hilbertSymbol K epsilon (b.adjacentProduct 0) = 1) :
    ∃ transformed : BONG.GoodBONG q L (N + 2),
      transformed.valueUnit (0 : Fin (N + 2)) =
          epsilon * b.valueUnit (0 : Fin (N + 2)) ∧
        Beli2009BinaryReachable (K := K)
          (fun i => b.valueUnit i) (fun i => transformed.valueUnit i) := by
  rcases b.toBONG.exists_segmentWitness 0 2 (by omega) with ⟨w⟩
  let s := w.toGoodBONG b.good
  have hsAlpha :
      (s.alphaValue (0 : Fin 1) : WithTop ℚ) =
        (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
    rw [← b.firstBinaryAlpha_eq_segmentAlpha w, hbinary]
  have hsDefect : (s.alphaValue (0 : Fin 1) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) epsilon := by
    rw [hsAlpha]
    exact hdefect
  have hsHilbert : hilbertSymbol K epsilon (s.adjacentProduct 0) = 1 := by
    have hvalue0 := w.valueUnit_eq (0 : Fin 2)
    have hvalue1 := w.valueUnit_eq (1 : Fin 2)
    have hadjacent : s.adjacentProduct 0 = b.adjacentProduct 0 := by
      unfold BONG.GoodBONG.adjacentProduct
      change -(w.bong.valueUnit 0 * w.bong.valueUnit 1) =
        -(b.toBONG.valueUnit 0 * b.toBONG.valueUnit 1)
      simpa [BONG.SegmentWitness.sourceIndex] using
        congrArg Neg.neg (congrArg₂ (· * ·) hvalue0 hvalue1)
    rw [hadjacent]
    exact hhilbert
  rcases s.binary_scaling_of_hilbert_of_alpha_le_defect epsilon hunit
      hsDefect hsHilbert with ⟨c, hc⟩
  rcases b.toBONG.beliLemma49_ii b.good w c.toBONG c.good with ⟨R⟩
  let transformed : BONG.GoodBONG q L (N + 2) := ⟨R.bong, R.good⟩
  have hinside := R.inside_eq (0 : Fin 2)
  have hvalue : transformed.valueUnit (0 : Fin (N + 2)) =
      c.valueUnit (0 : Fin 2) := by
    apply Units.ext
    change R.bong.value 0 = c.toBONG.value 0
    rw [← R.bong.quadratic_ambientVector,
      ← c.toBONG.quadratic_ambientVector]
    exact congrArg q.quadratic hinside
  have hsValue : s.valueUnit (0 : Fin 2) =
      b.valueUnit (0 : Fin (N + 2)) := by
    change w.bong.valueUnit 0 = b.toBONG.valueUnit 0
    simpa [BONG.SegmentWitness.sourceIndex] using
      w.valueUnit_eq (0 : Fin 2)
  refine ⟨transformed, ?_, ?_⟩
  · calc
      transformed.valueUnit (0 : Fin (N + 2)) =
          c.valueUnit (0 : Fin 2) := hvalue
      _ = epsilon * s.valueUnit (0 : Fin 2) := hc
      _ = epsilon * b.valueUnit (0 : Fin (N + 2)) :=
        congrArg (epsilon * ·) hsValue
  · exact reachable_of_firstBinarySegmentReplacement b w c R

theorem reachableFirstValueTransform_of_firstBinaryAlpha
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    {N : Nat} (b : BONG.GoodBONG q L (N + 2)) (epsilon : Kˣ)
    (hunit : IsValuationUnit K (epsilon : K))
    (hdefect : BONG.GoodBONG.defectOrder (K := K) epsilon =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hbinary : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hhilbert : hilbertSymbol K epsilon (b.adjacentProduct 0) = 1) :
    Nonempty (ReachableFirstValueTransform b) := by
  rcases exists_reachable_firstValueScaling_of_firstBinaryAlpha b epsilon hunit
      hdefect.symm.le hbinary hhilbert with ⟨transformed, hfirst, hreach⟩
  exact ⟨{
    transform := {
      epsilon := epsilon
      epsilon_isValuationUnit := hunit
      epsilon_defect := hdefect
      transformed := transformed
      firstValue_eq := hfirst
    }
    reachable := hreach
  }⟩

/-- Path-refined Hilbert-positive branch of Beli (2019), Lemma 8.14. -/
theorem reachableLemma814_binaryBranch
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 3))
    (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 3)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ))
    (hhilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin (N + 2))) = 1) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  have hunit := a.lemma814Epsilon_isValuationUnit b horder
  have hdefect := a.alpha_le_lemma814EpsilonDefect b conditions
  rcases exists_reachable_firstValueScaling_of_firstBinaryAlpha
      a (a.lemma814Epsilon b) hunit hdefect hbinary hhilbert with
    ⟨transformed, hfirst, hreachable⟩
  exact ⟨{
    transform := {
      transformed := transformed
      firstValue_eq := hfirst.trans (a.lemma814Epsilon_mul_firstValue b)
    }
    reachable := hreachable
  }⟩

/-- A reachable tail twist may be followed by the Hilbert-positive first
binary move.  This is the precise path-level bridge needed in the negative
Hilbert branch of Lemma 8.14: all global arithmetic is inherited from the
original BONG, while the two genuinely dynamic hypotheses are stated on the
concrete tail replacement. -/
theorem reachableLemma814_binaryBranch_after_tailReplacement
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 3))
    (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 3)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (D : ReachableTailReplacementData a)
    (hbinary : D.data.transformed.firstBinaryAlpha =
      (D.data.transformed.alphaValue
        (0 : Fin (N + 2)) : WithTop ℚ))
    (hhilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (D.data.transformed.adjacentProduct (0 : Fin (N + 2))) = 1) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  have hunit := a.lemma814Epsilon_isValuationUnit b horder
  have hdefectOriginal := a.alpha_le_lemma814EpsilonDefect b conditions
  have halphas := a.alpha_invariant D.data.transformed
  have hdefect :
      (D.data.transformed.alphaValue
          (0 : Fin (N + 2)) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) (a.lemma814Epsilon b) := by
    rw [← congrArg (fun x : ℚ => (x : WithTop ℚ))
      (halphas (0 : Fin (N + 2)))]
    exact hdefectOriginal
  rcases exists_reachable_firstValueScaling_of_firstBinaryAlpha
      D.data.transformed (a.lemma814Epsilon b) hunit hdefect hbinary hhilbert
      with ⟨transformed, hfirst, hreachable⟩
  exact ⟨{
    transform := {
      transformed := transformed
      firstValue_eq := by
        calc
          transformed.valueUnit (0 : Fin (N + 3)) =
              a.lemma814Epsilon b *
                D.data.transformed.valueUnit (0 : Fin (N + 3)) := hfirst
          _ = a.lemma814Epsilon b * a.valueUnit (0 : Fin (N + 3)) :=
            congrArg (a.lemma814Epsilon b * ·) D.data.firstValue_eq
          _ = b.valueUnit (0 : Fin 1) :=
            a.lemma814Epsilon_mul_firstValue b
    }
    reachable := D.reachable.trans hreachable
  }⟩

theorem reachableLemma88_halfGap_binary_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    {N : Nat} (b : BONG.GoodBONG q L (N + 2))
    (reference : Kˣ)
    (hrefUnit : IsValuationUnit K (reference : K))
    (hrefDefect : BONG.GoodBONG.defectOrder (K := K) reference =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hbinary : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 1)))
    (hresidueMore : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableFirstValueTransform b) := by
  have hnotPair := b.not_zero_twoEDefectPair_of_halfGap_unit
    reference hrefUnit hrefDefect hhalf
  rcases beli2019Lemma82_ii_unit hresidueMore
      (b.adjacentProduct (0 : Fin (N + 1))) reference hrefUnit hnotPair with
    ⟨epsilon, hepsilonUnit, hepsilonDefectRaw, hepsilonHilbert⟩
  have hepsilonDefect : BONG.GoodBONG.defectOrder (K := K) epsilon =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
    exact (defectOrder_eq_of_quadraticDefect_eq epsilon reference
      hepsilonDefectRaw).trans hrefDefect
  apply reachableFirstValueTransform_of_firstBinaryAlpha
    b epsilon hepsilonUnit hepsilonDefect hbinary
  rw [hilbertSymbol_comm]
  exact hepsilonHilbert

theorem reachableLemma88_strict_binary_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [DyadicUnitDefectSpectrumLaws K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    {N : Nat} (b : BONG.GoodBONG q L (N + 2))
    (hbinary : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hstrict : b.alphaValue (0 : Fin (N + 1)) <
      b.halfGapValue (0 : Fin (N + 1)))
    (hresidueMore : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableFirstValueTransform b) := by
  rcases b.exists_firstAlphaUnit_of_lt_halfGap hstrict with
    ⟨reference, hrefUnit, hrefDefect⟩
  have hsum := b.firstAdjacent_defectOrder_add_alpha_lt_twoE_of_strict_binary
    hbinary hstrict
  have hsumReference :
      BONG.GoodBONG.defectOrder (K := K) (b.adjacentProduct 0) +
          BONG.GoodBONG.defectOrder (K := K) reference <
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hrefDefect]
    exact hsum
  have hnotPair := not_zero_twoEDefectPair_of_defectOrder_add_lt_twoE
    (b.adjacentProduct 0) reference hsumReference
  rcases beli2019Lemma82_ii_unit hresidueMore (b.adjacentProduct 0) reference
      hrefUnit hnotPair with
    ⟨epsilon, hepsilonUnit, hepsilonDefectRaw, hepsilonHilbert⟩
  have hepsilonDefect : BONG.GoodBONG.defectOrder (K := K) epsilon =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
    exact (defectOrder_eq_of_quadraticDefect_eq epsilon reference
      hepsilonDefectRaw).trans hrefDefect
  apply reachableFirstValueTransform_of_firstBinaryAlpha
    b epsilon hepsilonUnit hepsilonDefect hbinary
  rw [hilbertSymbol_comm]
  exact hepsilonHilbert

theorem reachableLemma88_strict_of_adjacentDefect_le_tailAlpha
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [DyadicUnitDefectSpectrumLaws K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    {N : Nat} (b : BONG.GoodBONG q L (N + 3))
    (hle : b.adjacentDefect (0 : Fin (N + 2)) ≤
      (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ))
    (hstrict : b.alphaValue (0 : Fin (N + 2)) <
      b.halfGapValue (0 : Fin (N + 2)))
    (hresidueMore : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableFirstValueTransform b) := by
  apply reachableLemma88_strict_binary_of_largeResidue b
    (b.firstBinaryAlpha_eq_alpha_of_adjacentDefect_le_tailAlpha hle)
    hstrict hresidueMore

theorem reachableLemma88_strict_tail_of_tailTransform
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [DyadicUnitDefectSpectrumLaws K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    {N : Nat} (b : BONG.GoodBONG q L (N + 3))
    (htail :
      (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) <
        b.adjacentDefect (0 : Fin (N + 2)))
    (hstrict : b.alphaValue (0 : Fin (N + 2)) <
      b.halfGapValue (0 : Fin (N + 2)))
    (T : ReachableFirstValueTransform b.tail)
    (hresidueMore : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableFirstValueTransform b) := by
  rcases reachableTailReplacementData_of_firstValueTransform b T with
    ⟨D, hDReachable⟩
  have hglobal :=
    b.alpha_zero_eq_orderGap_add_tailAlpha_of_tailAlpha_lt_adjacentDefect
      htail hstrict
  have hbinaryOriginal :=
    D.firstBinaryAlpha_eq_of_strict_tail htail hglobal
  have halphas := b.alpha_invariant D.transformed
  have hbinary : D.transformed.firstBinaryAlpha =
      (D.transformed.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
    calc
      D.transformed.firstBinaryAlpha =
          (b.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := hbinaryOriginal
      _ = (D.transformed.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) :=
        congrArg (fun x : ℚ => (x : WithTop ℚ))
          (halphas (0 : Fin (N + 2)))
  have horders := b.order_invariant D.transformed
  have hhalf : D.transformed.halfGapValue (0 : Fin (N + 2)) =
      b.halfGapValue (0 : Fin (N + 2)) := by
    unfold BONG.GoodBONG.halfGapValue BONG.GoodBONG.orderGap
    rw [← horders (0 : Fin (N + 2)).succ,
      ← horders (0 : Fin (N + 2)).castSucc]
  have hstrictTransformed :
      D.transformed.alphaValue (0 : Fin (N + 2)) <
        D.transformed.halfGapValue (0 : Fin (N + 2)) := by
    rw [← halphas (0 : Fin (N + 2)), hhalf]
    exact hstrict
  rcases reachableLemma88_strict_binary_of_largeResidue D.transformed
      hbinary hstrictTransformed hresidueMore with ⟨S⟩
  refine ⟨{
    transform := D.compose_firstValueTransform S.transform
    reachable := ?_
  }⟩
  exact hDReachable.trans S.reachable

/-- In residue degree greater than one, the proof of Beli (2019), Lemma 8.8
uses only adjacent binary transformations.  This is the path-refined
sufficiency induction; the residue-two ternary and quaternary branches never
occur. -/
theorem reachableLemma88_sufficiency_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    {N : Nat} (b : BONG.GoodBONG q L (N + 2))
    (hnotExceptional : ¬b.Beli2019Lemma88Exceptional)
    (hresidueMore : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableFirstValueTransform b) := by
  induction N generalizing V with
  | zero =>
      have hbinary : b.firstBinaryAlpha =
          (b.alphaValue (0 : Fin 1) : WithTop ℚ) := by
        unfold BONG.GoodBONG.firstBinaryAlpha
        exact b.binary_alpha_eq_min_candidates.symm
      by_cases hhalf : b.AttainsHalfGap (0 : Fin 1)
      · have hnotA : ¬b.Beli2019Lemma88ExceptionA := by
          intro hA
          exact hnotExceptional ⟨hhalf, Or.inl hA⟩
        have hrealized : BONG.GoodBONG.IsValuationUnitDefect (K := K)
            (b.alphaValue (0 : Fin 1)) := by
          by_contra hnot
          exact hnotA hnot
        rcases hrealized with ⟨reference, hrefUnit, hrefDefect⟩
        exact reachableLemma88_halfGap_binary_of_largeResidue b
          reference hrefUnit hrefDefect hbinary hhalf hresidueMore
      · have hstrict : b.alphaValue (0 : Fin 1) <
            b.halfGapValue (0 : Fin 1) :=
          lt_of_le_of_ne (b.alphaValue_le_halfGapValue 0) hhalf
        exact reachableLemma88_strict_binary_of_largeResidue b
          hbinary hstrict hresidueMore
  | succ N ih =>
      by_cases hhalf : b.AttainsHalfGap (0 : Fin (N + 2))
      · have hbinary := b.firstBinaryAlpha_eq_alpha_of_halfGap hhalf
        have hnotA : ¬b.Beli2019Lemma88ExceptionA := by
          intro hA
          exact hnotExceptional ⟨hhalf, Or.inl hA⟩
        have hrealized : BONG.GoodBONG.IsValuationUnitDefect (K := K)
            (b.alphaValue (0 : Fin (N + 2))) := by
          by_contra hnot
          exact hnotA hnot
        rcases hrealized with ⟨reference, hrefUnit, hrefDefect⟩
        exact reachableLemma88_halfGap_binary_of_largeResidue b
          reference hrefUnit hrefDefect hbinary hhalf hresidueMore
      · have hstrict : b.alphaValue (0 : Fin (N + 2)) <
            b.halfGapValue (0 : Fin (N + 2)) :=
          lt_of_le_of_ne (b.alphaValue_le_halfGapValue 0) hhalf
        by_cases hle : b.adjacentDefect (0 : Fin (N + 2)) ≤
            (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ)
        · exact reachableLemma88_strict_of_adjacentDefect_le_tailAlpha b
            hle hstrict hresidueMore
        · have htail :
              (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) <
                b.adjacentDefect (0 : Fin (N + 2)) := lt_of_not_ge hle
          have htailStrict :=
            b.tailAlpha_lt_halfGap_of_global_strict htail hstrict
          have htailNotExceptional :
              ¬b.tail.Beli2019Lemma88Exceptional := by
            rintro ⟨htailHalf, _⟩
            exact (ne_of_lt htailStrict) htailHalf
          rcases ih b.tail htailNotExceptional with ⟨T⟩
          exact reachableLemma88_strict_tail_of_tailTransform b htail hstrict
            T hresidueMore

end Beli2009FinalRemarksProof.LargeResidueConnectivity

end Bong

namespace Bong

open Dyadic
open BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Beli2009FinalRemarksProof.LargeResidueConnectivity

/-
/-- Sharp dynamic form of the quaternary braid `0 -> 1 -> 2 -> 1 -> 0`.
The conclusion is exactly the coefficient scaling used in Beli (2019),
Lemma 9.2.  Every hypothesis is a concrete depth or Hilbert condition for
one of the five literal binary edges. -/
theorem reachable_rankFour_fiveStep_scaling_of_dynamic
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 4)
    (mu theta eta epsilon : valuationUnitSubgroup K)
    (hmuAlpha : a.adjacentBinaryAlpha (0 : Fin 3) ≤
      BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ))
    (hmuHilbert : hilbertSymbol K (a.adjacentProduct (0 : Fin 3))
      (mu : Kˣ) = 1)
    (hthetaAlpha : rankFourSecondBinaryAlphaAfterFirstMultiplier
        a (mu : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
    (hthetaHilbert : hilbertSymbol K
      ((mu : Kˣ) * a.adjacentProduct (1 : Fin 3)) (theta : Kˣ) = 1)
    (hetaAlpha : rankFourThirdBinaryAlphaAfterSecondMultiplier
        a (theta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ))
    (hetaHilbert : hilbertSymbol K
      ((theta : Kˣ) * a.adjacentProduct (2 : Fin 3)) (eta : Kˣ) = 1)
    (hkappaAlpha : rankFourSecondBinaryAlphaAfterOuterMultipliers
        a (mu : Kˣ) (eta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)))
    (hkappaHilbert : hilbertSymbol K
      (((mu : Kˣ) * (eta : Kˣ)) * a.adjacentProduct (1 : Fin 3))
      (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)) = 1)
    (hnuAlpha : rankFourFirstBinaryAlphaAfterRightMultiplier
        a (epsilon : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) ((mu : Kˣ)⁻¹))
    (hnuHilbert : hilbertSymbol K
      ((epsilon : Kˣ) * a.adjacentProduct (0 : Fin 3))
      ((mu : Kˣ)⁻¹) = 1) :
    Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i)
      ![a.valueUnit 0,
        (epsilon : Kˣ) * a.valueUnit 1,
        (epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 2,
        (eta : Kˣ) * a.valueUnit 3] := by
  have hmuGroup : valuationUnitClassHom K mu ∈
      beliNormGeneratorGroup K
        (a.valueUnit (1 : Fin 4) / a.valueUnit (0 : Fin 4)) := by
    exact valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (0 : Fin 3) mu hmuAlpha hmuHilbert
  rcases exists_goodBONG_binaryTransformation_exact a (0 : Fin 3)
      mu hmuGroup with ⟨c, hcValues⟩
  have hmuStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => a.valueUnit i) (fun i => c.valueUnit i) :=
    ⟨0, mu, hmuGroup, hcValues⟩
  have hcSecondAdjacent : c.adjacentProduct (1 : Fin 3) =
      (mu : Kˣ) * a.adjacentProduct (1 : Fin 3) := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hcValues (1 : Fin 3).castSucc,
      congrFun hcValues (1 : Fin 3).succ]
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]
  have hcSecondAlpha : c.adjacentBinaryAlpha (1 : Fin 3) =
      rankFourSecondBinaryAlphaAfterFirstMultiplier a (mu : Kˣ) := by
    have horders := a.order_invariant c
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFourSecondBinaryAlphaAfterFirstMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (1 : Fin 3).succ).symm,
      (horders (1 : Fin 3).castSucc).symm, hcSecondAdjacent]
  have hthetaGroup : valuationUnitClassHom K theta ∈
      beliNormGeneratorGroup K
        (c.valueUnit (2 : Fin 4) / c.valueUnit (1 : Fin 4)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      c (1 : Fin 3) theta
    · rw [hcSecondAlpha]
      exact hthetaAlpha
    · rw [hcSecondAdjacent]
      exact hthetaHilbert
  rcases exists_goodBONG_binaryTransformation_exact c (1 : Fin 3)
      theta hthetaGroup with ⟨d, hdValues⟩
  have hthetaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => c.valueUnit i) (fun i => d.valueUnit i) :=
    ⟨1, theta, hthetaGroup, hdValues⟩
  have hdThirdAdjacent : d.adjacentProduct (2 : Fin 3) =
      (theta : Kˣ) * a.adjacentProduct (2 : Fin 3) := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hdValues (2 : Fin 3).castSucc,
      congrFun hdValues (2 : Fin 3).succ,
      congrFun hcValues (2 : Fin 4),
      congrFun hcValues (3 : Fin 4)]
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]
  have hdThirdAlpha : d.adjacentBinaryAlpha (2 : Fin 3) =
      rankFourThirdBinaryAlphaAfterSecondMultiplier a (theta : Kˣ) := by
    have horders := a.order_invariant d
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFourThirdBinaryAlphaAfterSecondMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (2 : Fin 3).succ).symm,
      (horders (2 : Fin 3).castSucc).symm, hdThirdAdjacent]
  have hetaGroup : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K
        (d.valueUnit (3 : Fin 4) / d.valueUnit (2 : Fin 4)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      d (2 : Fin 3) eta
    · rw [hdThirdAlpha]
      exact hetaAlpha
    · rw [hdThirdAdjacent]
      exact hetaHilbert
  rcases exists_goodBONG_binaryTransformation_exact d (2 : Fin 3)
      eta hetaGroup with ⟨e, heValues⟩
  have hetaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => d.valueUnit i) (fun i => e.valueUnit i) :=
    ⟨2, eta, hetaGroup, heValues⟩
  have heSecondAdjacent : e.adjacentProduct (1 : Fin 3) =
      (((mu : Kˣ) * (eta : Kˣ)) * a.adjacentProduct (1 : Fin 3)) *
        (theta : Kˣ) ^ 2 := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun heValues (1 : Fin 3).castSucc,
      congrFun heValues (1 : Fin 3).succ,
      congrFun hdValues (1 : Fin 4),
      congrFun hdValues (2 : Fin 4),
      congrFun hcValues (1 : Fin 4),
      congrFun hcValues (2 : Fin 4)]
    apply Units.ext
    simp [beli2009BinaryTransformAt, pow_two]
    ring
  have heSecondAlpha : e.adjacentBinaryAlpha (1 : Fin 3) =
      rankFourSecondBinaryAlphaAfterOuterMultipliers
        a (mu : Kˣ) (eta : Kˣ) := by
    have horders := a.order_invariant e
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFourSecondBinaryAlphaAfterOuterMultipliers
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (1 : Fin 3).succ).symm,
      (horders (1 : Fin 3).castSucc).symm, heSecondAdjacent,
      BONG.GoodBONG.defectOrder_mul_square]
  let kappa : valuationUnitSubgroup K := epsilon / theta
  have hkappaGroup : valuationUnitClassHom K kappa ∈
      beliNormGeneratorGroup K
        (e.valueUnit (2 : Fin 4) / e.valueUnit (1 : Fin 4)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      e (1 : Fin 3) kappa
    · rw [heSecondAlpha]
      simpa only [kappa] using hkappaAlpha
    · rw [heSecondAdjacent, hilbertSymbol_mul_square_left]
      simpa only [kappa] using hkappaHilbert
  rcases exists_goodBONG_binaryTransformation_exact e (1 : Fin 3)
      kappa hkappaGroup with ⟨f, hfValues⟩
  have hkappaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => e.valueUnit i) (fun i => f.valueUnit i) :=
    ⟨1, kappa, hkappaGroup, hfValues⟩
  have hfFirstAdjacent : f.adjacentProduct (0 : Fin 3) =
      ((epsilon : Kˣ) * a.adjacentProduct (0 : Fin 3)) *
        (mu : Kˣ) ^ 2 := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hfValues (0 : Fin 3).castSucc,
      congrFun hfValues (0 : Fin 3).succ,
      congrFun heValues (0 : Fin 4),
      congrFun heValues (1 : Fin 4),
      congrFun hdValues (0 : Fin 4),
      congrFun hdValues (1 : Fin 4),
      congrFun hcValues (0 : Fin 4),
      congrFun hcValues (1 : Fin 4)]
    change -((mu : Kˣ) * a.valueUnit 0 *
      ((epsilon : Kˣ) * (theta : Kˣ)⁻¹ *
        ((theta : Kˣ) * ((mu : Kˣ) * a.valueUnit 1)))) = _
    apply Units.ext
    simp [pow_two]
    ring
  have hfFirstAlpha : f.adjacentBinaryAlpha (0 : Fin 3) =
      rankFourFirstBinaryAlphaAfterRightMultiplier a (epsilon : Kˣ) := by
    have horders := a.order_invariant f
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFourFirstBinaryAlphaAfterRightMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (0 : Fin 3).succ).symm,
      (horders (0 : Fin 3).castSucc).symm, hfFirstAdjacent,
      BONG.GoodBONG.defectOrder_mul_square]
  let nu : valuationUnitSubgroup K := mu⁻¹
  have hnuGroup : valuationUnitClassHom K nu ∈
      beliNormGeneratorGroup K
        (f.valueUnit (1 : Fin 4) / f.valueUnit (0 : Fin 4)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      f (0 : Fin 3) nu
    · rw [hfFirstAlpha]
      simpa only [nu, Subgroup.coe_inv] using hnuAlpha
    · rw [hfFirstAdjacent, hilbertSymbol_mul_square_left]
      simpa only [nu, Subgroup.coe_inv] using hnuHilbert
  rcases exists_goodBONG_binaryTransformation_exact f (0 : Fin 3)
      nu hnuGroup with ⟨g, hgValues⟩
  have hnuStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => f.valueUnit i) (fun i => g.valueUnit i) :=
    ⟨0, nu, hnuGroup, hgValues⟩
  have hgValuesRaw : (fun i => g.valueUnit i) =
      rankFourBraidFive (fun i => a.valueUnit i)
        (mu : Kˣ) (theta : Kˣ) (eta : Kˣ) (kappa : Kˣ) (nu : Kˣ) := by
    rw [hgValues, hfValues, heValues, hdValues, hcValues]
    rfl
  have hreach : Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => g.valueUnit i) :=
    hmuStep.reachable.trans <| hthetaStep.reachable.trans <|
      hetaStep.reachable.trans <| hkappaStep.reachable.trans hnuStep.reachable
  rw [hgValuesRaw] at hreach
  dsimp only [kappa, nu] at hreach
  rw [binaryTransform_fiveStep_zero_one_two_one_zero
    (K := K) (fun i => a.valueUnit i) mu theta eta epsilon] at hreach
  exact hreach
-/

end Beli2009FinalRemarksProof.LargeResidueConnectivity

end Bong

namespace Bong

open Dyadic
open BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Beli2009FinalRemarksProof.LargeResidueConnectivity

/-! ## Dynamic legality of the quaternary Lemma 9.2 braid -/

/-- The literal second binary alpha after multiplying the first pair by
`mu`.  Only the second adjacent product changes, from `A₁` to `mu*A₁`. -/
noncomputable def rankFourSecondBinaryAlphaAfterFirstMultiplier
    (a : BONG.GoodBONG q L 4) (mu : Kˣ) : WithTop ℚ :=
  min (a.halfGapCandidate (1 : Fin 3))
    (((((a.order (1 : Fin 3).succ -
          a.order (1 : Fin 3).castSucc : Int) : ℚ)) :
        WithTop ℚ) +
      BONG.GoodBONG.defectOrder (K := K)
        (mu * a.adjacentProduct (1 : Fin 3)))

/-- The literal third binary alpha after the first two braid moves.  The
third adjacent product is `theta*A₂`. -/
noncomputable def rankFourThirdBinaryAlphaAfterSecondMultiplier
    (a : BONG.GoodBONG q L 4) (theta : Kˣ) : WithTop ℚ :=
  min (a.halfGapCandidate (2 : Fin 3))
    (((((a.order (2 : Fin 3).succ -
          a.order (2 : Fin 3).castSucc : Int) : ℚ)) :
        WithTop ℚ) +
      BONG.GoodBONG.defectOrder (K := K)
        (theta * a.adjacentProduct (2 : Fin 3)))

/-- The literal second binary alpha after the first three braid moves.
The accumulated square factor `theta^2` is omitted because it does not
change the quadratic defect. -/
noncomputable def rankFourSecondBinaryAlphaAfterOuterMultipliers
    (a : BONG.GoodBONG q L 4) (mu eta : Kˣ) : WithTop ℚ :=
  min (a.halfGapCandidate (1 : Fin 3))
    (((((a.order (1 : Fin 3).succ -
          a.order (1 : Fin 3).castSucc : Int) : ℚ)) :
        WithTop ℚ) +
      BONG.GoodBONG.defectOrder (K := K)
        ((mu * eta) * a.adjacentProduct (1 : Fin 3)))

/-- The literal first binary alpha after the fourth braid move.  The
accumulated square factor `mu^2` is omitted. -/
noncomputable def rankFourFirstBinaryAlphaAfterRightMultiplier
    (a : BONG.GoodBONG q L 4) (epsilon : Kˣ) : WithTop ℚ :=
  min (a.halfGapCandidate (0 : Fin 3))
    (((((a.order (0 : Fin 3).succ -
          a.order (0 : Fin 3).castSucc : Int) : ℚ)) :
        WithTop ℚ) +
      BONG.GoodBONG.defectOrder (K := K)
        (epsilon * a.adjacentProduct (0 : Fin 3)))

/-
/-- Sharp dynamic form of the quaternary braid `0 -> 1 -> 2 -> 1 -> 0`.
The conclusion is exactly the coefficient scaling used in Beli (2019),
Lemma 9.2.  Every hypothesis is a concrete depth or Hilbert condition for
one of the five literal binary edges. -/
theorem reachable_rankFour_fiveStep_scaling_of_dynamic
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 4)
    (mu theta eta epsilon : valuationUnitSubgroup K)
    (hmuAlpha : a.adjacentBinaryAlpha (0 : Fin 3) <=
      BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ))
    (hmuHilbert : hilbertSymbol K (a.adjacentProduct (0 : Fin 3))
      (mu : Kˣ) = 1)
    (hthetaAlpha : rankFourSecondBinaryAlphaAfterFirstMultiplier
        a (mu : Kˣ) <=
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
    (hthetaHilbert : hilbertSymbol K
      ((mu : Kˣ) * a.adjacentProduct (1 : Fin 3)) (theta : Kˣ) = 1)
    (hetaAlpha : rankFourThirdBinaryAlphaAfterSecondMultiplier
        a (theta : Kˣ) <=
      BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ))
    (hetaHilbert : hilbertSymbol K
      ((theta : Kˣ) * a.adjacentProduct (2 : Fin 3)) (eta : Kˣ) = 1)
    (hkappaAlpha : rankFourSecondBinaryAlphaAfterOuterMultipliers
        a (mu : Kˣ) (eta : Kˣ) <=
      BONG.GoodBONG.defectOrder (K := K)
        (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)))
    (hkappaHilbert : hilbertSymbol K
      (((mu : Kˣ) * (eta : Kˣ)) * a.adjacentProduct (1 : Fin 3))
      (((epsilon / theta : valuationUnitSubgroup K) : Kˣ)) = 1)
    (hnuAlpha : rankFourFirstBinaryAlphaAfterRightMultiplier
        a (epsilon : Kˣ) <=
      BONG.GoodBONG.defectOrder (K := K) ((mu : Kˣ)⁻¹))
    (hnuHilbert : hilbertSymbol K
      ((epsilon : Kˣ) * a.adjacentProduct (0 : Fin 3))
      ((mu : Kˣ)⁻¹) = 1) :
    Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i)
      ![a.valueUnit 0,
        (epsilon : Kˣ) * a.valueUnit 1,
        (epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 2,
        (eta : Kˣ) * a.valueUnit 3] := by
  have hmuGroup : valuationUnitClassHom K mu in
      beliNormGeneratorGroup K
        (a.valueUnit (1 : Fin 4) / a.valueUnit (0 : Fin 4)) := by
    exact valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (0 : Fin 3) mu hmuAlpha hmuHilbert
  rcases exists_goodBONG_binaryTransformation_exact a (0 : Fin 3)
      mu hmuGroup with <c, hcValues>
  have hmuStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => a.valueUnit i) (fun i => c.valueUnit i) :=
    <0, mu, hmuGroup, hcValues>
  have hcSecondAdjacent : c.adjacentProduct (1 : Fin 3) =
      (mu : Kˣ) * a.adjacentProduct (1 : Fin 3) := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hcValues (1 : Fin 3).castSucc,
      congrFun hcValues (1 : Fin 3).succ]
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]
  have hcSecondAlpha : c.adjacentBinaryAlpha (1 : Fin 3) =
      rankFourSecondBinaryAlphaAfterFirstMultiplier a (mu : Kˣ) := by
    have horders := a.order_invariant c
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFourSecondBinaryAlphaAfterFirstMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (1 : Fin 3).succ).symm,
      (horders (1 : Fin 3).castSucc).symm, hcSecondAdjacent]
  have hthetaGroup : valuationUnitClassHom K theta in
      beliNormGeneratorGroup K
        (c.valueUnit (2 : Fin 4) / c.valueUnit (1 : Fin 4)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      c (1 : Fin 3) theta
    · rw [hcSecondAlpha]
      exact hthetaAlpha
    · rw [hcSecondAdjacent]
      exact hthetaHilbert
  rcases exists_goodBONG_binaryTransformation_exact c (1 : Fin 3)
      theta hthetaGroup with <d, hdValues>
  have hthetaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => c.valueUnit i) (fun i => d.valueUnit i) :=
    <1, theta, hthetaGroup, hdValues>
  have hdThirdAdjacent : d.adjacentProduct (2 : Fin 3) =
      (theta : Kˣ) * a.adjacentProduct (2 : Fin 3) := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hdValues (2 : Fin 3).castSucc,
      congrFun hdValues (2 : Fin 3).succ,
      congrFun hcValues (2 : Fin 4),
      congrFun hcValues (3 : Fin 4)]
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]
  have hdThirdAlpha : d.adjacentBinaryAlpha (2 : Fin 3) =
      rankFourThirdBinaryAlphaAfterSecondMultiplier a (theta : Kˣ) := by
    have horders := a.order_invariant d
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFourThirdBinaryAlphaAfterSecondMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (2 : Fin 3).succ).symm,
      (horders (2 : Fin 3).castSucc).symm, hdThirdAdjacent]
  have hetaGroup : valuationUnitClassHom K eta in
      beliNormGeneratorGroup K
        (d.valueUnit (3 : Fin 4) / d.valueUnit (2 : Fin 4)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      d (2 : Fin 3) eta
    · rw [hdThirdAlpha]
      exact hetaAlpha
    · rw [hdThirdAdjacent]
      exact hetaHilbert
  rcases exists_goodBONG_binaryTransformation_exact d (2 : Fin 3)
      eta hetaGroup with <e, heValues>
  have hetaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => d.valueUnit i) (fun i => e.valueUnit i) :=
    <2, eta, hetaGroup, heValues>
  have heSecondAdjacent : e.adjacentProduct (1 : Fin 3) =
      (((mu : Kˣ) * (eta : Kˣ)) * a.adjacentProduct (1 : Fin 3)) *
        (theta : Kˣ) ^ 2 := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun heValues (1 : Fin 3).castSucc,
      congrFun heValues (1 : Fin 3).succ,
      congrFun hdValues (1 : Fin 4),
      congrFun hdValues (2 : Fin 4),
      congrFun hcValues (1 : Fin 4),
      congrFun hcValues (2 : Fin 4)]
    apply Units.ext
    simp [beli2009BinaryTransformAt, pow_two]
    ring
  have heSecondAlpha : e.adjacentBinaryAlpha (1 : Fin 3) =
      rankFourSecondBinaryAlphaAfterOuterMultipliers
        a (mu : Kˣ) (eta : Kˣ) := by
    have horders := a.order_invariant e
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFourSecondBinaryAlphaAfterOuterMultipliers
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (1 : Fin 3).succ).symm,
      (horders (1 : Fin 3).castSucc).symm, heSecondAdjacent,
      BONG.GoodBONG.defectOrder_mul_square]
  let kappa : valuationUnitSubgroup K := epsilon / theta
  have hkappaGroup : valuationUnitClassHom K kappa in
      beliNormGeneratorGroup K
        (e.valueUnit (2 : Fin 4) / e.valueUnit (1 : Fin 4)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      e (1 : Fin 3) kappa
    · rw [heSecondAlpha]
      simpa only [kappa] using hkappaAlpha
    · rw [heSecondAdjacent, hilbertSymbol_mul_square_left]
      simpa only [kappa] using hkappaHilbert
  rcases exists_goodBONG_binaryTransformation_exact e (1 : Fin 3)
      kappa hkappaGroup with <f, hfValues>
  have hkappaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => e.valueUnit i) (fun i => f.valueUnit i) :=
    <1, kappa, hkappaGroup, hfValues>
  have hfFirstAdjacent : f.adjacentProduct (0 : Fin 3) =
      ((epsilon : Kˣ) * a.adjacentProduct (0 : Fin 3)) *
        (mu : Kˣ) ^ 2 := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hfValues (0 : Fin 3).castSucc,
      congrFun hfValues (0 : Fin 3).succ,
      congrFun heValues (0 : Fin 4),
      congrFun heValues (1 : Fin 4),
      congrFun hdValues (0 : Fin 4),
      congrFun hdValues (1 : Fin 4),
      congrFun hcValues (0 : Fin 4),
      congrFun hcValues (1 : Fin 4)]
    change -((mu : Kˣ) * a.valueUnit 0 *
      ((epsilon : Kˣ) * (theta : Kˣ)⁻¹ *
        ((theta : Kˣ) * ((mu : Kˣ) * a.valueUnit 1)))) = _
    apply Units.ext
    simp [pow_two]
    ring
  have hfFirstAlpha : f.adjacentBinaryAlpha (0 : Fin 3) =
      rankFourFirstBinaryAlphaAfterRightMultiplier a (epsilon : Kˣ) := by
    have horders := a.order_invariant f
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankFourFirstBinaryAlphaAfterRightMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [(horders (0 : Fin 3).succ).symm,
      (horders (0 : Fin 3).castSucc).symm, hfFirstAdjacent,
      BONG.GoodBONG.defectOrder_mul_square]
  let nu : valuationUnitSubgroup K := mu⁻¹
  have hnuGroup : valuationUnitClassHom K nu in
      beliNormGeneratorGroup K
        (f.valueUnit (1 : Fin 4) / f.valueUnit (0 : Fin 4)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      f (0 : Fin 3) nu
    · rw [hfFirstAlpha]
      simpa only [nu, Subgroup.coe_inv] using hnuAlpha
    · rw [hfFirstAdjacent, hilbertSymbol_mul_square_left]
      simpa only [nu, Subgroup.coe_inv] using hnuHilbert
  rcases exists_goodBONG_binaryTransformation_exact f (0 : Fin 3)
      nu hnuGroup with <g, hgValues>
  have hnuStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => f.valueUnit i) (fun i => g.valueUnit i) :=
    <0, nu, hnuGroup, hgValues>
  have hgValuesRaw : (fun i => g.valueUnit i) =
      rankFourBraidFive (fun i => a.valueUnit i)
        (mu : Kˣ) (theta : Kˣ) (eta : Kˣ) (kappa : Kˣ) (nu : Kˣ) := by
    rw [hgValues, hfValues, heValues, hdValues, hcValues]
    rfl
  have hreach : Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => g.valueUnit i) :=
    hmuStep.reachable.trans <| hthetaStep.reachable.trans <|
      hetaStep.reachable.trans <| hkappaStep.reachable.trans hnuStep.reachable
  rw [hgValuesRaw]
  simpa only [kappa, nu] using
    (binaryTransform_fiveStep_zero_one_two_one_zero
      (K := K) (fun i => a.valueUnit i) mu theta eta epsilon) ▸ hreach
-/

end Beli2009FinalRemarksProof.LargeResidueConnectivity

end Bong

namespace Bong

open Dyadic
open BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Beli2009FinalRemarksProof.LargeResidueConnectivity

/-! ## The quaternary braid used in the path-refined Lemma 9.2 -/

/-- First vertex of the adjacent-edge braid `0 -> 1 -> 2 -> 1 -> 0`. -/
def rankFourBraidOne (a : Fin 4 -> Kˣ) (mu : Kˣ) : Fin 4 -> Kˣ :=
  beli2009BinaryTransformAt a (0 : Fin 3) mu

/-- Second vertex of the adjacent-edge braid `0 -> 1 -> 2 -> 1 -> 0`. -/
def rankFourBraidTwo (a : Fin 4 -> Kˣ) (mu theta : Kˣ) : Fin 4 -> Kˣ :=
  beli2009BinaryTransformAt (rankFourBraidOne a mu) (1 : Fin 3) theta

/-- Third vertex of the adjacent-edge braid `0 -> 1 -> 2 -> 1 -> 0`. -/
def rankFourBraidThree (a : Fin 4 -> Kˣ) (mu theta eta : Kˣ) :
    Fin 4 -> Kˣ :=
  beli2009BinaryTransformAt (rankFourBraidTwo a mu theta) (2 : Fin 3) eta

/-- Fourth vertex of the adjacent-edge braid `0 -> 1 -> 2 -> 1 -> 0`. -/
def rankFourBraidFour
    (a : Fin 4 -> Kˣ) (mu theta eta kappa : Kˣ) : Fin 4 -> Kˣ :=
  beli2009BinaryTransformAt (rankFourBraidThree a mu theta eta)
    (1 : Fin 3) kappa

/-- Endpoint of the adjacent-edge braid `0 -> 1 -> 2 -> 1 -> 0`. -/
def rankFourBraidFive
    (a : Fin 4 -> Kˣ) (mu theta eta kappa nu : Kˣ) : Fin 4 -> Kˣ :=
  beli2009BinaryTransformAt (rankFourBraidFour a mu theta eta kappa)
    (0 : Fin 3) nu

/-- The five dynamic norm-group memberships are precisely the legality
conditions for the quaternary braid `0 -> 1 -> 2 -> 1 -> 0`. -/
theorem reachable_fiveStep_zero_one_two_one_zero
    (a : Fin 4 -> Kˣ)
    (mu theta eta kappa nu : valuationUnitSubgroup K)
    (hmu : valuationUnitClassHom K mu ∈
      beliNormGeneratorGroup K (a (1 : Fin 4) / a (0 : Fin 4)))
    (htheta : valuationUnitClassHom K theta ∈
      beliNormGeneratorGroup K
        (rankFourBraidOne a (mu : Kˣ) (2 : Fin 4) /
          rankFourBraidOne a (mu : Kˣ) (1 : Fin 4)))
    (heta : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K
        (rankFourBraidTwo a (mu : Kˣ) (theta : Kˣ) (3 : Fin 4) /
          rankFourBraidTwo a (mu : Kˣ) (theta : Kˣ) (2 : Fin 4)))
    (hkappa : valuationUnitClassHom K kappa ∈
      beliNormGeneratorGroup K
        (rankFourBraidThree a (mu : Kˣ) (theta : Kˣ) (eta : Kˣ)
            (2 : Fin 4) /
          rankFourBraidThree a (mu : Kˣ) (theta : Kˣ) (eta : Kˣ)
            (1 : Fin 4)))
    (hnu : valuationUnitClassHom K nu ∈
      beliNormGeneratorGroup K
        (rankFourBraidFour a (mu : Kˣ) (theta : Kˣ) (eta : Kˣ)
            (kappa : Kˣ) (1 : Fin 4) /
          rankFourBraidFour a (mu : Kˣ) (theta : Kˣ) (eta : Kˣ)
            (kappa : Kˣ) (0 : Fin 4))) :
    Beli2009BinaryReachable (K := K) a
      (rankFourBraidFive a (mu : Kˣ) (theta : Kˣ) (eta : Kˣ)
        (kappa : Kˣ) (nu : Kˣ)) := by
  have hzero : IsBeli2009BinaryTransformation (K := K) a
      (rankFourBraidOne a (mu : Kˣ)) := ⟨0, mu, hmu, rfl⟩
  have hone : IsBeli2009BinaryTransformation (K := K)
      (rankFourBraidOne a (mu : Kˣ))
      (rankFourBraidTwo a (mu : Kˣ) (theta : Kˣ)) :=
    ⟨1, theta, htheta, rfl⟩
  have htwo : IsBeli2009BinaryTransformation (K := K)
      (rankFourBraidTwo a (mu : Kˣ) (theta : Kˣ))
      (rankFourBraidThree a (mu : Kˣ) (theta : Kˣ) (eta : Kˣ)) :=
    ⟨2, eta, heta, rfl⟩
  have hone' : IsBeli2009BinaryTransformation (K := K)
      (rankFourBraidThree a (mu : Kˣ) (theta : Kˣ) (eta : Kˣ))
      (rankFourBraidFour a (mu : Kˣ) (theta : Kˣ) (eta : Kˣ)
        (kappa : Kˣ)) := ⟨1, kappa, hkappa, rfl⟩
  have hzero' : IsBeli2009BinaryTransformation (K := K)
      (rankFourBraidFour a (mu : Kˣ) (theta : Kˣ) (eta : Kˣ)
        (kappa : Kˣ))
      (rankFourBraidFive a (mu : Kˣ) (theta : Kˣ) (eta : Kˣ)
        (kappa : Kˣ) (nu : Kˣ)) := ⟨0, nu, hnu, rfl⟩
  exact hzero.reachable.trans <|
    hone.reachable.trans <|
      htwo.reachable.trans <|
        hone'.reachable.trans hzero'.reachable

/-- With `kappa = epsilon / theta` and `nu = mu⁻¹`, the quaternary
braid fixes the first coefficient and realizes exactly the scaling pattern
used in Beli (2019), Lemma 9.2. -/
theorem binaryTransform_fiveStep_zero_one_two_one_zero
    (a : Fin 4 -> Kˣ)
    (mu theta eta epsilon : valuationUnitSubgroup K) :
    rankFourBraidFive a (mu : Kˣ) (theta : Kˣ) (eta : Kˣ)
        (((epsilon / theta : valuationUnitSubgroup K) : Kˣ))
        (((mu : valuationUnitSubgroup K)⁻¹ : Kˣ)) =
      ![a 0, (epsilon : Kˣ) * a 1,
        (epsilon : Kˣ) * (eta : Kˣ) * a 2,
        (eta : Kˣ) * a 3] := by
  have hOne :
      (mu : Kˣ)⁻¹ * ((epsilon : Kˣ) *
        ((mu : Kˣ) * a 1)) =
        (epsilon : Kˣ) * a 1 := by
    calc
      _ = ((mu : Kˣ) * (mu : Kˣ)⁻¹) *
          ((epsilon : Kˣ) * a 1) := by ac_rfl
      _ = (epsilon : Kˣ) * a 1 := by simp
  have hTwo :
      (epsilon : Kˣ) * (theta : Kˣ)⁻¹ *
        ((eta : Kˣ) * ((theta : Kˣ) * a 2)) =
        (epsilon : Kˣ) * (eta : Kˣ) * a 2 := by
    calc
      _ = ((theta : Kˣ) * (theta : Kˣ)⁻¹) *
          ((epsilon : Kˣ) * (eta : Kˣ) * a 2) := by ac_rfl
      _ = (epsilon : Kˣ) * (eta : Kˣ) * a 2 := by simp
  funext i
  fin_cases i
  · simp [rankFourBraidFive, rankFourBraidFour, rankFourBraidThree,
      rankFourBraidTwo, rankFourBraidOne, beli2009BinaryTransformAt,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  · simpa [rankFourBraidFive, rankFourBraidFour, rankFourBraidThree,
      rankFourBraidTwo, rankFourBraidOne, beli2009BinaryTransformAt,
      div_eq_mul_inv] using hOne
  · simpa [rankFourBraidFive, rankFourBraidFour, rankFourBraidThree,
      rankFourBraidTwo, rankFourBraidOne, beli2009BinaryTransformAt,
      div_eq_mul_inv] using hTwo
  · simp [rankFourBraidFive, rankFourBraidFour, rankFourBraidThree,
      rankFourBraidTwo, rankFourBraidOne, beli2009BinaryTransformAt,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

end Beli2009FinalRemarksProof.LargeResidueConnectivity

end Bong

namespace Bong

open Dyadic
open BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Beli2009FinalRemarksProof.LargeResidueConnectivity

/-- A legal binary coefficient rescaling does not change any coefficient
order.  This rank-free form is used in the Property-B invariance proof. -/
theorem order_eq_of_values_eq_firstBinaryTransform
    {N : Nat} (a c : BONG.GoodBONG q L (N + 2))
    (eta : valuationUnitSubgroup K)
    (hvalues : (fun j => c.valueUnit j) =
      beli2009BinaryTransformAt (fun j => a.valueUnit j)
        (0 : Fin (N + 1)) (eta : Kˣ)) :
  ∀ j, c.order j = a.order j := by
  intro j
  change ordUnit K (c.valueUnit j) = ordUnit K (a.valueUnit j)
  rw [congrFun hvalues j]
  have hetaOrder : ordUnit K (eta : Kˣ) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K (eta : Kˣ)).1 eta.property
  by_cases hj0 : j = (0 : Fin (N + 2))
  · subst j
    change ordUnit K ((eta : Kˣ) * a.valueUnit 0) =
      ordUnit K (a.valueUnit 0)
    rw [ordUnit_mul, hetaOrder, zero_add]
  by_cases hj1 : j = (1 : Fin (N + 2))
  · subst j
    change ordUnit K ((eta : Kˣ) * a.valueUnit 1) =
      ordUnit K (a.valueUnit 1)
    rw [ordUnit_mul, hetaOrder, zero_add]
  rw [beli2009BinaryTransformAt_of_ne _ _ _ _
    (by simpa using hj0) (by simpa using hj1)]

theorem normalizedValue_zero_eq_of_values_eq_firstBinaryTransform
    {N : Nat} (a c : BONG.GoodBONG q L (N + 2))
    (eta : valuationUnitSubgroup K)
    (hvalues : (fun j => c.valueUnit j) =
      beli2009BinaryTransformAt (fun j => a.valueUnit j)
        (0 : Fin (N + 1)) (eta : Kˣ)) :
    c.toBONG.normalizedValue (0 : Fin (N + 2)) =
      (eta : Kˣ) * a.toBONG.normalizedValue (0 : Fin (N + 2)) := by
  change (fun j => c.toBONG.valueUnit j) =
    beli2009BinaryTransformAt (fun j => a.toBONG.valueUnit j)
      (0 : Fin (N + 1)) (eta : Kˣ) at hvalues
  unfold BONG.normalizedValue
  have horder : c.toBONG.order (0 : Fin (N + 2)) =
      a.toBONG.order (0 : Fin (N + 2)) :=
    order_eq_of_values_eq_firstBinaryTransform a c eta hvalues 0
  rw [congrFun hvalues (0 : Fin (N + 2)), horder]
  change ((eta : Kˣ) * a.valueUnit 0) *
      uniformizerUnit K ^ (-a.order 0) =
    (eta : Kˣ) *
      (a.valueUnit 0 * uniformizerUnit K ^ (-a.order 0))
  ac_rfl

theorem normalizedValue_one_eq_of_values_eq_firstBinaryTransform
    {N : Nat} (a c : BONG.GoodBONG q L (N + 2))
    (eta : valuationUnitSubgroup K)
    (hvalues : (fun j => c.valueUnit j) =
      beli2009BinaryTransformAt (fun j => a.valueUnit j)
        (0 : Fin (N + 1)) (eta : Kˣ)) :
    c.toBONG.normalizedValue (1 : Fin (N + 2)) =
      (eta : Kˣ) * a.toBONG.normalizedValue (1 : Fin (N + 2)) := by
  change (fun j => c.toBONG.valueUnit j) =
    beli2009BinaryTransformAt (fun j => a.toBONG.valueUnit j)
      (0 : Fin (N + 1)) (eta : Kˣ) at hvalues
  unfold BONG.normalizedValue
  have horder : c.toBONG.order (1 : Fin (N + 2)) =
      a.toBONG.order (1 : Fin (N + 2)) :=
    order_eq_of_values_eq_firstBinaryTransform a c eta hvalues 1
  rw [congrFun hvalues (1 : Fin (N + 2)), horder]
  change ((eta : Kˣ) * a.valueUnit 1) *
      uniformizerUnit K ^ (-a.order 1) =
    (eta : Kˣ) *
      (a.valueUnit 1 * uniformizerUnit K ^ (-a.order 1))
  ac_rfl

theorem normalizedValue_eq_of_values_eq_firstBinaryTransform_of_two_le
    {N : Nat} (a c : BONG.GoodBONG q L (N + 2))
    (eta : valuationUnitSubgroup K)
    (hvalues : (fun j => c.valueUnit j) =
      beli2009BinaryTransformAt (fun j => a.valueUnit j)
        (0 : Fin (N + 1)) (eta : Kˣ))
    (j : Fin (N + 2)) (hj : 2 ≤ j.1) :
    c.toBONG.normalizedValue j = a.toBONG.normalizedValue j := by
  change (fun j => c.toBONG.valueUnit j) =
    beli2009BinaryTransformAt (fun j => a.toBONG.valueUnit j)
      (0 : Fin (N + 1)) (eta : Kˣ) at hvalues
  unfold BONG.normalizedValue
  have horder : c.toBONG.order j = a.toBONG.order j :=
    order_eq_of_values_eq_firstBinaryTransform a c eta hvalues j
  rw [congrFun hvalues j, horder,
    beli2009BinaryTransformAt_of_ne]
  · intro heq
    subst j
    simp at hj
  · intro heq
    subst j
    simp at hj

theorem normalizedAdjacentDefectOrder_zero_eq_of_firstBinaryTransform
    {N : Nat} (a c : BONG.GoodBONG q L (N + 3))
    (eta : valuationUnitSubgroup K)
    (hvalues : (fun j => c.valueUnit j) =
      beli2009BinaryTransformAt (fun j => a.valueUnit j)
        (0 : Fin (N + 2)) (eta : Kˣ)) :
    c.toBONG.normalizedAdjacentDefectOrder (0 : Fin (N + 2)) =
      a.toBONG.normalizedAdjacentDefectOrder (0 : Fin (N + 2)) := by
  unfold BONG.normalizedAdjacentDefectOrder
  congr 1
  have hzero :=
    normalizedValue_zero_eq_of_values_eq_firstBinaryTransform a c eta hvalues
  have hone :=
    normalizedValue_one_eq_of_values_eq_firstBinaryTransform a c eta hvalues
  unfold BONG.normalizedAdjacentProduct
  have hcastZero :
      (Fin.castSucc (0 : Fin (N + 2)) : Fin (N + 3)) = 0 := rfl
  have hsuccZero :
      (Fin.succ (0 : Fin (N + 2)) : Fin (N + 3)) = 1 := rfl
  rw [hcastZero, hsuccZero, hzero, hone]
  have hproduct :
      -((eta : Kˣ) * a.toBONG.normalizedValue 0 *
          ((eta : Kˣ) * a.toBONG.normalizedValue 1)) =
        (-(a.toBONG.normalizedValue 0 * a.toBONG.normalizedValue 1)) *
          (eta : Kˣ) ^ 2 := by
    simp only [pow_two]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    ring
  rw [hproduct, quadraticDefect_mul_square]

theorem normalizedAdjacentDefectOrder_eq_of_firstBinaryTransform_of_two_le
    {N : Nat} (a c : BONG.GoodBONG q L (N + 3))
    (eta : valuationUnitSubgroup K)
    (hvalues : (fun j => c.valueUnit j) =
      beli2009BinaryTransformAt (fun j => a.valueUnit j)
        (0 : Fin (N + 2)) (eta : Kˣ))
    (i : Fin (N + 2)) (hi : 2 ≤ i.1) :
    c.toBONG.normalizedAdjacentDefectOrder i =
      a.toBONG.normalizedAdjacentDefectOrder i := by
  unfold BONG.normalizedAdjacentDefectOrder
  congr 1
  unfold BONG.normalizedAdjacentProduct
  have hiSucc : 2 ≤ (i.succ : Fin (N + 3)).1 := by
    simp only [Fin.val_succ]
    omega
  rw [normalizedValue_eq_of_values_eq_firstBinaryTransform_of_two_le
      a c eta hvalues i.castSucc hi,
    normalizedValue_eq_of_values_eq_firstBinaryTransform_of_two_le
      a c eta hvalues i.succ hiSucc]

theorem hasPropertyA_of_firstBinaryTransform
    {N : Nat} (a c : BONG.GoodBONG q L (N + 3))
    (eta : valuationUnitSubgroup K)
    (hvalues : (fun j => c.valueUnit j) =
      beli2009BinaryTransformAt (fun j => a.valueUnit j)
        (0 : Fin (N + 2)) (eta : Kˣ))
    (hA : a.toBONG.HasPropertyA) :
    c.toBONG.HasPropertyA := by
  intro i hi
  have hleft := order_eq_of_values_eq_firstBinaryTransform
    a c eta hvalues i
  have hright := order_eq_of_values_eq_firstBinaryTransform
    a c eta hvalues (⟨i.1 + 2, hi⟩ : Fin (N + 3))
  change c.order i < c.order ⟨i.1 + 2, hi⟩
  rw [hleft, hright]
  exact hA i hi

theorem normalizedAdjacentProduct_one_eq_of_firstBinaryTransform
    {N : Nat} (a c : BONG.GoodBONG q L (N + 3))
    (eta : valuationUnitSubgroup K)
    (hvalues : (fun j => c.valueUnit j) =
      beli2009BinaryTransformAt (fun j => a.valueUnit j)
        (0 : Fin (N + 2)) (eta : Kˣ)) :
    c.toBONG.normalizedAdjacentProduct (1 : Fin (N + 2)) =
      (eta : Kˣ) *
        a.toBONG.normalizedAdjacentProduct (1 : Fin (N + 2)) := by
  let two : Fin (N + 3) := ⟨2, by omega⟩
  have hone :=
    normalizedValue_one_eq_of_values_eq_firstBinaryTransform a c eta hvalues
  have htwo :=
    normalizedValue_eq_of_values_eq_firstBinaryTransform_of_two_le
      a c eta hvalues two (by simp [two])
  unfold BONG.normalizedAdjacentProduct
  have hcastOne :
      (Fin.castSucc (1 : Fin (N + 2)) : Fin (N + 3)) = 1 := rfl
  have hsuccOne :
      (Fin.succ (1 : Fin (N + 2)) : Fin (N + 3)) = two := by
    apply Fin.ext
    simp [two]
  rw [hcastOne, hsuccOne, hone, htwo]
  apply Units.ext
  simp only [Units.val_neg, Units.val_mul]
  ring

theorem min_defectOrder_le_normalizedAdjacentDefectOrder_one
    {N : Nat} (a c : BONG.GoodBONG q L (N + 3))
    (eta : valuationUnitSubgroup K)
    (hvalues : (fun j => c.valueUnit j) =
      beli2009BinaryTransformAt (fun j => a.valueUnit j)
        (0 : Fin (N + 2)) (eta : Kˣ)) :
    min (BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ))
        (a.toBONG.normalizedAdjacentDefectOrder (1 : Fin (N + 2))) ≤
      c.toBONG.normalizedAdjacentDefectOrder (1 : Fin (N + 2)) := by
  have hproduct :=
    normalizedAdjacentProduct_one_eq_of_firstBinaryTransform a c eta hvalues
  unfold BONG.normalizedAdjacentDefectOrder
  rw [hproduct]
  exact BONG.GoodBONG.defectOrder_mul_ge_min (K := K)
    (eta : Kˣ) (a.toBONG.normalizedAdjacentProduct (1 : Fin (N + 2)))

theorem propertyBTrigger_zero_iff_of_firstBinaryTransform
    {N : Nat} (a c : BONG.GoodBONG q L (N + 3))
    (eta : valuationUnitSubgroup K)
    (hvalues : (fun j => c.valueUnit j) =
      beli2009BinaryTransformAt (fun j => a.valueUnit j)
        (0 : Fin (N + 2)) (eta : Kˣ)) :
    c.toBONG.propertyBTrigger (0 : Fin (N + 2)) ↔
      a.toBONG.propertyBTrigger (0 : Fin (N + 2)) := by
  have hleft := order_eq_of_values_eq_firstBinaryTransform
    a c eta hvalues (0 : Fin (N + 3))
  have hright := order_eq_of_values_eq_firstBinaryTransform
    a c eta hvalues (1 : Fin (N + 3))
  have hdefect :=
    normalizedAdjacentDefectOrder_zero_eq_of_firstBinaryTransform
      a c eta hvalues
  unfold BONG.propertyBTrigger
  change
    let gap : Int := c.order 1 - c.order 0
    (gap ≤ 2 * (ramificationIndex K : Int) + 1 ∧ Odd gap) ∨
      (Even gap ∧
        c.toBONG.normalizedAdjacentDefectOrder 0 ≤
          ((((ramificationIndex K : ℚ) - (gap : ℚ) / 2) : ℚ) : WithTop ℚ))
    ↔
    let gap : Int := a.order 1 - a.order 0
    (gap ≤ 2 * (ramificationIndex K : Int) + 1 ∧ Odd gap) ∨
      (Even gap ∧
        a.toBONG.normalizedAdjacentDefectOrder 0 ≤
          ((((ramificationIndex K : ℚ) - (gap : ℚ) / 2) : ℚ) : WithTop ℚ))
  rw [hleft, hright, hdefect]

theorem propertyBTrigger_iff_of_firstBinaryTransform_of_two_le
    {N : Nat} (a c : BONG.GoodBONG q L (N + 3))
    (eta : valuationUnitSubgroup K)
    (hvalues : (fun j => c.valueUnit j) =
      beli2009BinaryTransformAt (fun j => a.valueUnit j)
        (0 : Fin (N + 2)) (eta : Kˣ))
    (i : Fin (N + 2)) (hi : 2 ≤ i.1) :
    c.toBONG.propertyBTrigger i ↔ a.toBONG.propertyBTrigger i := by
  have hleft := order_eq_of_values_eq_firstBinaryTransform
    a c eta hvalues i.castSucc
  have hright := order_eq_of_values_eq_firstBinaryTransform
    a c eta hvalues i.succ
  change c.toBONG.order i.castSucc = a.toBONG.order i.castSucc at hleft
  change c.toBONG.order i.succ = a.toBONG.order i.succ at hright
  have hdefect :=
    normalizedAdjacentDefectOrder_eq_of_firstBinaryTransform_of_two_le
      a c eta hvalues i hi
  unfold BONG.propertyBTrigger
  rw [hleft, hright, hdefect]

theorem natCast_le_defectOrder_of_natCast_le_quadraticDefect
    (x : Kˣ) (m : Nat)
    (h : (m : ℕ∞) ≤ quadraticDefect K x) :
    (((m : Nat) : ℚ) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) x := by
  by_cases htop : quadraticDefect K x = ⊤
  · unfold BONG.GoodBONG.defectOrder
    rw [htop]
    change (((m : Nat) : ℚ) : WithTop ℚ) ≤ ⊤
    exact le_top
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
    have hnat : m ≤ d := by
      rw [← hd] at h
      exact WithTop.coe_le_coe.mp h
    unfold BONG.GoodBONG.defectOrder
    rw [← hd]
    change (((m : Nat) : ℚ) : WithTop ℚ) ≤ ((d : ℚ) : WithTop ℚ)
    exact_mod_cast hnat

theorem normalizedAdjacentDefectOrder_nonneg
    {N : Nat} (b : BONG.GoodBONG q L (N + 2))
    (i : Fin (N + 1)) :
    (0 : WithTop ℚ) ≤ b.toBONG.normalizedAdjacentDefectOrder i := by
  change (0 : WithTop ℚ) ≤ BONG.GoodBONG.defectOrder (K := K)
    (b.toBONG.normalizedAdjacentProduct i)
  exact BONG.GoodBONG.defectOrder_nonneg (K := K)
    (b.toBONG.normalizedAdjacentProduct i)

theorem isSquare_of_valuationUnitClassHom_eq_one
    (eta : valuationUnitSubgroup K)
    (h : valuationUnitClassHom K eta = 1) :
    IsSquare (eta : Kˣ) := by
  have hetaSquare : eta ∈ Subgroup.square (valuationUnitSubgroup K) :=
    (QuotientGroup.eq_one_iff eta).1 h
  change IsSquare eta at hetaSquare
  rcases hetaSquare with ⟨s, hs⟩
  refine ⟨(s : Kˣ), ?_⟩
  exact congrArg ((↑) : valuationUnitSubgroup K → Kˣ) hs

/-- The only adjacent trigger that can change under a first binary move is
the next one.  Membership of the multiplier in `g(a₁/a₀)` prevents a new
low-defect trigger from appearing there.  This is the local calculation in
the proof of Beli's thesis Lemma 2.2.10. -/
theorem propertyBTrigger_one_of_firstBinaryTransform
    {N : Nat} (a c : BONG.GoodBONG q L (N + 3))
    (eta : valuationUnitSubgroup K)
    (heta : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K (a.valueUnit 1 / a.valueUnit 0))
    (hvalues : (fun j => c.valueUnit j) =
      beli2009BinaryTransformAt (fun j => a.valueUnit j)
        (0 : Fin (N + 2)) (eta : Kˣ))
    (hB : a.toBONG.HasPropertyB)
    (hc : c.toBONG.propertyBTrigger (1 : Fin (N + 2))) :
    a.toBONG.propertyBTrigger (1 : Fin (N + 2)) := by
  let p0 : Fin (N + 2) := ⟨0, by omega⟩
  let p1 : Fin (N + 2) := ⟨1, by omega⟩
  let v0 : Fin (N + 3) := ⟨0, by omega⟩
  let v1 : Fin (N + 3) := ⟨1, by omega⟩
  let v2 : Fin (N + 3) := ⟨2, by omega⟩
  have hp0 : p0 = (0 : Fin (N + 2)) := by ext; simp [p0]
  have hp1 : p1 = (1 : Fin (N + 2)) := by ext; simp [p1]
  have hv0 : v0 = (0 : Fin (N + 3)) := by ext; simp [v0]
  have hv1 : v1 = (1 : Fin (N + 3)) := by ext; simp [v1]
  have hp0cast : p0.castSucc = v0 := by ext; simp [p0, v0]
  have hp0succ : p0.succ = v1 := by ext; simp [p0, v1]
  have hp1cast : p1.castSucc = v1 := by ext; simp [p1, v1]
  have hp1succ : p1.succ = v2 := by ext; simp [p1, v2]
  have horders : ∀ j, c.toBONG.order j = a.toBONG.order j := by
    intro j
    exact order_eq_of_values_eq_firstBinaryTransform a c eta hvalues j
  let gap0 : Int := a.toBONG.order v1 - a.toBONG.order v0
  let gap1 : Int := a.toBONG.order v2 - a.toBONG.order v1
  let threshold1 : WithTop ℚ :=
    ((((ramificationIndex K : ℚ) - (gap1 : ℚ) / 2) : ℚ) : WithTop ℚ)
  have hcAtP1 : c.toBONG.propertyBTrigger p1 := by
    simpa only [hp1] using hc
  have hcCases :
      (gap1 ≤ 2 * (ramificationIndex K : Int) + 1 ∧ Odd gap1) ∨
        (Even gap1 ∧
          c.toBONG.normalizedAdjacentDefectOrder p1 ≤ threshold1) := by
    unfold BONG.propertyBTrigger at hcAtP1
    dsimp only at hcAtP1
    rw [hp1cast, hp1succ, horders v1, horders v2] at hcAtP1
    simpa only [gap1, threshold1] using hcAtP1
  by_contra hnotOne
  have hnotOne' : ¬a.toBONG.propertyBTrigger p1 := by
    simpa only [hp1] using hnotOne
  rcases hcCases with hcOdd | ⟨heven1, hcLow⟩
  · apply hnotOne'
    unfold BONG.propertyBTrigger
    dsimp only
    rw [hp1cast, hp1succ]
    exact Or.inl (by simpa only [gap1] using hcOdd)
  have hnonnegC :
      (0 : WithTop ℚ) ≤
        c.toBONG.normalizedAdjacentDefectOrder p1 :=
    normalizedAdjacentDefectOrder_nonneg c p1
  have hthresholdNonneg : (0 : WithTop ℚ) ≤ threshold1 :=
    hnonnegC.trans hcLow
  have hthresholdNonnegQ :
      (0 : ℚ) ≤ (ramificationIndex K : ℚ) - (gap1 : ℚ) / 2 := by
    change ((0 : ℚ) : WithTop ℚ) ≤
      ((((ramificationIndex K : ℚ) - (gap1 : ℚ) / 2) : ℚ) : WithTop ℚ)
      at hthresholdNonneg
    exact_mod_cast hthresholdNonneg
  have hgap1Upper : gap1 ≤ 2 * (ramificationIndex K : Int) := by
    have hq : (gap1 : ℚ) ≤ 2 * (ramificationIndex K : ℚ) := by
      linarith
    exact_mod_cast hq
  have hnotCases1 :=
    a.toBONG.not_propertyBTrigger_iff_large_or_even_high p1 hnotOne'
  have hhigh1 : threshold1 <
      a.toBONG.normalizedAdjacentDefectOrder p1 := by
    rcases hnotCases1 with hlarge1 | ⟨_heven1', _hupper1, hhigh1⟩
    · rw [hp1cast, hp1succ] at hlarge1
      change 2 * (ramificationIndex K : Int) + 1 < gap1 at hlarge1
      omega
    · simpa only [hp1cast, hp1succ, gap1, threshold1] using hhigh1
  have hnotZero : ¬a.toBONG.propertyBTrigger p0 := by
    intro hzeroTrigger
    have hright := (hB.2 p0 hzeroTrigger).2 v2 (by simp [p0, v2])
    rw [hp0succ] at hright
    change 2 * (ramificationIndex K : Int) + 1 ≤
      a.toBONG.order v2 - a.toBONG.order v1 at hright
    change 2 * (ramificationIndex K : Int) + 1 ≤ gap1 at hright
    omega
  have hnotCases0 :=
    a.toBONG.not_propertyBTrigger_iff_large_or_even_high p0 hnotZero
  let parameter : Kˣ := a.valueUnit 1 / a.valueUnit 0
  change valuationUnitClassHom K eta ∈
    beliNormGeneratorGroup K parameter at heta
  have hparameterEq : parameter =
      a.toBONG.adjacentParameter (0 : Fin (N + 3)) (by simp) := by
    unfold parameter BONG.GoodBONG.valueUnit BONG.adjacentParameter
    congr 2
  have hparameterOrder : ordUnit K parameter = gap0 := by
    rw [hparameterEq]
    have horder := a.toBONG.ordUnit_adjacentParameter_zero
    calc
      ordUnit K (a.toBONG.adjacentParameter 0 (by simp)) =
          a.toBONG.order 1 - a.toBONG.order 0 := horder
      _ = gap0 := by
        dsimp only [gap0]
        rw [hv0, hv1]
  rcases hnotCases0 with hlarge0 | ⟨heven0, hupper0, hhigh0⟩
  · rw [hp0cast, hp0succ] at hlarge0
    change 2 * (ramificationIndex K : Int) + 1 < gap0 at hlarge0
    have hparameterLarge :
        2 * (ramificationIndex K : Int) < ordUnit K parameter := by
      rw [hparameterOrder]
      omega
    rw [beliNormGeneratorGroup_of_two_e_lt K parameter hparameterLarge] at heta
    have hetaOne : valuationUnitClassHom K eta = 1 :=
      Subgroup.mem_bot.mp heta
    have hetaSquare : IsSquare (eta : Kˣ) :=
      isSquare_of_valuationUnitClassHom_eq_one eta hetaOne
    rcases hetaSquare with ⟨s, hs⟩
    have hsPow : (eta : Kˣ) = s ^ 2 := by
      simpa only [pow_two] using hs
    have hproduct :=
      normalizedAdjacentProduct_one_eq_of_firstBinaryTransform a c eta hvalues
    have hdefectEq :
        c.toBONG.normalizedAdjacentDefectOrder p1 =
          a.toBONG.normalizedAdjacentDefectOrder p1 := by
      rw [hp1]
      unfold BONG.normalizedAdjacentDefectOrder
      rw [hproduct, hsPow]
      have hcomm : s ^ 2 * a.toBONG.normalizedAdjacentProduct 1 =
          a.toBONG.normalizedAdjacentProduct 1 * s ^ 2 := mul_comm _ _
      rw [hcomm, quadraticDefect_mul_square]
    exact (not_le_of_gt hhigh1) (hdefectEq ▸ hcLow)
  · rw [hp0cast, hp0succ] at heven0 hupper0 hhigh0
    change Even gap0 at heven0
    change gap0 ≤ 2 * (ramificationIndex K : Int) at hupper0
    change
      threshold1 < a.toBONG.normalizedAdjacentDefectOrder p1 at hhigh1
    have hnotLargeParameter :
        ¬2 * (ramificationIndex K : Int) < ordUnit K parameter := by
      rw [hparameterOrder]
      omega
    have hevenLemma : Even a.toBONG.lemma62Gap := by
      unfold BONG.lemma62Gap
      rw [← hv0, ← hv1]
      exact heven0
    have hupperLemma :
        a.toBONG.lemma62Gap ≤ 2 * (ramificationIndex K : Int) := by
      unfold BONG.lemma62Gap
      rw [← hv0, ← hv1]
      exact hupper0
    have hhighLemma :
        ((((ramificationIndex K : ℚ) -
          (a.toBONG.lemma62Gap : ℚ) / 2) : ℚ) : WithTop ℚ) <
          a.toBONG.normalizedAdjacentDefectOrder (0 : Fin (N + 2)) := by
      unfold BONG.lemma62Gap
      rw [← hv0, ← hv1, ← hp0]
      exact hhigh0
    have hnotLowParameter :
        ¬2 * beliParameterDefect K parameter ≤
          (beliDefectCutoff K parameter : ℕ∞) := by
      intro hlow
      have hparameterLow : beliParameterDefect K
          (a.toBONG.adjacentParameter 0 (by simp)) ≤
          (a.toBONG.lemma62DefectCutoff : ℕ∞) := by
        apply a.toBONG.lemma62_parameterDefect_le_cutoff_of_low
          hevenLemma hupperLemma
        simpa only [hparameterEq] using hlow
      have hnormalizedLow :=
        a.toBONG.normalizedAdjacentDefectOrder_zero_le_of_lemma62_low
          hevenLemma hupperLemma hparameterLow
      exact (not_le_of_gt hhighLemma) hnormalizedLow
    rw [beliNormGeneratorGroup_of_high_defect K parameter
      hnotLargeParameter hnotLowParameter] at heta
    have hetaDepth :
        (beliHighDefectExponent K parameter : ℕ∞) ≤
          quadraticDefect K (eta : Kˣ) :=
      natCast_le_quadraticDefect_of_unitClass_mem eta
        (beliHighDefectExponent K parameter) heta
    have hetaDepthOrder :=
      natCast_le_defectOrder_of_natCast_le_quadraticDefect
        (eta : Kˣ) (beliHighDefectExponent K parameter) hetaDepth
    have hparameterAdmissible : IsBinaryParameterAdmissible parameter := by
      rw [hparameterEq]
      exact a.toBONG.adjacentParameter_isBinaryParameterAdmissible
        p0.castSucc (by simp [p0])
    have hevenParameter : Even (ordUnit K parameter) := by
      rw [hparameterOrder]
      exact heven0
    have hexponent := BONG.scratch_beliHighDefectExponent_cast
      (K := K) parameter hparameterAdmissible hevenParameter
    have hA02 := hB.hasPropertyA v0 (by simp [v0])
    have htarget :
        (⟨v0.1 + 2, by simpa [v0]⟩ : Fin (N + 3)) = v2 := by
      apply Fin.ext
      simp [v0, v2]
    rw [htarget] at hA02
    have hsum : 0 < gap0 + gap1 := by
      dsimp only [gap0, gap1]
      omega
    rcases heven0 with ⟨r, hr⟩
    have hexponentInt :
        (beliHighDefectExponent K parameter : Int) =
          (ramificationIndex K : Int) + r := by
      rw [hparameterOrder, hr] at hexponent
      have hhalf : (r + r) / 2 = r := by omega
      rw [hhalf] at hexponent
      exact hexponent
    have hsumQ : (0 : ℚ) < (gap0 : ℚ) + (gap1 : ℚ) := by
      exact_mod_cast hsum
    rw [hr] at hsumQ
    norm_num at hsumQ
    have hthresholdExponentQ :
        (ramificationIndex K : ℚ) - (gap1 : ℚ) / 2 <
          (beliHighDefectExponent K parameter : ℚ) := by
      have hexponentQ :
          (beliHighDefectExponent K parameter : ℚ) =
            (ramificationIndex K : ℚ) + (r : ℚ) := by
        exact_mod_cast hexponentInt
      rw [hexponentQ]
      linarith
    have hthresholdExponent :
        threshold1 <
          (((beliHighDefectExponent K parameter : Nat) : ℚ) : WithTop ℚ) := by
      change
        ((((ramificationIndex K : ℚ) - (gap1 : ℚ) / 2) : ℚ) : WithTop ℚ) <
          (((beliHighDefectExponent K parameter : Nat) : ℚ) : WithTop ℚ)
      exact_mod_cast hthresholdExponentQ
    have hetaHigh : threshold1 <
        BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) :=
      hthresholdExponent.trans_le hetaDepthOrder
    have hminHigh : threshold1 <
        min (BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ))
          (a.toBONG.normalizedAdjacentDefectOrder p1) :=
      (lt_min_iff).2 ⟨hetaHigh, hhigh1⟩
    have hproductLower :=
      min_defectOrder_le_normalizedAdjacentDefectOrder_one
        a c eta hvalues
    have hminHighOne : threshold1 <
        min (BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ))
          (a.toBONG.normalizedAdjacentDefectOrder (1 : Fin (N + 2))) := by
      simpa only [hp1] using hminHigh
    have hcLowOne :
        c.toBONG.normalizedAdjacentDefectOrder (1 : Fin (N + 2)) ≤
          threshold1 := by
      simpa only [hp1] using hcLow
    exact (not_le_of_gt (hminHighOne.trans_le hproductLower)) hcLowOne

/-- A first legal binary transformation preserves Property B.  All trigger
positions except `1` are literally unchanged; the preceding lemma supplies
the one nontrivial local calculation. -/
theorem hasPropertyB_of_firstBinaryTransform
    {N : Nat} (a c : BONG.GoodBONG q L (N + 3))
    (eta : valuationUnitSubgroup K)
    (heta : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K (a.valueUnit 1 / a.valueUnit 0))
    (hvalues : (fun j => c.valueUnit j) =
      beli2009BinaryTransformAt (fun j => a.valueUnit j)
        (0 : Fin (N + 2)) (eta : Kˣ))
    (hB : a.toBONG.HasPropertyB) :
    c.toBONG.HasPropertyB := by
  refine ⟨hasPropertyA_of_firstBinaryTransform
    a c eta hvalues hB.hasPropertyA, ?_⟩
  intro i hci
  have hai : a.toBONG.propertyBTrigger i := by
    by_cases hi0 : i.1 = 0
    · have hi : i = (0 : Fin (N + 2)) := Fin.ext hi0
      subst i
      exact (propertyBTrigger_zero_iff_of_firstBinaryTransform
        a c eta hvalues).1 hci
    by_cases hi1 : i.1 = 1
    · have hi : i = (1 : Fin (N + 2)) := Fin.ext hi1
      subst i
      exact propertyBTrigger_one_of_firstBinaryTransform
        a c eta heta hvalues hB hci
    · have hi2 : 2 ≤ i.1 := by omega
      exact (propertyBTrigger_iff_of_firstBinaryTransform_of_two_le
        a c eta hvalues i hi2).1 hci
  have haNeighbors := hB.2 i hai
  have horders : ∀ j, c.toBONG.order j = a.toBONG.order j := by
    intro j
    exact order_eq_of_values_eq_firstBinaryTransform a c eta hvalues j
  constructor
  · intro j hj
    rw [horders i.castSucc, horders j]
    exact haNeighbors.1 j hj
  · intro k hk
    rw [horders k, horders i.succ]
    exact haNeighbors.2 k hk

/-- Head alignment with the Property-B invariant retained on the transformed
BONG. -/
theorem exists_reachable_headAligned_hasPropertyB
    {N : Nat} (a b : BONG.GoodBONG q L (N + 3))
    (hB : a.toBONG.HasPropertyB) :
    ∃ c : BONG.GoodBONG q L (N + 3),
      c.valueUnit (0 : Fin (N + 3)) = b.valueUnit (0 : Fin (N + 3)) ∧
        Beli2009BinaryReachable (K := K)
          (fun i ↦ a.valueUnit i) (fun i ↦ c.valueUnit i) ∧
        c.toBONG.HasPropertyB := by
  let eta : valuationUnitSubgroup K :=
    a.toBONG.normGeneratorValueRatioValuationUnit
      b.toBONG.head b.toBONG.head_isNormGenerator
  have hetaSet : a.toBONG.normGeneratorValueRatioClass
        b.toBONG.head b.toBONG.head_isNormGenerator ∈
      a.toBONG.normGeneratorValueRatioClassSet :=
    ⟨b.toBONG.head, b.toBONG.head_isNormGenerator, rfl⟩
  have hetaGroup : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K
        (a.valueUnit (1 : Fin (N + 3)) /
          a.valueUnit (0 : Fin (N + 3))) := by
    have hmem :=
      (BeliLemma63Laws.valueRatioClassSet_subset_group_of_propertyB
        a.toBONG hB) hetaSet
    change a.toBONG.normGeneratorValueRatioClass
        b.toBONG.head b.toBONG.head_isNormGenerator ∈
      beliNormGeneratorGroup K
        (a.valueUnit (1 : Fin (N + 3)) /
          a.valueUnit (0 : Fin (N + 3)))
    convert hmem using 1 <;>
      simp [BONG.adjacentParameter, BONG.GoodBONG.valueUnit]
  rcases exists_goodBONG_binaryTransformation_exact a
      (0 : Fin (N + 2)) eta hetaGroup with ⟨c, hvalues⟩
  have htrans : IsBeli2009BinaryTransformation (K := K)
      (fun j ↦ a.valueUnit j) (fun j ↦ c.valueUnit j) :=
    ⟨(0 : Fin (N + 2)), eta, hetaGroup, hvalues⟩
  have hfirst : c.valueUnit (0 : Fin (N + 3)) =
      b.valueUnit (0 : Fin (N + 3)) := by
    rw [congrFun hvalues (0 : Fin (N + 3))]
    change (eta : Kˣ) * a.valueUnit 0 = b.valueUnit 0
    dsimp only [eta, BONG.normGeneratorValueRatioValuationUnit,
      BONG.normGeneratorValueRatioUnit]
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0, Units.val_div_eq_div_val,
      BONG.coe_valueUnit]
    rw [← b.toBONG.value_zero_eq_quadratic_head]
    field_simp [a.toBONG.value_ne_zero (0 : Fin (N + 3))]
    simpa only [BONG.GoodBONG.coe_valueUnit, BONG.GoodBONG.value] using
      (mul_comm (b.toBONG.value (0 : Fin (N + 3)))
        (a.toBONG.value (0 : Fin (N + 3))))
  have hcB := hasPropertyB_of_firstBinaryTransform
    a c eta hetaGroup hvalues hB
  exact ⟨c, hfirst, htrans.reachable, hcB⟩

/-- Rank-uniform version of lifting a projected-tail path through an aligned
head. -/
theorem reachable_of_headValue_eq_of_mappedTail_reachable_rankThree
    {N : Nat} (c d : BONG.GoodBONG q L (N + 3))
    (hhead : c.valueUnit (0 : Fin (N + 3)) =
      d.valueUnit (0 : Fin (N + 3)))
    (f : Lattice.Isometry
      (q.orthogonalSpace d.toBONG.head d.toBONG.head_isAnisotropic)
      (q.orthogonalSpace c.toBONG.head c.toBONG.head_isAnisotropic)
      (L.projectedLattice q d.toBONG.head d.toBONG.head_isAnisotropic)
      (L.projectedLattice q c.toBONG.head c.toBONG.head_isAnisotropic))
    (htail : Beli2009BinaryReachable (K := K)
      (fun i => c.tail.valueUnit i)
      (fun i => (d.tail.mapLatticeIsometry f).valueUnit i)) :
    Beli2009BinaryReachable (K := K)
      (fun i => c.valueUnit i) (fun i => d.valueUnit i) := by
  have hlift := Beli2009BinaryReachable.cons
    (c.valueUnit (0 : Fin (N + 3))) htail
  rw [cons_tailValues_eq c] at hlift
  have htarget :
      Fin.cons (c.valueUnit (0 : Fin (N + 3)))
          (fun i => (d.tail.mapLatticeIsometry f).valueUnit i) =
        (fun i => d.valueUnit i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hhead
    · calc
        (d.tail.mapLatticeIsometry f).valueUnit j =
            d.tail.valueUnit j :=
          BONG.GoodBONG.valueUnit_mapLatticeIsometry f d.tail j
        _ = d.valueUnit j.succ := by
          apply Units.ext
          exact d.toBONG.value_tail j
  rw [htarget] at hlift
  exact hlift

/-- Every Property-B good BONG is connected to every good BONG of the same
lattice.  The proof is induction on the projected-tail rank, using Lemma 6.6
to align the actual head vectors after the first binary move. -/
theorem reachable_of_hasPropertyB_rankThree
    (N : Nat)
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a b : BONG.GoodBONG r M (N + 3))
    (hB : a.toBONG.HasPropertyB) :
    Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => b.valueUnit i) := by
  induction N generalizing W with
  | zero =>
      rcases exists_reachable_headAligned_hasPropertyB a b hB with
        ⟨c, hhead, hac, hcB⟩
      have heq : r.quadratic b.toBONG.head =
          r.quadratic c.toBONG.head := by
        rw [← b.toBONG.value_zero_eq_quadratic_head,
          ← c.toBONG.value_zero_eq_quadratic_head]
        exact congrArg ((↑) : Kˣ → K) hhead |>.symm
      obtain ⟨rotation, hrotation⟩ :
          ∃ rotation : Lattice.IntegralRotation r M,
            rotation.apply c.toBONG.head = b.toBONG.head := by
        by_cases hH : c.toBONG.FirstBinaryIsHyperbolic
        · exact c.toBONG.exists_rotation_apply_head_of_firstBinary_hyperbolic
            hcB hH b.toBONG.head b.toBONG.head_isNormGenerator.mem heq
        · exact c.toBONG.exists_rotation_apply_head_of_not_firstBinary_hyperbolic
            hcB hH b.toBONG.head b.toBONG.head_isNormGenerator.mem heq
      let ambient : Lattice.Isometry r r M M :=
        rotation.toIntegralOrthogonalGroup
      have hambient : ambient.toLinearEquiv c.toBONG.head = b.toBONG.head :=
        hrotation
      let projected := ambient.projectedLatticeIsometryOfEq
        c.toBONG.head c.toBONG.head_isAnisotropic
        b.toBONG.head b.toBONG.head_isAnisotropic hambient
      have htail : Beli2009BinaryReachable (K := K)
          (fun i => c.tail.valueUnit i)
          (fun i => (b.tail.mapLatticeIsometry projected.symm).valueUnit i) :=
        reachable_rankTwo c.tail (b.tail.mapLatticeIsometry projected.symm)
      have hcb := reachable_of_headValue_eq_of_mappedTail_reachable_rankThree
        c b hhead projected.symm htail
      exact hac.trans hcb
  | succ N ih =>
      rcases exists_reachable_headAligned_hasPropertyB a b hB with
        ⟨c, hhead, hac, hcB⟩
      have heq : r.quadratic b.toBONG.head =
          r.quadratic c.toBONG.head := by
        rw [← b.toBONG.value_zero_eq_quadratic_head,
          ← c.toBONG.value_zero_eq_quadratic_head]
        exact congrArg ((↑) : Kˣ → K) hhead |>.symm
      obtain ⟨rotation, hrotation⟩ :
          ∃ rotation : Lattice.IntegralRotation r M,
            rotation.apply c.toBONG.head = b.toBONG.head := by
        by_cases hH : c.toBONG.FirstBinaryIsHyperbolic
        · exact c.toBONG.exists_rotation_apply_head_of_firstBinary_hyperbolic
            hcB hH b.toBONG.head b.toBONG.head_isNormGenerator.mem heq
        · exact c.toBONG.exists_rotation_apply_head_of_not_firstBinary_hyperbolic
            hcB hH b.toBONG.head b.toBONG.head_isNormGenerator.mem heq
      let ambient : Lattice.Isometry r r M M :=
        rotation.toIntegralOrthogonalGroup
      have hambient : ambient.toLinearEquiv c.toBONG.head = b.toBONG.head :=
        hrotation
      let projected := ambient.projectedLatticeIsometryOfEq
        c.toBONG.head c.toBONG.head_isAnisotropic
        b.toBONG.head b.toBONG.head_isAnisotropic hambient
      have htail : Beli2009BinaryReachable (K := K)
          (fun i => c.tail.valueUnit i)
          (fun i => (b.tail.mapLatticeIsometry projected.symm).valueUnit i) := by
        exact ih c.tail (b.tail.mapLatticeIsometry projected.symm) hcB.tail
      have hcb := reachable_of_headValue_eq_of_mappedTail_reachable_rankThree
        c b hhead projected.symm htail
      exact hac.trans hcb

end Beli2009FinalRemarksProof.LargeResidueConnectivity

end Bong

namespace Bong

open Dyadic
open BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Beli2009FinalRemarksProof.LargeResidueConnectivity

/-- Corollary 8.10 together with the adjacent-binary path producing its
normal form. -/
structure ReachableCorollary810Data
    {N : Nat} (b : BONG.GoodBONG q L (N + 2)) where
  data : b.Beli2019Corollary810Data
  reachable : Beli2009BinaryReachable (K := K)
    (fun i => b.valueUnit i) (fun i => data.transformed.valueUnit i)

/-- Path-refined Corollary 8.10 over a dyadic field whose residue field has
more than two elements. -/
theorem reachableCorollary810_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    {N : Nat} (b : BONG.GoodBONG q L (N + 2))
    (hresidueMore : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableCorollary810Data b) := by
  cases N with
  | zero =>
      have hbinary : b.firstBinaryAlpha =
          (b.alphaValue (0 : Fin 1) : WithTop ℚ) := by
        unfold BONG.GoodBONG.firstBinaryAlpha
        exact b.binary_alpha_eq_min_candidates.symm
      exact ⟨{
        data := {
          transformed := b
          headValue_eq := rfl
          firstBinaryAlpha_eq := hbinary
        }
        reachable := .refl
      }⟩
  | succ N =>
      by_cases hbinary : b.firstBinaryAlpha =
          (b.alphaValue (0 : Fin (N + 2)) : WithTop ℚ)
      · exact ⟨{
          data := {
            transformed := b
            headValue_eq := rfl
            firstBinaryAlpha_eq := hbinary
          }
          reachable := .refl
        }⟩
      · have hhalfNe :
            ¬b.AttainsHalfGap (0 : Fin (N + 2)) := by
          intro hhalf
          exact hbinary (b.firstBinaryAlpha_eq_alpha_of_halfGap hhalf)
        have hstrict : b.alphaValue (0 : Fin (N + 2)) <
            b.halfGapValue (0 : Fin (N + 2)) :=
          lt_of_le_of_ne (b.alphaValue_le_halfGapValue 0) hhalfNe
        have hadjacentNotLe : ¬b.adjacentDefect (0 : Fin (N + 2)) ≤
            (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
          intro hle
          exact hbinary
            (b.firstBinaryAlpha_eq_alpha_of_adjacentDefect_le_tailAlpha hle)
        have htail :
            (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) <
              b.adjacentDefect (0 : Fin (N + 2)) :=
          lt_of_not_ge hadjacentNotLe
        have htailStrict :=
          b.tailAlpha_lt_halfGap_of_global_strict htail hstrict
        have htailNotExceptional :
            ¬b.tail.Beli2019Lemma88Exceptional := by
          rintro ⟨htailHalf, _⟩
          exact (ne_of_lt htailStrict) htailHalf
        rcases reachableLemma88_sufficiency_of_largeResidue b.tail
            htailNotExceptional hresidueMore with ⟨T⟩
        rcases reachableTailReplacementData_of_firstValueTransform b T with
          ⟨D, hDReachable⟩
        have hglobal :=
          b.alpha_zero_eq_orderGap_add_tailAlpha_of_tailAlpha_lt_adjacentDefect
            htail hstrict
        have hbinaryOriginal :=
          D.firstBinaryAlpha_eq_of_strict_tail htail hglobal
        have halphas := b.alpha_invariant D.transformed
        have hbinaryTransformed : D.transformed.firstBinaryAlpha =
            (D.transformed.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
          calc
            D.transformed.firstBinaryAlpha =
                (b.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) :=
              hbinaryOriginal
            _ = (D.transformed.alphaValue
                (0 : Fin (N + 2)) : WithTop ℚ) :=
              congrArg (fun x : ℚ => (x : WithTop ℚ))
                (halphas (0 : Fin (N + 2)))
        exact ⟨{
          data := {
            transformed := D.transformed
            headValue_eq := D.firstValue_eq
            firstBinaryAlpha_eq := hbinaryTransformed
          }
          reachable := hDReachable
        }⟩

/-- Path-refined first normal form for Lemma 8.14 over a residue field with
more than two elements. -/
theorem reachableLemma814FirstNormalForm_of_largeResidue
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 3))
    (b : BONG.GoodBONG r M 1)
    (hfirst : a.order (0 : Fin (N + 3)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (hresidueMore : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableLemma814FirstNormalForm a b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases reachableCorollary810_of_largeResidue
      (K := K) (q := q) (L := L) a hresidueMore with ⟨R⟩
  let D := R.data
  have horders : a.SameOrders D.transformed :=
    a.order_invariant D.transformed
  have hfirst' : D.transformed.order (0 : Fin (N + 3)) =
      b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin (N + 3))]
    exact hfirst
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classificationV)
    (classificationW := classificationW) D.transformed b hfirst conditions
  have hinvariant := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) D.transformed b
  exact ⟨{
    data := {
      transformed := D.transformed
      headValue_eq := D.headValue_eq
      firstOrder_eq := hfirst'
      firstBinaryAlpha_eq := D.firstBinaryAlpha_eq
      conditions := hconditions
      notExceptional := fun E ↦ hnotExceptional (hinvariant.mpr E)
    }
    reachable := R.reachable
  }⟩

/-- A valuation-unit square class satisfying the binary alpha bound and the
binary determinant norm condition is an allowed adjacent multiplier.  This
packages Remark 5.2 in the form needed by path constructions. -/
theorem valuationUnitClass_mem_normGenerator_of_cut_le_hilbert
    [QuadraticDefectLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    (parameter : Kˣ) (hparameter : BONG.IsBinaryParameterAdmissible parameter)
    (u : valuationUnitSubgroup K)
    (hdefect : beli2009BinaryAlphaCut (K := K) parameter ≤
      BONG.GoodBONG.defectOrder (K := K) (u : Kˣ))
    (hhilbert : hilbertSymbol K (-parameter) (u : Kˣ) = 1) :
    valuationUnitClassHom K u ∈ beliNormGeneratorGroup K parameter := by
  have hcongruence : valuationUnitClassHom K u ∈
      beli2009BinaryAlphaCongruenceGroup (K := K) parameter :=
    valuationUnitClassHom_mem_beli2009BinaryAlphaCongruenceGroup
      (K := K) parameter hparameter u hdefect
  have hnorm : valuationUnitClassHom K u ∈
      quadraticNormValuationClassSubgroup K (-parameter) := by
    refine ⟨u, (hilbertSymbol_eq_one_iff K _ _).mp hhilbert, rfl⟩
  rw [beli2009Lemma51 (K := K) parameter hparameter]
  exact ⟨hcongruence, hnorm⟩

/-- Good-BONG specialization of the preceding parameter-level criterion. -/
theorem valuationUnitClass_mem_normGenerator_of_alpha_le_hilbert
    [QuadraticDefectLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    (b : BONG.GoodBONG q L 2) (u : valuationUnitSubgroup K)
    (hdefect : (b.alphaValue (0 : Fin 1) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (u : Kˣ))
    (hhilbert : hilbertSymbol K
      (-(b.valueUnit (0 : Fin 2) * b.valueUnit (1 : Fin 2))) (u : Kˣ) = 1) :
    valuationUnitClassHom K u ∈
      beliNormGeneratorGroup K b.toBONG.binaryParameter := by
  apply valuationUnitClass_mem_normGenerator_of_cut_le_hilbert
    b.toBONG.binaryParameter
      b.toBONG.binaryParameter_isBinaryParameterAdmissible u
  · rw [b.binaryAlphaCut_parameter_eq]
    exact hdefect
  · change hilbertSymbol K (b.adjacentProduct 0) (u : Kˣ) = 1 at hhilbert
    rw [b.binary_adjacentProduct_eq_parameter_mul_square,
      hilbertSymbol_mul_square_left] at hhilbert
    exact hhilbert

/-- Literal-adjacent form of Remark 5.2.  This removes all segment-index
bookkeeping from the ternary path constructions below. -/
theorem valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
    [QuadraticDefectLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    {N : Nat} (b : BONG.GoodBONG q L (N + 2)) (i : Fin (N + 1))
    (u : valuationUnitSubgroup K)
    (hdefect : b.adjacentBinaryAlpha i ≤
      BONG.GoodBONG.defectOrder (K := K) (u : Kˣ))
    (hhilbert : hilbertSymbol K (b.adjacentProduct i) (u : Kˣ) = 1) :
    valuationUnitClassHom K u ∈ beliNormGeneratorGroup K
      (b.valueUnit i.succ / b.valueUnit i.castSucc) := by
  rcases b.toBONG.exists_segmentWitness i.1 2 (by omega) with ⟨w⟩
  let s := w.toGoodBONG b.good
  have hsourceZero : w.sourceIndex (0 : Fin 2) = i.castSucc := by
    apply Fin.ext
    simp [BONG.SegmentWitness.sourceIndex]
  have hsourceOne : w.sourceIndex (1 : Fin 2) = i.succ := by
    apply Fin.ext
    simp [BONG.SegmentWitness.sourceIndex]
  have hvalueZero : s.valueUnit (0 : Fin 2) =
      b.valueUnit i.castSucc := by
    change w.bong.valueUnit 0 = b.toBONG.valueUnit i.castSucc
    rw [w.valueUnit_eq, hsourceZero]
  have hvalueOne : s.valueUnit (1 : Fin 2) =
      b.valueUnit i.succ := by
    change w.bong.valueUnit 1 = b.toBONG.valueUnit i.succ
    rw [w.valueUnit_eq, hsourceOne]
  have hsAlpha : (s.alphaValue (0 : Fin 1) : WithTop ℚ) =
      b.adjacentBinaryAlpha i := by
    exact (b.adjacentBinaryAlpha_eq_segmentAlpha i w).symm
  have hsDefect : (s.alphaValue (0 : Fin 1) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (u : Kˣ) := by
    rw [hsAlpha]
    exact hdefect
  have hsHilbert : hilbertSymbol K
      (-(s.valueUnit (0 : Fin 2) * s.valueUnit (1 : Fin 2)))
      (u : Kˣ) = 1 := by
    rw [hvalueZero, hvalueOne]
    exact hhilbert
  have hmem := valuationUnitClass_mem_normGenerator_of_alpha_le_hilbert
    s u hsDefect hsHilbert
  have hparameter : s.toBONG.binaryParameter =
      b.valueUnit i.succ / b.valueUnit i.castSucc := by
    unfold BONG.binaryParameter
    change s.valueUnit 1 / s.valueUnit 0 = _
    rw [hvalueZero, hvalueOne]
  rwa [hparameter] at hmem

/-- If neither of the two norm hyperplanes contains the prescribed
principal-unit layer, their intersection supplies a valuation-unit class in
the norm group of `-parameter` on which the `epsilon` Hilbert character is
nontrivial.  This is the group-theoretic choice used in the ternary detour. -/
theorem exists_valuationUnit_principal_norm_hilbert_neg_one
    [BeliHilbertCongruenceLaws K]
    (parameter epsilon : Kˣ) (k : Nat)
    (hnotEpsilon : ¬principalUnitSquareClassSubgroup K k ≤
      quadraticNormSquareClassSubgroup K epsilon)
    (hnotProduct : ¬principalUnitSquareClassSubgroup K k ≤
      quadraticNormSquareClassSubgroup K ((-parameter) * epsilon)) :
    ∃ u : valuationUnitSubgroup K,
      valuationUnitClassHom K u ∈
          principalUnitValuationClassSubgroup K k ∧
        valuationUnitClassHom K u ∈
          quadraticNormValuationClassSubgroup K (-parameter) ∧
        hilbertSymbol K epsilon (u : Kˣ) = -1 := by
  let U := principalUnitSquareClassSubgroup K k
  let Np := quadraticNormSquareClassSubgroup K (-parameter)
  let Ne := quadraticNormSquareClassSubgroup K epsilon
  have hnotInter : ¬Np ⊓ U ≤ Ne := by
    intro hle
    have hor : U ≤ Ne ∨
        U ≤ quadraticNormSquareClassSubgroup K
          ((-parameter) * epsilon) :=
      (quadraticNorm_inf_le_quadraticNorm_iff
        (K := K) (-parameter) epsilon U).mp hle
    exact hor.elim hnotEpsilon hnotProduct
  rcases SetLike.not_le_iff_exists.mp hnotInter with
    ⟨z, hzInter, hzNotNorm⟩
  have hzImage : z ∈ valuationUnitClassSubgroupSquareImage K
      (principalUnitValuationClassSubgroup K k ⊓
        quadraticNormValuationClassSubgroup K (-parameter)) := by
    rw [valuationUnitClassSubgroupSquareImage_principalUnit_inf_norm]
    exact ⟨hzInter.2, hzInter.1⟩
  rcases hzImage with ⟨c, hc, hcz⟩
  obtain ⟨u, rfl⟩ := Quotient.exists_rep c
  refine ⟨u, hc.1, hc.2, ?_⟩
  have hne : hilbertSymbol K epsilon (u : Kˣ) ≠ 1 := by
    intro hhilbert
    apply hzNotNorm
    rw [← hcz]
    exact ⟨(u : Kˣ),
      (hilbertSymbol_eq_one_iff K epsilon (u : Kˣ)).mp hhilbert,
      rfl⟩
  exact (Int.units_eq_one_or
    (hilbertSymbol K epsilon (u : Kˣ))).resolve_left hne

/-- Membership in the `k`-th principal-unit layer gives the corresponding
embedded lower bound on Beli's rational defect order.  This is the bridge
from the square-class filtration used by Lemma 1.3 to the alpha inequalities
used by adjacent binary transformations. -/
theorem natCast_le_defectOrder_of_unitClass_mem
    (u : valuationUnitSubgroup K) (k : Nat)
    (hmem : valuationUnitClassHom K u ∈
      principalUnitValuationClassSubgroup K k) :
    (((k : Nat) : ℚ) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (u : Kˣ) := by
  have hraw : (k : ℕ∞) ≤ quadraticDefect K (u : Kˣ) :=
    natCast_le_quadraticDefect_of_unitClass_mem u k hmem
  cases hdefect : quadraticDefect K (u : Kˣ) with
  | top =>
      rw [BONG.GoodBONG.defectOrder, hdefect]
      exact le_top
  | coe d =>
      rw [hdefect] at hraw
      have hkd : k ≤ d := WithTop.coe_le_coe.mp hraw
      calc
        (((k : Nat) : ℚ) : WithTop ℚ) ≤
            (((d : Nat) : ℚ) : WithTop ℚ) := by exact_mod_cast hkd
        _ = BONG.GoodBONG.defectOrder (K := K) (u : Kˣ) := by
          unfold BONG.GoodBONG.defectOrder
          rw [hdefect]
          exact (WithTop.map_coe (fun m : Nat => (m : ℚ)) d).symm

/-- Reverse bridge for a finite natural depth: a rational defect-order lower
bound reflects to the underlying extended-natural quadratic defect. -/
theorem natCast_le_quadraticDefect_of_natCast_le_defectOrder
    (x : Kˣ) (k : Nat)
    (h : (((k : Nat) : ℚ) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) x) :
    (k : ℕ∞) ≤ quadraticDefect K x := by
  unfold BONG.GoodBONG.defectOrder at h
  cases hdefect : quadraticDefect K x with
  | top => exact le_top
  | coe d =>
      rw [hdefect] at h
      change (((k : Nat) : ℚ) : WithTop ℚ) ≤
        (((d : Nat) : ℚ) : WithTop ℚ) at h
      have hkd : k ≤ d := by exact_mod_cast h
      exact_mod_cast hkd

/-- A finite natural value of the rational defect order reflects exactly to
the corresponding extended-natural quadratic defect. -/
theorem quadraticDefect_eq_natCast_of_defectOrder_eq_natCast
    (x : Kˣ) (k : Nat)
    (h : BONG.GoodBONG.defectOrder (K := K) x =
      (((k : Nat) : ℚ) : WithTop ℚ)) :
    quadraticDefect K x = (k : ℕ∞) := by
  have hfinite : quadraticDefect K x ≠ ⊤ :=
    BONG.GoodBONG.quadraticDefect_ne_top_of_defectOrder_eq_coe
      x (k : ℚ) h
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hdk : d = k := by
    unfold BONG.GoodBONG.defectOrder at h
    rw [← hd] at h
    change (((d : Nat) : ℚ) : WithTop ℚ) =
      (((k : Nat) : ℚ) : WithTop ℚ) at h
    exact_mod_cast h
  exact hd.symm.trans (congrArg (fun n : Nat => (n : ℕ∞)) hdk)

/-- `ENat`-native version of the non-strict defect-sum reflection.  The
production lemma predates mathlib's opaque `ENat` wrapper and therefore has a
`WithTop Nat` order in its conclusion; this restatement keeps the derived
`ENat` order used by the local Hilbert laws. -/
theorem quadraticDefect_add_le_twoE_of_defectOrder_add_le_twoE_enat
    (a b : Kˣ)
    (h : BONG.GoodBONG.defectOrder (K := K) a +
        BONG.GoodBONG.defectOrder (K := K) b ≤
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) :
    quadraticDefect K a + quadraticDefect K b ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞) := by
  cases ha : quadraticDefect K a with
  | top =>
      unfold BONG.GoodBONG.defectOrder at h
      rw [ha] at h
      change (⊤ : WithTop ℚ) + _ ≤ _ at h
      have htop : (⊤ : WithTop ℚ) ≤
          (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
        simpa only [top_add] using h
      exact ((not_le_of_gt (WithTop.coe_lt_top _)) htop).elim
  | coe m =>
      cases hb : quadraticDefect K b with
      | top =>
          unfold BONG.GoodBONG.defectOrder at h
          rw [hb] at h
          change _ + (⊤ : WithTop ℚ) ≤ _ at h
          have htop : (⊤ : WithTop ℚ) ≤
              (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
            simpa only [add_top] using h
          exact ((not_le_of_gt (WithTop.coe_lt_top _)) htop).elim
      | coe n =>
          have hmn : (m : ℚ) + (n : ℚ) ≤
              (2 * ramificationIndex K : Nat) := by
            unfold BONG.GoodBONG.defectOrder at h
            rw [ha, hb] at h
            change ((m : ℚ) : WithTop ℚ) + (n : ℚ) ≤ _ at h
            norm_cast at h
            exact_mod_cast h
          change (m : ℕ∞) + (n : ℕ∞) ≤
            ((2 * ramificationIndex K : Nat) : ℕ∞)
          exact_mod_cast hmn

/-- Inversion does not change a Hilbert symbol, since its values are signs. -/
theorem hilbertSymbol_inv_left_eq
    [HilbertSymbolLaws K] (a b : Kˣ) :
    hilbertSymbol K a⁻¹ b = hilbertSymbol K a b := by
  have hinv := map_inv (hilbertCharacter K b) a
  change hilbertSymbol K b a⁻¹ = (hilbertSymbol K b a)⁻¹ at hinv
  calc
    hilbertSymbol K a⁻¹ b = hilbertSymbol K b a⁻¹ :=
      hilbertSymbol_comm K _ _
    _ = (hilbertSymbol K b a)⁻¹ := hinv
    _ = (hilbertSymbol K a b)⁻¹ := by
      rw [hilbertSymbol_comm K b a]
    _ = hilbertSymbol K a b := by
      rcases Int.units_eq_one_or (hilbertSymbol K a b) with h | h <;>
        rw [h] <;> norm_num

/-- Rational-depth form of the two-character principal-layer choice.  The
chosen valuation unit is a norm from `-parameter`, is Hilbert-negative
against `epsilon`, and has defect order at least the prescribed natural
depth. -/
theorem exists_valuationUnit_depth_norm_hilbert_neg_one
    [BeliHilbertCongruenceLaws K]
    (parameter epsilon : Kˣ) (k : Nat)
    (hnotEpsilon : ¬principalUnitSquareClassSubgroup K k ≤
      quadraticNormSquareClassSubgroup K epsilon)
    (hnotProduct : ¬principalUnitSquareClassSubgroup K k ≤
      quadraticNormSquareClassSubgroup K ((-parameter) * epsilon)) :
    ∃ u : valuationUnitSubgroup K,
      (((k : Nat) : ℚ) : WithTop ℚ) ≤
          BONG.GoodBONG.defectOrder (K := K) (u : Kˣ) ∧
        hilbertSymbol K (-parameter) (u : Kˣ) = 1 ∧
        hilbertSymbol K epsilon (u : Kˣ) = -1 := by
  rcases exists_valuationUnit_principal_norm_hilbert_neg_one
      parameter epsilon k hnotEpsilon hnotProduct with
    ⟨u, huDepth, huNorm, huEpsilon⟩
  refine ⟨u, natCast_le_defectOrder_of_unitClass_mem u k huDepth, ?_,
    huEpsilon⟩
  exact (hilbertSymbol_eq_one_iff K (-parameter) (u : Kˣ)).2
    (Beli2009FinalRemarksProof.isQuadraticNorm_of_unitClass_mem
      (-parameter) u huNorm)

/-- A positive principal depth cannot be contained in a quadratic norm
hyperplane when the corresponding defect sum is at most the dyadic
endpoint.  This is the contrapositive form of Beli (2003), Lemma 1.2(iii),
used in the simultaneous-choice argument. -/
theorem not_principalUnitSquareClassSubgroup_le_quadraticNorm_of_sum_le
    [BeliHilbertCongruenceLaws K]
    (a : Kˣ) (k : Nat) (hk : 0 < k)
    (hsum : quadraticDefect K a + (k : ℕ∞) ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ¬principalUnitSquareClassSubgroup K k ≤
      quadraticNormSquareClassSubgroup K a := by
  intro hle
  have hstrict : ((2 * ramificationIndex K : Nat) : ℕ∞) <
      quadraticDefect K a + k :=
    (principalUnitSquareClassSubgroup_le_quadraticNorm_iff
      (K := K) a k hk).mp hle
  exact (not_lt_of_ge hsum) hstrict

/-- Defect-sum form of the two-character principal-layer choice. -/
theorem exists_valuationUnit_depth_norm_hilbert_neg_one_of_sums_le
    [BeliHilbertCongruenceLaws K]
    (parameter epsilon : Kˣ) (k : Nat) (hk : 0 < k)
    (hsumEpsilon : quadraticDefect K epsilon + (k : ℕ∞) ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hsumProduct : quadraticDefect K ((-parameter) * epsilon) +
        (k : ℕ∞) ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ u : valuationUnitSubgroup K,
      (((k : Nat) : ℚ) : WithTop ℚ) ≤
          BONG.GoodBONG.defectOrder (K := K) (u : Kˣ) ∧
        hilbertSymbol K (-parameter) (u : Kˣ) = 1 ∧
        hilbertSymbol K epsilon (u : Kˣ) = -1 := by
  apply exists_valuationUnit_depth_norm_hilbert_neg_one
    parameter epsilon k
  · exact not_principalUnitSquareClassSubgroup_le_quadraticNorm_of_sum_le
      epsilon k hk hsumEpsilon
  · exact not_principalUnitSquareClassSubgroup_le_quadraticNorm_of_sum_le
      ((-parameter) * epsilon) k hk hsumProduct

/-- The zero-one-zero adjacent detour is a legal reachability path whenever
its three dynamic binary parameters admit the indicated multipliers. -/
theorem reachable_threeStep_zero_one_zero
    (a : Fin 3 → Kˣ)
    (mu eta nu : valuationUnitSubgroup K)
    (hmu : valuationUnitClassHom K mu ∈
      beliNormGeneratorGroup K
        (a (1 : Fin 3) / a (0 : Fin 3)))
    (heta : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K
        (beli2009BinaryTransformAt a (0 : Fin 2) (mu : Kˣ) (2 : Fin 3) /
          beli2009BinaryTransformAt a (0 : Fin 2) (mu : Kˣ) (1 : Fin 3)))
    (hnu : valuationUnitClassHom K nu ∈
      beliNormGeneratorGroup K
        (beli2009BinaryTransformAt
            (beli2009BinaryTransformAt a (0 : Fin 2) (mu : Kˣ))
              (1 : Fin 2) (eta : Kˣ) (1 : Fin 3) /
          beli2009BinaryTransformAt
            (beli2009BinaryTransformAt a (0 : Fin 2) (mu : Kˣ))
              (1 : Fin 2) (eta : Kˣ) (0 : Fin 3))) :
    Beli2009BinaryReachable (K := K) a
      (beli2009BinaryTransformAt
        (beli2009BinaryTransformAt
          (beli2009BinaryTransformAt a (0 : Fin 2) (mu : Kˣ))
            (1 : Fin 2) (eta : Kˣ))
        (0 : Fin 2) (nu : Kˣ)) := by
  have hzero : IsBeli2009BinaryTransformation (K := K) a
      (beli2009BinaryTransformAt a (0 : Fin 2) (mu : Kˣ)) :=
    ⟨0, mu, hmu, rfl⟩
  have hone : IsBeli2009BinaryTransformation (K := K)
      (beli2009BinaryTransformAt a (0 : Fin 2) (mu : Kˣ))
      (beli2009BinaryTransformAt
        (beli2009BinaryTransformAt a (0 : Fin 2) (mu : Kˣ))
          (1 : Fin 2) (eta : Kˣ)) :=
    ⟨1, eta, heta, rfl⟩
  have hzero' : IsBeli2009BinaryTransformation (K := K)
      (beli2009BinaryTransformAt
        (beli2009BinaryTransformAt a (0 : Fin 2) (mu : Kˣ))
          (1 : Fin 2) (eta : Kˣ))
      (beli2009BinaryTransformAt
        (beli2009BinaryTransformAt
          (beli2009BinaryTransformAt a (0 : Fin 2) (mu : Kˣ))
            (1 : Fin 2) (eta : Kˣ))
        (0 : Fin 2) (nu : Kˣ)) :=
    ⟨0, nu, hnu, rfl⟩
  exact hzero.reachable.trans (hone.reachable.trans hzero'.reachable)

/-- Algebraic endpoint of the zero-one-zero detour. -/
theorem binaryTransform_threeStep_zero_one_zero
    (a : Fin 3 → Kˣ) (mu eta epsilon : valuationUnitSubgroup K) :
    beli2009BinaryTransformAt
        (beli2009BinaryTransformAt
          (beli2009BinaryTransformAt a (0 : Fin 2) (mu : Kˣ))
            (1 : Fin 2) (eta : Kˣ))
        (0 : Fin 2) ((epsilon / mu : valuationUnitSubgroup K) : Kˣ) =
      ![epsilon * a 0, epsilon * eta * a 1, eta * a 2] := by
  funext i
  fin_cases i
  · simp [beli2009BinaryTransformAt, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]
    calc
      (mu : Kˣ) * (epsilon * ((mu : Kˣ)⁻¹ * a 0)) =
          ((mu : Kˣ) * (mu : Kˣ)⁻¹) * (epsilon * a 0) := by
        ac_rfl
      _ = epsilon * a 0 := by simp
  · simp [beli2009BinaryTransformAt, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]
    calc
      (mu : Kˣ) * (eta * (epsilon * ((mu : Kˣ)⁻¹ * a 1))) =
          ((mu : Kˣ) * (mu : Kˣ)⁻¹) *
            (eta * (epsilon * a 1)) := by
        ac_rfl
      _ = eta * (epsilon * a 1) := by simp
  · simp [beli2009BinaryTransformAt, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]

/-- The coefficient formula used by the ternary constructions is exactly the
endpoint vector of the adjacent paths above. -/
theorem ternaryScaledValues_eq_vector
    (a : BONG.GoodBONG q L 3)
    (epsilon eta : valuationUnitSubgroup K) :
    (fun i ↦ a.ternaryScaledValues (epsilon : Kˣ) (eta : Kˣ) i) =
      ![(epsilon : Kˣ) * a.valueUnit 0,
        (epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 1,
        (eta : Kˣ) * a.valueUnit 2] := by
  funext i
  fin_cases i <;> rfl

/-- A concrete good BONG with the ternary-scaled values is reached by the
`0→1→0` detour whenever its three dynamic multipliers are locally legal. -/
theorem reachable_ternaryScaledValues_threeStep
    (a c : BONG.GoodBONG q L 3)
    (mu eta epsilon : valuationUnitSubgroup K)
    (hmu : valuationUnitClassHom K mu ∈
      beliNormGeneratorGroup K
        (a.valueUnit (1 : Fin 3) / a.valueUnit (0 : Fin 3)))
    (heta : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K
        (beli2009BinaryTransformAt (fun i ↦ a.valueUnit i)
            (0 : Fin 2) (mu : Kˣ) (2 : Fin 3) /
          beli2009BinaryTransformAt (fun i ↦ a.valueUnit i)
            (0 : Fin 2) (mu : Kˣ) (1 : Fin 3)))
    (hfinal : valuationUnitClassHom K (epsilon / mu) ∈
      beliNormGeneratorGroup K
        (beli2009BinaryTransformAt
              (beli2009BinaryTransformAt (fun i ↦ a.valueUnit i)
                (0 : Fin 2) (mu : Kˣ))
              (1 : Fin 2) (eta : Kˣ) (1 : Fin 3) /
          beli2009BinaryTransformAt
              (beli2009BinaryTransformAt (fun i ↦ a.valueUnit i)
                (0 : Fin 2) (mu : Kˣ))
              (1 : Fin 2) (eta : Kˣ) (0 : Fin 3)))
    (hvalues : ∀ i,
      c.valueUnit i =
        a.ternaryScaledValues (epsilon : Kˣ) (eta : Kˣ) i) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ c.valueUnit i) := by
  have hreach := reachable_threeStep_zero_one_zero
    (K := K) (fun i ↦ a.valueUnit i) mu eta (epsilon / mu)
      hmu heta hfinal
  rw [binaryTransform_threeStep_zero_one_zero
    (K := K) (fun i ↦ a.valueUnit i) mu eta epsilon] at hreach
  have htarget :
      ![(epsilon : Kˣ) * a.valueUnit 0,
        (epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 1,
        (eta : Kˣ) * a.valueUnit 2] =
      (fun i ↦ c.valueUnit i) := by
    rw [← ternaryScaledValues_eq_vector a epsilon eta]
    funext i
    exact (hvalues i).symm
  rwa [htarget] at hreach

/-- The direct left-to-right realization of a ternary scaling.  The first
move multiplies coordinates `0,1` by `epsilon`; the second multiplies the
new coordinates `1,2` by `eta`. -/
theorem reachable_twoStep_zero_one
    (a : Fin 3 → Kˣ)
    (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : valuationUnitClassHom K epsilon ∈
      beliNormGeneratorGroup K
        (a (1 : Fin 3) / a (0 : Fin 3)))
    (heta : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K
        (beli2009BinaryTransformAt a (0 : Fin 2) (epsilon : Kˣ)
            (2 : Fin 3) /
          beli2009BinaryTransformAt a (0 : Fin 2) (epsilon : Kˣ)
            (1 : Fin 3))) :
    Beli2009BinaryReachable (K := K) a
      (beli2009BinaryTransformAt
        (beli2009BinaryTransformAt a (0 : Fin 2) (epsilon : Kˣ))
        (1 : Fin 2) (eta : Kˣ)) := by
  have hzero : IsBeli2009BinaryTransformation (K := K) a
      (beli2009BinaryTransformAt a (0 : Fin 2) (epsilon : Kˣ)) :=
    ⟨0, epsilon, hepsilon, rfl⟩
  have hone : IsBeli2009BinaryTransformation (K := K)
      (beli2009BinaryTransformAt a (0 : Fin 2) (epsilon : Kˣ))
      (beli2009BinaryTransformAt
        (beli2009BinaryTransformAt a (0 : Fin 2) (epsilon : Kˣ))
        (1 : Fin 2) (eta : Kˣ)) :=
    ⟨1, eta, heta, rfl⟩
  exact hzero.reachable.trans hone.reachable

/-- Algebraic endpoint of the direct left-to-right ternary path. -/
theorem binaryTransform_twoStep_zero_one
    (a : Fin 3 → Kˣ) (epsilon eta : valuationUnitSubgroup K) :
    beli2009BinaryTransformAt
        (beli2009BinaryTransformAt a (0 : Fin 2) (epsilon : Kˣ))
        (1 : Fin 2) (eta : Kˣ) =
      ![epsilon * a 0, epsilon * eta * a 1, eta * a 2] := by
  funext i
  fin_cases i <;>
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]

/-- A concrete ternary scaling is reached directly from left to right when
both dynamic binary memberships hold. -/
theorem reachable_ternaryScaledValues_twoStep_zero_one
    (a c : BONG.GoodBONG q L 3)
    (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : valuationUnitClassHom K epsilon ∈
      beliNormGeneratorGroup K
        (a.valueUnit (1 : Fin 3) / a.valueUnit (0 : Fin 3)))
    (heta : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K
        (beli2009BinaryTransformAt (fun i ↦ a.valueUnit i)
            (0 : Fin 2) (epsilon : Kˣ) (2 : Fin 3) /
          beli2009BinaryTransformAt (fun i ↦ a.valueUnit i)
            (0 : Fin 2) (epsilon : Kˣ) (1 : Fin 3)))
    (hvalues : ∀ i,
      c.valueUnit i =
        a.ternaryScaledValues (epsilon : Kˣ) (eta : Kˣ) i) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ c.valueUnit i) := by
  have hreach := reachable_twoStep_zero_one
    (K := K) (fun i ↦ a.valueUnit i) epsilon eta hepsilon heta
  rw [binaryTransform_twoStep_zero_one
    (K := K) (fun i ↦ a.valueUnit i) epsilon eta] at hreach
  have htarget :
      ![(epsilon : Kˣ) * a.valueUnit 0,
        (epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 1,
        (eta : Kˣ) * a.valueUnit 2] =
      (fun i ↦ c.valueUnit i) := by
    rw [← ternaryScaledValues_eq_vector a epsilon eta]
    funext i
    exact (hvalues i).symm
  rwa [htarget] at hreach

/-- The direct right-to-left realization of a ternary scaling. -/
theorem reachable_twoStep_one_zero
    (a : Fin 3 → Kˣ)
    (epsilon eta : valuationUnitSubgroup K)
    (heta : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K
        (a (2 : Fin 3) / a (1 : Fin 3)))
    (hepsilon : valuationUnitClassHom K epsilon ∈
      beliNormGeneratorGroup K
        (beli2009BinaryTransformAt a (1 : Fin 2) (eta : Kˣ)
            (1 : Fin 3) /
          beli2009BinaryTransformAt a (1 : Fin 2) (eta : Kˣ)
            (0 : Fin 3))) :
    Beli2009BinaryReachable (K := K) a
      (beli2009BinaryTransformAt
        (beli2009BinaryTransformAt a (1 : Fin 2) (eta : Kˣ))
        (0 : Fin 2) (epsilon : Kˣ)) := by
  have hone : IsBeli2009BinaryTransformation (K := K) a
      (beli2009BinaryTransformAt a (1 : Fin 2) (eta : Kˣ)) :=
    ⟨1, eta, heta, rfl⟩
  have hzero : IsBeli2009BinaryTransformation (K := K)
      (beli2009BinaryTransformAt a (1 : Fin 2) (eta : Kˣ))
      (beli2009BinaryTransformAt
        (beli2009BinaryTransformAt a (1 : Fin 2) (eta : Kˣ))
        (0 : Fin 2) (epsilon : Kˣ)) :=
    ⟨0, epsilon, hepsilon, rfl⟩
  exact hone.reachable.trans hzero.reachable

/-- Algebraic endpoint of the direct right-to-left ternary path. -/
theorem binaryTransform_twoStep_one_zero
    (a : Fin 3 → Kˣ) (epsilon eta : valuationUnitSubgroup K) :
    beli2009BinaryTransformAt
        (beli2009BinaryTransformAt a (1 : Fin 2) (eta : Kˣ))
        (0 : Fin 2) (epsilon : Kˣ) =
      ![epsilon * a 0, epsilon * eta * a 1, eta * a 2] := by
  funext i
  fin_cases i <;>
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]

/-- A concrete ternary scaling is reached directly from right to left when
both dynamic binary memberships hold. -/
theorem reachable_ternaryScaledValues_twoStep_one_zero
    (a c : BONG.GoodBONG q L 3)
    (epsilon eta : valuationUnitSubgroup K)
    (heta : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K
        (a.valueUnit (2 : Fin 3) / a.valueUnit (1 : Fin 3)))
    (hepsilon : valuationUnitClassHom K epsilon ∈
      beliNormGeneratorGroup K
        (beli2009BinaryTransformAt (fun i ↦ a.valueUnit i)
            (1 : Fin 2) (eta : Kˣ) (1 : Fin 3) /
          beli2009BinaryTransformAt (fun i ↦ a.valueUnit i)
            (1 : Fin 2) (eta : Kˣ) (0 : Fin 3)))
    (hvalues : ∀ i,
      c.valueUnit i =
        a.ternaryScaledValues (epsilon : Kˣ) (eta : Kˣ) i) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ c.valueUnit i) := by
  have hreach := reachable_twoStep_one_zero
    (K := K) (fun i ↦ a.valueUnit i) epsilon eta heta hepsilon
  rw [binaryTransform_twoStep_one_zero
    (K := K) (fun i ↦ a.valueUnit i) epsilon eta] at hreach
  have htarget :
      ![(epsilon : Kˣ) * a.valueUnit 0,
        (epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 1,
        (eta : Kˣ) * a.valueUnit 2] =
      (fun i ↦ c.valueUnit i) := by
    rw [← ternaryScaledValues_eq_vector a epsilon eta]
    funext i
    exact (hvalues i).symm
  rwa [htarget] at hreach

/-- The alternating `1→0→1` realization of a ternary scaling.  Its
middle multiplier is `epsilon`; the two right-hand moves split `eta` as
`theta * (eta / theta)`. -/
theorem reachable_threeStep_one_zero_one
    (a : Fin 3 → Kˣ)
    (theta epsilon eta : valuationUnitSubgroup K)
    (htheta : valuationUnitClassHom K theta ∈
      beliNormGeneratorGroup K
        (a (2 : Fin 3) / a (1 : Fin 3)))
    (hepsilon : valuationUnitClassHom K epsilon ∈
      beliNormGeneratorGroup K
        (beli2009BinaryTransformAt a (1 : Fin 2) (theta : Kˣ)
            (1 : Fin 3) /
          beli2009BinaryTransformAt a (1 : Fin 2) (theta : Kˣ)
            (0 : Fin 3)))
    (hetaTheta : valuationUnitClassHom K (eta / theta) ∈
      beliNormGeneratorGroup K
        (beli2009BinaryTransformAt
            (beli2009BinaryTransformAt a (1 : Fin 2) (theta : Kˣ))
              (0 : Fin 2) (epsilon : Kˣ) (2 : Fin 3) /
          beli2009BinaryTransformAt
            (beli2009BinaryTransformAt a (1 : Fin 2) (theta : Kˣ))
              (0 : Fin 2) (epsilon : Kˣ) (1 : Fin 3))) :
    Beli2009BinaryReachable (K := K) a
      (beli2009BinaryTransformAt
        (beli2009BinaryTransformAt
          (beli2009BinaryTransformAt a (1 : Fin 2) (theta : Kˣ))
            (0 : Fin 2) (epsilon : Kˣ))
        (1 : Fin 2) ((eta / theta : valuationUnitSubgroup K) : Kˣ)) := by
  have hone : IsBeli2009BinaryTransformation (K := K) a
      (beli2009BinaryTransformAt a (1 : Fin 2) (theta : Kˣ)) :=
    ⟨1, theta, htheta, rfl⟩
  have hzero : IsBeli2009BinaryTransformation (K := K)
      (beli2009BinaryTransformAt a (1 : Fin 2) (theta : Kˣ))
      (beli2009BinaryTransformAt
        (beli2009BinaryTransformAt a (1 : Fin 2) (theta : Kˣ))
          (0 : Fin 2) (epsilon : Kˣ)) :=
    ⟨0, epsilon, hepsilon, rfl⟩
  have hone' : IsBeli2009BinaryTransformation (K := K)
      (beli2009BinaryTransformAt
        (beli2009BinaryTransformAt a (1 : Fin 2) (theta : Kˣ))
          (0 : Fin 2) (epsilon : Kˣ))
      (beli2009BinaryTransformAt
        (beli2009BinaryTransformAt
          (beli2009BinaryTransformAt a (1 : Fin 2) (theta : Kˣ))
            (0 : Fin 2) (epsilon : Kˣ))
        (1 : Fin 2) ((eta / theta : valuationUnitSubgroup K) : Kˣ)) :=
    ⟨1, eta / theta, hetaTheta, rfl⟩
  exact hone.reachable.trans (hzero.reachable.trans hone'.reachable)

/-- Algebraic endpoint of the alternating `1→0→1` path. -/
theorem binaryTransform_threeStep_one_zero_one
    (a : Fin 3 → Kˣ)
    (theta epsilon eta : valuationUnitSubgroup K) :
    beli2009BinaryTransformAt
        (beli2009BinaryTransformAt
          (beli2009BinaryTransformAt a (1 : Fin 2) (theta : Kˣ))
            (0 : Fin 2) (epsilon : Kˣ))
        (1 : Fin 2) ((eta / theta : valuationUnitSubgroup K) : Kˣ) =
      ![epsilon * a 0, epsilon * eta * a 1, eta * a 2] := by
  funext i
  fin_cases i
  · simp [beli2009BinaryTransformAt]
  · simp [beli2009BinaryTransformAt, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]
    calc
      (theta : Kˣ) *
            ((epsilon : Kˣ) * ((eta : Kˣ) * ((theta : Kˣ)⁻¹ * a 1))) =
          ((theta : Kˣ) * (theta : Kˣ)⁻¹) *
            ((epsilon : Kˣ) * ((eta : Kˣ) * a 1)) := by
              ac_rfl
      _ = epsilon * (eta * a 1) := by simp
  · simp [beli2009BinaryTransformAt, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]
    calc
      (theta : Kˣ) * ((eta : Kˣ) * ((theta : Kˣ)⁻¹ * a 2)) =
          ((theta : Kˣ) * (theta : Kˣ)⁻¹) * ((eta : Kˣ) * a 2) := by
            ac_rfl
      _ = eta * a 2 := by simp

/-- Under the ternary Hasse identity, legality of the first Hilbert
condition in the `0→1` order forces legality of the second one. -/
theorem hilbert_second_eq_one_of_ternary_hasse_of_first_eq_one
    [HilbertSymbolLaws K]
    (A₀ A₁ epsilon eta : Kˣ)
    (hhasse : hilbertSymbol K (eta * A₀) (epsilon * A₁) =
      hilbertSymbol K A₀ A₁)
    (hfirst : hilbertSymbol K epsilon A₀ = 1) :
    hilbertSymbol K eta (epsilon * A₁) = 1 := by
  have hA₀ : hilbertSymbol K A₀ (epsilon * A₁) =
      hilbertSymbol K A₀ A₁ := by
    rw [hilbertSymbol_mul_right,
      hilbertSymbol_comm K A₀ epsilon, hfirst]
    simp
  have h := hhasse
  rw [hilbertSymbol_mul_left, hA₀] at h
  rcases Int.units_eq_one_or (hilbertSymbol K A₀ A₁) with hA | hA
  · rw [hA] at h
    simpa using h
  · rw [hA] at h
    norm_num at h ⊢
    exact h

/-- Symmetric right-to-left form of the preceding Hilbert implication. -/
theorem hilbert_first_eq_one_of_ternary_hasse_of_second_eq_one
    [HilbertSymbolLaws K]
    (A₀ A₁ epsilon eta : Kˣ)
    (hhasse : hilbertSymbol K (eta * A₀) (epsilon * A₁) =
      hilbertSymbol K A₀ A₁)
    (hsecond : hilbertSymbol K eta A₁ = 1) :
    hilbertSymbol K epsilon (eta * A₀) = 1 := by
  have heta : hilbertSymbol K eta (epsilon * A₁) =
      hilbertSymbol K eta epsilon := by
    rw [hilbertSymbol_mul_right, hsecond]
    simp
  have hA₀ : hilbertSymbol K A₀ (epsilon * A₁) =
      hilbertSymbol K A₀ epsilon * hilbertSymbol K A₀ A₁ := by
    exact hilbertSymbol_mul_right K A₀ epsilon A₁
  have h := hhasse
  rw [hilbertSymbol_mul_left, heta, hA₀] at h
  have hprod : hilbertSymbol K eta epsilon *
      hilbertSymbol K A₀ epsilon = 1 := by
    rcases Int.units_eq_one_or (hilbertSymbol K A₀ A₁) with hA | hA
    · rw [hA] at h
      simpa using h
    · rw [hA] at h
      norm_num at h ⊢
      exact h
  rw [hilbertSymbol_mul_right,
    hilbertSymbol_comm K epsilon eta,
    hilbertSymbol_comm K epsilon A₀]
  exact hprod

/-- For the alternating `1→0→1` path, the ternary Hasse identity and
the Hilbert legality of its first two moves force legality of the third. -/
theorem hilbert_third_eq_one_of_ternary_hasse
    [HilbertSymbolLaws K]
    (A₀ A₁ theta epsilon eta : Kˣ)
    (hhasse : hilbertSymbol K (eta * A₀) (epsilon * A₁) =
      hilbertSymbol K A₀ A₁)
    (htheta : hilbertSymbol K theta A₁ = 1)
    (hepsilon : hilbertSymbol K epsilon (theta * A₀) = 1) :
    hilbertSymbol K (eta / theta) (epsilon * A₁) = 1 := by
  have hthetaInvA₁ : hilbertSymbol K theta⁻¹ A₁ = 1 := by
    rw [show theta⁻¹ = theta * (theta⁻¹) ^ 2 by group,
      hilbertSymbol_mul_square_left, htheta]
  have hthetaInvEpsilon : hilbertSymbol K theta⁻¹ epsilon =
      hilbertSymbol K theta epsilon := by
    rw [show theta⁻¹ = theta * (theta⁻¹) ^ 2 by group,
      hilbertSymbol_mul_square_left]
  have hepsilonExpanded : hilbertSymbol K epsilon theta *
      hilbertSymbol K epsilon A₀ = 1 := by
    simpa only [hilbertSymbol_mul_right] using hepsilon
  have hcore : hilbertSymbol K eta epsilon *
      hilbertSymbol K eta A₁ * hilbertSymbol K A₀ epsilon = 1 := by
    have h := hhasse
    rw [hilbertSymbol_mul_left, hilbertSymbol_mul_right,
      hilbertSymbol_mul_right] at h
    rcases Int.units_eq_one_or (hilbertSymbol K A₀ A₁) with hA | hA
    · rw [hA] at h
      simpa [mul_assoc] using h
    · rw [hA] at h
      norm_num at h ⊢
      exact h
  have hcore' : hilbertSymbol K eta epsilon *
      hilbertSymbol K eta A₁ * hilbertSymbol K epsilon A₀ = 1 := by
    rw [hilbertSymbol_comm K epsilon A₀]
    exact hcore
  rw [div_eq_mul_inv, hilbertSymbol_mul_left,
    hilbertSymbol_mul_right, hilbertSymbol_mul_right,
    hthetaInvA₁, mul_one, hthetaInvEpsilon,
    hilbertSymbol_comm K theta epsilon]
  calc
    (hilbertSymbol K eta epsilon * hilbertSymbol K eta A₁) *
          hilbertSymbol K epsilon theta =
        (hilbertSymbol K eta epsilon * hilbertSymbol K eta A₁ *
          hilbertSymbol K epsilon A₀) *
          (hilbertSymbol K epsilon A₀ *
            hilbertSymbol K epsilon theta) := by
              rcases Int.units_eq_one_or
                (hilbertSymbol K epsilon A₀) with hA | hA <;>
                rw [hA] <;> norm_num
    _ = 1 := by
      rw [hcore']
      simpa [mul_comm] using hepsilonExpanded

/-- A two-character correction used by the ternary detour.  Start with a
negative partner for `eta` of the prescribed defect.  If its pairing with
`A` has the wrong sign, multiplication by `epsilon` flips that sign while
preserving the negative pairing with `eta` and the required defect lower
bound. -/
theorem exists_valuationUnit_two_negative_correction
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    (epsilon eta A reference : Kˣ)
    (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hrefUnit : IsValuationUnit K (reference : K))
    (hepsilonDepth : BONG.GoodBONG.defectOrder (K := K) reference ≤
      BONG.GoodBONG.defectOrder (K := K) epsilon)
    (hsum : quadraticDefect K eta + quadraticDefect K reference ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hepsilonEta : hilbertSymbol K epsilon eta = 1)
    (hepsilonA : hilbertSymbol K epsilon A = -1) :
    ∃ rho : Kˣ,
      IsValuationUnit K (rho : K) ∧
        BONG.GoodBONG.defectOrder (K := K) reference ≤
          BONG.GoodBONG.defectOrder (K := K) rho ∧
        hilbertSymbol K rho eta = -1 ∧
        hilbertSymbol K rho A = -1 := by
  rcases (beli2019Lemma82_i eta reference).2 hsum with
    ⟨x, hxDefect, hxEta⟩
  have hrefNonzero := quadraticDefect_ne_zero_of_isValuationUnit
    reference hrefUnit
  have hxNonzero : quadraticDefect K x ≠ 0 := by
    rw [hxDefect]
    exact hrefNonzero
  rcases exists_valuationUnit_same_defect_same_hilbert eta x hxNonzero with
    ⟨u, huUnit, huDefectX, huEtaX⟩
  have huDefect : quadraticDefect K u = quadraticDefect K reference :=
    huDefectX.trans hxDefect
  have huDepth : BONG.GoodBONG.defectOrder (K := K) u =
      BONG.GoodBONG.defectOrder (K := K) reference := by
    exact defectOrder_eq_of_quadraticDefect_eq u reference huDefect
  have huEta : hilbertSymbol K u eta = -1 := by
    rw [hilbertSymbol_comm K]
    exact huEtaX.trans hxEta
  rcases Int.units_eq_one_or (hilbertSymbol K u A) with huA | huA
  · have hproductUnit : IsValuationUnit K ((epsilon * u : Kˣ) : K) := by
      rw [IsValuationUnit, Units.val_mul, ord_mul,
        hepsilonUnit, huUnit, zero_add]
    refine ⟨epsilon * u, hproductUnit, ?_, ?_, ?_⟩
    · exact (le_min hepsilonDepth huDepth.ge).trans
        (BONG.GoodBONG.defectOrder_mul_ge_min (K := K) epsilon u)
    · rw [hilbertSymbol_mul_left, hepsilonEta, huEta]
      norm_num
    · rw [hilbertSymbol_mul_left, hepsilonA, huA]
      norm_num
  · exact ⟨u, huUnit, huDepth.ge, huEta, huA⟩

/-- A simultaneous two-character Hilbert choice at a prescribed unit-defect
depth.  Lemma 8.2(i) first supplies negative partners for `chi` and
`chi * psi`.  If neither partner already has the requested second sign,
their product does; the defect-product inequality keeps it at least as deep
as the reference class. -/
theorem exists_valuationUnit_hilbert_neg_one_of_two_sums_le
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    (chi psi reference : Kˣ)
    (hrefUnit : IsValuationUnit K (reference : K))
    (hchi : quadraticDefect K chi + quadraticDefect K reference ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hproduct : quadraticDefect K (chi * psi) +
        quadraticDefect K reference ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ theta : Kˣ,
      IsValuationUnit K (theta : K) ∧
        BONG.GoodBONG.defectOrder (K := K) reference ≤
          BONG.GoodBONG.defectOrder (K := K) theta ∧
        hilbertSymbol K chi theta = -1 ∧
        hilbertSymbol K psi theta = 1 := by
  rcases (beli2019Lemma82_i chi reference).2 hchi with
    ⟨x, hxDefect, hxChi⟩
  have hrefNonzero := quadraticDefect_ne_zero_of_isValuationUnit
    reference hrefUnit
  have hxNonzero : quadraticDefect K x ≠ 0 := by
    rw [hxDefect]
    exact hrefNonzero
  rcases exists_valuationUnit_same_defect_same_hilbert chi x hxNonzero with
    ⟨u, huUnit, huDefectX, huChiX⟩
  have huDefect : quadraticDefect K u = quadraticDefect K reference :=
    huDefectX.trans hxDefect
  have huDepth : BONG.GoodBONG.defectOrder (K := K) u =
      BONG.GoodBONG.defectOrder (K := K) reference :=
    defectOrder_eq_of_quadraticDefect_eq u reference huDefect
  have huChi : hilbertSymbol K chi u = -1 :=
    huChiX.trans hxChi
  rcases Int.units_eq_one_or (hilbertSymbol K psi u) with huPsi | huPsi
  · exact ⟨u, huUnit, huDepth.ge, huChi, huPsi⟩
  · rcases (beli2019Lemma82_i (chi * psi) reference).2 hproduct with
      ⟨y, hyDefect, hyProduct⟩
    have hyNonzero : quadraticDefect K y ≠ 0 := by
      rw [hyDefect]
      exact hrefNonzero
    rcases exists_valuationUnit_same_defect_same_hilbert
        (chi * psi) y hyNonzero with
      ⟨v, hvUnit, hvDefectY, hvProductY⟩
    have hvDefect : quadraticDefect K v = quadraticDefect K reference :=
      hvDefectY.trans hyDefect
    have hvDepth : BONG.GoodBONG.defectOrder (K := K) v =
        BONG.GoodBONG.defectOrder (K := K) reference :=
      defectOrder_eq_of_quadraticDefect_eq v reference hvDefect
    have hvProduct : hilbertSymbol K (chi * psi) v = -1 :=
      hvProductY.trans hyProduct
    rcases Int.units_eq_one_or (hilbertSymbol K chi v) with hvChi | hvChi
    · have hvPsi : hilbertSymbol K psi v = -1 := by
        rw [hilbertSymbol_mul_left, hvChi] at hvProduct
        simpa using hvProduct
      have huvUnit : IsValuationUnit K (((u * v : Kˣ) : K)) := by
        rw [IsValuationUnit, Units.val_mul, ord_mul,
          huUnit, hvUnit, zero_add]
      refine ⟨u * v, huvUnit, ?_, ?_, ?_⟩
      · exact (le_min huDepth.ge hvDepth.ge).trans
          (BONG.GoodBONG.defectOrder_mul_ge_min (K := K) u v)
      · rw [hilbertSymbol_mul_right, huChi, hvChi]
        norm_num
      · rw [hilbertSymbol_mul_right, huPsi, hvPsi]
        norm_num
    · have hvPsi : hilbertSymbol K psi v = 1 := by
        rw [hilbertSymbol_mul_left, hvChi] at hvProduct
        have := hvProduct
        norm_num at this ⊢
        exact this
      exact ⟨v, hvUnit, hvDepth.ge, hvChi, hvPsi⟩

/-- Over a residue field with more than two elements, a non-endpoint defect
layer has a neighbour on which any Hilbert character allowed by Lemma 8.2(i)
is negative.  Besides having the same defect as `a`, the chosen class remains
in that defect layer after multiplication by `a`.

The only nontrivial case is when the first negative partner cancels with
`a`.  Lemma 8.1(i) supplies another neighbour `c`.  If `c` has positive
Hilbert sign, `c * w` has the required negative sign.  The two strict-defect
domination calculations show that both `c * w` and `a * (c * w)` still have
the original defect. -/
theorem exists_same_defect_product_hilbert_neg_one_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (z a : Kˣ)
    (haFinite : quadraticDefect K a ≠ ⊤)
    (haNonzero : quadraticDefect K a ≠ 0)
    (haNotTwoE : quadraticDefect K a ≠
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hsum : quadraticDefect K z + quadraticDefect K a ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ theta : Kˣ,
      quadraticDefect K theta = quadraticDefect K a ∧
        quadraticDefect K (a * theta) = quadraticDefect K a ∧
        hilbertSymbol K z theta = -1 := by
  rcases (beli2019Lemma82_i z a).2 hsum with
    ⟨w, hwDefect, hwNeg⟩
  by_cases haw : quadraticDefect K (a * w) = quadraticDefect K a
  · exact ⟨w, hwDefect, haw, hwNeg⟩
  rcases beli2019Lemma81_i hres a haNonzero haNotTwoE with
    ⟨c, hcDefect, hacDefect⟩
  by_cases hcNeg : hilbertSymbol K z c = -1
  · exact ⟨c, hcDefect, hacDefect, hcNeg⟩
  have hcOne : hilbertSymbol K z c = 1 :=
    (Int.units_eq_one_or (hilbertSymbol K z c)).resolve_right hcNeg
  have haLeAw : quadraticDefect K a ≤ quadraticDefect K (a * w) := by
    have hdom := quadraticDefect_mul_ge_min K a w
    rw [hwDefect, min_self] at hdom
    exact hdom
  have haLtAw : quadraticDefect K a < quadraticDefect K (a * w) :=
    lt_of_le_of_ne haLeAw (Ne.symm haw)
  have hcAw : quadraticDefect K (c * (a * w)) =
      quadraticDefect K a := by
    have h := quadraticDefect_mul_eq_left_of_lt_right
      (K := K) (a := c) (b := a * w) (by
      simpa only [hcDefect] using haLtAw)
    exact h.trans hcDefect
  have hthetaProduct : quadraticDefect K (a * (c * w)) =
      quadraticDefect K a := by
    rw [show a * (c * w) = c * (a * w) by ac_rfl]
    exact hcAw
  have hacLtAw : quadraticDefect K (a * c) <
      quadraticDefect K (a * w) := by
    simpa only [hacDefect] using haLtAw
  have hacaw : quadraticDefect K ((a * c) * (a * w)) =
      quadraticDefect K a := by
    have h := quadraticDefect_mul_eq_left_of_lt_right (K := K) hacLtAw
    exact h.trans hacDefect
  have hthetaDefect : quadraticDefect K (c * w) =
      quadraticDefect K a := by
    have hsquare : (a * c) * (a * w) = (c * w) * a ^ 2 := by
      simp only [pow_two]
      ac_rfl
    rw [hsquare, quadraticDefect_mul_square] at hacaw
    exact hacaw
  refine ⟨c * w, hthetaDefect, hthetaProduct, ?_⟩
  rw [hilbertSymbol_mul_right, hcOne, hwNeg]
  norm_num

/-- Normalize the quotient `w / x` by an even valuation.  The resulting
multiplier is a valuation unit and its product with `x` differs from `w` by
the displayed square.  Unlike the one-character normalization lemmas, this
factorization preserves *all* Hilbert pairings and is therefore suitable for
two-character detours. -/
theorem exists_valuationUnit_multiplier_mul_square_eq
    [QuadraticDefectLaws K]
    (x w : Kˣ)
    (hxEven : Even (ordUnit K x))
    (hwNonzero : quadraticDefect K w ≠ 0) :
    ∃ eta s : Kˣ,
      IsValuationUnit K (eta : K) ∧ (eta * x) * s ^ 2 = w := by
  have hwEven : Even (ordUnit K w) := by
    rcases Int.even_or_odd (ordUnit K w) with heven | hodd
    · exact heven
    · exact (hwNonzero (quadraticDefect_eq_zero_of_odd_ordUnit w hodd)).elim
  let t : Kˣ := w / x
  have htEven : Even (ordUnit K t) := by
    dsimp only [t]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv]
    exact hwEven.sub hxEven
  rcases htEven with ⟨k, hk⟩
  let s : Kˣ := uniformizerPowerUnit K k
  let eta : Kˣ := t / s ^ 2
  have hsOrder : ordUnit K s = k :=
    ordUnit_uniformizerPowerUnit (K := K) k
  have hetaOrder : ordUnit K eta = 0 := by
    dsimp only [eta]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow,
      hsOrder, hk]
    omega
  have hetaUnit : IsValuationUnit K (eta : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K eta).2 hetaOrder
  refine ⟨eta, s, hetaUnit, ?_⟩
  dsimp only [eta, t]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- At an anisotropic ternary equal-depth boundary, the large-residue
neighbour lemma can be oriented to give exactly the two Hilbert signs needed
by the `1→0→1` detour.  The output multiplier is a valuation unit, its
product with `A₀` stays in the original defect layer, and the multiplier
itself is at least that deep. -/
theorem exists_valuationUnit_anisotropic_detour_neighbor
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (epsilon A₀ A₁ : Kˣ)
    (hA₀Even : Even (ordUnit K A₀))
    (hA₀Finite : quadraticDefect K A₀ ≠ ⊤)
    (hA₀Nonzero : quadraticDefect K A₀ ≠ 0)
    (hA₀NotTwoE : quadraticDefect K A₀ ≠
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hsum : quadraticDefect K (epsilon * A₁) +
        quadraticDefect K A₀ ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hepsilonA₀ : hilbertSymbol K epsilon A₀ = -1)
    (hA₀A₁ : hilbertSymbol K A₀ A₁ = -1) :
    ∃ theta : Kˣ,
      IsValuationUnit K (theta : K) ∧
        BONG.GoodBONG.defectOrder (K := K) A₀ ≤
          BONG.GoodBONG.defectOrder (K := K) theta ∧
        quadraticDefect K (theta * A₀) = quadraticDefect K A₀ ∧
        hilbertSymbol K theta A₁ = 1 ∧
        hilbertSymbol K theta epsilon = -1 := by
  rcases exists_same_defect_product_hilbert_neg_one_of_largeResidue
      hres (epsilon * A₁) A₀ hA₀Finite hA₀Nonzero hA₀NotTwoE hsum with
    ⟨u, huDefect, hA₀uDefect, huCombined⟩
  have hraw : ∃ w : Kˣ,
      quadraticDefect K w = quadraticDefect K A₀ ∧
        quadraticDefect K (A₀ * w) = quadraticDefect K A₀ ∧
        hilbertSymbol K w A₁ = -1 ∧
        hilbertSymbol K w epsilon = 1 := by
    by_cases huA₁ : hilbertSymbol K u A₁ = -1
    · have huEpsilon : hilbertSymbol K u epsilon = 1 := by
        have h := huCombined
        rw [hilbertSymbol_mul_left,
          hilbertSymbol_comm K epsilon u,
          hilbertSymbol_comm K A₁ u, huA₁] at h
        rcases Int.units_eq_one_or (hilbertSymbol K u epsilon) with he | he
        · exact he
        · rw [he] at h
          norm_num at h
      exact ⟨u, huDefect, hA₀uDefect, huA₁, huEpsilon⟩
    · have huA₁One : hilbertSymbol K u A₁ = 1 :=
        (Int.units_eq_one_or (hilbertSymbol K u A₁)).resolve_right huA₁
      have huEpsilon : hilbertSymbol K u epsilon = -1 := by
        have h := huCombined
        rw [hilbertSymbol_mul_left,
          hilbertSymbol_comm K epsilon u,
          hilbertSymbol_comm K A₁ u, huA₁One] at h
        simpa using h
      refine ⟨u * A₀, ?_, ?_, ?_, ?_⟩
      · simpa only [mul_comm] using hA₀uDefect
      · have hsquare : A₀ * (u * A₀) = u * A₀ ^ 2 := by
          simp only [pow_two]
          ac_rfl
        rw [hsquare, quadraticDefect_mul_square, huDefect]
      · rw [hilbertSymbol_mul_left, huA₁One, hA₀A₁]
        norm_num
      · rw [hilbertSymbol_mul_left, huEpsilon,
          hilbertSymbol_comm K A₀ epsilon, hepsilonA₀]
        norm_num
  rcases hraw with ⟨w, hwDefect, hA₀wDefect, hwA₁, hwEpsilon⟩
  have hwNonzero : quadraticDefect K w ≠ 0 := by
    rw [hwDefect]
    exact hA₀Nonzero
  rcases exists_valuationUnit_multiplier_mul_square_eq
      A₀ w hA₀Even hwNonzero with
    ⟨theta, s, hthetaUnit, hfactor⟩
  have hthetaProduct : quadraticDefect K (theta * A₀) =
      quadraticDefect K A₀ := by
    calc
      quadraticDefect K (theta * A₀) =
          quadraticDefect K ((theta * A₀) * s ^ 2) :=
        (quadraticDefect_mul_square K (theta * A₀) s).symm
      _ = quadraticDefect K w := congrArg (quadraticDefect K) hfactor
      _ = quadraticDefect K A₀ := hwDefect
  have hthetaDepth : BONG.GoodBONG.defectOrder (K := K) A₀ ≤
      BONG.GoodBONG.defectOrder (K := K) theta := by
    by_contra hnot
    have hlt : BONG.GoodBONG.defectOrder (K := K) theta <
        BONG.GoodBONG.defectOrder (K := K) A₀ := lt_of_not_ge hnot
    have hdom := BONG.GoodBONG.defectOrder_mul_eq_left_of_lt_right
      (K := K) hlt
    have heq : BONG.GoodBONG.defectOrder (K := K) theta =
        BONG.GoodBONG.defectOrder (K := K) A₀ := by
      rw [← hdom]
      exact defectOrder_eq_of_quadraticDefect_eq
        (theta * A₀) A₀ hthetaProduct
    exact (ne_of_lt hlt) heq
  have hthetaA₁ : hilbertSymbol K theta A₁ = 1 := by
    have hpair : hilbertSymbol K ((theta * A₀) * s ^ 2) A₁ = -1 := by
      rw [hfactor]
      exact hwA₁
    rw [hilbertSymbol_mul_square_left, hilbertSymbol_mul_left,
      hA₀A₁] at hpair
    rcases Int.units_eq_one_or (hilbertSymbol K theta A₁) with h | h
    · exact h
    · rw [h] at hpair
      norm_num at hpair
  have hthetaEpsilon : hilbertSymbol K theta epsilon = -1 := by
    have hpair : hilbertSymbol K ((theta * A₀) * s ^ 2) epsilon = 1 := by
      rw [hfactor]
      exact hwEpsilon
    rw [hilbertSymbol_mul_square_left, hilbertSymbol_mul_left,
      hilbertSymbol_comm K A₀ epsilon, hepsilonA₀] at hpair
    rcases Int.units_eq_one_or (hilbertSymbol K theta epsilon) with h | h
    · rw [h] at hpair
      norm_num at hpair
    · exact h
  exact ⟨theta, hthetaUnit, hthetaDepth, hthetaProduct,
    hthetaA₁, hthetaEpsilon⟩

/-- In a valid ternary scaling, simultaneous failure of the two direct
binary moves forces `epsilon` and `eta` to pair trivially. -/
theorem hilbert_epsilon_eta_eq_one_of_ternary_scaling_deadlock
    [HilbertSymbolLaws K]
    (A₀ A₁ epsilon eta : Kˣ)
    (hepsilonA₀ : hilbertSymbol K epsilon A₀ = -1)
    (hetaA₁ : hilbertSymbol K eta A₁ = -1)
    (hscaled : hilbertSymbol K (eta * A₀) (epsilon * A₁) =
      hilbertSymbol K A₀ A₁) :
    hilbertSymbol K epsilon eta = 1 := by
  have hexpanded := hscaled
  rw [hilbertSymbol_mul_left, hilbertSymbol_mul_right,
    hilbertSymbol_mul_right,
    hilbertSymbol_comm K A₀ epsilon, hepsilonA₀, hetaA₁] at hexpanded
  rcases Int.units_eq_one_or (hilbertSymbol K eta epsilon) with h | h
  · rw [hilbertSymbol_comm K]
    exact h
  · rw [h] at hexpanded
    norm_num at hexpanded

/-- Hilbert-symbol verification for the three legs of the zero-one-zero
detour with `mu = epsilon * rho` and final multiplier `rho⁻¹`. -/
theorem ternaryDetour_hilbert_conditions
    [HilbertSymbolLaws K]
    (A₀ A₁ epsilon eta rho : Kˣ)
    (hepsilonA₀ : hilbertSymbol K epsilon A₀ = -1)
    (hetaA₁ : hilbertSymbol K eta A₁ = -1)
    (hepsilonEta : hilbertSymbol K epsilon eta = 1)
    (hrhoEta : hilbertSymbol K rho eta = -1)
    (hrhoA₀ : hilbertSymbol K rho A₀ = -1) :
    hilbertSymbol K (epsilon * rho) A₀ = 1 ∧
      hilbertSymbol K eta ((epsilon * rho) * A₁) = 1 ∧
      hilbertSymbol K rho⁻¹ (eta * A₀) = 1 := by
  constructor
  · rw [hilbertSymbol_mul_left, hepsilonA₀, hrhoA₀]
    norm_num
  constructor
  · rw [hilbertSymbol_mul_right, hilbertSymbol_mul_right,
      hilbertSymbol_comm K eta epsilon,
      hilbertSymbol_comm K eta rho,
      hepsilonEta, hrhoEta, hetaA₁]
    norm_num
  · have hinv : rho⁻¹ = rho * (rho⁻¹) ^ 2 := by group
    rw [hinv, hilbertSymbol_mul_square_left,
      hilbertSymbol_mul_right, hrhoEta, hrhoA₀]
    norm_num

/-- Reverse the coefficient order and invert every coefficient.  This is
the value-sequence operation induced by BONG reverse duality. -/
def reverseInvValues {N : Nat} (a : Fin N → Kˣ) : Fin N → Kˣ :=
  fun i ↦ (a (Fin.rev i))⁻¹

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
@[simp] theorem reverseInvValues_reverseInvValues
    {N : Nat} (a : Fin N → Kˣ) :
    reverseInvValues (K := K) (reverseInvValues (K := K) a) = a := by
  funext i
  simp [reverseInvValues]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
theorem reverseInvValues_binaryTransformAt
    {N : Nat} (a : Fin (N + 1) → Kˣ) (i : Fin N) (eta : Kˣ) :
    reverseInvValues (K := K) (beli2009BinaryTransformAt a i eta) =
      beli2009BinaryTransformAt (reverseInvValues (K := K) a)
        (Fin.rev i) eta⁻¹ := by
  funext j
  by_cases hleft : j = (Fin.rev i).castSucc
  · subst j
    simp [reverseInvValues, mul_inv_rev, mul_comm]
  by_cases hright : j = (Fin.rev i).succ
  · subst j
    simp [reverseInvValues, mul_inv_rev, mul_comm]
  have hrevLeft : Fin.rev j ≠ i.castSucc := by
    intro h
    apply hright
    apply Fin.rev_injective
    simpa using h
  have hrevRight : Fin.rev j ≠ i.succ := by
    intro h
    apply hleft
    apply Fin.rev_injective
    simpa using h
  simp only [reverseInvValues]
  rw [beli2009BinaryTransformAt_of_ne _ _ _ _ hrevLeft hrevRight,
    beli2009BinaryTransformAt_of_ne _ _ _ _ hleft hright]
  rfl

theorem Beli2009ValueSequenceEquivalent.reverseInv
    {N : Nat} {a b : Fin (N + 1) → Kˣ}
    (h : Beli2009ValueSequenceEquivalent (K := K) a b) :
    Beli2009ValueSequenceEquivalent (K := K)
      (reverseInvValues (K := K) a) (reverseInvValues (K := K) b) := by
  intro i
  simp only [reverseInvValues]
  rw [unitSquareClass_inv_local, unitSquareClass_inv_local, h]

theorem IsBeli2009BinaryTransformation.reverseInv
    {N : Nat} {a b : Fin (N + 1) → Kˣ}
    (h : IsBeli2009BinaryTransformation (K := K) a b) :
    IsBeli2009BinaryTransformation (K := K)
      (reverseInvValues (K := K) a) (reverseInvValues (K := K) b) := by
  rcases h with ⟨i, eta, heta, rfl⟩
  refine ⟨Fin.rev i, eta⁻¹, ?_, ?_⟩
  · have hparameter :
        reverseInvValues (K := K) a (Fin.rev i).succ /
            reverseInvValues (K := K) a (Fin.rev i).castSucc =
          a i.succ / a i.castSucc := by
      simp [reverseInvValues, div_eq_mul_inv]
      ac_rfl
    rw [hparameter, map_inv]
    exact (beliNormGeneratorGroup K
      (a i.succ / a i.castSucc)).inv_mem heta
  · exact reverseInvValues_binaryTransformAt a i (eta : Kˣ)

theorem IsBeli2009BinaryStep.reverseInv
    {N : Nat} {a b : Fin (N + 1) → Kˣ}
    (h : IsBeli2009BinaryStep (K := K) a b) :
    IsBeli2009BinaryStep (K := K)
      (reverseInvValues (K := K) a) (reverseInvValues (K := K) b) := by
  rcases h with h | h
  · exact Or.inl (Beli2009ValueSequenceEquivalent.reverseInv h)
  · exact Or.inr (IsBeli2009BinaryTransformation.reverseInv h)

theorem Beli2009BinaryReachable.reverseInv
    {N : Nat} {a b : Fin (N + 1) → Kˣ}
    (h : Beli2009BinaryReachable (K := K) a b) :
    Beli2009BinaryReachable (K := K)
      (reverseInvValues (K := K) a) (reverseInvValues (K := K) b) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      exact ih.tail (IsBeli2009BinaryStep.reverseInv hstep)

/-- Right-endpoint Corollary 8.10 together with its binary path. -/
structure ReachableCorollary810RightData
    {N : Nat} (b : BONG.GoodBONG q L (N + 2)) where
  data : b.Beli2019Corollary810RightData
  reachable : Beli2009BinaryReachable (K := K)
    (fun i ↦ b.valueUnit i) (fun i ↦ data.transformed.valueUnit i)

/-- Path-refined right-endpoint Corollary 8.10, obtained by transporting the
left-endpoint path through reverse duality. -/
theorem reachableCorollary810_right_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    {N : Nat} (b : BONG.GoodBONG q L (N + 2))
    (hresidueMore : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableCorollary810RightData b) := by
  rcases b.exists_reverseDual_with_alpha with
    ⟨c, _hcVectors, hcValuesRaw, hcOrders, _hcAlphas⟩
  have hcValues : ∀ j,
      c.valueUnit j = (b.valueUnit (Fin.rev j))⁻¹ := by
    intro j
    change c.toBONG.valueUnit j =
      (b.toBONG.valueUnit (Fin.rev j))⁻¹
    apply Units.ext
    exact hcValuesRaw j
  rcases reachableCorollary810_of_largeResidue c hresidueMore with ⟨R⟩
  let D := R.data
  rcases D.transformed.exists_reverseDual_with_alpha with
    ⟨e, _heVectors, heValuesRaw, heOrders, heAlphas⟩
  have heValues : ∀ j,
      e.valueUnit j = (D.transformed.valueUnit (Fin.rev j))⁻¹ := by
    intro j
    change e.toBONG.valueUnit j =
      (D.transformed.toBONG.valueUnit (Fin.rev j))⁻¹
    apply Units.ext
    exact heValuesRaw j
  let hbidual : Lattice.dualLattice q (Lattice.dualLattice q L) = L :=
    Lattice.dualLattice_dualLattice q L
  let transformed : BONG.GoodBONG q L (N + 2) :=
    e.castLattice hbidual
  have hrevLastValue : Fin.rev (Fin.last (N + 1)) =
      (0 : Fin (N + 2)) := by
    apply Fin.ext
    simp
  have hrevLastAlpha : Fin.rev (Fin.last N) =
      (0 : Fin (N + 1)) := by
    apply Fin.ext
    simp
  have hlastValue : transformed.valueUnit (Fin.last (N + 1)) =
      b.valueUnit (Fin.last (N + 1)) := by
    simp only [transformed, BONG.GoodBONG.valueUnit_castLattice]
    rw [heValues, hrevLastValue, D.headValue_eq, hcValues]
    have hrevZero : Fin.rev (0 : Fin (N + 2)) =
        Fin.last (N + 1) := by
      apply Fin.ext
      simp
    rw [hrevZero, inv_inv]
  have hlastBinary : transformed.lastBinaryAlpha =
      (transformed.alphaValue (Fin.last N) : WithTop ℚ) := by
    simp only [transformed, BONG.GoodBONG.lastBinaryAlpha,
      BONG.GoodBONG.adjacentBinaryAlpha_castLattice,
      BONG.GoodBONG.alphaValue_castLattice]
    calc
      e.lastBinaryAlpha = D.transformed.firstBinaryAlpha :=
        D.transformed.lastBinaryAlpha_eq_firstBinaryAlpha_of_reverseDual
          e heValues heOrders
      _ = (D.transformed.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) :=
        D.firstBinaryAlpha_eq
      _ = (e.alphaValue (Fin.last N) : WithTop ℚ) := by
        rw [heAlphas, hrevLastAlpha]
  have hreverseReach :=
    Beli2009BinaryReachable.reverseInv R.reachable
  have hsource : reverseInvValues (K := K) (fun i ↦ c.valueUnit i) =
      (fun i ↦ b.valueUnit i) := by
    funext i
    simp [reverseInvValues, hcValues]
  have htarget : reverseInvValues (K := K)
      (fun i ↦ D.transformed.valueUnit i) =
        (fun i ↦ transformed.valueUnit i) := by
    funext i
    simp [reverseInvValues, transformed, heValues]
  rw [hsource, htarget] at hreverseReach
  exact ⟨{
    data := {
      transformed := transformed
      lastValue_eq := hlastValue
      lastBinaryAlpha_eq := hlastBinary
    }
    reachable := hreverseReach
  }⟩

/-- For ternary good BONGs on one lattice, fixing the head value fixes the
square class, hence the defect and the literal alpha, of the final binary
edge.  The only global input is the unconditional determinant comparison. -/
theorem rankThree_lastBinaryAlpha_eq_of_headValue_eq
    (a b : BONG.GoodBONG q L 3)
    (hhead : a.valueUnit (0 : Fin 3) = b.valueUnit (0 : Fin 3)) :
    a.lastBinaryAlpha = b.lastBinaryAlpha := by
  have horders := a.order_invariant b
  have hfull : IsSquare (a.comparisonPrefixUnit b 3) :=
    Beli2009AmbientDeterminantLaws.fullComparison_isSquare
      (QuadraticSpace.isIsometric_refl q) a b
  have hfull' : IsSquare
      ((a.valueUnit 0 * a.valueUnit 1 * a.valueUnit 2) *
        (b.valueUnit 0 * b.valueUnit 1 * b.valueUnit 2)) := by
    simpa [BONG.GoodBONG.comparisonPrefixUnit,
      BONG.GoodBONG.prefixProduct,
      BONG.GoodBONG.valueUnit,
      BONG.prefixProduct_succ] using hfull
  have htail : IsSquare
      ((a.valueUnit 1 * a.valueUnit 2) *
        (b.valueUnit 1 * b.valueUnit 2)) := by
    have hheadSquare : IsSquare (a.valueUnit 0 ^ 2) :=
      ⟨a.valueUnit 0, pow_two _⟩
    have hquot := hfull'.div hheadSquare
    have heq :
        ((a.valueUnit 0 * a.valueUnit 1 * a.valueUnit 2) *
            (b.valueUnit 0 * b.valueUnit 1 * b.valueUnit 2)) /
              a.valueUnit 0 ^ 2 =
          (a.valueUnit 1 * a.valueUnit 2) *
            (b.valueUnit 1 * b.valueUnit 2) := by
      rw [hhead]
      simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]
    rw [heq] at hquot
    exact hquot
  have hadjacentSquare : IsSquare
      (a.adjacentProduct (1 : Fin 2) *
        b.adjacentProduct (1 : Fin 2)) := by
    simpa [BONG.GoodBONG.adjacentProduct] using htail
  have hquot : IsSquare
      (b.adjacentProduct (1 : Fin 2) /
        a.adjacentProduct (1 : Fin 2)) := by
    have hden : IsSquare (a.adjacentProduct (1 : Fin 2) ^ 2) :=
      ⟨a.adjacentProduct (1 : Fin 2), pow_two _⟩
    have h := hadjacentSquare.div hden
    have heq :
        (a.adjacentProduct (1 : Fin 2) *
            b.adjacentProduct (1 : Fin 2)) /
              a.adjacentProduct (1 : Fin 2) ^ 2 =
          b.adjacentProduct (1 : Fin 2) /
            a.adjacentProduct (1 : Fin 2) := by
      simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]
    rw [heq] at h
    exact h
  have hclass :
      squareClass K (b.adjacentProduct (1 : Fin 2)) =
        squareClass K (a.adjacentProduct (1 : Fin 2)) :=
    squareClass_eq_of_div_isSquare _ _ hquot
  have hdefect :
      a.adjacentDefect (1 : Fin 2) =
        b.adjacentDefect (1 : Fin 2) := by
    unfold BONG.GoodBONG.adjacentDefect BONG.GoodBONG.defectOrder
    rw [quadraticDefect_eq_of_squareClass_eq _ _ hclass.symm]
  unfold BONG.GoodBONG.lastBinaryAlpha
    BONG.GoodBONG.adjacentBinaryAlpha
    BONG.GoodBONG.halfGapCandidate
    BONG.GoodBONG.leftDefectCandidate
  have hdefectLast :
      a.adjacentDefect (Fin.last 1) =
        b.adjacentDefect (Fin.last 1) := by
    simpa using hdefect
  rw [horders (Fin.last 1).succ, horders (Fin.last 1).castSucc,
    hdefectLast]

/-- The dual ternary endpoint-preservation statement: fixing the last value
fixes the literal alpha of the first binary edge. -/
theorem rankThree_firstBinaryAlpha_eq_of_lastValue_eq
    (a b : BONG.GoodBONG q L 3)
    (hlast : a.valueUnit (2 : Fin 3) = b.valueUnit (2 : Fin 3)) :
    a.firstBinaryAlpha = b.firstBinaryAlpha := by
  have horders := a.order_invariant b
  have hfull : IsSquare (a.comparisonPrefixUnit b 3) :=
    Beli2009AmbientDeterminantLaws.fullComparison_isSquare
      (QuadraticSpace.isIsometric_refl q) a b
  have hfull' : IsSquare
      ((a.valueUnit 0 * a.valueUnit 1 * a.valueUnit 2) *
        (b.valueUnit 0 * b.valueUnit 1 * b.valueUnit 2)) := by
    simpa [BONG.GoodBONG.comparisonPrefixUnit,
      BONG.GoodBONG.prefixProduct,
      BONG.GoodBONG.valueUnit,
      BONG.prefixProduct_succ] using hfull
  have hheadPair : IsSquare
      ((a.valueUnit 0 * a.valueUnit 1) *
        (b.valueUnit 0 * b.valueUnit 1)) := by
    have hlastSquare : IsSquare (a.valueUnit 2 ^ 2) :=
      ⟨a.valueUnit 2, pow_two _⟩
    have hquot := hfull'.div hlastSquare
    have heq :
        ((a.valueUnit 0 * a.valueUnit 1 * a.valueUnit 2) *
            (b.valueUnit 0 * b.valueUnit 1 * b.valueUnit 2)) /
              a.valueUnit 2 ^ 2 =
          (a.valueUnit 0 * a.valueUnit 1) *
            (b.valueUnit 0 * b.valueUnit 1) := by
      rw [hlast]
      simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]
    rw [heq] at hquot
    exact hquot
  have hadjacentSquare : IsSquare
      (a.adjacentProduct (0 : Fin 2) *
        b.adjacentProduct (0 : Fin 2)) := by
    simpa [BONG.GoodBONG.adjacentProduct] using hheadPair
  have hquot : IsSquare
      (b.adjacentProduct (0 : Fin 2) /
        a.adjacentProduct (0 : Fin 2)) := by
    have hden : IsSquare (a.adjacentProduct (0 : Fin 2) ^ 2) :=
      ⟨a.adjacentProduct (0 : Fin 2), pow_two _⟩
    have h := hadjacentSquare.div hden
    have heq :
        (a.adjacentProduct (0 : Fin 2) *
            b.adjacentProduct (0 : Fin 2)) /
              a.adjacentProduct (0 : Fin 2) ^ 2 =
          b.adjacentProduct (0 : Fin 2) /
            a.adjacentProduct (0 : Fin 2) := by
      simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]
    rw [heq] at h
    exact h
  have hclass :
      squareClass K (b.adjacentProduct (0 : Fin 2)) =
        squareClass K (a.adjacentProduct (0 : Fin 2)) :=
    squareClass_eq_of_div_isSquare _ _ hquot
  have hdefect :
      a.adjacentDefect (0 : Fin 2) =
        b.adjacentDefect (0 : Fin 2) := by
    unfold BONG.GoodBONG.adjacentDefect BONG.GoodBONG.defectOrder
    rw [quadraticDefect_eq_of_squareClass_eq _ _ hclass.symm]
  unfold BONG.GoodBONG.firstBinaryAlpha
    BONG.GoodBONG.halfGapCandidate
    BONG.GoodBONG.leftDefectCandidate
  rw [horders (0 : Fin 2).succ, horders (0 : Fin 2).castSucc,
    hdefect]

/-- For ternary good BONGs on one lattice, equality of the final adjacent
defect already fixes the literal alpha of the final binary edge.  This is
the local form used to control the middle cut in a `0→1→0` detour. -/
theorem rankThree_lastBinaryAlpha_eq_of_lastAdjacentDefect_eq
    (a c : BONG.GoodBONG q L 3)
    (hdefect : a.adjacentDefect (1 : Fin 2) =
      c.adjacentDefect (1 : Fin 2)) :
    a.lastBinaryAlpha = c.lastBinaryAlpha := by
  have horders := a.order_invariant c
  unfold BONG.GoodBONG.lastBinaryAlpha
    BONG.GoodBONG.adjacentBinaryAlpha
    BONG.GoodBONG.halfGapCandidate
    BONG.GoodBONG.leftDefectCandidate
  have hdefectLast :
      a.adjacentDefect (Fin.last 1) =
        c.adjacentDefect (Fin.last 1) := by
    simpa using hdefect
  rw [horders (Fin.last 1).succ, horders (Fin.last 1).castSucc,
    hdefectLast]

/-- Symmetric local endpoint statement for the first binary edge. -/
theorem rankThree_firstBinaryAlpha_eq_of_firstAdjacentDefect_eq
    (a c : BONG.GoodBONG q L 3)
    (hdefect : a.adjacentDefect (0 : Fin 2) =
      c.adjacentDefect (0 : Fin 2)) :
    a.firstBinaryAlpha = c.firstBinaryAlpha := by
  have horders := a.order_invariant c
  unfold BONG.GoodBONG.firstBinaryAlpha
    BONG.GoodBONG.halfGapCandidate
    BONG.GoodBONG.leftDefectCandidate
  rw [horders (0 : Fin 2).succ, horders (0 : Fin 2).castSucc,
    hdefect]

/-- A ternary good BONG in which both literal binary edges realize their
corresponding global alphas, together with the binary-transformation path
from the original BONG. -/
structure ReachableRankThreeDoubleNormalForm
    (b : BONG.GoodBONG q L 3) where
  transformed : BONG.GoodBONG q L 3
  reachable : Beli2009BinaryReachable (K := K)
    (fun i ↦ b.valueUnit i) (fun i ↦ transformed.valueUnit i)
  firstBinaryAlpha_eq : transformed.firstBinaryAlpha =
    (transformed.alphaValue (0 : Fin 2) : WithTop ℚ)
  lastBinaryAlpha_eq : transformed.lastBinaryAlpha =
    (transformed.alphaValue (1 : Fin 2) : WithTop ℚ)

/-- Sequential left- and right-endpoint Corollary 8.10 normalizations give a
simultaneous ternary normal form.  Endpoint preservation shows that the
second normalization cannot destroy the first one. -/
theorem reachableRankThreeDoubleNormalForm_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (b : BONG.GoodBONG q L 3)
    (hresidueMore : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableRankThreeDoubleNormalForm b) := by
  rcases reachableCorollary810_of_largeResidue b hresidueMore with ⟨R₀⟩
  let c := R₀.data.transformed
  rcases reachableCorollary810_right_of_largeResidue c hresidueMore with
    ⟨R₁⟩
  let d := R₁.data.transformed
  have hlast : d.valueUnit (2 : Fin 3) = c.valueUnit (2 : Fin 3) := by
    simpa [c, d] using R₁.data.lastValue_eq
  have hfirstPreserved : d.firstBinaryAlpha = c.firstBinaryAlpha :=
    rankThree_firstBinaryAlpha_eq_of_lastValue_eq d c hlast
  have halphas : c.SameAlphas d := c.alpha_invariant d
  have hfirst : d.firstBinaryAlpha =
      (d.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    calc
      d.firstBinaryAlpha = c.firstBinaryAlpha := hfirstPreserved
      _ = (c.alphaValue (0 : Fin 2) : WithTop ℚ) := by
        simpa [c] using R₀.data.firstBinaryAlpha_eq
      _ = (d.alphaValue (0 : Fin 2) : WithTop ℚ) :=
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) (halphas 0)
  have hlastBinary : d.lastBinaryAlpha =
      (d.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    simpa [d] using R₁.data.lastBinaryAlpha_eq
  exact ⟨{
    transformed := d
    reachable := R₀.reachable.trans R₁.reachable
    firstBinaryAlpha_eq := hfirst
    lastBinaryAlpha_eq := hlastBinary
  }⟩

structure RankThreeComparisonData
    (a b : BONG.GoodBONG q L 3) where
  epsilon : valuationUnitSubgroup K
  eta : valuationUnitSubgroup K
  middleSquare : Kˣ
  epsilon_eq : (epsilon : Kˣ) = b.valueUnit 0 / a.valueUnit 0
  eta_eq : (eta : Kˣ) = b.valueUnit 2 / a.valueUnit 2
  middle_eq : b.valueUnit 1 =
    (epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 1 * middleSquare ^ 2
  middleSquare_isValuationUnit :
    IsValuationUnit K (middleSquare : K)
  epsilon_defect : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
    BONG.GoodBONG.defectOrder (K := K) (epsilon : Kˣ)
  eta_defect : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
    BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ)
  adjacent_hasse :
    hilbertSymbol K ((eta : Kˣ) * a.adjacentProduct (0 : Fin 2))
        ((epsilon : Kˣ) * a.adjacentProduct (1 : Fin 2)) =
      hilbertSymbol K (a.adjacentProduct (0 : Fin 2))
        (a.adjacentProduct (1 : Fin 2))

/-- When two ternary good BONGs belong to the same lattice, the canonical
unary segment of the second one is already realized by that second BONG.
Lemma 8.14 necessity therefore rules out every exceptional alternative for
this unary target.  Keeping this consequence explicit lets the path-refined
argument reuse the sharp full-defect bounds proved in the paper-facing
Lemma 8.14 development. -/
theorem not_lemma814Exceptional_firstUnarySegment_of_sameLattice
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    (a b : BONG.GoodBONG q L 3) :
    ¬a.Beli2019Lemma814Exceptional b.firstUnarySegment := by
  apply a.beli2019Lemma814_necessity b.firstUnarySegment
  exact ⟨{
    transformed := b
    firstValue_eq := b.firstUnarySegment_valueUnit_zero.symm
  }⟩

noncomputable def rankThreeComparisonData
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DiagonalIsometryInvariantLaws K]
    (a b : BONG.GoodBONG q L 3) :
    RankThreeComparisonData a b := by
  have conditions : ClassificationConditions a b :=
    (a.beli2009Theorem31_concrete
      (QuadraticSpace.isIsometric_refl q) b).mp
        (Lattice.isIsometric_refl q L)
  have horders := conditions.sameOrders
  let epsilonRaw : Kˣ := b.valueUnit 0 / a.valueUnit 0
  have hepsilonOrder : ordUnit K epsilonRaw = 0 := by
    dsimp only [epsilonRaw]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv]
    change b.order 0 + -a.order 0 = 0
    rw [horders 0]
    simp
  have hepsilonUnit : IsValuationUnit K (epsilonRaw : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K epsilonRaw).2 hepsilonOrder
  let epsilon : valuationUnitSubgroup K := ⟨epsilonRaw, hepsilonUnit⟩
  let etaRaw : Kˣ := b.valueUnit 2 / a.valueUnit 2
  have hetaOrder : ordUnit K etaRaw = 0 := by
    dsimp only [etaRaw]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv]
    change b.order 2 + -a.order 2 = 0
    rw [horders 2]
    simp
  have hetaUnit : IsValuationUnit K (etaRaw : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K etaRaw).2 hetaOrder
  let eta : valuationUnitSubgroup K := ⟨etaRaw, hetaUnit⟩
  have hfull : IsSquare (a.comparisonPrefixUnit b 3) :=
    Beli2009AmbientDeterminantLaws.fullComparison_isSquare
      (QuadraticSpace.isIsometric_refl q) a b
  have hfull' : IsSquare
      ((a.valueUnit 0 * a.valueUnit 1 * a.valueUnit 2) *
        (b.valueUnit 0 * b.valueUnit 1 * b.valueUnit 2)) := by
    simpa [BONG.GoodBONG.comparisonPrefixUnit,
      BONG.GoodBONG.prefixProduct, BONG.GoodBONG.valueUnit,
      BONG.prefixProduct_succ] using hfull
  let factor : Kˣ :=
    (epsilon : Kˣ) * (eta : Kˣ) *
      a.valueUnit 0 * a.valueUnit 1 * a.valueUnit 2
  have hfactorSquare : IsSquare (factor ^ 2) :=
    ⟨factor, pow_two _⟩
  have hmiddleSquare := hfull'.div hfactorSquare
  have hquotient :
      ((a.valueUnit 0 * a.valueUnit 1 * a.valueUnit 2) *
          (b.valueUnit 0 * b.valueUnit 1 * b.valueUnit 2)) /
            factor ^ 2 =
        b.valueUnit 1 /
          ((epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 1) := by
    dsimp only [factor, epsilon, eta, epsilonRaw, etaRaw]
    simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]
  rw [hquotient] at hmiddleSquare
  let middleSquare : Kˣ := Classical.choose hmiddleSquare
  have hmiddleSquareEq :
      b.valueUnit 1 /
          ((epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 1) =
        middleSquare * middleSquare :=
    Classical.choose_spec hmiddleSquare
  have hmiddle : b.valueUnit 1 =
      (epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 1 *
        middleSquare ^ 2 := by
    simp only [pow_two]
    rw [← hmiddleSquareEq]
    simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]
  have hmiddleSquareOrder : ordUnit K middleSquare = 0 := by
    have horder := congrArg (ordUnit K) hmiddle
    have hepsilonOrder' : ordUnit K (epsilon : Kˣ) = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K (epsilon : Kˣ)).1
        epsilon.property
    have hetaOrder' : ordUnit K (eta : Kˣ) = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K (eta : Kˣ)).1 eta.property
    rw [ordUnit_mul, ordUnit_mul, ordUnit_mul, ordUnit_pow,
      hepsilonOrder', hetaOrder'] at horder
    change b.order 1 = 0 + 0 + a.order 1 + 2 * ordUnit K middleSquare
      at horder
    rw [← horders 1] at horder
    omega
  have hmiddleSquareUnit : IsValuationUnit K (middleSquare : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K middleSquare).2
      hmiddleSquareOrder
  have hprefixZero : a.comparisonPrefixProduct b (0 : Fin 2) =
      (epsilon : Kˣ) * a.valueUnit 0 ^ 2 := by
    unfold BONG.GoodBONG.comparisonPrefixProduct
      BONG.GoodBONG.prefixProduct
    change a.toBONG.prefixProduct 1 * b.toBONG.prefixProduct 1 = _
    rw [a.toBONG.prefixProduct_succ 0 (by omega),
      b.toBONG.prefixProduct_succ 0 (by omega),
      a.toBONG.prefixProduct_zero, b.toBONG.prefixProduct_zero]
    dsimp only [epsilon, epsilonRaw]
    simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm,
      BONG.GoodBONG.valueUnit]
  have hepsilonDefect := conditions.prefixDefectBounds (0 : Fin 2)
  rw [hprefixZero, BONG.GoodBONG.defectOrder_mul_square] at hepsilonDefect
  have hprefixOne : a.comparisonPrefixProduct b (1 : Fin 2) =
      (eta : Kˣ) *
        ((epsilon : Kˣ) * a.valueUnit 0 * a.valueUnit 1 *
          middleSquare) ^ 2 := by
    unfold BONG.GoodBONG.comparisonPrefixProduct
      BONG.GoodBONG.prefixProduct
    change a.toBONG.prefixProduct 2 * b.toBONG.prefixProduct 2 = _
    rw [a.toBONG.prefixProduct_succ 1 (by omega),
      a.toBONG.prefixProduct_succ 0 (by omega),
      b.toBONG.prefixProduct_succ 1 (by omega),
      b.toBONG.prefixProduct_succ 0 (by omega),
      a.toBONG.prefixProduct_zero, b.toBONG.prefixProduct_zero]
    simp only [one_mul]
    change (a.valueUnit 0 * a.valueUnit 1) *
      (b.valueUnit 0 * b.valueUnit 1) = _
    rw [hmiddle]
    dsimp only [epsilon, epsilonRaw]
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_div_eq_div_val]
    field_simp
  have hetaDefect := conditions.prefixDefectBounds (1 : Fin 2)
  rw [hprefixOne, BONG.GoodBONG.defectOrder_mul_square] at hetaDefect
  let scaled := a.ternaryScaledValues (epsilon : Kˣ) (eta : Kˣ)
  let multipliers : Fin 3 → Kˣ := ![(1 : Kˣ), middleSquare, 1]
  have hpoint : ∀ i, b.valueUnit i = scaled i * multipliers i ^ 2 := by
    intro i
    fin_cases i
    · dsimp [scaled, multipliers]
      dsimp only [epsilon, epsilonRaw]
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    · simpa [scaled, multipliers, mul_assoc] using hmiddle
    · dsimp [scaled, multipliers]
      dsimp only [eta, etaRaw]
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hrepBScaled : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients b.valueUnit)
      (BONG.GoodBONG.diagonalUnitCoefficients scaled) :=
    Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
      b.valueUnit scaled multipliers hpoint
  have hrepAB : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients a.valueUnit)
      (BONG.GoodBONG.diagonalUnitCoefficients b.valueUnit) := by
    exact a.toBONG.diagonalRepresents_values b.toBONG
  have hhasseBScaled :=
    DiagonalIsometryInvariantLaws.hasse_eq b.valueUnit scaled hrepBScaled
  have hhasseAB :=
    DiagonalIsometryInvariantLaws.hasse_eq a.valueUnit b.valueUnit hrepAB
  have hhasseScaledA : diagonalHasseSymbol K scaled =
      diagonalHasseSymbol K a.valueUnit :=
    hhasseBScaled.symm.trans hhasseAB.symm
  have hadjacent :
      hilbertSymbol K ((eta : Kˣ) * a.adjacentProduct (0 : Fin 2))
          ((epsilon : Kˣ) * a.adjacentProduct (1 : Fin 2)) =
        hilbertSymbol K (a.adjacentProduct (0 : Fin 2))
          (a.adjacentProduct (1 : Fin 2)) := by
    rw [diagonalHasseSymbol_fin_three_eq_adjacent,
      diagonalHasseSymbol_fin_three_eq_adjacent] at hhasseScaledA
    have hfirst :
        -(scaled (0 : Fin 3) * scaled (1 : Fin 3)) =
          ((eta : Kˣ) * a.adjacentProduct (0 : Fin 2)) *
            (epsilon : Kˣ) ^ 2 := by
      apply Units.ext
      simp [scaled, BONG.GoodBONG.ternaryScaledValues,
        BONG.GoodBONG.adjacentProduct]
      ring
    have hsecond :
        -(scaled (1 : Fin 3) * scaled (2 : Fin 3)) =
          ((epsilon : Kˣ) * a.adjacentProduct (1 : Fin 2)) *
            (eta : Kˣ) ^ 2 := by
      apply Units.ext
      simp [scaled, BONG.GoodBONG.ternaryScaledValues,
        BONG.GoodBONG.adjacentProduct]
      ring
    rw [hfirst, hsecond, hilbertSymbol_mul_square_left,
      hilbertSymbol_mul_square_right] at hhasseScaledA
    rcases Int.units_eq_one_or (hilbertSymbol K (-1) (-1)) with h | h
    · rw [h] at hhasseScaledA
      simpa [BONG.GoodBONG.adjacentProduct] using hhasseScaledA
    · rw [h] at hhasseScaledA
      norm_num at hhasseScaledA ⊢
      simpa [BONG.GoodBONG.adjacentProduct] using hhasseScaledA
  exact {
    epsilon := epsilon
    eta := eta
    middleSquare := middleSquare
    epsilon_eq := rfl
    eta_eq := rfl
    middle_eq := hmiddle
    middleSquare_isValuationUnit := hmiddleSquareUnit
    epsilon_defect := hepsilonDefect
    eta_defect := hetaDefect
    adjacent_hasse := hadjacent
  }

/-- The exact ternary-scaled endpoint supplied by the comparison data differs
from the target BONG only by the valuation-unit square in the middle
coordinate. -/
theorem RankThreeComparisonData.scaled_equivalent
    (a b : BONG.GoodBONG q L 3) (D : RankThreeComparisonData a b) :
    Beli2009ValueSequenceEquivalent (K := K)
      (fun i ↦ a.ternaryScaledValues (D.epsilon : Kˣ) (D.eta : Kˣ) i)
      (fun i ↦ b.valueUnit i) := by
  intro i
  fin_cases i
  · change unitSquareClass K ((D.epsilon : Kˣ) * a.valueUnit 0) =
      unitSquareClass K (b.valueUnit 0)
    rw [D.epsilon_eq]
    simp
  · change unitSquareClass K
        ((D.epsilon : Kˣ) * (D.eta : Kˣ) * a.valueUnit 1) =
      unitSquareClass K (b.valueUnit 1)
    rw [D.middle_eq,
      unitSquareClass_mul_unit_square K
        ((D.epsilon : Kˣ) * (D.eta : Kˣ) * a.valueUnit 1)
        D.middleSquare D.middleSquare_isValuationUnit]
  · change unitSquareClass K ((D.eta : Kˣ) * a.valueUnit 2) =
      unitSquareClass K (b.valueUnit 2)
    rw [D.eta_eq]
    simp

/-- Direct left-to-right ternary connectivity.  Once the source first edge
and target last edge are normalized, a positive first Hilbert sign makes
both adjacent binary moves legal. -/
theorem reachable_rankThree_twoStep_zero_one
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a b : BONG.GoodBONG q L 3) (D : RankThreeComparisonData a b)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hlast : b.lastBinaryAlpha =
      (b.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hepsilonHilbert : hilbertSymbol K (D.epsilon : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = 1) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ b.valueUnit i) := by
  have hepsilonAlpha : a.adjacentBinaryAlpha (0 : Fin 2) =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    simpa only [BONG.GoodBONG.adjacentBinaryAlpha_zero] using hfirst
  have hepsilonHilbert' : hilbertSymbol K
      (a.adjacentProduct (0 : Fin 2)) (D.epsilon : Kˣ) = 1 := by
    rw [hilbertSymbol_comm K]
    exact hepsilonHilbert
  have hepsilonGroup : valuationUnitClassHom K D.epsilon ∈
      beliNormGeneratorGroup K
        (a.valueUnit (1 : Fin 3) / a.valueUnit (0 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (0 : Fin 2) D.epsilon
    · rw [hepsilonAlpha]
      exact D.epsilon_defect
    · exact hepsilonHilbert'
  rcases exists_goodBONG_binaryTransformation_exact a (0 : Fin 2)
      D.epsilon hepsilonGroup with ⟨c, hcValues⟩
  have hfirstStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ c.valueUnit i) :=
    ⟨0, D.epsilon, hepsilonGroup, hcValues⟩
  have hhead : c.valueUnit (0 : Fin 3) = b.valueUnit (0 : Fin 3) := by
    rw [congrFun hcValues (0 : Fin 3)]
    change (D.epsilon : Kˣ) * a.valueUnit 0 = b.valueUnit 0
    rw [D.epsilon_eq]
    simp
  have hlastPreserved :=
    rankThree_lastBinaryAlpha_eq_of_headValue_eq c b hhead
  have halphas : a.SameAlphas b := a.alpha_invariant b
  have hcLastAlpha : c.adjacentBinaryAlpha (1 : Fin 2) =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    calc
      c.adjacentBinaryAlpha (1 : Fin 2) = c.lastBinaryAlpha := rfl
      _ = b.lastBinaryAlpha := hlastPreserved
      _ = (b.alphaValue (1 : Fin 2) : WithTop ℚ) := hlast
      _ = (a.alphaValue (1 : Fin 2) : WithTop ℚ) :=
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) (halphas 1).symm
  have hetaHilbertBase : hilbertSymbol K (D.eta : Kˣ)
      ((D.epsilon : Kˣ) * a.adjacentProduct (1 : Fin 2)) = 1 :=
    hilbert_second_eq_one_of_ternary_hasse_of_first_eq_one
      (a.adjacentProduct (0 : Fin 2))
      (a.adjacentProduct (1 : Fin 2))
      (D.epsilon : Kˣ) (D.eta : Kˣ)
      D.adjacent_hasse hepsilonHilbert
  have hcAdjacent : c.adjacentProduct (1 : Fin 2) =
      (D.epsilon : Kˣ) * a.adjacentProduct (1 : Fin 2) := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hcValues (1 : Fin 2).castSucc,
      congrFun hcValues (1 : Fin 2).succ]
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]
  have hetaHilbert : hilbertSymbol K
      (c.adjacentProduct (1 : Fin 2)) (D.eta : Kˣ) = 1 := by
    rw [hcAdjacent, hilbertSymbol_comm K]
    exact hetaHilbertBase
  have hetaGroup : valuationUnitClassHom K D.eta ∈
      beliNormGeneratorGroup K
        (c.valueUnit (2 : Fin 3) / c.valueUnit (1 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      c (1 : Fin 2) D.eta
    · rw [hcLastAlpha]
      exact D.eta_defect
    · exact hetaHilbert
  rcases exists_goodBONG_binaryTransformation_exact c (1 : Fin 2)
      D.eta hetaGroup with ⟨d, hdValues⟩
  have hsecondStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ c.valueUnit i) (fun i ↦ d.valueUnit i) :=
    ⟨1, D.eta, hetaGroup, hdValues⟩
  have hdScaled : (fun i ↦ d.valueUnit i) =
      (fun i ↦ a.ternaryScaledValues
        (D.epsilon : Kˣ) (D.eta : Kˣ) i) := by
    calc
      (fun i ↦ d.valueUnit i) =
          beli2009BinaryTransformAt (fun i ↦ c.valueUnit i)
            (1 : Fin 2) (D.eta : Kˣ) := hdValues
      _ = beli2009BinaryTransformAt
          (beli2009BinaryTransformAt (fun i ↦ a.valueUnit i)
            (0 : Fin 2) (D.epsilon : Kˣ))
          (1 : Fin 2) (D.eta : Kˣ) := by rw [hcValues]
      _ = ![(D.epsilon : Kˣ) * a.valueUnit 0,
          (D.epsilon : Kˣ) * (D.eta : Kˣ) * a.valueUnit 1,
          (D.eta : Kˣ) * a.valueUnit 2] :=
        binaryTransform_twoStep_zero_one (K := K)
          (fun i ↦ a.valueUnit i) D.epsilon D.eta
      _ = (fun i ↦ a.ternaryScaledValues
          (D.epsilon : Kˣ) (D.eta : Kˣ) i) :=
        (ternaryScaledValues_eq_vector a D.epsilon D.eta).symm
  have hequivalent : Beli2009ValueSequenceEquivalent (K := K)
      (fun i ↦ d.valueUnit i) (fun i ↦ b.valueUnit i) := by
    rw [hdScaled]
    exact D.scaled_equivalent a b
  exact hfirstStep.reachable.trans
    (hsecondStep.reachable.trans hequivalent.reachable)

/-- Direct right-to-left ternary connectivity, symmetric to the preceding
theorem. -/
theorem reachable_rankThree_twoStep_one_zero
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a b : BONG.GoodBONG q L 3) (D : RankThreeComparisonData a b)
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hfirst : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hetaHilbert : hilbertSymbol K (D.eta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = 1) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ b.valueUnit i) := by
  have hetaAlpha : a.adjacentBinaryAlpha (1 : Fin 2) =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    exact hlast
  have hetaHilbert' : hilbertSymbol K
      (a.adjacentProduct (1 : Fin 2)) (D.eta : Kˣ) = 1 := by
    rw [hilbertSymbol_comm K]
    exact hetaHilbert
  have hetaGroup : valuationUnitClassHom K D.eta ∈
      beliNormGeneratorGroup K
        (a.valueUnit (2 : Fin 3) / a.valueUnit (1 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (1 : Fin 2) D.eta
    · rw [hetaAlpha]
      exact D.eta_defect
    · exact hetaHilbert'
  rcases exists_goodBONG_binaryTransformation_exact a (1 : Fin 2)
      D.eta hetaGroup with ⟨c, hcValues⟩
  have hfirstStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ c.valueUnit i) :=
    ⟨1, D.eta, hetaGroup, hcValues⟩
  have hlastValue : c.valueUnit (2 : Fin 3) =
      b.valueUnit (2 : Fin 3) := by
    rw [congrFun hcValues (2 : Fin 3)]
    change (D.eta : Kˣ) * a.valueUnit 2 = b.valueUnit 2
    rw [D.eta_eq]
    simp
  have hfirstPreserved :=
    rankThree_firstBinaryAlpha_eq_of_lastValue_eq c b hlastValue
  have halphas : a.SameAlphas b := a.alpha_invariant b
  have hcFirstAlpha : c.adjacentBinaryAlpha (0 : Fin 2) =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    calc
      c.adjacentBinaryAlpha (0 : Fin 2) = c.firstBinaryAlpha := rfl
      _ = b.firstBinaryAlpha := hfirstPreserved
      _ = (b.alphaValue (0 : Fin 2) : WithTop ℚ) := hfirst
      _ = (a.alphaValue (0 : Fin 2) : WithTop ℚ) :=
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) (halphas 0).symm
  have hepsilonHilbertBase : hilbertSymbol K (D.epsilon : Kˣ)
      ((D.eta : Kˣ) * a.adjacentProduct (0 : Fin 2)) = 1 :=
    hilbert_first_eq_one_of_ternary_hasse_of_second_eq_one
      (a.adjacentProduct (0 : Fin 2))
      (a.adjacentProduct (1 : Fin 2))
      (D.epsilon : Kˣ) (D.eta : Kˣ)
      D.adjacent_hasse hetaHilbert
  have hcAdjacent : c.adjacentProduct (0 : Fin 2) =
      (D.eta : Kˣ) * a.adjacentProduct (0 : Fin 2) := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hcValues (0 : Fin 2).castSucc,
      congrFun hcValues (0 : Fin 2).succ]
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]
    exact mul_comm _ _
  have hepsilonHilbert : hilbertSymbol K
      (c.adjacentProduct (0 : Fin 2)) (D.epsilon : Kˣ) = 1 := by
    rw [hcAdjacent, hilbertSymbol_comm K]
    exact hepsilonHilbertBase
  have hepsilonGroup : valuationUnitClassHom K D.epsilon ∈
      beliNormGeneratorGroup K
        (c.valueUnit (1 : Fin 3) / c.valueUnit (0 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      c (0 : Fin 2) D.epsilon
    · rw [hcFirstAlpha]
      exact D.epsilon_defect
    · exact hepsilonHilbert
  rcases exists_goodBONG_binaryTransformation_exact c (0 : Fin 2)
      D.epsilon hepsilonGroup with ⟨d, hdValues⟩
  have hsecondStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ c.valueUnit i) (fun i ↦ d.valueUnit i) :=
    ⟨0, D.epsilon, hepsilonGroup, hdValues⟩
  have hdScaled : (fun i ↦ d.valueUnit i) =
      (fun i ↦ a.ternaryScaledValues
        (D.epsilon : Kˣ) (D.eta : Kˣ) i) := by
    calc
      (fun i ↦ d.valueUnit i) =
          beli2009BinaryTransformAt (fun i ↦ c.valueUnit i)
            (0 : Fin 2) (D.epsilon : Kˣ) := hdValues
      _ = beli2009BinaryTransformAt
          (beli2009BinaryTransformAt (fun i ↦ a.valueUnit i)
            (1 : Fin 2) (D.eta : Kˣ))
          (0 : Fin 2) (D.epsilon : Kˣ) := by rw [hcValues]
      _ = ![(D.epsilon : Kˣ) * a.valueUnit 0,
          (D.epsilon : Kˣ) * (D.eta : Kˣ) * a.valueUnit 1,
          (D.eta : Kˣ) * a.valueUnit 2] :=
        binaryTransform_twoStep_one_zero (K := K)
          (fun i ↦ a.valueUnit i) D.epsilon D.eta
      _ = (fun i ↦ a.ternaryScaledValues
          (D.epsilon : Kˣ) (D.eta : Kˣ) i) :=
        (ternaryScaledValues_eq_vector a D.epsilon D.eta).symm
  have hequivalent : Beli2009ValueSequenceEquivalent (K := K)
      (fun i ↦ d.valueUnit i) (fun i ↦ b.valueUnit i) := by
    rw [hdScaled]
    exact D.scaled_equivalent a b
  exact hfirstStep.reachable.trans
    (hsecondStep.reachable.trans hequivalent.reachable)

/-- The literal last-binary alpha after a left-hand multiplier in ternary
rank.  The multiplier changes the last adjacent square class from `A₁` to
`mu * A₁`, while all coefficient orders stay fixed. -/
noncomputable def rankThreeLastBinaryAlphaAfterLeftMultiplier
    (a : BONG.GoodBONG q L 3) (mu : Kˣ) : WithTop ℚ :=
  min (a.halfGapCandidate (1 : Fin 2))
    (((((a.order (1 : Fin 2).succ -
          a.order (1 : Fin 2).castSucc : Int) : ℚ)) :
        WithTop ℚ) +
      BONG.GoodBONG.defectOrder (K := K)
        (mu * a.adjacentProduct (1 : Fin 2)))

/-- The `0→1→0` deadlock detour in its sharp dynamic form.  The first and
third multipliers split `epsilon` as `(epsilon * rho) * rho⁻¹`; the Hilbert
identities make all three moves norm-compatible.  Only the actual literal
last-binary alpha after the first move must be dominated by the middle
multiplier. -/
theorem reachable_rankThree_threeStep_zero_one_zero_of_dynamicLastAlpha
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a b : BONG.GoodBONG q L 3) (D : RankThreeComparisonData a b)
    (hfirstA : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hfirstB : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hepsilonDeadlock : hilbertSymbol K (D.epsilon : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (hetaDeadlock : hilbertSymbol K (D.eta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = -1)
    (rho : valuationUnitSubgroup K)
    (hrhoDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ))
    (hrhoEta : hilbertSymbol K (rho : Kˣ) (D.eta : Kˣ) = -1)
    (hrhoFirst : hilbertSymbol K (rho : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (hdynamic : rankThreeLastBinaryAlphaAfterLeftMultiplier
        a ((D.epsilon : Kˣ) * (rho : Kˣ)) ≤
      BONG.GoodBONG.defectOrder (K := K) (D.eta : Kˣ)) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ b.valueUnit i) := by
  let mu : valuationUnitSubgroup K := D.epsilon * rho
  let nu : valuationUnitSubgroup K := D.epsilon / mu
  have hepsilonEta : hilbertSymbol K (D.epsilon : Kˣ)
      (D.eta : Kˣ) = 1 :=
    hilbert_epsilon_eta_eq_one_of_ternary_scaling_deadlock
      (a.adjacentProduct (0 : Fin 2))
      (a.adjacentProduct (1 : Fin 2))
      (D.epsilon : Kˣ) (D.eta : Kˣ)
      hepsilonDeadlock hetaDeadlock D.adjacent_hasse
  have hdetour := ternaryDetour_hilbert_conditions
    (K := K) (a.adjacentProduct (0 : Fin 2))
      (a.adjacentProduct (1 : Fin 2))
      (D.epsilon : Kˣ) (D.eta : Kˣ) (rho : Kˣ)
      hepsilonDeadlock hetaDeadlock hepsilonEta hrhoEta hrhoFirst
  have hmuDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) := by
    exact (le_min D.epsilon_defect hrhoDepth).trans
      (BONG.GoodBONG.defectOrder_mul_ge_min
        (K := K) (D.epsilon : Kˣ) (rho : Kˣ))
  have hmuHilbert : hilbertSymbol K
      (a.adjacentProduct (0 : Fin 2)) (mu : Kˣ) = 1 := by
    rw [hilbertSymbol_comm K]
    simpa only [mu, Subgroup.coe_mul] using hdetour.1
  have hmuGroup : valuationUnitClassHom K mu ∈
      beliNormGeneratorGroup K
        (a.valueUnit (1 : Fin 3) / a.valueUnit (0 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (0 : Fin 2) mu
    · simpa only [BONG.GoodBONG.adjacentBinaryAlpha_zero, hfirstA]
      using hmuDepth
    · exact hmuHilbert
  rcases exists_goodBONG_binaryTransformation_exact a (0 : Fin 2)
      mu hmuGroup with ⟨c, hcValues⟩
  have hcAdjacent : c.adjacentProduct (1 : Fin 2) =
      (mu : Kˣ) * a.adjacentProduct (1 : Fin 2) := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hcValues (1 : Fin 2).castSucc,
      congrFun hcValues (1 : Fin 2).succ]
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]
  have hcLastAlpha : c.adjacentBinaryAlpha (1 : Fin 2) =
      rankThreeLastBinaryAlphaAfterLeftMultiplier
        a ((D.epsilon : Kˣ) * (rho : Kˣ)) := by
    have horders := a.order_invariant c
    have horderOne : c.order (1 : Fin 2).castSucc =
        a.order (1 : Fin 2).castSucc :=
      (horders (1 : Fin 2).castSucc).symm
    have horderTwo : c.order (1 : Fin 2).succ =
        a.order (1 : Fin 2).succ :=
      (horders (1 : Fin 2).succ).symm
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankThreeLastBinaryAlphaAfterLeftMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [horderTwo, horderOne, hcAdjacent]
    rfl
  have hcLastAlphaLe : c.adjacentBinaryAlpha (1 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (D.eta : Kˣ) := by
    rw [hcLastAlpha]
    exact hdynamic
  have hetaHilbert : hilbertSymbol K
      (c.adjacentProduct (1 : Fin 2)) (D.eta : Kˣ) = 1 := by
    rw [hcAdjacent, hilbertSymbol_comm K]
    simpa only [mu, Subgroup.coe_mul] using hdetour.2.1
  have hetaGroup : valuationUnitClassHom K D.eta ∈
      beliNormGeneratorGroup K
        (c.valueUnit (2 : Fin 3) / c.valueUnit (1 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      c (1 : Fin 2) D.eta
    · exact hcLastAlphaLe
    · exact hetaHilbert
  rcases exists_goodBONG_binaryTransformation_exact c (1 : Fin 2)
      D.eta hetaGroup with ⟨d, hdValues⟩
  have hdLastValue : d.valueUnit (2 : Fin 3) =
      b.valueUnit (2 : Fin 3) := by
    calc
      d.valueUnit (2 : Fin 3) =
          (D.eta : Kˣ) * c.valueUnit (2 : Fin 3) := by
        rw [congrFun hdValues (2 : Fin 3)]
        rfl
      _ = (D.eta : Kˣ) * a.valueUnit (2 : Fin 3) := by
        rw [congrFun hcValues (2 : Fin 3)]
        simp [beli2009BinaryTransformAt]
      _ = b.valueUnit (2 : Fin 3) := by
        rw [D.eta_eq]
        simp
  have hdFirstPreserved :=
    rankThree_firstBinaryAlpha_eq_of_lastValue_eq d b hdLastValue
  have habAlphas : a.SameAlphas b := a.alpha_invariant b
  have hdFirstAlpha : d.adjacentBinaryAlpha (0 : Fin 2) =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    calc
      d.adjacentBinaryAlpha (0 : Fin 2) = d.firstBinaryAlpha := rfl
      _ = b.firstBinaryAlpha := hdFirstPreserved
      _ = (b.alphaValue (0 : Fin 2) : WithTop ℚ) := hfirstB
      _ = (a.alphaValue (0 : Fin 2) : WithTop ℚ) :=
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) (habAlphas 0).symm
  have hnuRho : (nu : Kˣ) = (rho : Kˣ)⁻¹ := by
    dsimp only [nu, mu]
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hnuDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (nu : Kˣ) := by
    rw [hnuRho, BONG.GoodBONG.defectOrder_inv]
    exact hrhoDepth
  have hdAdjacent : d.adjacentProduct (0 : Fin 2) =
      ((D.eta : Kˣ) * a.adjacentProduct (0 : Fin 2)) *
        (mu : Kˣ) ^ 2 := by
    have hdZero : d.valueUnit (0 : Fin 3) =
        c.valueUnit (0 : Fin 3) := by
      rw [congrFun hdValues (0 : Fin 3)]
      simp [beli2009BinaryTransformAt]
    have hdOne : d.valueUnit (1 : Fin 3) =
        (D.eta : Kˣ) * c.valueUnit (1 : Fin 3) := by
      rw [congrFun hdValues (1 : Fin 3)]
      rfl
    have hcZero : c.valueUnit (0 : Fin 3) =
        (mu : Kˣ) * a.valueUnit (0 : Fin 3) := by
      rw [congrFun hcValues (0 : Fin 3)]
      rfl
    have hcOne : c.valueUnit (1 : Fin 3) =
        (mu : Kˣ) * a.valueUnit (1 : Fin 3) := by
      rw [congrFun hcValues (1 : Fin 3)]
      rfl
    have hcastZero : (Fin.castSucc (0 : Fin 2) : Fin 3) =
        (0 : Fin 3) := rfl
    have hsuccZero : (Fin.succ (0 : Fin 2) : Fin 3) =
        (1 : Fin 3) := rfl
    unfold BONG.GoodBONG.adjacentProduct
    rw [hcastZero, hsuccZero, hdZero, hdOne, hcZero, hcOne]
    apply Units.ext
    simp [pow_two]
    ring
  have hnuHilbert : hilbertSymbol K
      (d.adjacentProduct (0 : Fin 2)) (nu : Kˣ) = 1 := by
    rw [hdAdjacent, hilbertSymbol_mul_square_left, hnuRho,
      hilbertSymbol_comm K]
    exact hdetour.2.2
  have hnuGroup : valuationUnitClassHom K nu ∈
      beliNormGeneratorGroup K
        (d.valueUnit (1 : Fin 3) / d.valueUnit (0 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      d (0 : Fin 2) nu
    · rw [hdFirstAlpha]
      exact hnuDepth
    · exact hnuHilbert
  have hetaRaw : valuationUnitClassHom K D.eta ∈
      beliNormGeneratorGroup K
        (beli2009BinaryTransformAt (fun i ↦ a.valueUnit i)
            (0 : Fin 2) (mu : Kˣ) (2 : Fin 3) /
          beli2009BinaryTransformAt (fun i ↦ a.valueUnit i)
            (0 : Fin 2) (mu : Kˣ) (1 : Fin 3)) := by
    rw [← congrFun hcValues (2 : Fin 3),
      ← congrFun hcValues (1 : Fin 3)]
    exact hetaGroup
  have hnuRaw : valuationUnitClassHom K nu ∈
      beliNormGeneratorGroup K
        (beli2009BinaryTransformAt
              (beli2009BinaryTransformAt (fun i ↦ a.valueUnit i)
                (0 : Fin 2) (mu : Kˣ))
              (1 : Fin 2) (D.eta : Kˣ) (1 : Fin 3) /
          beli2009BinaryTransformAt
              (beli2009BinaryTransformAt (fun i ↦ a.valueUnit i)
                (0 : Fin 2) (mu : Kˣ))
              (1 : Fin 2) (D.eta : Kˣ) (0 : Fin 3)) := by
    have hdValuesRaw : (fun j ↦ d.valueUnit j) =
        beli2009BinaryTransformAt
          (beli2009BinaryTransformAt (fun j ↦ a.valueUnit j)
            (0 : Fin 2) (mu : Kˣ))
          (1 : Fin 2) (D.eta : Kˣ) := by
      rw [hdValues, hcValues]
    rw [← congrFun hdValuesRaw (1 : Fin 3),
      ← congrFun hdValuesRaw (0 : Fin 3)]
    exact hnuGroup
  have hreach := reachable_threeStep_zero_one_zero
    (K := K) (fun i ↦ a.valueUnit i) mu D.eta nu
      hmuGroup hetaRaw hnuRaw
  have hreachScaled : Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i)
      (fun i ↦ a.ternaryScaledValues
        (D.epsilon : Kˣ) (D.eta : Kˣ) i) := by
    have hnuDef : nu = D.epsilon / mu := rfl
    rw [hnuDef,
      binaryTransform_threeStep_zero_one_zero
        (K := K) (fun i ↦ a.valueUnit i) mu D.eta D.epsilon,
      ← ternaryScaledValues_eq_vector a D.epsilon D.eta] at hreach
    exact hreach
  exact hreachScaled.trans (D.scaled_equivalent a b).reachable

/-- If the normalized last alpha is already bounded by its half-gap term,
the sharp dynamic hypothesis of the `0→1→0` detour is automatic. -/
theorem reachable_rankThree_threeStep_zero_one_zero_of_lastHalfGapBound
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a b : BONG.GoodBONG q L 3) (D : RankThreeComparisonData a b)
    (hfirstA : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hfirstB : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hepsilonDeadlock : hilbertSymbol K (D.epsilon : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (hetaDeadlock : hilbertSymbol K (D.eta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = -1)
    (rho : valuationUnitSubgroup K)
    (hrhoDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ))
    (hrhoEta : hilbertSymbol K (rho : Kˣ) (D.eta : Kˣ) = -1)
    (hrhoFirst : hilbertSymbol K (rho : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (hhalfGap : a.halfGapCandidate (1 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (D.eta : Kˣ)) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ b.valueUnit i) := by
  apply reachable_rankThree_threeStep_zero_one_zero_of_dynamicLastAlpha
    a b D hfirstA hfirstB hepsilonDeadlock hetaDeadlock rho
      hrhoDepth hrhoEta hrhoFirst
  unfold rankThreeLastBinaryAlphaAfterLeftMultiplier
  exact (min_le_left _ _).trans hhalfGap

/-- At equal outer order, Remark 8.7 converts an exact transformed last
adjacent defect `alpha₀` into the dynamic `alpha₁` bound needed by the
`0→1→0` detour. -/
theorem reachable_rankThree_threeStep_zero_one_zero_of_lastProductAlpha
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a b : BONG.GoodBONG q L 3) (D : RankThreeComparisonData a b)
    (hfirstA : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hfirstB : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hepsilonDeadlock : hilbertSymbol K (D.epsilon : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (hetaDeadlock : hilbertSymbol K (D.eta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = -1)
    (rho : valuationUnitSubgroup K)
    (hrhoDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ))
    (hrhoEta : hilbertSymbol K (rho : Kˣ) (D.eta : Kˣ) = -1)
    (hrhoFirst : hilbertSymbol K (rho : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hproduct : BONG.GoodBONG.defectOrder (K := K)
        (((D.epsilon : Kˣ) * (rho : Kˣ)) *
          a.adjacentProduct (1 : Fin 2)) =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ)) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ b.valueUnit i) := by
  apply reachable_rankThree_threeStep_zero_one_zero_of_dynamicLastAlpha
    a b D hfirstA hfirstB hepsilonDeadlock hetaDeadlock rho
      hrhoDepth hrhoEta hrhoFirst
  refine (min_le_right _ _).trans ?_
  rw [hproduct]
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [BONG.GoodBONG.remark87PreviousValue,
      BONG.GoodBONG.remark87NextValue] using houter)
  have hrelation :
      (((((a.order (2 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ)) :
          WithTop ℚ) +
        (a.alphaValue (0 : Fin 2) : WithTop ℚ)) =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    have h := hremark.currentAlpha_eq
    change a.alphaValue (1 : Fin 2) =
      ((a.order (0 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ) +
        a.alphaValue (0 : Fin 2) at h
    have h' := congrArg (fun x : ℚ => (x : WithTop ℚ)) h
    rw [houter] at h'
    simpa only [WithTop.coe_add, WithTop.coe_sub, Int.cast_sub,
      Int.cast_ofNat] using h'.symm
  exact hrelation.le.trans D.eta_defect

/-- The two-character Hilbert choice supplies the auxiliary multiplier for
the `0→1→0` detour whenever a reference depth satisfies the two standard
defect-sum bounds. -/
theorem reachable_rankThree_threeStep_zero_one_zero_of_lastHalfGapReference
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a b : BONG.GoodBONG q L 3) (D : RankThreeComparisonData a b)
    (hfirstA : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hfirstB : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hepsilonDeadlock : hilbertSymbol K (D.epsilon : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (hetaDeadlock : hilbertSymbol K (D.eta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = -1)
    (reference : Kˣ)
    (hrefUnit : IsValuationUnit K (reference : K))
    (hrefDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) reference)
    (hsumEta : quadraticDefect K (D.eta : Kˣ) +
        quadraticDefect K reference ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hsumFirst : quadraticDefect K (a.adjacentProduct (0 : Fin 2)) +
        quadraticDefect K reference ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hhalfGap : a.halfGapCandidate (1 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (D.eta : Kˣ)) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ b.valueUnit i) := by
  have hsumProduct : quadraticDefect K
        ((D.eta : Kˣ) *
          ((D.eta : Kˣ) * a.adjacentProduct (0 : Fin 2))) +
        quadraticDefect K reference ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    have hsquare : (D.eta : Kˣ) *
        ((D.eta : Kˣ) * a.adjacentProduct (0 : Fin 2)) =
      a.adjacentProduct (0 : Fin 2) * (D.eta : Kˣ) ^ 2 := by
      simp only [pow_two, mul_assoc, mul_left_comm, mul_comm]
    rw [hsquare, quadraticDefect_mul_square]
    exact hsumFirst
  rcases exists_valuationUnit_hilbert_neg_one_of_two_sums_le
      (D.eta : Kˣ)
      ((D.eta : Kˣ) * a.adjacentProduct (0 : Fin 2))
      reference hrefUnit hsumEta hsumProduct with
    ⟨rhoRaw, hrhoUnit, hrhoDepthRaw, hetaRho, hproductRho⟩
  let rho : valuationUnitSubgroup K := ⟨rhoRaw, hrhoUnit⟩
  have hrhoDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ) :=
    hrefDepth.trans (by
      simpa only [rho, Subgroup.coe_mk] using hrhoDepthRaw)
  have hrhoEta : hilbertSymbol K (rho : Kˣ) (D.eta : Kˣ) = -1 := by
    rw [hilbertSymbol_comm K]
    simpa only [rho, Subgroup.coe_mk] using hetaRho
  have hrhoFirst : hilbertSymbol K (rho : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1 := by
    have hproductRho' : hilbertSymbol K
        ((D.eta : Kˣ) * a.adjacentProduct (0 : Fin 2))
        (rho : Kˣ) = 1 := by
      simpa only [rho, Subgroup.coe_mk] using hproductRho
    rw [hilbertSymbol_mul_left,
      show hilbertSymbol K (D.eta : Kˣ) (rho : Kˣ) = -1 by
        simpa only [rho, Subgroup.coe_mk] using hetaRho] at hproductRho'
    rw [hilbertSymbol_comm K]
    have hcancel := congrArg (fun z : ℤˣ => (-1 : ℤˣ) * z) hproductRho'
    simpa [mul_assoc] using hcancel
  exact reachable_rankThree_threeStep_zero_one_zero_of_lastHalfGapBound
    a b D hfirstA hfirstB hepsilonDeadlock hetaDeadlock rho
      hrhoDepth hrhoEta hrhoFirst hhalfGap

/-- Compatibility form of the left-to-right ternary detour.  Preserving the
last adjacent defect is sufficient for the sharp dynamic hypothesis. -/
theorem reachable_rankThree_threeStep_zero_one_zero_of_defectPreserved
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a b : BONG.GoodBONG q L 3) (D : RankThreeComparisonData a b)
    (hfirstA : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hlastA : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hfirstB : b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hepsilonDeadlock : hilbertSymbol K (D.epsilon : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (hetaDeadlock : hilbertSymbol K (D.eta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = -1)
    (rho : valuationUnitSubgroup K)
    (hrhoDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ))
    (hrhoEta : hilbertSymbol K (rho : Kˣ) (D.eta : Kˣ) = -1)
    (hrhoFirst : hilbertSymbol K (rho : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (hpreserve : BONG.GoodBONG.defectOrder (K := K)
        (((D.epsilon : Kˣ) * (rho : Kˣ)) *
          a.adjacentProduct (1 : Fin 2)) =
      BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (1 : Fin 2))) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ b.valueUnit i) := by
  apply reachable_rankThree_threeStep_zero_one_zero_of_dynamicLastAlpha
    a b D hfirstA hfirstB hepsilonDeadlock hetaDeadlock rho
      hrhoDepth hrhoEta hrhoFirst
  have hdynamicEq : rankThreeLastBinaryAlphaAfterLeftMultiplier
      a ((D.epsilon : Kˣ) * (rho : Kˣ)) = a.lastBinaryAlpha := by
    unfold rankThreeLastBinaryAlphaAfterLeftMultiplier
      BONG.GoodBONG.lastBinaryAlpha
      BONG.GoodBONG.adjacentBinaryAlpha
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    have hlastIndex : (Fin.last 1 : Fin 2) = (1 : Fin 2) := by
      apply Fin.ext
      simp
    rw [hlastIndex, hpreserve]
  rw [hdynamicEq, hlastA]
  exact D.eta_defect

/-- The literal first-binary alpha after a right-hand multiplier in ternary
rank.  The multiplier changes the first adjacent square class from `A₀` to
`theta * A₀`, while all coefficient orders stay fixed. -/
noncomputable def rankThreeFirstBinaryAlphaAfterRightMultiplier
    (a : BONG.GoodBONG q L 3) (theta : Kˣ) : WithTop ℚ :=
  min (a.halfGapCandidate (0 : Fin 2))
    (((((a.order (0 : Fin 2).succ -
          a.order (0 : Fin 2).castSucc : Int) : ℚ)) :
        WithTop ℚ) +
      BONG.GoodBONG.defectOrder (K := K)
        (theta * a.adjacentProduct (0 : Fin 2)))

/-- The symmetric `1→0→1` deadlock detour in its sharp dynamic form.
The initial right-hand move only has to make the *new literal first-binary
alpha* no larger than the defect of `epsilon`; equality of the old and new
first adjacent defects is unnecessary.  The final dynamic binary block is
compared with the target normalized last edge.

This is the form needed at the equal-defect boundary: Beli's Section 8
choices can lower the first adjacent defect to a different alpha and still
make the middle left-hand move legal. -/
theorem reachable_rankThree_threeStep_one_zero_one_of_dynamicFirstAlpha
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a b : BONG.GoodBONG q L 3) (D : RankThreeComparisonData a b)
    (hlastA : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hlastB : b.lastBinaryAlpha =
      (b.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hepsilonDeadlock : hilbertSymbol K (D.epsilon : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (theta : valuationUnitSubgroup K)
    (hthetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
    (hthetaLast : hilbertSymbol K (theta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = 1)
    (hthetaEpsilon : hilbertSymbol K (theta : Kˣ)
      (D.epsilon : Kˣ) = -1)
    (hdynamic : rankThreeFirstBinaryAlphaAfterRightMultiplier
        a (theta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (D.epsilon : Kˣ)) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ b.valueUnit i) := by
  have hthetaHilbert : hilbertSymbol K
      (a.adjacentProduct (1 : Fin 2)) (theta : Kˣ) = 1 := by
    rw [hilbertSymbol_comm K]
    exact hthetaLast
  have hthetaGroup : valuationUnitClassHom K theta ∈
      beliNormGeneratorGroup K
        (a.valueUnit (2 : Fin 3) / a.valueUnit (1 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (1 : Fin 2) theta
    · change a.lastBinaryAlpha ≤
        BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ)
      rw [hlastA]
      exact hthetaDepth
    · exact hthetaHilbert
  rcases exists_goodBONG_binaryTransformation_exact a (1 : Fin 2)
      theta hthetaGroup with ⟨c, hcValues⟩
  have hthetaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ c.valueUnit i) :=
    ⟨1, theta, hthetaGroup, hcValues⟩
  have hcAdjacent : c.adjacentProduct (0 : Fin 2) =
      (theta : Kˣ) * a.adjacentProduct (0 : Fin 2) := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hcValues (0 : Fin 2).castSucc,
      congrFun hcValues (0 : Fin 2).succ]
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]
    exact mul_comm _ _
  have hcFirstAlpha : c.adjacentBinaryAlpha (0 : Fin 2) =
      rankThreeFirstBinaryAlphaAfterRightMultiplier a (theta : Kˣ) := by
    have horders := a.order_invariant c
    have horderZero : c.order (0 : Fin 2).castSucc =
        a.order (0 : Fin 2).castSucc :=
      (horders (0 : Fin 2).castSucc).symm
    have horderOne : c.order (0 : Fin 2).succ =
        a.order (0 : Fin 2).succ :=
      (horders (0 : Fin 2).succ).symm
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankThreeFirstBinaryAlphaAfterRightMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [horderOne, horderZero, hcAdjacent]
  have hcFirstAlphaLe : c.adjacentBinaryAlpha (0 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (D.epsilon : Kˣ) := by
    rw [hcFirstAlpha]
    exact hdynamic
  have hepsilonHilbert : hilbertSymbol K
      (c.adjacentProduct (0 : Fin 2)) (D.epsilon : Kˣ) = 1 := by
    rw [hcAdjacent, hilbertSymbol_mul_left, hthetaEpsilon,
      hilbertSymbol_comm K (a.adjacentProduct (0 : Fin 2))
        (D.epsilon : Kˣ), hepsilonDeadlock]
    norm_num
  have hepsilonGroup : valuationUnitClassHom K D.epsilon ∈
      beliNormGeneratorGroup K
        (c.valueUnit (1 : Fin 3) / c.valueUnit (0 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      c (0 : Fin 2) D.epsilon
    · exact hcFirstAlphaLe
    · exact hepsilonHilbert
  rcases exists_goodBONG_binaryTransformation_exact c (0 : Fin 2)
      D.epsilon hepsilonGroup with ⟨d, hdValues⟩
  have hepsilonStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ c.valueUnit i) (fun i ↦ d.valueUnit i) :=
    ⟨0, D.epsilon, hepsilonGroup, hdValues⟩
  have hdAdjacent : d.adjacentProduct (1 : Fin 2) =
      ((D.epsilon : Kˣ) * a.adjacentProduct (1 : Fin 2)) *
        (theta : Kˣ) ^ 2 := by
    have hdOne : d.valueUnit (1 : Fin 3) =
        (D.epsilon : Kˣ) * c.valueUnit (1 : Fin 3) := by
      rw [congrFun hdValues (1 : Fin 3)]
      rfl
    have hdTwo : d.valueUnit (2 : Fin 3) = c.valueUnit (2 : Fin 3) := by
      rw [congrFun hdValues (2 : Fin 3)]
      simp [beli2009BinaryTransformAt]
    have hcOne : c.valueUnit (1 : Fin 3) =
        (theta : Kˣ) * a.valueUnit (1 : Fin 3) := by
      rw [congrFun hcValues (1 : Fin 3)]
      rfl
    have hcTwo : c.valueUnit (2 : Fin 3) =
        (theta : Kˣ) * a.valueUnit (2 : Fin 3) := by
      rw [congrFun hcValues (2 : Fin 3)]
      rfl
    unfold BONG.GoodBONG.adjacentProduct
    change -(d.valueUnit (1 : Fin 3) * d.valueUnit (2 : Fin 3)) = _
    rw [hdOne, hdTwo, hcOne, hcTwo]
    apply Units.ext
    simp [pow_two]
    ring
  have hbAdjacent : b.adjacentProduct (1 : Fin 2) =
      ((D.epsilon : Kˣ) * a.adjacentProduct (1 : Fin 2)) *
        ((D.eta : Kˣ) * D.middleSquare) ^ 2 := by
    unfold BONG.GoodBONG.adjacentProduct
    change -(b.valueUnit (1 : Fin 3) * b.valueUnit (2 : Fin 3)) = _
    rw [D.middle_eq]
    have hbLast : b.valueUnit (2 : Fin 3) =
        (D.eta : Kˣ) * a.valueUnit (2 : Fin 3) := by
      rw [D.eta_eq]
      simp
    rw [hbLast]
    apply Units.ext
    simp [pow_two]
    ring
  have hdbDefect : d.adjacentDefect (1 : Fin 2) =
      b.adjacentDefect (1 : Fin 2) := by
    unfold BONG.GoodBONG.adjacentDefect
    rw [hdAdjacent, hbAdjacent,
      BONG.GoodBONG.defectOrder_mul_square,
      BONG.GoodBONG.defectOrder_mul_square]
  have hdLastPreserved : d.lastBinaryAlpha = b.lastBinaryAlpha :=
    rankThree_lastBinaryAlpha_eq_of_lastAdjacentDefect_eq d b hdbDefect
  have hdbAlphas : d.SameAlphas b := d.alpha_invariant b
  have hdLastAlpha : d.adjacentBinaryAlpha (1 : Fin 2) =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    have habAlphas : a.SameAlphas b := a.alpha_invariant b
    calc
      d.adjacentBinaryAlpha (1 : Fin 2) = d.lastBinaryAlpha := rfl
      _ = b.lastBinaryAlpha := hdLastPreserved
      _ = (b.alphaValue (1 : Fin 2) : WithTop ℚ) := hlastB
      _ = (a.alphaValue (1 : Fin 2) : WithTop ℚ) :=
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) (habAlphas 1).symm
  let xi : valuationUnitSubgroup K := D.eta / theta
  have hthetaInvDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) ((theta : Kˣ)⁻¹) := by
    rw [BONG.GoodBONG.defectOrder_inv]
    exact hthetaDepth
  have hxiDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (xi : Kˣ) := by
    have hmin := le_min D.eta_defect hthetaInvDepth
    change (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        ((D.eta : Kˣ) * (theta : Kˣ)⁻¹)
    exact hmin.trans
      (BONG.GoodBONG.defectOrder_mul_ge_min
        (K := K) (D.eta : Kˣ) ((theta : Kˣ)⁻¹))
  have hthirdBase : hilbertSymbol K (D.eta / (theta : Kˣ))
      ((D.epsilon : Kˣ) * a.adjacentProduct (1 : Fin 2)) = 1 := by
    apply hilbert_third_eq_one_of_ternary_hasse
      (K := K) (a.adjacentProduct (0 : Fin 2))
        (a.adjacentProduct (1 : Fin 2)) (theta : Kˣ)
        (D.epsilon : Kˣ) (D.eta : Kˣ)
        D.adjacent_hasse hthetaLast
    rw [hilbertSymbol_mul_right,
      hilbertSymbol_comm K (D.epsilon : Kˣ) (theta : Kˣ),
      hthetaEpsilon, hepsilonDeadlock]
    norm_num
  have hxiHilbert : hilbertSymbol K
      (d.adjacentProduct (1 : Fin 2)) (xi : Kˣ) = 1 := by
    rw [hdAdjacent, hilbertSymbol_mul_square_left, hilbertSymbol_comm K]
    simpa only [xi, Subgroup.coe_div] using hthirdBase
  have hxiGroup : valuationUnitClassHom K xi ∈
      beliNormGeneratorGroup K
        (d.valueUnit (2 : Fin 3) / d.valueUnit (1 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      d (1 : Fin 2) xi
    · rw [hdLastAlpha]
      exact hxiDepth
    · exact hxiHilbert
  rcases exists_goodBONG_binaryTransformation_exact d (1 : Fin 2)
      xi hxiGroup with ⟨e, heValues⟩
  have hxiStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ d.valueUnit i) (fun i ↦ e.valueUnit i) :=
    ⟨1, xi, hxiGroup, heValues⟩
  have heScaled : (fun i ↦ e.valueUnit i) =
      (fun i ↦ a.ternaryScaledValues
        (D.epsilon : Kˣ) (D.eta : Kˣ) i) := by
    calc
      (fun i ↦ e.valueUnit i) =
          beli2009BinaryTransformAt (fun i ↦ d.valueUnit i)
            (1 : Fin 2) (xi : Kˣ) := heValues
      _ = beli2009BinaryTransformAt
          (beli2009BinaryTransformAt
            (beli2009BinaryTransformAt (fun i ↦ a.valueUnit i)
              (1 : Fin 2) (theta : Kˣ))
            (0 : Fin 2) (D.epsilon : Kˣ))
          (1 : Fin 2) ((D.eta / theta : valuationUnitSubgroup K) : Kˣ) := by
            rw [hdValues, hcValues]
      _ = ![(D.epsilon : Kˣ) * a.valueUnit 0,
          (D.epsilon : Kˣ) * (D.eta : Kˣ) * a.valueUnit 1,
          (D.eta : Kˣ) * a.valueUnit 2] :=
        binaryTransform_threeStep_one_zero_one (K := K)
          (fun i ↦ a.valueUnit i) theta D.epsilon D.eta
      _ = (fun i ↦ a.ternaryScaledValues
          (D.epsilon : Kˣ) (D.eta : Kˣ) i) :=
        (ternaryScaledValues_eq_vector a D.epsilon D.eta).symm
  have hequivalent : Beli2009ValueSequenceEquivalent (K := K)
      (fun i ↦ e.valueUnit i) (fun i ↦ b.valueUnit i) := by
    rw [heScaled]
    exact D.scaled_equivalent a b
  exact hthetaStep.reachable.trans
    (hepsilonStep.reachable.trans
      (hxiStep.reachable.trans hequivalent.reachable))

/-- If the first alpha is bounded by its half-gap term, the dynamic middle
move of the `1→0→1` detour is automatic. -/
theorem reachable_rankThree_threeStep_one_zero_one_of_firstHalfGapBound
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a b : BONG.GoodBONG q L 3) (D : RankThreeComparisonData a b)
    (hlastA : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hlastB : b.lastBinaryAlpha =
      (b.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hepsilonDeadlock : hilbertSymbol K (D.epsilon : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (theta : valuationUnitSubgroup K)
    (hthetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
    (hthetaLast : hilbertSymbol K (theta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = 1)
    (hthetaEpsilon : hilbertSymbol K (theta : Kˣ)
      (D.epsilon : Kˣ) = -1)
    (hhalfGap : a.halfGapCandidate (0 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (D.epsilon : Kˣ)) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ b.valueUnit i) := by
  apply reachable_rankThree_threeStep_one_zero_one_of_dynamicFirstAlpha
    a b D hlastA hlastB hepsilonDeadlock theta hthetaDepth
      hthetaLast hthetaEpsilon
  unfold rankThreeFirstBinaryAlphaAfterRightMultiplier
  exact (min_le_left _ _).trans hhalfGap

/-- At equal outer order, Remark 8.7 converts an exact transformed first
adjacent defect `alpha₁` into the dynamic `alpha₀` bound needed by the
`1→0→1` detour. -/
theorem reachable_rankThree_threeStep_one_zero_one_of_firstProductAlpha
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a b : BONG.GoodBONG q L 3) (D : RankThreeComparisonData a b)
    (hlastA : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hlastB : b.lastBinaryAlpha =
      (b.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hepsilonDeadlock : hilbertSymbol K (D.epsilon : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (theta : valuationUnitSubgroup K)
    (hthetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
    (hthetaLast : hilbertSymbol K (theta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = 1)
    (hthetaEpsilon : hilbertSymbol K (theta : Kˣ)
      (D.epsilon : Kˣ) = -1)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hproduct : BONG.GoodBONG.defectOrder (K := K)
        ((theta : Kˣ) * a.adjacentProduct (0 : Fin 2)) =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ)) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ b.valueUnit i) := by
  apply reachable_rankThree_threeStep_one_zero_one_of_dynamicFirstAlpha
    a b D hlastA hlastB hepsilonDeadlock theta hthetaDepth
      hthetaLast hthetaEpsilon
  refine (min_le_right _ _).trans ?_
  rw [hproduct]
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [BONG.GoodBONG.remark87PreviousValue,
      BONG.GoodBONG.remark87NextValue] using houter)
  have hrelation :
      (((((a.order (1 : Fin 3) - a.order (0 : Fin 3) : Int) : ℚ)) :
          WithTop ℚ) +
        (a.alphaValue (1 : Fin 2) : WithTop ℚ)) =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    have h := hremark.previousAlpha_eq
    change a.alphaValue (0 : Fin 2) =
      ((a.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) +
        a.alphaValue (1 : Fin 2) at h
    have h' := congrArg (fun x : ℚ => (x : WithTop ℚ)) h
    rw [← houter] at h'
    simpa only [WithTop.coe_add, WithTop.coe_sub, Int.cast_sub,
      Int.cast_ofNat] using h'.symm
  exact hrelation.le.trans D.epsilon_defect

/-- The standard two-character defect choice supplies the auxiliary
right-edge multiplier in the half-gap branch. -/
theorem reachable_rankThree_threeStep_one_zero_one_of_firstHalfGapReference
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a b : BONG.GoodBONG q L 3) (D : RankThreeComparisonData a b)
    (hlastA : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hlastB : b.lastBinaryAlpha =
      (b.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hepsilonDeadlock : hilbertSymbol K (D.epsilon : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (reference : Kˣ)
    (hrefUnit : IsValuationUnit K (reference : K))
    (hrefDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) reference)
    (hsumEpsilon : quadraticDefect K (D.epsilon : Kˣ) +
        quadraticDefect K reference ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hsumEpsilonLast : quadraticDefect K
        ((D.epsilon : Kˣ) * a.adjacentProduct (1 : Fin 2)) +
        quadraticDefect K reference ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hhalfGap : a.halfGapCandidate (0 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (D.epsilon : Kˣ)) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ b.valueUnit i) := by
  rcases exists_valuationUnit_hilbert_neg_one_of_two_sums_le
      (D.epsilon : Kˣ) (a.adjacentProduct (1 : Fin 2))
      reference hrefUnit hsumEpsilon hsumEpsilonLast with
    ⟨thetaRaw, hthetaUnit, hthetaDepthRaw,
      hepsilonTheta, hlastTheta⟩
  let theta : valuationUnitSubgroup K := ⟨thetaRaw, hthetaUnit⟩
  have hthetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) :=
    hrefDepth.trans (by
      simpa only [theta, Subgroup.coe_mk] using hthetaDepthRaw)
  have hthetaLast : hilbertSymbol K (theta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = 1 := by
    rw [hilbertSymbol_comm K]
    simpa only [theta, Subgroup.coe_mk] using hlastTheta
  have hthetaEpsilon : hilbertSymbol K (theta : Kˣ)
      (D.epsilon : Kˣ) = -1 := by
    rw [hilbertSymbol_comm K]
    simpa only [theta, Subgroup.coe_mk] using hepsilonTheta
  exact reachable_rankThree_threeStep_one_zero_one_of_firstHalfGapBound
    a b D hlastA hlastB hepsilonDeadlock theta hthetaDepth
      hthetaLast hthetaEpsilon hhalfGap

/-- Compatibility form of the symmetric ternary detour.  Preservation of the
first adjacent defect is a sufficient condition for the sharp dynamic depth
hypothesis above. -/
theorem reachable_rankThree_threeStep_one_zero_one_of_firstDefectPreserved
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a b : BONG.GoodBONG q L 3) (D : RankThreeComparisonData a b)
    (hfirstA : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hlastA : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hlastB : b.lastBinaryAlpha =
      (b.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hepsilonDeadlock : hilbertSymbol K (D.epsilon : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (theta : valuationUnitSubgroup K)
    (hthetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
    (hthetaLast : hilbertSymbol K (theta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = 1)
    (hthetaEpsilon : hilbertSymbol K (theta : Kˣ)
      (D.epsilon : Kˣ) = -1)
    (hpreserve : BONG.GoodBONG.defectOrder (K := K)
      ((theta : Kˣ) * a.adjacentProduct (0 : Fin 2)) =
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2))) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ b.valueUnit i) := by
  apply reachable_rankThree_threeStep_one_zero_one_of_dynamicFirstAlpha
    a b D hlastA hlastB hepsilonDeadlock theta hthetaDepth
      hthetaLast hthetaEpsilon
  have hdynamicEq : rankThreeFirstBinaryAlphaAfterRightMultiplier
      a (theta : Kˣ) = a.firstBinaryAlpha := by
    unfold rankThreeFirstBinaryAlphaAfterRightMultiplier
      BONG.GoodBONG.firstBinaryAlpha
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [hpreserve]
  rw [hdynamicEq, hfirstA]
  exact D.epsilon_defect

/-- In the equal-outer ternary configuration, a normalized first literal
binary alpha which does not attain the half-gap forces the raw first
adjacent defect to be exactly the second global alpha.  This is the small
algebraic identity hidden in Remark 8.7: the first binary formula gives
`alpha_1 = (R_2-R_1)+d(-a_1a_2)`, while Remark 8.7 gives
`alpha_2 = (R_1-R_2)+alpha_1`. -/
theorem firstAdjacentDefect_eq_secondAlpha_of_normalized_notHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 3)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hnotHalf : ¬a.AttainsHalfGap (0 : Fin 2)) :
    BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (0 : Fin 2)) =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
  have hhalfStrictRat : a.alphaValue (0 : Fin 2) <
      a.halfGapValue (0 : Fin 2) :=
    lt_of_le_of_ne (a.alphaValue_le_halfGapValue (0 : Fin 2))
      (by simpa only [BONG.GoodBONG.AttainsHalfGap] using hnotHalf)
  have hhalfStrict : (a.alphaValue (0 : Fin 2) : WithTop ℚ) <
      a.halfGapCandidate (0 : Fin 2) := by
    rw [← a.coe_halfGapValue]
    exact_mod_cast hhalfStrictRat
  have hleftLe : a.leftDefectCandidate (0 : Fin 2) (0 : Fin 2) ≤
      a.halfGapCandidate (0 : Fin 2) := by
    by_contra hnot
    have hhalfLe : a.halfGapCandidate (0 : Fin 2) ≤
        a.leftDefectCandidate (0 : Fin 2) (0 : Fin 2) :=
      le_of_not_ge hnot
    have hfirstHalf := hfirst
    unfold BONG.GoodBONG.firstBinaryAlpha at hfirstHalf
    rw [min_eq_left hhalfLe] at hfirstHalf
    exact (ne_of_gt hhalfStrict) hfirstHalf
  have hleftEq : a.leftDefectCandidate (0 : Fin 2) (0 : Fin 2) =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    have h := hfirst
    unfold BONG.GoodBONG.firstBinaryAlpha at h
    rw [min_eq_right hleftLe] at h
    exact h
  have hleftFormula :
      ((((a.order (1 : Fin 3) - a.order (0 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2))) =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    simpa [BONG.GoodBONG.leftDefectCandidate,
      BONG.GoodBONG.adjacentDefect] using hleftEq
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [BONG.GoodBONG.remark87PreviousValue,
      BONG.GoodBONG.remark87NextValue] using houter)
  have hcurrent : a.alphaValue (1 : Fin 2) =
      ((a.order (0 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ) +
        a.alphaValue (0 : Fin 2) := by
    simpa [BONG.GoodBONG.remark87PreviousValue,
      BONG.GoodBONG.remark87MiddleValue,
      BONG.GoodBONG.remark87PreviousAlpha,
      BONG.GoodBONG.remark87CurrentAlpha] using hremark.currentAlpha_eq
  calc
    BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2)) =
        (0 : WithTop ℚ) + BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2)) := by simp
    _ = (((a.order (0 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) +
        (((a.order (1 : Fin 3) - a.order (0 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2)) := by
      congr 1
      norm_cast
      push_cast
      ring
    _ = (((a.order (0 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) +
        ((((a.order (1 : Fin 3) - a.order (0 : Fin 3) : Int) : ℚ) :
            WithTop ℚ) +
          BONG.GoodBONG.defectOrder (K := K)
            (a.adjacentProduct (0 : Fin 2))) := by
      rw [add_assoc]
    _ = (((a.order (0 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) + (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
      rw [hleftFormula]
    _ = (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
      exact (congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hcurrent).symm

/-- Without an equal-outer assumption, normalization plus failure of the
half-gap still identifies the literal first left-defect candidate with the
first global alpha.  This is the local equation
`(R₁-R₀)+d(-a₀a₁)=alpha₀` used in the unequal-outer branch. -/
theorem firstLeftDefectCandidate_eq_alpha_of_normalized_notHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 3)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hnotHalf : ¬a.AttainsHalfGap (0 : Fin 2)) :
    a.leftDefectCandidate (0 : Fin 2) (0 : Fin 2) =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
  have hhalfStrictRat : a.alphaValue (0 : Fin 2) <
      a.halfGapValue (0 : Fin 2) :=
    lt_of_le_of_ne (a.alphaValue_le_halfGapValue (0 : Fin 2))
      (by simpa only [BONG.GoodBONG.AttainsHalfGap] using hnotHalf)
  have hhalfStrict : (a.alphaValue (0 : Fin 2) : WithTop ℚ) <
      a.halfGapCandidate (0 : Fin 2) := by
    rw [← a.coe_halfGapValue]
    exact_mod_cast hhalfStrictRat
  have hleftLe : a.leftDefectCandidate (0 : Fin 2) (0 : Fin 2) ≤
      a.halfGapCandidate (0 : Fin 2) := by
    by_contra hnot
    have hhalfLe : a.halfGapCandidate (0 : Fin 2) ≤
        a.leftDefectCandidate (0 : Fin 2) (0 : Fin 2) :=
      le_of_not_ge hnot
    have hfirstHalf := hfirst
    unfold BONG.GoodBONG.firstBinaryAlpha at hfirstHalf
    rw [min_eq_left hhalfLe] at hfirstHalf
    exact (ne_of_gt hhalfStrict) hfirstHalf
  have h := hfirst
  unfold BONG.GoodBONG.firstBinaryAlpha at h
  rw [min_eq_right hleftLe] at h
  exact h

/-- Symmetric endpoint form of
`firstAdjacentDefect_eq_secondAlpha_of_normalized_notHalfGap`.  If the
literal final binary alpha is normalized and is strict below its half-gap,
then the raw final adjacent defect is exactly the first global alpha. -/
theorem secondAdjacentDefect_eq_firstAlpha_of_normalized_notHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 3)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hnotHalf : ¬a.AttainsHalfGap (1 : Fin 2)) :
    BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (1 : Fin 2)) =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
  have hhalfStrictRat : a.alphaValue (1 : Fin 2) <
      a.halfGapValue (1 : Fin 2) :=
    lt_of_le_of_ne (a.alphaValue_le_halfGapValue (1 : Fin 2))
      (by simpa only [BONG.GoodBONG.AttainsHalfGap] using hnotHalf)
  have hhalfStrict : (a.alphaValue (1 : Fin 2) : WithTop ℚ) <
      a.halfGapCandidate (1 : Fin 2) := by
    rw [← a.coe_halfGapValue]
    exact_mod_cast hhalfStrictRat
  have hlastIndex : (Fin.last 1 : Fin 2) = (1 : Fin 2) := by
    apply Fin.ext
    simp
  have hleftLe : a.leftDefectCandidate (1 : Fin 2) (1 : Fin 2) ≤
      a.halfGapCandidate (1 : Fin 2) := by
    by_contra hnot
    have hhalfLe : a.halfGapCandidate (1 : Fin 2) ≤
        a.leftDefectCandidate (1 : Fin 2) (1 : Fin 2) :=
      le_of_not_ge hnot
    have hlastHalf := hlast
    unfold BONG.GoodBONG.lastBinaryAlpha
      BONG.GoodBONG.adjacentBinaryAlpha at hlastHalf
    rw [hlastIndex, min_eq_left hhalfLe] at hlastHalf
    exact (ne_of_gt hhalfStrict) hlastHalf
  have hleftEq : a.leftDefectCandidate (1 : Fin 2) (1 : Fin 2) =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    have h := hlast
    unfold BONG.GoodBONG.lastBinaryAlpha
      BONG.GoodBONG.adjacentBinaryAlpha at h
    rw [hlastIndex, min_eq_right hleftLe] at h
    exact h
  have hleftFormula :
      ((((a.order (2 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (1 : Fin 2))) =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    simpa [BONG.GoodBONG.leftDefectCandidate,
      BONG.GoodBONG.adjacentDefect] using hleftEq
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [BONG.GoodBONG.remark87PreviousValue,
      BONG.GoodBONG.remark87NextValue] using houter)
  have hnextIndex :
      BONG.GoodBONG.remark87NextValue (0 : Fin 1) =
        (2 : Fin 3) := by
    apply Fin.ext
    simp [BONG.GoodBONG.remark87NextValue]
  have hprevious : a.alphaValue (0 : Fin 2) =
      ((a.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) +
        a.alphaValue (1 : Fin 2) := by
    have h := hremark.previousAlpha_eq
    rw [hnextIndex] at h
    simpa [BONG.GoodBONG.remark87PreviousValue,
      BONG.GoodBONG.remark87MiddleValue,
      BONG.GoodBONG.remark87PreviousAlpha,
      BONG.GoodBONG.remark87CurrentAlpha] using h
  calc
    BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (1 : Fin 2)) =
        (0 : WithTop ℚ) + BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (1 : Fin 2)) := by simp
    _ = (((a.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) +
        (((a.order (2 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (1 : Fin 2)) := by
      congr 1
      norm_cast
      ring
    _ = (((a.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) +
        ((((a.order (2 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ) :
            WithTop ℚ) +
          BONG.GoodBONG.defectOrder (K := K)
            (a.adjacentProduct (1 : Fin 2))) := by
      rw [add_assoc]
    _ = (((a.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) + (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
      rw [hleftFormula]
    _ = (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
      exact (congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hprevious).symm

/-- Symmetric local equation at the last edge, without any relation between
the two outer orders. -/
theorem lastLeftDefectCandidate_eq_alpha_of_normalized_notHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 3)
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hnotHalf : ¬a.AttainsHalfGap (1 : Fin 2)) :
    a.leftDefectCandidate (1 : Fin 2) (1 : Fin 2) =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
  have hhalfStrictRat : a.alphaValue (1 : Fin 2) <
      a.halfGapValue (1 : Fin 2) :=
    lt_of_le_of_ne (a.alphaValue_le_halfGapValue (1 : Fin 2))
      (by simpa only [BONG.GoodBONG.AttainsHalfGap] using hnotHalf)
  have hhalfStrict : (a.alphaValue (1 : Fin 2) : WithTop ℚ) <
      a.halfGapCandidate (1 : Fin 2) := by
    rw [← a.coe_halfGapValue]
    exact_mod_cast hhalfStrictRat
  have hlastIndex : (Fin.last 1 : Fin 2) = (1 : Fin 2) := by
    apply Fin.ext
    simp
  have hleftLe : a.leftDefectCandidate (1 : Fin 2) (1 : Fin 2) ≤
      a.halfGapCandidate (1 : Fin 2) := by
    by_contra hnot
    have hhalfLe : a.halfGapCandidate (1 : Fin 2) ≤
        a.leftDefectCandidate (1 : Fin 2) (1 : Fin 2) :=
      le_of_not_ge hnot
    have hlastHalf := hlast
    unfold BONG.GoodBONG.lastBinaryAlpha
      BONG.GoodBONG.adjacentBinaryAlpha at hlastHalf
    rw [hlastIndex, min_eq_left hhalfLe] at hlastHalf
    exact (ne_of_gt hhalfStrict) hlastHalf
  have h := hlast
  unfold BONG.GoodBONG.lastBinaryAlpha
    BONG.GoodBONG.adjacentBinaryAlpha at h
  rw [hlastIndex, min_eq_right hleftLe] at h
  exact h

/-- Rational form of the first strict literal-edge equation. -/
theorem firstAdjacentDefectOrder_eq_alpha_sub_gap_of_normalized_notHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 3)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hnotHalf : ¬a.AttainsHalfGap (0 : Fin 2)) :
    BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (0 : Fin 2)) =
      ((a.alphaValue (0 : Fin 2) -
        ((a.order (1 : Fin 3) - a.order (0 : Fin 3) : Int) : ℚ) : ℚ) :
          WithTop ℚ) := by
  have hleft :=
    firstLeftDefectCandidate_eq_alpha_of_normalized_notHalfGap
      a hfirst hnotHalf
  have hformula :
      ((((a.order (1 : Fin 3) - a.order (0 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2))) =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    simpa [BONG.GoodBONG.leftDefectCandidate,
      BONG.GoodBONG.adjacentDefect] using hleft
  have hfinite : BONG.GoodBONG.defectOrder (K := K)
      (a.adjacentProduct (0 : Fin 2)) ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hformula
    exact WithTop.coe_ne_top hformula.symm
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hfinite
  rw [← hd] at hformula ⊢
  norm_cast at hformula ⊢
  push_cast at hformula ⊢
  linarith

/-- Rational form of the last strict literal-edge equation. -/
theorem secondAdjacentDefectOrder_eq_alpha_sub_gap_of_normalized_notHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 3)
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hnotHalf : ¬a.AttainsHalfGap (1 : Fin 2)) :
    BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (1 : Fin 2)) =
      ((a.alphaValue (1 : Fin 2) -
        ((a.order (2 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ) : ℚ) :
          WithTop ℚ) := by
  have hleft :=
    lastLeftDefectCandidate_eq_alpha_of_normalized_notHalfGap
      a hlast hnotHalf
  have hformula :
      ((((a.order (2 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (1 : Fin 2))) =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    simpa [BONG.GoodBONG.leftDefectCandidate,
      BONG.GoodBONG.adjacentDefect] using hleft
  have hfinite : BONG.GoodBONG.defectOrder (K := K)
      (a.adjacentProduct (1 : Fin 2)) ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hformula
    exact WithTop.coe_ne_top hformula.symm
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hfinite
  rw [← hd] at hformula ⊢
  norm_cast at hformula ⊢
  push_cast at hformula ⊢
  linarith

/-- Property P1 bounds the first strict adjacent defect by the second global
alpha.  This is the first endpoint inequality needed in the unequal-outer
ternary detour. -/
theorem firstAdjacentDefectOrder_le_secondAlpha_of_normalized_notHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 3)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hnotHalf : ¬a.AttainsHalfGap (0 : Fin 2)) :
    BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (0 : Fin 2)) ≤
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
  rw [firstAdjacentDefectOrder_eq_alpha_sub_gap_of_normalized_notHalfGap
      a hfirst hnotHalf]
  norm_cast
  push_cast
  have hp1 : (a.order (0 : Fin 3) : ℚ) + a.alphaValue (0 : Fin 2) ≤
      (a.order (1 : Fin 3) : ℚ) + a.alphaValue (1 : Fin 2) := by
    simpa [BONG.GoodBONG.alphaLeftEndpoint] using
      (a.alpha_p1 (0 : Fin 2) (by omega)).1
  linarith

/-- Property P1 bounds the last strict adjacent defect by the first global
alpha.  Equality is the only cancellation boundary left by the elementary
two-character correction. -/
theorem secondAdjacentDefectOrder_le_firstAlpha_of_normalized_notHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 3)
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hnotHalf : ¬a.AttainsHalfGap (1 : Fin 2)) :
    BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (1 : Fin 2)) ≤
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
  rw [secondAdjacentDefectOrder_eq_alpha_sub_gap_of_normalized_notHalfGap
      a hlast hnotHalf]
  norm_cast
  push_cast
  have hp1 : -(a.order (2 : Fin 3) : ℚ) + a.alphaValue (1 : Fin 2) ≤
      -(a.order (1 : Fin 3) : ℚ) + a.alphaValue (0 : Fin 2) := by
    simpa [BONG.GoodBONG.alphaRightEndpoint] using
      (a.alpha_p1 (0 : Fin 2) (by omega)).2
  linarith

/-- Property A (`R₀<R₂`) makes the two strict literal adjacent defects
have a strictly subcritical sum.  Algebraically the order gaps telescope:
`d(A₀)+d(A₁)=alpha₀+alpha₁-(R₂-R₀)<2e`. -/
theorem unequalOuter_adjacentDefectOrder_sum_lt_twoE_of_normalized_notHalfGaps
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (conditions : a.Lemma813Conditions b)
    (houter : a.Lemma814UnequalOuterBound b)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hnotFirst : ¬a.AttainsHalfGap (0 : Fin 2))
    (hnotLast : ¬a.AttainsHalfGap (1 : Fin 2)) :
    BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2)) +
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (1 : Fin 2)) <
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
  rw [firstAdjacentDefectOrder_eq_alpha_sub_gap_of_normalized_notHalfGap
      a hfirst hnotFirst,
    secondAdjacentDefectOrder_eq_alpha_sub_gap_of_normalized_notHalfGap
      a hlast hnotLast]
  norm_cast
  push_cast
  have hsum :=
    a.alphaSum_le_twoE_of_lemma814UnequalOuterBound b conditions houter
  have horders : (a.order (0 : Fin 3) : ℚ) <
      (a.order (2 : Fin 3) : ℚ) := by
    exact_mod_cast houter.1
  push_cast at hsum
  linarith

/-- The complementary unit chosen in the printed unequal-outer proof lies
strictly deeper than the first adjacent square class.  This is the exact
inequality that makes multiplication by that unit preserve the first
literal binary alpha. -/
theorem firstAdjacentDefectOrder_lt_complementary_of_unequalOuter
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (houter : a.Lemma814UnequalOuterBound b)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hnotFirst : ¬a.AttainsHalfGap (0 : Fin 2))
    (d : ℚ)
    (hfull : a.truncatedPrefixDefect b (-1) 3 1 =
      (d : WithTop ℚ))
    (eta : Kˣ)
    (heta : BONG.GoodBONG.defectOrder (K := K) eta =
      ((2 * (ramificationIndex K : ℚ) - d : ℚ) : WithTop ℚ)) :
    BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (0 : Fin 2)) <
      BONG.GoodBONG.defectOrder (K := K) eta := by
  rw [firstAdjacentDefectOrder_eq_alpha_sub_gap_of_normalized_notHalfGap
      a hfirst hnotFirst,
    heta]
  norm_cast
  push_cast
  have hbound := houter.2
  rw [hfull] at hbound
  norm_cast at hbound
  push_cast at hbound
  have horders : (a.order (0 : Fin 3) : ℚ) <
      (a.order (2 : Fin 3) : ℚ) := by
    exact_mod_cast houter.1
  linarith

/-- Under the unequal-outer numerical bound the two adjacent alphas cannot
both be their half-gap candidates: their sum would exceed `2e` by half the
strict outer-order increase. -/
theorem not_both_attainHalfGap_of_unequalOuter
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (conditions : a.Lemma813Conditions b)
    (houter : a.Lemma814UnequalOuterBound b)
    (hfirstHalf : a.AttainsHalfGap (0 : Fin 2)) :
    ¬a.AttainsHalfGap (1 : Fin 2) := by
  intro hlastHalf
  have hsum :=
    a.alphaSum_le_twoE_of_lemma814UnequalOuterBound b conditions houter
  have houterRat : (a.order (0 : Fin 3) : ℚ) <
      (a.order (2 : Fin 3) : ℚ) := by
    exact_mod_cast houter.1
  unfold BONG.GoodBONG.AttainsHalfGap BONG.GoodBONG.halfGapValue
    BONG.GoodBONG.orderGap at hfirstHalf hlastHalf
  push_cast at hfirstHalf hlastHalf
  rw [hfirstHalf, hlastHalf] at hsum
  push_cast at hsum
  linarith

/-- If the first alpha attains its half-gap in the unequal-outer branch,
the second alpha is bounded by the raw first adjacent defect.  This is the
numerical input needed by the principal-layer Hilbert choice. -/
theorem secondAlpha_le_firstAdjacentDefect_of_firstHalfGap_unequalOuter
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (conditions : a.Lemma813Conditions b)
    (houter : a.Lemma814UnequalOuterBound b)
    (hfirstHalf : a.AttainsHalfGap (0 : Fin 2)) :
    (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      a.adjacentDefect (0 : Fin 2) := by
  have hsum :=
    a.alphaSum_le_twoE_of_lemma814UnequalOuterBound b conditions houter
  have hcandidate := a.alpha_le_leftDefectCandidate
    (i := (0 : Fin 2)) (j := (0 : Fin 2)) le_rfl
  rw [← a.coe_alphaValue] at hcandidate
  change
    (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      (((a.order (1 : Fin 3) - a.order (0 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) + a.adjacentDefect (0 : Fin 2) at hcandidate
  by_cases htop : a.adjacentDefect (0 : Fin 2) = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hd] at hcandidate ⊢
    norm_cast at hcandidate ⊢
    unfold BONG.GoodBONG.AttainsHalfGap
      BONG.GoodBONG.halfGapValue BONG.GoodBONG.orderGap at hfirstHalf
    push_cast at hfirstHalf hcandidate
    linarith

/-- If the last alpha attains its half-gap, the first alpha is bounded by
the full comparison defect.  The proof isolates the lower quantity
`R₁-R₂+alpha₁`, which is bounded by both factors of the full defect
and equals `2e-alpha₁` at the half-gap boundary. -/
theorem firstAlpha_le_fullDefect_of_lastHalfGap_unequalOuter
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (conditions : a.Lemma813Conditions b)
    (houter : a.Lemma814UnequalOuterBound b)
    (hlastHalf : a.AttainsHalfGap (1 : Fin 2)) :
    (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      a.truncatedPrefixDefect b (-1) 3 1 := by
  let lower : WithTop ℚ :=
    (((a.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) :
      WithTop ℚ) + (a.alphaValue (1 : Fin 2) : WithTop ℚ)
  have hlowerAlpha : lower ≤
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    have hp1 := (a.alpha_p1 (0 : Fin 2) (by omega)).2
    have hrat :
        ((a.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) +
            a.alphaValue (1 : Fin 2) ≤
          a.alphaValue (0 : Fin 2) := by
      unfold BONG.GoodBONG.alphaRightEndpoint at hp1
      change -(a.order (2 : Fin 3) : ℚ) +
          a.alphaValue (1 : Fin 2) ≤
        -(a.order (1 : Fin 3) : ℚ) +
          a.alphaValue (0 : Fin 2) at hp1
      push_cast at hp1 ⊢
      linarith
    dsimp only [lower]
    exact_mod_cast hrat
  have hlowerAdjacent : lower ≤
      a.adjacentDefect (1 : Fin 2) := by
    have hcandidate := a.alpha_le_leftDefectCandidate
      (i := (1 : Fin 2)) (j := (1 : Fin 2)) le_rfl
    rw [← a.coe_alphaValue] at hcandidate
    change
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        (((a.order (2 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) + a.adjacentDefect (1 : Fin 2) at hcandidate
    by_cases htop : a.adjacentDefect (1 : Fin 2) = ⊤
    · rw [htop]
      exact le_top
    · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
      rw [← hd] at hcandidate ⊢
      dsimp only [lower]
      norm_cast at hcandidate ⊢
      push_cast at hcandidate ⊢
      linarith
  have hlowerEpsilon : lower ≤
      BONG.GoodBONG.defectOrder (K := K) (a.lemma814Epsilon b) :=
    hlowerAlpha.trans (a.alpha_le_lemma814EpsilonDefect b conditions)
  have hlowerProduct : lower ≤
      BONG.GoodBONG.defectOrder (K := K)
        (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) :=
    (le_min hlowerEpsilon hlowerAdjacent).trans
      (BONG.GoodBONG.defectOrder_mul_ge_min
        (K := K) (a.lemma814Epsilon b)
          (a.adjacentProduct (1 : Fin 2)))
  have hlowerFull : lower ≤ a.truncatedPrefixDefect b (-1) 3 1 := by
    rw [a.lemma814TernaryFullDefect_eq_epsilon_mul_secondAdjacent b]
    exact hlowerProduct
  have hsum :=
    a.alphaSum_le_twoE_of_lemma814UnequalOuterBound b conditions houter
  have hfirstLeLower : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      lower := by
    dsimp only [lower]
    norm_cast
    unfold BONG.GoodBONG.AttainsHalfGap
      BONG.GoodBONG.halfGapValue BONG.GoodBONG.orderGap at hlastHalf
    push_cast at hlastHalf ⊢
    linarith
  exact hfirstLeLower.trans hlowerFull

/-- In the strict unequal-outer branch one may choose the auxiliary
right-edge unit at *exactly* the second alpha depth.  Its product with the
first adjacent class is no deeper than the latter.  At unequal depths this
is automatic; at the equal-depth boundary the large-residue neighbour lemma
prevents cancellation while imposing the required negative Hilbert sign. -/
theorem exists_unequalOuter_strict_eta_of_largeResidue
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (conditions : a.Lemma813Conditions b)
    (houter : a.Lemma814UnequalOuterBound b)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hnotFirst : ¬a.AttainsHalfGap (0 : Fin 2))
    (hnotLast : ¬a.AttainsHalfGap (1 : Fin 2)) :
    ∃ eta : Kˣ,
      IsValuationUnit K (eta : K) ∧
        BONG.GoodBONG.defectOrder (K := K) eta =
          (a.alphaValue (1 : Fin 2) : WithTop ℚ) ∧
        BONG.GoodBONG.defectOrder (K := K)
            (eta * a.adjacentProduct (0 : Fin 2)) ≤
          BONG.GoodBONG.defectOrder (K := K)
            (a.adjacentProduct (0 : Fin 2)) ∧
        hilbertSymbol K
            (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) eta = -1 := by
  have hfirstOdd := a.beli2009Lemma27_iv (0 : Fin 2) hnotFirst
  have hsecondOdd := a.beli2009Lemma27_iv (1 : Fin 2) hnotLast
  have hfirstNonnegative : 0 ≤ a.alphaValue (0 : Fin 2) :=
    (a.beli2009Lemma27_i (0 : Fin 2)).1
  have hsecondNonnegative : 0 ≤ a.alphaValue (1 : Fin 2) :=
    (a.beli2009Lemma27_i (1 : Fin 2)).1
  have hfirstPositive : 0 < a.alphaValue (0 : Fin 2) := by
    rcases hfirstOdd with ⟨z, hzOdd, hz⟩
    have hzNonnegative : 0 ≤ z := by
      rw [hz] at hfirstNonnegative
      exact_mod_cast hfirstNonnegative
    have hzPositive : 0 < z := by
      rcases hzOdd with ⟨m, hm⟩
      omega
    rw [hz]
    exact_mod_cast hzPositive
  have hsum :=
    a.alphaSum_le_twoE_of_lemma814UnequalOuterBound b
      conditions houter
  have hsecondLt : a.alphaValue (1 : Fin 2) <
      2 * (ramificationIndex K : ℚ) := by
    linarith
  rcases DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      (a.alphaValue (1 : Fin 2)) hsecondOdd hsecondNonnegative hsecondLt with
    ⟨reference, hrefUnit, hrefDefect⟩
  have hsumTop :=
    a.secondAlpha_add_fullDefect_le_twoE_of_unequalOuter b houter
  have htwoE : (2 : WithTop ℚ) *
        ((ramificationIndex K : ℚ) : WithTop ℚ) =
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    norm_num
  rw [htwoE] at hsumTop
  have hsumOrder : BONG.GoodBONG.defectOrder (K := K)
          (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) +
        BONG.GoodBONG.defectOrder (K := K) reference ≤
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hrefDefect,
      ← a.lemma814TernaryFullDefect_eq_epsilon_mul_secondAdjacent b]
    simpa only [add_comm] using hsumTop
  have hsumQuadratic :=
    quadraticDefect_add_le_twoE_of_defectOrder_add_le_twoE_enat
      (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
      reference hsumOrder
  let A₀ : Kˣ := a.adjacentProduct (0 : Fin 2)
  let z : Kˣ := a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)
  have hA₀Order :=
    firstAdjacentDefectOrder_eq_alpha_sub_gap_of_normalized_notHalfGap
      a hfirst hnotFirst
  by_cases heq : BONG.GoodBONG.defectOrder (K := K) A₀ =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ)
  · have hA₀RefOrder : BONG.GoodBONG.defectOrder (K := K) A₀ =
        BONG.GoodBONG.defectOrder (K := K) reference := by
      rw [heq, hrefDefect]
    have hA₀RefQuadratic : quadraticDefect K A₀ =
        quadraticDefect K reference :=
      BONG.GoodBONG.quadraticDefect_eq_of_defectOrder_eq
        A₀ reference hA₀RefOrder
    have hA₀Finite : quadraticDefect K A₀ ≠ ⊤ := by
      rw [hA₀RefQuadratic]
      intro htop
      have htopOrder : BONG.GoodBONG.defectOrder (K := K) reference = ⊤ := by
        unfold BONG.GoodBONG.defectOrder
        rw [htop]
        rfl
      rw [hrefDefect] at htopOrder
      exact WithTop.coe_ne_top htopOrder
    have hA₀Nonzero : quadraticDefect K A₀ ≠ 0 := by
      rw [hA₀RefQuadratic]
      exact quadraticDefect_ne_zero_of_isValuationUnit reference hrefUnit
    have hA₀NotTwoE : quadraticDefect K A₀ ≠
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      intro htwo
      have horderTwo : BONG.GoodBONG.defectOrder (K := K) A₀ =
          (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
        unfold BONG.GoodBONG.defectOrder
        rw [htwo]
        rfl
      rw [heq] at horderTwo
      have halphaTwo : a.alphaValue (1 : Fin 2) =
          2 * (ramificationIndex K : ℚ) := by
        have h := WithTop.coe_eq_coe.mp horderTwo
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
      exact (ne_of_lt hsecondLt) halphaTwo
    have hsumZA₀ : quadraticDefect K z + quadraticDefect K A₀ ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      simpa only [z, hA₀RefQuadratic] using hsumQuadratic
    rcases exists_same_defect_product_hilbert_neg_one_of_largeResidue
        hres z A₀ hA₀Finite hA₀Nonzero hA₀NotTwoE hsumZA₀ with
      ⟨w, hwDefect, hA₀wDefect, hwHilbert⟩
    have hwEven : Even (ordUnit K w) := by
      rcases Int.even_or_odd (ordUnit K w) with heven | hodd
      · exact heven
      · exact (hA₀Nonzero (by
          rw [← hwDefect]
          exact quadraticDefect_eq_zero_of_odd_ordUnit w hodd)).elim
    rcases BONG.GoodBONG.exists_valuationUnit_eq_mul_square_of_even_order
        w hwEven with ⟨eta, s, hetaUnit, hetaFactor⟩
    have hetaDefect : BONG.GoodBONG.defectOrder (K := K) eta =
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
      have hq : quadraticDefect K eta = quadraticDefect K A₀ := by
        rw [hetaFactor, quadraticDefect_mul_square]
        exact hwDefect
      exact (defectOrder_eq_of_quadraticDefect_eq eta A₀ hq).trans heq
    have hetaProduct : quadraticDefect K (eta * A₀) =
        quadraticDefect K A₀ := by
      rw [hetaFactor]
      rw [show (w * s ^ 2) * A₀ = (A₀ * w) * s ^ 2 by ac_rfl,
        quadraticDefect_mul_square]
      exact hA₀wDefect
    have hetaProductOrder : BONG.GoodBONG.defectOrder (K := K)
        (eta * A₀) ≤ BONG.GoodBONG.defectOrder (K := K) A₀ := by
      exact (defectOrder_eq_of_quadraticDefect_eq
        (eta * A₀) A₀ hetaProduct).le
    have hetaHilbert : hilbertSymbol K z eta = -1 := by
      rw [hetaFactor, hilbertSymbol_mul_square_right]
      exact hwHilbert
    exact ⟨eta, hetaUnit, hetaDefect,
      by simpa only [A₀] using hetaProductOrder,
      by simpa only [z] using hetaHilbert⟩
  · rcases (beli2019Lemma82_i z reference).2
        (by simpa only [z] using hsumQuadratic) with
      ⟨w, hwDefect, hwHilbert⟩
    have hwNonzero : quadraticDefect K w ≠ 0 := by
      rw [hwDefect]
      exact quadraticDefect_ne_zero_of_isValuationUnit reference hrefUnit
    rcases exists_valuationUnit_same_defect_same_hilbert z w hwNonzero with
      ⟨eta, hetaUnit, hetaDefectW, hetaHilbertW⟩
    have hetaDefectQ : quadraticDefect K eta =
        quadraticDefect K reference := hetaDefectW.trans hwDefect
    have hetaDefect : BONG.GoodBONG.defectOrder (K := K) eta =
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) :=
      (defectOrder_eq_of_quadraticDefect_eq eta reference hetaDefectQ).trans
        hrefDefect
    have hdepthNe : BONG.GoodBONG.defectOrder (K := K) eta ≠
        BONG.GoodBONG.defectOrder (K := K) A₀ := by
      rw [hetaDefect]
      exact fun h ↦ heq h.symm
    have hetaProductEq := BONG.GoodBONG.defectOrder_mul_eq_min_of_ne
      (K := K) hdepthNe
    have hetaProductLe : BONG.GoodBONG.defectOrder (K := K) (eta * A₀) ≤
        BONG.GoodBONG.defectOrder (K := K) A₀ := by
      rw [hetaProductEq]
      exact min_le_right _ _
    have hetaHilbert : hilbertSymbol K z eta = -1 :=
      hetaHilbertW.trans hwHilbert
    exact ⟨eta, hetaUnit, hetaDefect,
      by simpa only [A₀] using hetaProductLe,
      by simpa only [z] using hetaHilbert⟩

/- Dynamic two-step form of the negative-Hilbert branch of Lemma 8.14 in
ternary rank.  A legal right-edge multiplier makes the subsequent prescribed
left-edge multiplier norm-compatible.  The transformed literal first binary
alpha, rather than preservation of the old adjacent defect, is the exact
depth hypothesis needed for that second move. -/
/-- The previously missing anisotropic equal-depth branch of the ternary
deadlock is a genuine three-step binary path over a large residue field.
The fixed-layer neighbour theorem supplies a right-edge multiplier with the
two required Hilbert signs, while exact preservation of the first adjacent
defect discharges the sharp dynamic-alpha condition. -/
theorem reachable_rankThree_anisotropic_equalDepth_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a b : BONG.GoodBONG q L 3) (D : RankThreeComparisonData a b)
    (hfirstA : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hlastA : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hlastB : b.lastBinaryAlpha =
      (b.alphaValue (1 : Fin 2) : WithTop ℚ))
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hanisotropic : a.Lemma814FirstThreeAnisotropic)
    (hepsilonDeadlock : hilbertSymbol K (D.epsilon : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (hA₀Depth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (0 : Fin 2)))
    (hA₀Finite : quadraticDefect K
      (a.adjacentProduct (0 : Fin 2)) ≠ ⊤)
    (hA₀Nonzero : quadraticDefect K
      (a.adjacentProduct (0 : Fin 2)) ≠ 0)
    (hA₀NotTwoE : quadraticDefect K
      (a.adjacentProduct (0 : Fin 2)) ≠
        ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hsum : quadraticDefect K
          ((D.epsilon : Kˣ) * a.adjacentProduct (1 : Fin 2)) +
        quadraticDefect K (a.adjacentProduct (0 : Fin 2)) ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ b.valueUnit i) := by
  have hA₀Even :=
    a.ternaryAdjacentOrders_even_of_equalOuter houter |>.1
  have hA₀A₁ : hilbertSymbol K
      (a.adjacentProduct (0 : Fin 2))
      (a.adjacentProduct (1 : Fin 2)) = -1 :=
    a.adjacentHilbert_neg_of_firstThreeAnisotropic hanisotropic
  rcases exists_valuationUnit_anisotropic_detour_neighbor
      hres (D.epsilon : Kˣ)
      (a.adjacentProduct (0 : Fin 2))
      (a.adjacentProduct (1 : Fin 2))
      hA₀Even hA₀Finite hA₀Nonzero hA₀NotTwoE hsum
      hepsilonDeadlock hA₀A₁ with
    ⟨thetaRaw, hthetaUnit, hthetaDepthRaw, hthetaProduct,
      hthetaLast, hthetaEpsilon⟩
  let theta : valuationUnitSubgroup K := ⟨thetaRaw, hthetaUnit⟩
  have hthetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) :=
    hA₀Depth.trans (by
      simpa only [theta, Subgroup.coe_mk] using hthetaDepthRaw)
  have hpreserve : BONG.GoodBONG.defectOrder (K := K)
      ((theta : Kˣ) * a.adjacentProduct (0 : Fin 2)) =
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2)) := by
    exact defectOrder_eq_of_quadraticDefect_eq
      ((theta : Kˣ) * a.adjacentProduct (0 : Fin 2))
      (a.adjacentProduct (0 : Fin 2)) (by
        simpa only [theta, Subgroup.coe_mk] using hthetaProduct)
  exact reachable_rankThree_threeStep_one_zero_one_of_firstDefectPreserved
    a b D hfirstA hlastA hlastB hepsilonDeadlock theta hthetaDepth
      (by simpa only [theta, Subgroup.coe_mk] using hthetaLast)
      (by simpa only [theta, Subgroup.coe_mk] using hthetaEpsilon)
      hpreserve

theorem reachableLemma814_rankThree_negative_of_dynamicTheta
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hepsilonHilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (theta : valuationUnitSubgroup K)
    (hthetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
    (hthetaLast : hilbertSymbol K (theta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = 1)
    (hthetaEpsilon : hilbertSymbol K (theta : Kˣ)
      (a.lemma814Epsilon b) = -1)
    (hdynamic : rankThreeFirstBinaryAlphaAfterRightMultiplier
        a (theta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (a.lemma814Epsilon b)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  have hthetaAlpha : a.adjacentBinaryAlpha (1 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) := by
    rw [show a.adjacentBinaryAlpha (1 : Fin 2) = a.lastBinaryAlpha by rfl,
      hlast]
    exact hthetaDepth
  have hthetaHilbert : hilbertSymbol K
      (a.adjacentProduct (1 : Fin 2)) (theta : Kˣ) = 1 := by
    rw [hilbertSymbol_comm K]
    exact hthetaLast
  have hthetaGroup : valuationUnitClassHom K theta ∈
      beliNormGeneratorGroup K
        (a.valueUnit (2 : Fin 3) / a.valueUnit (1 : Fin 3)) := by
    exact valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (1 : Fin 2) theta hthetaAlpha hthetaHilbert
  rcases exists_goodBONG_binaryTransformation_exact a (1 : Fin 2)
      theta hthetaGroup with ⟨c, hcValues⟩
  have hthetaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ c.valueUnit i) :=
    ⟨1, theta, hthetaGroup, hcValues⟩
  have hcAdjacent : c.adjacentProduct (0 : Fin 2) =
      (theta : Kˣ) * a.adjacentProduct (0 : Fin 2) := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hcValues (0 : Fin 2).castSucc,
      congrFun hcValues (0 : Fin 2).succ]
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]
    exact mul_comm _ _
  have hcFirstAlpha : c.adjacentBinaryAlpha (0 : Fin 2) =
      rankThreeFirstBinaryAlphaAfterRightMultiplier a (theta : Kˣ) := by
    have horders := a.order_invariant c
    have horderZero : c.order (0 : Fin 2).castSucc =
        a.order (0 : Fin 2).castSucc :=
      (horders (0 : Fin 2).castSucc).symm
    have horderOne : c.order (0 : Fin 2).succ =
        a.order (0 : Fin 2).succ :=
      (horders (0 : Fin 2).succ).symm
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankThreeFirstBinaryAlphaAfterRightMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [horderOne, horderZero, hcAdjacent]
  let epsilon : valuationUnitSubgroup K :=
    ⟨a.lemma814Epsilon b, a.lemma814Epsilon_isValuationUnit b horder⟩
  have hepsilonHilbert' : hilbertSymbol K
      (c.adjacentProduct (0 : Fin 2)) (epsilon : Kˣ) = 1 := by
    rw [hcAdjacent, hilbertSymbol_mul_left]
    simpa only [epsilon, Subgroup.coe_mk] using
      (show hilbertSymbol K (theta : Kˣ) (a.lemma814Epsilon b) *
          hilbertSymbol K (a.adjacentProduct (0 : Fin 2))
            (a.lemma814Epsilon b) = 1 by
        rw [hthetaEpsilon,
          hilbertSymbol_comm K (a.adjacentProduct (0 : Fin 2))
            (a.lemma814Epsilon b), hepsilonHilbert]
        norm_num)
  have hepsilonGroup : valuationUnitClassHom K epsilon ∈
      beliNormGeneratorGroup K
        (c.valueUnit (1 : Fin 3) / c.valueUnit (0 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      c (0 : Fin 2) epsilon
    · rw [hcFirstAlpha]
      simpa only [epsilon, Subgroup.coe_mk] using hdynamic
    · exact hepsilonHilbert'
  rcases exists_goodBONG_binaryTransformation_exact c (0 : Fin 2)
      epsilon hepsilonGroup with ⟨d, hdValues⟩
  have hepsilonStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ c.valueUnit i) (fun i ↦ d.valueUnit i) :=
    ⟨0, epsilon, hepsilonGroup, hdValues⟩
  have hcHead : c.valueUnit (0 : Fin 3) = a.valueUnit (0 : Fin 3) := by
    rw [congrFun hcValues (0 : Fin 3)]
    simp [beli2009BinaryTransformAt]
  have hdHead : d.valueUnit (0 : Fin 3) = b.valueUnit (0 : Fin 1) := by
    calc
      d.valueUnit (0 : Fin 3) =
          (epsilon : Kˣ) * c.valueUnit (0 : Fin 3) := by
        rw [congrFun hdValues (0 : Fin 3)]
        rfl
      _ = a.lemma814Epsilon b * a.valueUnit (0 : Fin 3) := by
        rw [hcHead]
      _ = b.valueUnit (0 : Fin 1) :=
        a.lemma814Epsilon_mul_firstValue b
  exact ⟨{
    transform := {
      transformed := d
      firstValue_eq := hdHead
    }
    reachable := hthetaStep.reachable.trans hepsilonStep.reachable
  }⟩

/-- In the half-gap branch, the principal-unit filtration produces the
right-edge detour multiplier directly.  The two defect-sum inequalities say
that the depth-`k` layer is contained in neither relevant norm hyperplane;
Beli's Lemma 1.3 then supplies a class which is positive on the last
adjacent product and negative on the prescribed first multiplier. -/
theorem reachableLemma814_rankThree_negative_of_halfGap_principalChoice
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hepsilonHilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (k : Nat) (hk : 0 < k)
    (hsecondNat : a.alphaValue (1 : Fin 2) = (k : ℚ))
    (hsumEpsilon : quadraticDefect K (a.lemma814Epsilon b) +
        (k : ℕ∞) ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hsumProduct : quadraticDefect K
          (a.adjacentProduct (1 : Fin 2) * a.lemma814Epsilon b) +
        (k : ℕ∞) ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hhalfGap : a.halfGapCandidate (0 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (a.lemma814Epsilon b)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  have hsumProduct' : quadraticDefect K
        ((-(-(a.adjacentProduct (1 : Fin 2)))) * a.lemma814Epsilon b) +
      (k : ℕ∞) ≤
    ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    simpa using hsumProduct
  rcases exists_valuationUnit_depth_norm_hilbert_neg_one_of_sums_le
      (-(a.adjacentProduct (1 : Fin 2))) (a.lemma814Epsilon b)
      k hk hsumEpsilon hsumProduct' with
    ⟨theta, hthetaDepthNat, hthetaLastRaw, hthetaEpsilonRaw⟩
  have hthetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) := by
    rw [hsecondNat]
    exact hthetaDepthNat
  have hthetaLast : hilbertSymbol K (theta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = 1 := by
    rw [hilbertSymbol_comm K]
    simpa using hthetaLastRaw
  have hthetaEpsilon : hilbertSymbol K (theta : Kˣ)
      (a.lemma814Epsilon b) = -1 := by
    rw [hilbertSymbol_comm K]
    exact hthetaEpsilonRaw
  apply reachableLemma814_rankThree_negative_of_dynamicTheta
    a b horder conditions hlast hepsilonHilbert theta hthetaDepth
      hthetaLast hthetaEpsilon
  unfold rankThreeFirstBinaryAlphaAfterRightMultiplier
  exact (min_le_left _ _).trans hhalfGap

/-- Unequal outer orders with a first half-gap reduce to the principal-layer
choice above.  The opposite edge is necessarily strict, hence its alpha is a
positive odd integer.  The half-gap identity and the global alpha-sum bound
place that integer below the first adjacent defect, supplying the two defect
sum inequalities required by Lemma 1.3. -/
theorem reachableLemma814_rankThree_negative_of_unequalOuter_firstHalfGap
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (houter : a.Lemma814UnequalOuterBound b)
    (hfirstHalf : a.AttainsHalfGap (0 : Fin 2))
    (hepsilonFirst : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  have hnotLast :=
    not_both_attainHalfGap_of_unequalOuter
      a b conditions houter hfirstHalf
  have hsecondOdd := a.beli2009Lemma27_iv (1 : Fin 2) hnotLast
  have hsecondNonnegative : 0 ≤ a.alphaValue (1 : Fin 2) :=
    (a.beli2009Lemma27_i (1 : Fin 2)).1
  have hsecondPositive :=
    a.secondAlpha_pos_of_lemma814UnequalOuterBound
      b conditions houter hepsilonFirst
  have hfirstNonnegative : 0 ≤ a.alphaValue (0 : Fin 2) :=
    (a.beli2009Lemma27_i (0 : Fin 2)).1
  have hsumAlpha :=
    a.alphaSum_le_twoE_of_lemma814UnequalOuterBound b conditions houter
  have hsecondLe : a.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) := by
    linarith
  have hsecondNe : a.alphaValue (1 : Fin 2) ≠
      2 * (ramificationIndex K : ℚ) := by
    intro hendpoint
    rcases hsecondOdd with ⟨z, hzOdd, hz⟩
    have hzEndpoint : z = 2 * (ramificationIndex K : Int) := by
      exact_mod_cast hz.symm.trans hendpoint
    rcases hzOdd with ⟨m, hm⟩
    omega
  have hsecondLt : a.alphaValue (1 : Fin 2) <
      2 * (ramificationIndex K : ℚ) :=
    lt_of_le_of_ne hsecondLe hsecondNe
  rcases hsecondOdd with ⟨z, hzOdd, hz⟩
  have hzNonnegative : 0 ≤ z := by
    rw [hz] at hsecondNonnegative
    exact_mod_cast hsecondNonnegative
  let k : Nat := z.toNat
  have hkInt : (k : Int) = z := by
    simpa only [k] using Int.toNat_of_nonneg hzNonnegative
  have hsecondNat : a.alphaValue (1 : Fin 2) = (k : ℚ) := by
    calc
      a.alphaValue (1 : Fin 2) = (z : ℚ) := hz
      _ = (k : ℚ) := by exact_mod_cast hkInt.symm
  have hk : 0 < k := by
    exact_mod_cast (show 0 < (k : Int) by
      rw [hkInt]
      exact_mod_cast (show (0 : ℚ) < (z : ℚ) by
        rw [← hz]
        exact hsecondPositive))
  rcases DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      (a.alphaValue (1 : Fin 2)) ⟨z, hzOdd, hz⟩
      hsecondNonnegative hsecondLt with
    ⟨reference, hrefUnit, hrefDefect⟩
  have hrefDefectNat : BONG.GoodBONG.defectOrder (K := K) reference =
      (((k : Nat) : ℚ) : WithTop ℚ) := by
    rw [hrefDefect, hsecondNat]
  have hrefQuadratic : quadraticDefect K reference = (k : ℕ∞) :=
    quadraticDefect_eq_natCast_of_defectOrder_eq_natCast
      reference k hrefDefectNat
  have hsecondFirst :=
    secondAlpha_le_firstAdjacentDefect_of_firstHalfGap_unequalOuter
      a b conditions houter hfirstHalf
  have hkFirst : (k : ℕ∞) ≤ quadraticDefect K
      (a.adjacentProduct (0 : Fin 2)) :=
    natCast_le_quadraticDefect_of_natCast_le_defectOrder
      (a.adjacentProduct (0 : Fin 2)) k (by
        rw [← hsecondNat]
        exact hsecondFirst)
  have hrawEpsilon : quadraticDefect K (a.lemma814Epsilon b) +
        quadraticDefect K (a.adjacentProduct (0 : Fin 2)) ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞) :=
    (BONG.beli2019Lemma82_i (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2))).mp
        ⟨a.adjacentProduct (0 : Fin 2), rfl, hepsilonFirst⟩
  have hsumEpsilon : quadraticDefect K (a.lemma814Epsilon b) +
        (k : ℕ∞) ≤ ((2 * ramificationIndex K : Nat) : ℕ∞) :=
    calc
      quadraticDefect K (a.lemma814Epsilon b) + (k : ℕ∞) =
          (k : ℕ∞) + quadraticDefect K (a.lemma814Epsilon b) :=
        add_comm _ _
      _ ≤ quadraticDefect K (a.adjacentProduct (0 : Fin 2)) +
          quadraticDefect K (a.lemma814Epsilon b) :=
        add_le_add_left hkFirst _
      _ = quadraticDefect K (a.lemma814Epsilon b) +
          quadraticDefect K (a.adjacentProduct (0 : Fin 2)) :=
        add_comm _ _
      _ ≤ ((2 * ramificationIndex K : Nat) : ℕ∞) := hrawEpsilon
  have hsumTop :=
    a.secondAlpha_add_fullDefect_le_twoE_of_unequalOuter b houter
  have htwoE : (2 : WithTop ℚ) *
        ((ramificationIndex K : ℚ) : WithTop ℚ) =
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    norm_num
  rw [htwoE] at hsumTop
  have hsumOrder : BONG.GoodBONG.defectOrder (K := K)
          (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) +
        BONG.GoodBONG.defectOrder (K := K) reference ≤
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hrefDefect,
      ← a.lemma814TernaryFullDefect_eq_epsilon_mul_secondAdjacent b]
    simpa only [mul_comm, add_comm, Nat.cast_mul, Nat.cast_ofNat]
      using hsumTop
  have hsumQuadratic :=
    quadraticDefect_add_le_twoE_of_defectOrder_add_le_twoE_enat
      (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
      reference hsumOrder
  have hsumProduct : quadraticDefect K
        (a.adjacentProduct (1 : Fin 2) * a.lemma814Epsilon b) +
        (k : ℕ∞) ≤ ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    rw [← hrefQuadratic]
    simpa only [mul_comm] using hsumQuadratic
  have hhalfGap : a.halfGapCandidate (0 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (a.lemma814Epsilon b) := by
    calc
      a.halfGapCandidate (0 : Fin 2) =
          (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
        rw [← a.coe_halfGapValue]
        exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hfirstHalf.symm
      _ ≤ BONG.GoodBONG.defectOrder (K := K) (a.lemma814Epsilon b) :=
        a.alpha_le_lemma814EpsilonDefect b conditions
  exact reachableLemma814_rankThree_negative_of_halfGap_principalChoice
    a b horder conditions hlast hepsilonFirst k hk hsecondNat
      hsumEpsilon hsumProduct hhalfGap

/-- In the isotropic half-gap branch, no auxiliary principal-layer choice is
needed.  The inverse of the first adjacent square class (after removing its
even valuation by a square) is a legal right-edge multiplier: isotropy gives
the positive last Hilbert sign, while the assumed negative first sign is
unchanged by inversion. -/
theorem reachableLemma814_rankThree_negative_of_isotropic_halfGap
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hisotropic : a.Lemma814FirstThreeIsotropic)
    (hhalf : a.AttainsHalfGap (0 : Fin 2))
    (hepsilonHilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  have hadjacentEven := a.ternaryAdjacentOrders_even_of_equalOuter houter
  have hinverseEven : Even
      (ordUnit K (a.adjacentProduct (0 : Fin 2))⁻¹) := by
    rw [ordUnit_inv]
    exact hadjacentEven.1.neg
  rcases BONG.GoodBONG.exists_valuationUnit_eq_mul_square_of_even_order
      (a.adjacentProduct (0 : Fin 2))⁻¹ hinverseEven with
    ⟨thetaRaw, squareFactor, hthetaUnit, hthetaFactor⟩
  let theta : valuationUnitSubgroup K := ⟨thetaRaw, hthetaUnit⟩
  have hthetaDefect : BONG.GoodBONG.defectOrder (K := K) thetaRaw =
      BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (0 : Fin 2)) := by
    rw [hthetaFactor, BONG.GoodBONG.defectOrder_mul_square,
      BONG.GoodBONG.defectOrder_inv]
  have hsecondLower : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (0 : Fin 2)) := by
    have hremark := a.beli2019Remark87 (0 : Fin 1) (by
      simpa [BONG.GoodBONG.remark87PreviousValue,
        BONG.GoodBONG.remark87NextValue] using houter)
    simpa [BONG.GoodBONG.adjacentDefect,
      BONG.GoodBONG.remark87PreviousAlpha,
      BONG.GoodBONG.remark87CurrentAlpha] using
        hremark.currentAlpha_le_previousRawDefect
  have hthetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) := by
    simpa only [theta, Subgroup.coe_mk, hthetaDefect] using hsecondLower
  have hthetaLast : hilbertSymbol K (theta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = 1 := by
    have horiginal :=
      (a.lemma814FirstThreeIsotropic_iff_adjacentHilbertOne).mp hisotropic
    simpa only [theta, Subgroup.coe_mk, hthetaFactor,
      hilbertSymbol_mul_square_left, hilbertSymbol_inv_left_eq] using
        horiginal
  have hthetaEpsilon : hilbertSymbol K (theta : Kˣ)
      (a.lemma814Epsilon b) = -1 := by
    have hbase : hilbertSymbol K (a.adjacentProduct (0 : Fin 2))
        (a.lemma814Epsilon b) = -1 := by
      rw [hilbertSymbol_comm K]
      exact hepsilonHilbert
    simpa only [theta, Subgroup.coe_mk, hthetaFactor,
      hilbertSymbol_mul_square_left, hilbertSymbol_inv_left_eq] using
        hbase
  have hhalfGap : a.halfGapCandidate (0 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (a.lemma814Epsilon b) := by
    calc
      a.halfGapCandidate (0 : Fin 2) =
          (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
        rw [← a.coe_halfGapValue]
        exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hhalf.symm
      _ ≤ BONG.GoodBONG.defectOrder (K := K) (a.lemma814Epsilon b) :=
        a.alpha_le_lemma814EpsilonDefect b conditions
  apply reachableLemma814_rankThree_negative_of_dynamicTheta
    a b horder conditions hlast hepsilonHilbert theta hthetaDepth
      hthetaLast hthetaEpsilon
  unfold rankThreeFirstBinaryAlphaAfterRightMultiplier
  exact (min_le_left _ _).trans hhalfGap

/-- In the strict isotropic branch, an auxiliary multiplier having the
paper's exact transformed-product defect gives a direct right-to-left
binary path as soon as its two Hilbert signs have the favorable
orientation.  Remark 8.7 converts the product defect `alpha₁` into the
dynamic first-binary alpha `alpha₀`. -/
theorem reachableLemma814_rankThree_negative_of_isotropic_productChoice
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hepsilonHilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (etaRaw : Kˣ) (hetaUnit : IsValuationUnit K (etaRaw : K))
    (hetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) etaRaw)
    (hproduct : BONG.GoodBONG.defectOrder (K := K)
        (etaRaw * a.adjacentProduct (0 : Fin 2)) =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hetaLast : hilbertSymbol K etaRaw
      (a.adjacentProduct (1 : Fin 2)) = 1)
    (hetaEpsilon : hilbertSymbol K etaRaw
      (a.lemma814Epsilon b) = -1) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  let eta : valuationUnitSubgroup K := ⟨etaRaw, hetaUnit⟩
  apply reachableLemma814_rankThree_negative_of_dynamicTheta
    a b horder conditions hlast hepsilonHilbert eta
  · simpa only [eta, Subgroup.coe_mk] using hetaDepth
  · simpa only [eta, Subgroup.coe_mk] using hetaLast
  · simpa only [eta, Subgroup.coe_mk] using hetaEpsilon
  · unfold rankThreeFirstBinaryAlphaAfterRightMultiplier
    refine (min_le_right _ _).trans ?_
    rw [show ((eta : valuationUnitSubgroup K) : Kˣ) = etaRaw by rfl,
      hproduct]
    have hremark := a.beli2019Remark87 (0 : Fin 1) (by
      simpa [BONG.GoodBONG.remark87PreviousValue,
        BONG.GoodBONG.remark87NextValue] using houter)
    have hrelation :
        (((((a.order (1 : Fin 3) - a.order (0 : Fin 3) : Int) : ℚ)) :
            WithTop ℚ) +
          (a.alphaValue (1 : Fin 2) : WithTop ℚ)) =
        (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
      have h := hremark.previousAlpha_eq
      change a.alphaValue (0 : Fin 2) =
        ((a.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) +
          a.alphaValue (1 : Fin 2) at h
      have h' := congrArg (fun x : ℚ => (x : WithTop ℚ)) h
      rw [← houter] at h'
      simpa only [WithTop.coe_add, WithTop.coe_sub, Int.cast_sub,
        Int.cast_ofNat] using h'.symm
    exact hrelation.le.trans
      (a.alpha_le_lemma814EpsilonDefect b conditions)

/-- The auxiliary unit constructed in the strict isotropic paragraph of
Lemma 8.14, exposed together with the exact data needed by the
path-refinement.  Over a large residue field Lemma 8.2(ii) gives the
positive Hilbert partner without the residue-two exceptional subcase. -/
theorem exists_rankThree_isotropicStrict_multiplier
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hisotropic : a.Lemma814FirstThreeIsotropic)
    (hfirstStrict : ¬a.AttainsHalfGap (0 : Fin 2)) :
    ∃ eta : Kˣ,
      IsValuationUnit K (eta : K) ∧
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
          BONG.GoodBONG.defectOrder (K := K) eta ∧
        BONG.GoodBONG.defectOrder (K := K)
            (eta * a.adjacentProduct (0 : Fin 2)) =
          (a.alphaValue (1 : Fin 2) : WithTop ℚ) ∧
        hilbertSymbol K
            (eta * a.adjacentProduct (0 : Fin 2))
            (a.lemma814Epsilon b *
              a.adjacentProduct (1 : Fin 2)) = 1 := by
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [BONG.GoodBONG.remark87PreviousValue,
      BONG.GoodBONG.remark87NextValue] using houter)
  have hsecondNotHalf :
      a.alphaValue (1 : Fin 2) ≠ a.halfGapValue (1 : Fin 2) := by
    intro hsecondHalf
    apply hfirstStrict
    apply hremark.attainsHalfGap_iff.mpr
    exact hsecondHalf
  have hsecondOdd := a.beli2009Lemma27_iv (1 : Fin 2) hsecondNotHalf
  have hfirstNonnegative : 0 ≤ a.alphaValue (0 : Fin 2) :=
    (a.beli2009Lemma27_i (0 : Fin 2)).1
  have hsecondNonnegative : 0 ≤ a.alphaValue (1 : Fin 2) :=
    (a.beli2009Lemma27_i (1 : Fin 2)).1
  have hsecondLe : a.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) := by
    have hsum := hremark.alphaSum_le_twoE
    change a.alphaValue (0 : Fin 2) + a.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) at hsum
    linarith
  have hsecondNe : a.alphaValue (1 : Fin 2) ≠
      2 * (ramificationIndex K : ℚ) := by
    intro hendpoint
    rcases hsecondOdd with ⟨z, hzOdd, hz⟩
    have hzEndpoint : z = 2 * (ramificationIndex K : Int) := by
      exact_mod_cast hz.symm.trans hendpoint
    rcases hzOdd with ⟨k, hk⟩
    omega
  have hsecondLt : a.alphaValue (1 : Fin 2) <
      2 * (ramificationIndex K : ℚ) :=
    lt_of_le_of_ne hsecondLe hsecondNe
  rcases DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      (a.alphaValue (1 : Fin 2)) hsecondOdd hsecondNonnegative
      hsecondLt with
    ⟨reference, hrefUnit, hrefDefect⟩
  have hrefNonzero : quadraticDefect K reference ≠ 0 :=
    quadraticDefect_ne_zero_of_isValuationUnit reference hrefUnit
  have hrefNotTwoE : quadraticDefect K reference ≠
      ((2 * ramificationIndex K : Nat) : WithTop Nat) := by
    intro hrefTwoE
    have horderEndpoint : BONG.GoodBONG.defectOrder (K := K) reference =
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      unfold BONG.GoodBONG.defectOrder
      rw [hrefTwoE]
      rfl
    rw [hrefDefect] at horderEndpoint
    have hendpoint : a.alphaValue (1 : Fin 2) =
        2 * (ramificationIndex K : ℚ) := by
      have h := WithTop.coe_eq_coe.mp horderEndpoint
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
    exact (ne_of_lt hsecondLt) hendpoint
  have hnotZeroTwoE :
      ¬IsZeroTwoEDefectPair (K := K)
        (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
        reference := by
    rintro (hleft | hright)
    · exact hrefNotTwoE hleft.2
    · exact hrefNonzero hright.2
  rcases beli2019Lemma82_ii_unit hres
      (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
      reference hrefUnit hnotZeroTwoE with
    ⟨u, huUnit, huDefect, huHilbert⟩
  have huNonzero : quadraticDefect K u ≠ 0 := by
    rw [huDefect]
    exact hrefNonzero
  have hadjacentEven := a.ternaryAdjacentOrders_even_of_equalOuter houter
  rcases exists_valuationUnit_multiplier_same_defect_same_hilbert
      (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
      (a.adjacentProduct (0 : Fin 2)) u hadjacentEven.1 huNonzero with
    ⟨eta, hetaUnit, hetaDefectU, hetaHilbertU⟩
  have hetaQuadraticDefect :
      quadraticDefect K (eta * a.adjacentProduct (0 : Fin 2)) =
        quadraticDefect K reference :=
    hetaDefectU.trans (huDefect.trans rfl)
  have hetaProductDefect :
      BONG.GoodBONG.defectOrder (K := K)
          (eta * a.adjacentProduct (0 : Fin 2)) =
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    have h := defectOrder_eq_of_quadraticDefect_eq
      (eta * a.adjacentProduct (0 : Fin 2)) reference
      hetaQuadraticDefect
    rw [hrefDefect] at h
    exact h
  have hfirstAdjacentLower :
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2)) := by
    simpa [BONG.GoodBONG.adjacentDefect,
      BONG.GoodBONG.remark87PreviousAlpha,
      BONG.GoodBONG.remark87CurrentAlpha] using
        hremark.currentAlpha_le_previousRawDefect
  have hetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) eta := by
    by_contra hnot
    have hetaLt : BONG.GoodBONG.defectOrder (K := K) eta <
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) := lt_of_not_ge hnot
    have hetaLtAdjacent : BONG.GoodBONG.defectOrder (K := K) eta <
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2)) :=
      hetaLt.trans_le hfirstAdjacentLower
    have hdomination :=
      BONG.GoodBONG.defectOrder_mul_eq_left_of_lt_right hetaLtAdjacent
    have hetaEq : BONG.GoodBONG.defectOrder (K := K) eta =
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) :=
      hdomination.symm.trans hetaProductDefect
    exact (ne_of_lt hetaLt) hetaEq
  have hcandidate : hilbertSymbol K
      (eta * a.adjacentProduct (0 : Fin 2))
      (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) = 1 := by
    calc
      hilbertSymbol K
          (eta * a.adjacentProduct (0 : Fin 2))
          (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) =
          hilbertSymbol K
            (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
            (eta * a.adjacentProduct (0 : Fin 2)) :=
        hilbertSymbol_comm K _ _
      _ = hilbertSymbol K
          (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) u :=
        hetaHilbertU
      _ = 1 := huHilbert
  exact ⟨eta, hetaUnit, hetaDepth, hetaProductDefect, hcandidate⟩

/-- The strict isotropic construction either already gives the favorable
right-to-left detour, or leaves one sharply identified opposite-orientation
multiplier.  This disjunction is useful because the latter, rather than the
whole isotropic case, is the sole input to the longer alternating path. -/
theorem reachableLemma814_rankThree_negative_of_isotropic_notHalfGap_or_opposite
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hisotropic : a.Lemma814FirstThreeIsotropic)
    (hnotHalf : ¬a.AttainsHalfGap (0 : Fin 2))
    (hepsilonHilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) ∨
      ∃ eta : Kˣ,
        IsValuationUnit K (eta : K) ∧
          (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
            BONG.GoodBONG.defectOrder (K := K) eta ∧
          BONG.GoodBONG.defectOrder (K := K)
              (eta * a.adjacentProduct (0 : Fin 2)) =
            (a.alphaValue (1 : Fin 2) : WithTop ℚ) ∧
          hilbertSymbol K eta (a.adjacentProduct (1 : Fin 2)) = -1 ∧
          hilbertSymbol K eta (a.lemma814Epsilon b) = 1 := by
  rcases exists_rankThree_isotropicStrict_multiplier hres a b houter
      hisotropic hnotHalf with
    ⟨eta, hetaUnit, hetaDepth, hproduct, hcandidate⟩
  have horiginal : hilbertSymbol K
      (a.adjacentProduct (0 : Fin 2))
      (a.adjacentProduct (1 : Fin 2)) = 1 :=
    (a.lemma814FirstThreeIsotropic_iff_adjacentHilbertOne).mp hisotropic
  have hepsilonFirst : hilbertSymbol K
      (a.adjacentProduct (0 : Fin 2)) (a.lemma814Epsilon b) = -1 := by
    rw [hilbertSymbol_comm K]
    exact hepsilonHilbert
  have hsignProduct :
      hilbertSymbol K eta (a.lemma814Epsilon b) *
          hilbertSymbol K eta (a.adjacentProduct (1 : Fin 2)) = -1 := by
    have h := hcandidate
    rw [hilbertSymbol_mul_left, hilbertSymbol_mul_right,
      hilbertSymbol_mul_right, hepsilonFirst, horiginal] at h
    have h' := congrArg (fun z : ℤˣ => z * (-1)) h
    simpa [mul_assoc] using h'
  rcases Int.units_eq_one_or
      (hilbertSymbol K eta (a.adjacentProduct (1 : Fin 2))) with
    hetaLast | hetaLast
  · have hetaEpsilon : hilbertSymbol K eta
        (a.lemma814Epsilon b) = -1 := by
      rw [hetaLast, mul_one] at hsignProduct
      exact hsignProduct
    exact Or.inl
      (reachableLemma814_rankThree_negative_of_isotropic_productChoice
        a b horder conditions hlast houter hepsilonHilbert eta hetaUnit
          hetaDepth hproduct hetaLast hetaEpsilon)
  · have hetaEpsilon : hilbertSymbol K eta
        (a.lemma814Epsilon b) = 1 := by
      rw [hetaLast] at hsignProduct
      rcases Int.units_eq_one_or
          (hilbertSymbol K eta (a.lemma814Epsilon b)) with h | h
      · exact h
      · rw [h] at hsignProduct
        norm_num at hsignProduct
    exact Or.inr ⟨eta, hetaUnit, hetaDepth, hproduct,
      hetaLast, hetaEpsilon⟩

/-- The anisotropic half-gap branch is also reachable.  Oddness makes the
second alpha a positive natural depth.  The nonexceptional full-defect bound
and Lemma 8.2(i) put the depth-`k` principal layer outside both relevant norm
hyperplanes, so the preceding principal-choice detour applies. -/
theorem reachableLemma814_rankThree_negative_of_anisotropic_halfGap
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hanisotropic : a.Lemma814FirstThreeAnisotropic)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (hhalf : a.AttainsHalfGap (0 : Fin 2))
    (hepsilonHilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [BONG.GoodBONG.remark87PreviousValue,
      BONG.GoodBONG.remark87NextValue] using houter)
  have hsecondHalf : a.AttainsHalfGap (1 : Fin 2) := by
    simpa [BONG.GoodBONG.remark87PreviousAlpha,
      BONG.GoodBONG.remark87CurrentAlpha] using
        hremark.attainsHalfGap_iff.mp hhalf
  have hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    unfold BONG.GoodBONG.lastBinaryAlpha
    simpa using a.adjacentBinaryAlpha_eq_alpha_of_attainsHalfGap
      (1 : Fin 2) hsecondHalf
  have hsecondOdd :=
    a.secondAlpha_isOddRationalInteger_of_equalOuter_anisotropic
      houter hanisotropic
  have hfirstNonnegative : 0 ≤ a.alphaValue (0 : Fin 2) :=
    (a.beli2009Lemma27_i (0 : Fin 2)).1
  have hsecondNonnegative : 0 ≤ a.alphaValue (1 : Fin 2) :=
    (a.beli2009Lemma27_i (1 : Fin 2)).1
  have hsecondLe : a.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) := by
    have hsum := hremark.alphaSum_le_twoE
    change a.alphaValue (0 : Fin 2) + a.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) at hsum
    linarith
  have hsecondNe : a.alphaValue (1 : Fin 2) ≠
      2 * (ramificationIndex K : ℚ) := by
    intro hendpoint
    rcases hsecondOdd with ⟨z, hzOdd, hz⟩
    have hzEndpoint : z = 2 * (ramificationIndex K : Int) := by
      exact_mod_cast hz.symm.trans hendpoint
    rcases hzOdd with ⟨m, hm⟩
    omega
  have hsecondLt : a.alphaValue (1 : Fin 2) <
      2 * (ramificationIndex K : ℚ) :=
    lt_of_le_of_ne hsecondLe hsecondNe
  rcases hsecondOdd with ⟨z, hzOdd, hz⟩
  have hzNonnegative : 0 ≤ z := by
    rw [hz] at hsecondNonnegative
    exact_mod_cast hsecondNonnegative
  let k : Nat := z.toNat
  have hkInt : (k : Int) = z := by
    simpa only [k] using Int.toNat_of_nonneg hzNonnegative
  have hsecondNat : a.alphaValue (1 : Fin 2) = (k : ℚ) := by
    calc
      a.alphaValue (1 : Fin 2) = (z : ℚ) := hz
      _ = (k : ℚ) := by exact_mod_cast hkInt.symm
  have hk : 0 < k := by
    have hzPositive : 0 < z := by
      rcases hzOdd with ⟨m, hm⟩
      omega
    exact_mod_cast (show 0 < (k : Int) by simpa only [hkInt] using hzPositive)
  rcases DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      (a.alphaValue (1 : Fin 2)) ⟨z, hzOdd, hz⟩
      hsecondNonnegative hsecondLt with
    ⟨reference, _hrefUnit, hrefDefect⟩
  have hrefDefectNat : BONG.GoodBONG.defectOrder (K := K) reference =
      (((k : Nat) : ℚ) : WithTop ℚ) := by
    rw [hrefDefect, hsecondNat]
  have hrefQuadratic : quadraticDefect K reference = (k : ℕ∞) :=
    quadraticDefect_eq_natCast_of_defectOrder_eq_natCast
      reference k hrefDefectNat
  have hsumTop :=
    a.secondAlpha_add_fullDefect_le_twoE_of_notExceptional_anisotropic
      b houter hanisotropic hnotExceptional
  have hsumDefectOrder :
      BONG.GoodBONG.defectOrder (K := K)
          (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) +
          BONG.GoodBONG.defectOrder (K := K) reference ≤
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hrefDefect,
      ← a.lemma814TernaryFullDefect_eq_epsilon_mul_secondAdjacent b]
    simpa only [add_comm, Nat.cast_mul, Nat.cast_ofNat] using hsumTop
  have hsumQuadratic :=
    quadraticDefect_add_le_twoE_of_defectOrder_add_le_twoE_enat
      (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
      reference hsumDefectOrder
  have hsumProduct : quadraticDefect K
        (a.adjacentProduct (1 : Fin 2) * a.lemma814Epsilon b) +
        (k : ℕ∞) ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    rw [← hrefQuadratic]
    simpa only [mul_comm] using hsumQuadratic
  have hsecondLower : (((k : Nat) : ℚ) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (0 : Fin 2)) := by
    rw [← hsecondNat]
    simpa [BONG.GoodBONG.adjacentDefect,
      BONG.GoodBONG.remark87PreviousAlpha,
      BONG.GoodBONG.remark87CurrentAlpha] using
        hremark.currentAlpha_le_previousRawDefect
  have hkFirst : (k : ℕ∞) ≤ quadraticDefect K
      (a.adjacentProduct (0 : Fin 2)) :=
    natCast_le_quadraticDefect_of_natCast_le_defectOrder
      (a.adjacentProduct (0 : Fin 2)) k hsecondLower
  have hrawEpsilon : quadraticDefect K (a.lemma814Epsilon b) +
        quadraticDefect K (a.adjacentProduct (0 : Fin 2)) ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞) :=
    (BONG.beli2019Lemma82_i (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2))).mp
        ⟨a.adjacentProduct (0 : Fin 2), rfl, hepsilonHilbert⟩
  have hsumEpsilon : quadraticDefect K (a.lemma814Epsilon b) +
        (k : ℕ∞) ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞) :=
    calc
      quadraticDefect K (a.lemma814Epsilon b) + (k : ℕ∞) =
          (k : ℕ∞) + quadraticDefect K (a.lemma814Epsilon b) := add_comm _ _
      _ ≤ quadraticDefect K (a.adjacentProduct (0 : Fin 2)) +
          quadraticDefect K (a.lemma814Epsilon b) :=
        add_le_add_left hkFirst _
      _ = quadraticDefect K (a.lemma814Epsilon b) +
          quadraticDefect K (a.adjacentProduct (0 : Fin 2)) := add_comm _ _
      _ ≤ ((2 * ramificationIndex K : Nat) : ℕ∞) := hrawEpsilon
  have hhalfGap : a.halfGapCandidate (0 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (a.lemma814Epsilon b) := by
    calc
      a.halfGapCandidate (0 : Fin 2) =
          (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
        rw [← a.coe_halfGapValue]
        exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hhalf.symm
      _ ≤ BONG.GoodBONG.defectOrder (K := K) (a.lemma814Epsilon b) :=
        a.alpha_le_lemma814EpsilonDefect b conditions
  exact reachableLemma814_rankThree_negative_of_halfGap_principalChoice
    a b horder conditions hlast hepsilonHilbert k hk hsecondNat
      hsumEpsilon hsumProduct hhalfGap

/-- The complementary anisotropic branch, where the first alpha is strict
below its half-gap.  Double endpoint normalization and Remark 8.7 identify
the first adjacent defect with the odd second alpha.  The nonexceptional
full-defect inequality is therefore exactly the sum bound required by the
large-residue fixed-layer neighbour lemma.  Its multiplier preserves the
first adjacent defect and supplies the two Hilbert signs of the right-left
detour. -/
theorem reachableLemma814_rankThree_negative_of_anisotropic_notHalfGap
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hanisotropic : a.Lemma814FirstThreeAnisotropic)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (hnotHalf : ¬a.AttainsHalfGap (0 : Fin 2))
    (hepsilonHilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  have hA₀DefectOrder :=
    firstAdjacentDefect_eq_secondAlpha_of_normalized_notHalfGap
      a houter hfirst hnotHalf
  have hsecondOdd :=
    a.secondAlpha_isOddRationalInteger_of_equalOuter_anisotropic
      houter hanisotropic
  have hsecondNonnegative : 0 ≤ a.alphaValue (1 : Fin 2) :=
    (a.beli2009Lemma27_i (1 : Fin 2)).1
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [BONG.GoodBONG.remark87PreviousValue,
      BONG.GoodBONG.remark87NextValue] using houter)
  have hsecondLe : a.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) := by
    have hfirstNonnegative : 0 ≤ a.alphaValue (0 : Fin 2) :=
      (a.beli2009Lemma27_i (0 : Fin 2)).1
    have hsum := hremark.alphaSum_le_twoE
    change a.alphaValue (0 : Fin 2) + a.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) at hsum
    linarith
  have hsecondNe : a.alphaValue (1 : Fin 2) ≠
      2 * (ramificationIndex K : ℚ) := by
    intro hendpoint
    rcases hsecondOdd with ⟨z, hzOdd, hz⟩
    have hzEndpoint : z = 2 * (ramificationIndex K : Int) := by
      exact_mod_cast hz.symm.trans hendpoint
    rcases hzOdd with ⟨m, hm⟩
    omega
  have hsecondLt : a.alphaValue (1 : Fin 2) <
      2 * (ramificationIndex K : ℚ) :=
    lt_of_le_of_ne hsecondLe hsecondNe
  rcases hsecondOdd with ⟨z, hzOdd, hz⟩
  have hzNonnegative : 0 ≤ z := by
    rw [hz] at hsecondNonnegative
    exact_mod_cast hsecondNonnegative
  let k : Nat := z.toNat
  have hkInt : (k : Int) = z := by
    simpa only [k] using Int.toNat_of_nonneg hzNonnegative
  have hsecondNat : a.alphaValue (1 : Fin 2) = (k : ℚ) := by
    calc
      a.alphaValue (1 : Fin 2) = (z : ℚ) := hz
      _ = (k : ℚ) := by exact_mod_cast hkInt.symm
  have hk : 0 < k := by
    have hzPositive : 0 < z := by
      rcases hzOdd with ⟨m, hm⟩
      omega
    exact_mod_cast (show 0 < (k : Int) by simpa only [hkInt] using hzPositive)
  have hkLt : k < 2 * ramificationIndex K := by
    exact_mod_cast (show (k : ℚ) < 2 * (ramificationIndex K : ℚ) by
      rw [← hsecondNat]
      exact hsecondLt)
  have hA₀DefectNat : BONG.GoodBONG.defectOrder (K := K)
      (a.adjacentProduct (0 : Fin 2)) =
        (((k : Nat) : ℚ) : WithTop ℚ) := by
    rw [hA₀DefectOrder, hsecondNat]
  have hA₀Quadratic : quadraticDefect K
      (a.adjacentProduct (0 : Fin 2)) = (k : ℕ∞) :=
    quadraticDefect_eq_natCast_of_defectOrder_eq_natCast
      (a.adjacentProduct (0 : Fin 2)) k hA₀DefectNat
  have hA₀Finite : quadraticDefect K
      (a.adjacentProduct (0 : Fin 2)) ≠ ⊤ := by
    rw [hA₀Quadratic]
    exact WithTop.coe_ne_top
  have hA₀Nonzero : quadraticDefect K
      (a.adjacentProduct (0 : Fin 2)) ≠ 0 := by
    rw [hA₀Quadratic]
    exact_mod_cast (ne_of_gt hk)
  have hA₀NotTwoE : quadraticDefect K
      (a.adjacentProduct (0 : Fin 2)) ≠
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    rw [hA₀Quadratic]
    exact_mod_cast (ne_of_lt hkLt)
  have hsumTop :=
    a.secondAlpha_add_fullDefect_le_twoE_of_notExceptional_anisotropic
      b houter hanisotropic hnotExceptional
  have hsumDefectOrder :
      BONG.GoodBONG.defectOrder (K := K)
          (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) +
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2)) ≤
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hA₀DefectOrder,
      ← a.lemma814TernaryFullDefect_eq_epsilon_mul_secondAdjacent b]
    simpa only [add_comm, Nat.cast_mul, Nat.cast_ofNat] using hsumTop
  have hsum :=
    quadraticDefect_add_le_twoE_of_defectOrder_add_le_twoE_enat
      (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
      (a.adjacentProduct (0 : Fin 2)) hsumDefectOrder
  have hA₀Even := a.ternaryAdjacentOrders_even_of_equalOuter houter |>.1
  have hA₀A₁ := a.adjacentHilbert_neg_of_firstThreeAnisotropic hanisotropic
  rcases exists_valuationUnit_anisotropic_detour_neighbor
      hres (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2))
      (a.adjacentProduct (1 : Fin 2))
      hA₀Even hA₀Finite hA₀Nonzero hA₀NotTwoE hsum
      hepsilonHilbert hA₀A₁ with
    ⟨thetaRaw, hthetaUnit, hthetaDepthRaw, hthetaProduct,
      hthetaLast, hthetaEpsilon⟩
  let theta : valuationUnitSubgroup K := ⟨thetaRaw, hthetaUnit⟩
  have hthetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) := by
    rw [← hA₀DefectOrder]
    simpa only [theta, Subgroup.coe_mk] using hthetaDepthRaw
  have hpreserve : BONG.GoodBONG.defectOrder (K := K)
      ((theta : Kˣ) * a.adjacentProduct (0 : Fin 2)) =
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2)) :=
    defectOrder_eq_of_quadraticDefect_eq _ _ (by
      simpa only [theta, Subgroup.coe_mk] using hthetaProduct)
  have hdynamicEq : rankThreeFirstBinaryAlphaAfterRightMultiplier
      a (theta : Kˣ) = a.firstBinaryAlpha := by
    unfold rankThreeFirstBinaryAlphaAfterRightMultiplier
      BONG.GoodBONG.firstBinaryAlpha
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [hpreserve]
  apply reachableLemma814_rankThree_negative_of_dynamicTheta
    a b horder conditions hlast hepsilonHilbert theta hthetaDepth
  · simpa only [theta, Subgroup.coe_mk] using hthetaLast
  · simpa only [theta, Subgroup.coe_mk] using hthetaEpsilon
  · rw [hdynamicEq, hfirst]
    exact a.alpha_le_lemma814EpsilonDefect b conditions

/-- Complete path-refined anisotropic equal-outer ternary branch.  A positive
first Hilbert sign is the direct binary move.  For a negative sign, Remark
8.7 splits into the half-gap principal-layer detour and the strict
fixed-defect neighbour detour proved above. -/
theorem reachableLemma814_rankThree_anisotropic_of_largeResidue
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hanisotropic : a.Lemma814FirstThreeAnisotropic)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases Int.units_eq_one_or
      (hilbertSymbol K (a.lemma814Epsilon b)
        (a.adjacentProduct (0 : Fin 2))) with hpositive | hnegative
  · exact reachableLemma814_binaryBranch
      a b horder conditions hfirst hpositive
  · by_cases hhalf : a.AttainsHalfGap (0 : Fin 2)
    · exact reachableLemma814_rankThree_negative_of_anisotropic_halfGap
        a b horder conditions houter hanisotropic hnotExceptional hhalf
          hnegative
    · exact reachableLemma814_rankThree_negative_of_anisotropic_notHalfGap
        hres a b horder conditions hfirst hlast houter hanisotropic
          hnotExceptional hhalf hnegative

/-- Strict-reference specialization of the symmetric ternary detour.  The
simultaneous Hilbert choice supplies a right-edge multiplier which is
positive on the last adjacent product and negative on `epsilon`.  Strict
depth above the first adjacent product makes the only required defect
preservation automatic. -/
theorem reachable_rankThree_of_epsilonNegative_of_strictReference
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a b : BONG.GoodBONG q L 3) (D : RankThreeComparisonData a b)
    (hfirstA : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hlastA : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hlastB : b.lastBinaryAlpha =
      (b.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hepsilonNegative : hilbertSymbol K (D.epsilon : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (reference : Kˣ)
    (hrefUnit : IsValuationUnit K (reference : K))
    (hsecondReference :
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) reference)
    (hfirstAdjacentStrict :
      BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2)) <
        BONG.GoodBONG.defectOrder (K := K) reference)
    (hsumEpsilon :
      quadraticDefect K (D.epsilon : Kˣ) +
          quadraticDefect K reference ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hsumEpsilonSecond :
      quadraticDefect K
            ((D.epsilon : Kˣ) * a.adjacentProduct (1 : Fin 2)) +
          quadraticDefect K reference ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ b.valueUnit i) := by
  rcases exists_valuationUnit_hilbert_neg_one_of_two_sums_le
      (D.epsilon : Kˣ) (a.adjacentProduct (1 : Fin 2))
      reference hrefUnit hsumEpsilon hsumEpsilonSecond with
    ⟨thetaRaw, hthetaUnit, hthetaDepth,
      hepsilonTheta, hsecondTheta⟩
  let theta : valuationUnitSubgroup K := ⟨thetaRaw, hthetaUnit⟩
  have hthetaSecondDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) :=
    hsecondReference.trans (by
      simpa only [theta, Subgroup.coe_mk] using hthetaDepth)
  have hthetaStrict : BONG.GoodBONG.defectOrder (K := K)
      (a.adjacentProduct (0 : Fin 2)) <
        BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) :=
    hfirstAdjacentStrict.trans_le (by
      simpa only [theta, Subgroup.coe_mk] using hthetaDepth)
  have hpreserve : BONG.GoodBONG.defectOrder (K := K)
      ((theta : Kˣ) * a.adjacentProduct (0 : Fin 2)) =
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2)) := by
    exact BONG.GoodBONG.defectOrder_mul_eq_right_of_lt_left
      (K := K) hthetaStrict
  apply reachable_rankThree_threeStep_one_zero_one_of_firstDefectPreserved
    a b D hfirstA hlastA hlastB hepsilonNegative theta
      hthetaSecondDepth
  · rw [hilbertSymbol_comm K]
    simpa only [theta, Subgroup.coe_mk] using hsecondTheta
  · rw [hilbertSymbol_comm K]
    simpa only [theta, Subgroup.coe_mk] using hepsilonTheta
  · exact hpreserve

/-- A strict-defect two-step form of the negative-Hilbert branch of
Lemma 8.14 in ternary rank.  The auxiliary multiplier is chosen in a
strictly deeper defect layer than the first adjacent product.  Consequently
the initial right-hand binary move cannot change the first literal binary
alpha.  Its two prescribed Hilbert signs then make the final left-hand move
legal, and that move gives the required first value exactly.

This statement isolates the genuinely difficult boundary of the omitted
binary-connectivity assertion: only the case in which every admissible
auxiliary defect is equal to the first adjacent defect remains. -/
theorem reachableLemma814_rankThree_negative_of_strictReference
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hepsilonHilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (reference : Kˣ)
    (hrefUnit : IsValuationUnit K (reference : K))
    (hsecondReference :
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) reference)
    (hfirstAdjacentStrict :
      BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2)) <
        BONG.GoodBONG.defectOrder (K := K) reference)
    (hsumEpsilon :
      quadraticDefect K (a.lemma814Epsilon b) +
          quadraticDefect K reference ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hsumEpsilonSecond :
      quadraticDefect K
            (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) +
          quadraticDefect K reference ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases exists_valuationUnit_hilbert_neg_one_of_two_sums_le
      (a.lemma814Epsilon b) (a.adjacentProduct (1 : Fin 2))
      reference hrefUnit hsumEpsilon hsumEpsilonSecond with
    ⟨thetaRaw, hthetaUnit, hthetaDepth,
      hepsilonTheta, hsecondTheta⟩
  let theta : valuationUnitSubgroup K := ⟨thetaRaw, hthetaUnit⟩
  have hthetaAlpha : a.adjacentBinaryAlpha (1 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) := by
    calc
      a.adjacentBinaryAlpha (1 : Fin 2) =
          (a.alphaValue (1 : Fin 2) : WithTop ℚ) := hlast
      _ ≤ BONG.GoodBONG.defectOrder (K := K) reference :=
        hsecondReference
      _ ≤ BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) := by
        simpa only [theta, Subgroup.coe_mk] using hthetaDepth
  have hthetaHilbert : hilbertSymbol K
      (a.adjacentProduct (1 : Fin 2)) (theta : Kˣ) = 1 := by
    simpa only [theta, Subgroup.coe_mk] using hsecondTheta
  have hthetaGroup : valuationUnitClassHom K theta ∈
      beliNormGeneratorGroup K
        (a.valueUnit (2 : Fin 3) / a.valueUnit (1 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (1 : Fin 2) theta hthetaAlpha hthetaHilbert
  rcases exists_goodBONG_binaryTransformation_exact a (1 : Fin 2)
      theta hthetaGroup with ⟨c, hcValues⟩
  have hthetaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ c.valueUnit i) :=
    ⟨1, theta, hthetaGroup, hcValues⟩
  have hcAdjacent : c.adjacentProduct (0 : Fin 2) =
      (theta : Kˣ) * a.adjacentProduct (0 : Fin 2) := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hcValues (0 : Fin 2).castSucc,
      congrFun hcValues (0 : Fin 2).succ]
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]
    exact mul_comm _ _
  have hfirstAdjacentTheta :
      BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2)) <
        BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) :=
    hfirstAdjacentStrict.trans_le (by
      simpa only [theta, Subgroup.coe_mk] using hthetaDepth)
  have hcDefect : a.adjacentDefect (0 : Fin 2) =
      c.adjacentDefect (0 : Fin 2) := by
    unfold BONG.GoodBONG.adjacentDefect
    rw [hcAdjacent,
      BONG.GoodBONG.defectOrder_mul_eq_right_of_lt_left
        (K := K) hfirstAdjacentTheta]
  have hcFirstPreserved : c.firstBinaryAlpha = a.firstBinaryAlpha :=
    (rankThree_firstBinaryAlpha_eq_of_firstAdjacentDefect_eq
      a c hcDefect).symm
  have hcFirstAlpha : c.adjacentBinaryAlpha (0 : Fin 2) =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    calc
      c.adjacentBinaryAlpha (0 : Fin 2) = c.firstBinaryAlpha := rfl
      _ = a.firstBinaryAlpha := hcFirstPreserved
      _ = (a.alphaValue (0 : Fin 2) : WithTop ℚ) := hfirst
  let epsilon : valuationUnitSubgroup K :=
    ⟨a.lemma814Epsilon b, a.lemma814Epsilon_isValuationUnit b horder⟩
  have hepsilonDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (epsilon : Kˣ) := by
    simpa only [epsilon, Subgroup.coe_mk] using
      a.alpha_le_lemma814EpsilonDefect b conditions
  have hepsilonHilbert' : hilbertSymbol K
      (c.adjacentProduct (0 : Fin 2)) (epsilon : Kˣ) = 1 := by
    rw [hcAdjacent, hilbertSymbol_comm K, hilbertSymbol_mul_right]
    simpa only [epsilon, theta, Subgroup.coe_mk] using
      (show hilbertSymbol K (a.lemma814Epsilon b) thetaRaw *
          hilbertSymbol K (a.lemma814Epsilon b)
            (a.adjacentProduct (0 : Fin 2)) = 1 by
        rw [hepsilonTheta, hepsilonHilbert]
        norm_num)
  have hepsilonGroup : valuationUnitClassHom K epsilon ∈
      beliNormGeneratorGroup K
        (c.valueUnit (1 : Fin 3) / c.valueUnit (0 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      c (0 : Fin 2) epsilon
    · rw [hcFirstAlpha]
      exact hepsilonDepth
    · exact hepsilonHilbert'
  rcases exists_goodBONG_binaryTransformation_exact c (0 : Fin 2)
      epsilon hepsilonGroup with ⟨d, hdValues⟩
  have hepsilonStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ c.valueUnit i) (fun i ↦ d.valueUnit i) :=
    ⟨0, epsilon, hepsilonGroup, hdValues⟩
  have hcHead : c.valueUnit (0 : Fin 3) = a.valueUnit (0 : Fin 3) := by
    rw [congrFun hcValues (0 : Fin 3)]
    simp [beli2009BinaryTransformAt]
  have hdHead : d.valueUnit (0 : Fin 3) = b.valueUnit (0 : Fin 1) := by
    calc
      d.valueUnit (0 : Fin 3) =
          (epsilon : Kˣ) * c.valueUnit (0 : Fin 3) := by
        rw [congrFun hdValues (0 : Fin 3)]
        rfl
      _ = a.lemma814Epsilon b * a.valueUnit (0 : Fin 3) := by
        rw [hcHead]
      _ = b.valueUnit (0 : Fin 1) :=
        a.lemma814Epsilon_mul_firstValue b
  exact ⟨{
    transform := {
      transformed := d
      firstValue_eq := hdHead
    }
    reachable := hthetaStep.reachable.trans hepsilonStep.reachable
  }⟩

/-- Concatenate a fixed prefix with a coefficient sequence, with the finite
index reassociation needed by the binary-transformation API. -/
def appendPrefixValues
    {P N : Nat} (pre : Fin P → Kˣ) (a : Fin (N + 1) → Kˣ) :
    Fin (P + N + 1) → Kˣ :=
  Fin.append pre a ∘ Fin.cast (by omega)

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
@[simp] theorem appendPrefixValues_castAdd
    {P N : Nat} (pre : Fin P → Kˣ) (a : Fin (N + 1) → Kˣ)
    (i : Fin P) :
    appendPrefixValues pre a (Fin.castAdd (N + 1) i) = pre i := by
  simp [appendPrefixValues]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
@[simp] theorem appendPrefixValues_natAdd
    {P N : Nat} (pre : Fin P → Kˣ) (a : Fin (N + 1) → Kˣ)
    (i : Fin (N + 1)) :
    appendPrefixValues pre a (Fin.natAdd P i) = a i := by
  simp [appendPrefixValues]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
theorem binaryTransformAt_appendPrefixValues
    {P N : Nat} (pre : Fin P → Kˣ) (a : Fin (N + 1) → Kˣ)
    (i : Fin N) (eta : Kˣ) :
    beli2009BinaryTransformAt (appendPrefixValues pre a)
        (Fin.natAdd P i) eta =
      appendPrefixValues pre (beli2009BinaryTransformAt a i eta) := by
  funext j
  refine Fin.addCases (m := P) (n := N + 1) ?_ ?_ j
  · intro k
    have hcast :
        Fin.castAdd (N + 1) k ≠ Fin.natAdd P i.castSucc := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    have hsucc : Fin.castAdd (N + 1) k ≠ (Fin.natAdd P i).succ := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [appendPrefixValues, beli2009BinaryTransformAt,
      Function.update, hcast, hsucc]
  · intro k
    have hcast :
        (Fin.natAdd P i).castSucc = Fin.natAdd P i.castSucc := by
      apply Fin.ext
      simp
    have hsucc : (Fin.natAdd P i).succ = Fin.natAdd P i.succ := by
      apply Fin.ext
      simp
      omega
    simp [appendPrefixValues, beli2009BinaryTransformAt,
      Function.update, hcast, hsucc]

theorem Beli2009ValueSequenceEquivalent.appendPrefix
    {P N : Nat} (pre : Fin P → Kˣ)
    {a b : Fin (N + 1) → Kˣ}
    (h : Beli2009ValueSequenceEquivalent (K := K) a b) :
    Beli2009ValueSequenceEquivalent (K := K)
      (appendPrefixValues pre a) (appendPrefixValues pre b) := by
  intro j
  refine Fin.addCases (m := P) (n := N + 1) ?_ ?_ j
  · intro k
    simp
  · intro k
    simpa [appendPrefixValues] using h k

theorem IsBeli2009BinaryTransformation.appendPrefix
    {P N : Nat} (pre : Fin P → Kˣ)
    {a b : Fin (N + 1) → Kˣ}
    (h : IsBeli2009BinaryTransformation (K := K) a b) :
    IsBeli2009BinaryTransformation (K := K)
      (appendPrefixValues pre a) (appendPrefixValues pre b) := by
  rcases h with ⟨i, eta, heta, rfl⟩
  refine ⟨Fin.natAdd P i, eta, ?_, ?_⟩
  · have hcast :
        (Fin.natAdd P i).castSucc = Fin.natAdd P i.castSucc := by
      apply Fin.ext
      simp
    have hsucc : (Fin.natAdd P i).succ = Fin.natAdd P i.succ := by
      apply Fin.ext
      simp
      omega
    rw [hcast, hsucc]
    simpa using heta
  · exact (binaryTransformAt_appendPrefixValues pre a i (eta : Kˣ)).symm

theorem IsBeli2009BinaryStep.appendPrefix
    {P N : Nat} (pre : Fin P → Kˣ)
    {a b : Fin (N + 1) → Kˣ}
    (h : IsBeli2009BinaryStep (K := K) a b) :
    IsBeli2009BinaryStep (K := K)
      (appendPrefixValues pre a) (appendPrefixValues pre b) := by
  rcases h with h | h
  · exact Or.inl (Beli2009ValueSequenceEquivalent.appendPrefix pre h)
  · exact Or.inr (IsBeli2009BinaryTransformation.appendPrefix pre h)

theorem Beli2009BinaryReachable.appendPrefix
    {P N : Nat} (pre : Fin P → Kˣ)
    {a b : Fin (N + 1) → Kˣ}
    (h : Beli2009BinaryReachable (K := K) a b) :
    Beli2009BinaryReachable (K := K)
      (appendPrefixValues pre a) (appendPrefixValues pre b) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      exact ih.tail (IsBeli2009BinaryStep.appendPrefix pre hstep)

/-- Concatenate a fixed suffix by iterated `Fin.snoc`.  This presentation
keeps all original edge indices definitionally stable. -/
def appendSuffixValues
    {N : Nat} (a : Fin (N + 1) → Kˣ) :
    {S : Nat} → (Fin S → Kˣ) → Fin (N + S + 1) → Kˣ
  | 0, _ => a ∘ Fin.cast (by omega)
  | S + 1, suf =>
      Fin.snoc (appendSuffixValues a (Fin.init suf)) (suf (Fin.last S))

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
def appendSuffixLeftIndex {N S : Nat} (i : Fin (N + 1)) :
    Fin (N + S + 1) :=
  ⟨i.1, by omega⟩

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
@[simp] theorem appendSuffixValues_castAdd
    {N S : Nat} (a : Fin (N + 1) → Kˣ) (suf : Fin S → Kˣ)
    (i : Fin (N + 1)) :
    appendSuffixValues a suf (appendSuffixLeftIndex (S := S) i) = a i := by
  induction S with
  | zero =>
      simp only [appendSuffixValues, Function.comp_apply]
      congr 1
  | succ S ih =>
      have hindex : appendSuffixLeftIndex (S := S + 1) i =
          (appendSuffixLeftIndex (S := S) i).castSucc := by
        apply Fin.ext
        rfl
      rw [hindex, appendSuffixValues, Fin.snoc_castSucc,
        ih (Fin.init suf)]

/-- Index of a fixed-suffix entry in `appendSuffixValues`. -/
def appendSuffixIndex {N S : Nat} (i : Fin S) : Fin (N + S + 1) :=
  ⟨N + 1 + i.1, by omega⟩

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
@[simp] theorem appendSuffixValues_appendSuffixIndex
    {N S : Nat} (a : Fin (N + 1) → Kˣ) (suf : Fin S → Kˣ)
    (i : Fin S) :
    appendSuffixValues a suf (appendSuffixIndex (N := N) i) = suf i := by
  induction S with
  | zero => exact Fin.elim0 i
  | succ S ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hindex : appendSuffixIndex (N := N) (Fin.last S) =
            Fin.last (N + S + 1) := by
          apply Fin.ext
          simp [appendSuffixIndex]
          omega
        rw [hindex, appendSuffixValues]
        exact Fin.snoc_last (n := N + S + 1)
          (α := fun _ => Kˣ) (suf (Fin.last S))
          (appendSuffixValues a (Fin.init suf))
      · have hindex : appendSuffixIndex (N := N) j.castSucc =
            (appendSuffixIndex (N := N) j).castSucc := by
          apply Fin.ext
          rfl
        rw [hindex, appendSuffixValues, Fin.snoc_castSucc,
          ih (Fin.init suf)]
        rfl

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
theorem binaryTransformAt_appendSuffixValues
    {N S : Nat} (a : Fin (N + 1) → Kˣ) (suf : Fin S → Kˣ)
    (i : Fin N) (eta : Kˣ) :
    beli2009BinaryTransformAt (appendSuffixValues a suf)
        (Fin.castAdd S i) eta =
      appendSuffixValues (beli2009BinaryTransformAt a i eta) suf := by
  induction S with
  | zero =>
      funext j
      simp [appendSuffixValues, beli2009BinaryTransformAt, Function.update]
  | succ S ih =>
      have hindex : Fin.castAdd (S + 1) i =
          (Fin.castAdd S i).castSucc := by
        apply Fin.ext
        rfl
      rw [hindex, appendSuffixValues, binaryTransformAt_snoc,
        ih (Fin.init suf)]
      rfl

theorem Beli2009ValueSequenceEquivalent.appendSuffix
    {N S : Nat} (suf : Fin S → Kˣ)
    {a b : Fin (N + 1) → Kˣ}
    (h : Beli2009ValueSequenceEquivalent (K := K) a b) :
    Beli2009ValueSequenceEquivalent (K := K)
      (appendSuffixValues a suf) (appendSuffixValues b suf) := by
  induction S with
  | zero =>
      simpa [appendSuffixValues] using h
  | succ S ih =>
      change Beli2009ValueSequenceEquivalent (K := K)
        (Fin.snoc (appendSuffixValues a (Fin.init suf)) (suf (Fin.last S)))
        (Fin.snoc (appendSuffixValues b (Fin.init suf)) (suf (Fin.last S)))
      exact Beli2009ValueSequenceEquivalent.snoc (suf (Fin.last S))
        (ih (Fin.init suf))

theorem IsBeli2009BinaryTransformation.appendSuffix
    {N S : Nat} (suf : Fin S → Kˣ)
    {a b : Fin (N + 1) → Kˣ}
    (h : IsBeli2009BinaryTransformation (K := K) a b) :
    IsBeli2009BinaryTransformation (K := K)
      (appendSuffixValues a suf) (appendSuffixValues b suf) := by
  induction S with
  | zero =>
      simpa [appendSuffixValues] using h
  | succ S ih =>
      change IsBeli2009BinaryTransformation (K := K)
        (Fin.snoc (appendSuffixValues a (Fin.init suf)) (suf (Fin.last S)))
        (Fin.snoc (appendSuffixValues b (Fin.init suf)) (suf (Fin.last S)))
      exact IsBeli2009BinaryTransformation.snoc (suf (Fin.last S))
        (ih (Fin.init suf))

theorem IsBeli2009BinaryStep.appendSuffix
    {N S : Nat} (suf : Fin S → Kˣ)
    {a b : Fin (N + 1) → Kˣ}
    (h : IsBeli2009BinaryStep (K := K) a b) :
    IsBeli2009BinaryStep (K := K)
      (appendSuffixValues a suf) (appendSuffixValues b suf) := by
  rcases h with h | h
  · exact Or.inl (Beli2009ValueSequenceEquivalent.appendSuffix suf h)
  · exact Or.inr (IsBeli2009BinaryTransformation.appendSuffix suf h)

theorem Beli2009BinaryReachable.appendSuffix
    {N S : Nat} (suf : Fin S → Kˣ)
    {a b : Fin (N + 1) → Kˣ}
    (h : Beli2009BinaryReachable (K := K) a b) :
    Beli2009BinaryReachable (K := K)
      (appendSuffixValues a suf) (appendSuffixValues b suf) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      exact ih.tail (IsBeli2009BinaryStep.appendSuffix suf hstep)

/-- Reindex both endpoints of a reachability path along equality of the
number of adjacent edges. -/
theorem Beli2009BinaryReachable.castEdgeCount
    {M N : Nat} (h : M = N)
    {a b : Fin (M + 1) → Kˣ}
    (R : Beli2009BinaryReachable (K := K) a b) :
    Beli2009BinaryReachable (K := K)
      (fun i : Fin (N + 1) ↦
        a (Fin.cast (congrArg (fun z => z + 1) h).symm i))
      (fun i : Fin (N + 1) ↦
        b (Fin.cast (congrArg (fun z => z + 1) h).symm i)) := by
  subst N
  simpa using R

@[simp] theorem valueUnit_castLength_connectivity
    {X : Type*} [AddCommGroup X] [Module K X]
    {f : QuadraticSpace K X} {M : Lattice K X} {m n : Nat}
    (b : BONG.GoodBONG f M m) (h : m = n) (i : Fin n) :
    (b.castLength h).valueUnit i = b.valueUnit ⟨i.1, by omega⟩ := by
  subst n
  rfl

/-- Values before a replaced segment are unchanged. -/
theorem segmentReplacement_valueUnit_before
    {n start length : Nat} {bound : start + length ≤ n}
    (b : BONG.GoodBONG q L n)
    (w : BONG.SegmentWitness b.toBONG start length bound)
    (c : BONG.GoodBONG (q.restrict w.carrier w.nondegenerate)
      w.lattice length)
    (R : BONG.SegmentReplacementWitness b.toBONG w c.toBONG)
    (i : Fin n) (hi : i.1 < start) :
    (⟨R.bong, R.good⟩ : BONG.GoodBONG q L n).valueUnit i =
      b.valueUnit i := by
  apply Units.ext
  change R.bong.value i = b.toBONG.value i
  rw [← R.bong.quadratic_ambientVector,
    ← b.toBONG.quadratic_ambientVector, R.before_eq i hi]

/-- Values inside a replaced segment are exactly its new local values. -/
theorem segmentReplacement_valueUnit_inside
    {n start length : Nat} {bound : start + length ≤ n}
    (b : BONG.GoodBONG q L n)
    (w : BONG.SegmentWitness b.toBONG start length bound)
    (c : BONG.GoodBONG (q.restrict w.carrier w.nondegenerate)
      w.lattice length)
    (R : BONG.SegmentReplacementWitness b.toBONG w c.toBONG)
    (i : Fin length) :
    (⟨R.bong, R.good⟩ : BONG.GoodBONG q L n).valueUnit
        ⟨start + i.1, by omega⟩ = c.valueUnit i := by
  apply Units.ext
  change R.bong.value ⟨start + i.1, by omega⟩ = c.toBONG.value i
  rw [← R.bong.quadratic_ambientVector,
    ← c.toBONG.quadratic_ambientVector, R.inside_eq i]
  rfl

/-- Values after a replaced segment are unchanged. -/
theorem segmentReplacement_valueUnit_after
    {n start length : Nat} {bound : start + length ≤ n}
    (b : BONG.GoodBONG q L n)
    (w : BONG.SegmentWitness b.toBONG start length bound)
    (c : BONG.GoodBONG (q.restrict w.carrier w.nondegenerate)
      w.lattice length)
    (R : BONG.SegmentReplacementWitness b.toBONG w c.toBONG)
    (i : Fin n) (hi : start + length ≤ i.1) :
    (⟨R.bong, R.good⟩ : BONG.GoodBONG q L n).valueUnit i =
      b.valueUnit i := by
  apply Units.ext
  change R.bong.value i = b.toBONG.value i
  rw [← R.bong.quadratic_ambientVector,
    ← b.toBONG.quadratic_ambientVector, R.after_eq i hi]

/-- A binary path on an initial segment lifts through its global segment
replacement while the final `S` coefficients remain fixed. -/
theorem reachable_of_prefixSegmentReplacement
    {n M S : Nat} (hrank : n = M + S + 1)
    (b : BONG.GoodBONG q L n)
    (w : BONG.SegmentWitness b.toBONG 0 (M + 1) (by omega))
    (c : BONG.GoodBONG (q.restrict w.carrier w.nondegenerate)
      w.lattice (M + 1))
    (R : BONG.SegmentReplacementWitness b.toBONG w c.toBONG)
    (hlocal : Beli2009BinaryReachable (K := K)
      (fun i ↦ (w.toGoodBONG b.good).valueUnit i)
      (fun i ↦ c.valueUnit i)) :
    Beli2009BinaryReachable (K := K)
      (fun i : Fin (M + S + 1) ↦ b.valueUnit (Fin.cast hrank.symm i))
      (fun i : Fin (M + S + 1) ↦
        (⟨R.bong, R.good⟩ : BONG.GoodBONG q L n).valueUnit
          (Fin.cast hrank.symm i)) := by
  subst n
  let suf : Fin S → Kˣ := fun j ↦
    b.valueUnit ⟨M + 1 + j.1, by omega⟩
  have hlift := Beli2009BinaryReachable.appendSuffix suf hlocal
  have hsource : appendSuffixValues
      (fun i ↦ (w.toGoodBONG b.good).valueUnit i) suf =
      (fun i ↦ b.valueUnit i) := by
    funext j
    by_cases hj : j.1 < M + 1
    · let k : Fin (M + 1) := ⟨j.1, hj⟩
      have hindex : j = appendSuffixLeftIndex (S := S) k := by
        apply Fin.ext
        rfl
      rw [hindex, appendSuffixValues_castAdd]
      change w.bong.valueUnit k = b.toBONG.valueUnit j
      rw [w.valueUnit_eq]
      congr 1
      apply Fin.ext
      simp [BONG.SegmentWitness.sourceIndex, k]
    · let k : Fin S := ⟨j.1 - (M + 1), by omega⟩
      have hindex : j = appendSuffixIndex (N := M) k := by
        apply Fin.ext
        simp [appendSuffixIndex, k]
        omega
      rw [hindex, appendSuffixValues_appendSuffixIndex]
      rfl
  have htarget : appendSuffixValues (fun i ↦ c.valueUnit i) suf =
      (fun i ↦
        (⟨R.bong, R.good⟩ : BONG.GoodBONG q L (M + S + 1)).valueUnit i) := by
    funext j
    by_cases hj : j.1 < M + 1
    · let k : Fin (M + 1) := ⟨j.1, hj⟩
      have hindex : j = appendSuffixLeftIndex (S := S) k := by
        apply Fin.ext
        rfl
      rw [hindex, appendSuffixValues_castAdd]
      have hinside := segmentReplacement_valueUnit_inside b w c R k
      simpa [appendSuffixLeftIndex] using hinside.symm
    · let k : Fin S := ⟨j.1 - (M + 1), by omega⟩
      have hindex : j = appendSuffixIndex (N := M) k := by
        apply Fin.ext
        simp [appendSuffixIndex, k]
        omega
      rw [hindex, appendSuffixValues_appendSuffixIndex]
      have hafter := segmentReplacement_valueUnit_after b w c R
        (appendSuffixIndex (N := M) k) (by
          simp [appendSuffixIndex])
      simpa [suf, appendSuffixIndex] using hafter.symm
  rw [hsource, htarget] at hlift
  simpa using hlift

/-- A binary path on a final segment lifts through its global segment
replacement while the first `P` coefficients remain fixed. -/
theorem reachable_of_suffixSegmentReplacement
    {n P M : Nat} (hrank : n = P + M + 1)
    (b : BONG.GoodBONG q L n)
    (w : BONG.SegmentWitness b.toBONG P (M + 1) (by omega))
    (c : BONG.GoodBONG (q.restrict w.carrier w.nondegenerate)
      w.lattice (M + 1))
    (R : BONG.SegmentReplacementWitness b.toBONG w c.toBONG)
    (hlocal : Beli2009BinaryReachable (K := K)
      (fun i ↦ (w.toGoodBONG b.good).valueUnit i)
      (fun i ↦ c.valueUnit i)) :
    Beli2009BinaryReachable (K := K)
      (fun i : Fin (P + M + 1) ↦ b.valueUnit (Fin.cast hrank.symm i))
      (fun i : Fin (P + M + 1) ↦
        (⟨R.bong, R.good⟩ : BONG.GoodBONG q L n).valueUnit
          (Fin.cast hrank.symm i)) := by
  subst n
  let pre : Fin P → Kˣ := fun j ↦
    b.valueUnit ⟨j.1, by omega⟩
  have hlift := Beli2009BinaryReachable.appendPrefix pre hlocal
  have hsource : appendPrefixValues pre
      (fun i ↦ (w.toGoodBONG b.good).valueUnit i) =
      (fun i ↦ b.valueUnit i) := by
    funext j
    refine Fin.addCases (m := P) (n := M + 1) ?_ ?_ j
    · intro k
      simp [pre]
      congr 1
    · intro k
      rw [appendPrefixValues_natAdd]
      change w.bong.valueUnit k = b.toBONG.valueUnit (Fin.natAdd P k)
      rw [w.valueUnit_eq]
      congr 1
  have htarget : appendPrefixValues pre (fun i ↦ c.valueUnit i) =
      (fun i ↦
        (⟨R.bong, R.good⟩ : BONG.GoodBONG q L (P + M + 1)).valueUnit i) := by
    funext j
    refine Fin.addCases (m := P) (n := M + 1) ?_ ?_ j
    · intro k
      rw [appendPrefixValues_castAdd]
      have hbefore := segmentReplacement_valueUnit_before b w c R
        (Fin.castAdd (M + 1) k) (by simp)
      have hpreIndex : (⟨k.1, by omega⟩ : Fin (P + M + 1)) =
          Fin.castAdd (M + 1) k := by
        apply Fin.ext
        rfl
      rw [show pre k = b.valueUnit ⟨k.1, by omega⟩ by rfl,
        hpreIndex]
      exact hbefore.symm
    · intro k
      rw [appendPrefixValues_natAdd]
      have hinside := segmentReplacement_valueUnit_inside b w c R k
      have hinsideIndex : (⟨P + k.1, by omega⟩ : Fin (P + M + 1)) =
          Fin.natAdd P k := by
        apply Fin.ext
        simp
      rw [← hinsideIndex]
      exact hinside.symm
  rw [hsource, htarget] at hlift
  simpa using hlift

/-- Corollary 8.11 together with an explicit chain of adjacent binary
transformations producing its normal form. -/
structure ReachableCorollary811Data
    {N : Nat} (b : BONG.GoodBONG q L (N + 2)) (i : Fin (N + 1)) where
  data : b.Beli2019Corollary811Data i
  reachable : Beli2009BinaryReachable (K := K)
    (fun j ↦ b.valueUnit j) (fun j ↦ data.transformed.valueUnit j)

/-- Path-refined Beli (2019), Corollary 8.11 over residue fields with more
than two elements. -/
theorem reachableCorollary811_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    {N : Nat} (b : BONG.GoodBONG q L (N + 2)) (i : Fin (N + 1))
    (hresidueMore : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableCorollary811Data b i) := by
  classical
  let p := BONG.GoodBONG.prefixPairLocalization i
  let s := BONG.GoodBONG.suffixPairLocalization i
  rcases b.toBONG.exists_segmentWitness p.start p.length p.bound with ⟨wp⟩
  rcases b.toBONG.exists_segmentWitness s.start s.length s.bound with ⟨ws⟩
  let bp := wp.toGoodBONG b.good
  let bs := ws.toGoodBONG b.good
  have hmin : (b.alphaValue i : WithTop ℚ) =
      min (bp.alphaValue p.localPivot : WithTop ℚ)
        (bs.alphaValue s.localPivot : WithTop ℚ) := by
    simpa only [p, s, bp, bs] using
      b.alpha_eq_min_prefixSuffixSegmentAlpha i wp ws
  rcases le_total
      (bp.alphaValue p.localPivot : WithTop ℚ)
      (bs.alphaValue s.localPivot : WithTop ℚ) with hprefix | hsuffix
  · have hchosen : (b.alphaValue i : WithTop ℚ) =
        (bp.alphaValue p.localPivot : WithTop ℚ) :=
      hmin.trans (min_eq_left hprefix)
    have hpDiff : p.stop - p.start = i.1 + 1 := by
      dsimp [p, BONG.GoodBONG.prefixPairLocalization]
    let hpRank : p.length = (i.1 + 1) + 1 :=
      congrArg (fun k => k + 1) hpDiff
    let bpExact : BONG.GoodBONG
        (q.restrict wp.carrier wp.nondegenerate) wp.lattice
        ((i.1 + 1) + 1) :=
      bp.castLength hpRank
    rcases reachableCorollary810_right_of_largeResidue bpExact
        hresidueMore with ⟨DR⟩
    let D := DR.data
    let c : BONG.GoodBONG
        (q.restrict wp.carrier wp.nondegenerate) wp.lattice p.length :=
      D.transformed.castLength hpRank.symm
    have hlocalCast :=
      Beli2009BinaryReachable.castEdgeCount hpDiff.symm DR.reachable
    have hlocal : Beli2009BinaryReachable (K := K)
        (fun j ↦ bp.valueUnit j) (fun j ↦ c.valueUnit j) := by
      convert hlocalCast using 1 <;>
        funext j <;>
        simp only [bpExact, c, valueUnit_castLength_connectivity] <;>
        congr 1
    have hsegmentAlphas := bpExact.alpha_invariant D.transformed
    have hc : c.adjacentBinaryAlpha p.localPivot =
        (bp.alphaValue p.localPivot : WithTop ℚ) := by
      calc
        c.adjacentBinaryAlpha p.localPivot =
            D.transformed.adjacentBinaryAlpha
              (Fin.cast (hpDiff.symm).symm p.localPivot) :=
          D.transformed.adjacentBinaryAlpha_castLength
            hpDiff.symm p.localPivot
        _ = D.transformed.lastBinaryAlpha :=
          congrArg D.transformed.adjacentBinaryAlpha (Eq.refl _)
        _ = (D.transformed.alphaValue (Fin.last i.1) : WithTop ℚ) :=
          D.lastBinaryAlpha_eq
        _ = (bp.alphaValue p.localPivot : WithTop ℚ) :=
          congrArg (fun x : ℚ => (x : WithTop ℚ))
            (hsegmentAlphas (Fin.last i.1)).symm
    rcases b.toBONG.beliLemma49_ii b.good wp c.toBONG c.good with ⟨R⟩
    let transformed : BONG.GoodBONG q L (N + 2) := ⟨R.bong, R.good⟩
    have hpivot : p.pivotFin = i := Eq.refl _
    have hinside := b.adjacentBinaryAlpha_eq_of_segmentReplacement p wp c R
    rw [hpivot] at hinside
    have hglobalAlphas := b.alpha_invariant transformed
    let htotal : N + 2 =
        (p.stop - p.start) + (N - i.1) + 1 := by
      dsimp [p, BONG.GoodBONG.prefixPairLocalization]
      omega
    have hglobalCast := reachable_of_prefixSegmentReplacement
      htotal b wp c R hlocal
    have hedge : (p.stop - p.start) + (N - i.1) = N + 1 := by
      dsimp [p, BONG.GoodBONG.prefixPairLocalization]
      omega
    have hglobalReindexed :=
      Beli2009BinaryReachable.castEdgeCount hedge hglobalCast
    have hglobal : Beli2009BinaryReachable (K := K)
        (fun j ↦ b.valueUnit j) (fun j ↦ transformed.valueUnit j) := by
      convert hglobalReindexed using 1 <;>
        funext j <;>
        congr 1
    exact ⟨{
      data := {
        transformed := transformed
        adjacentBinaryAlpha_eq := by
          calc
            transformed.adjacentBinaryAlpha i =
                c.adjacentBinaryAlpha p.localPivot := hinside
            _ = (bp.alphaValue p.localPivot : WithTop ℚ) := hc
            _ = (b.alphaValue i : WithTop ℚ) := hchosen.symm
            _ = (transformed.alphaValue i : WithTop ℚ) :=
              congrArg (fun x : ℚ => (x : WithTop ℚ)) (hglobalAlphas i)
      }
      reachable := hglobal
    }⟩
  · have hchosen : (b.alphaValue i : WithTop ℚ) =
        (bs.alphaValue s.localPivot : WithTop ℚ) :=
      hmin.trans (min_eq_right hsuffix)
    have hsDiff : s.stop - s.start = (N - i.1) + 1 := by
      dsimp [s, BONG.GoodBONG.suffixPairLocalization]
      omega
    let hsRank : s.length = ((N - i.1) + 1) + 1 :=
      congrArg (fun k => k + 1) hsDiff
    let bsExact : BONG.GoodBONG
        (q.restrict ws.carrier ws.nondegenerate) ws.lattice
        (((N - i.1) + 1) + 1) :=
      bs.castLength hsRank
    rcases reachableCorollary810_of_largeResidue bsExact
        hresidueMore with ⟨DR⟩
    let D := DR.data
    let c : BONG.GoodBONG
        (q.restrict ws.carrier ws.nondegenerate) ws.lattice s.length :=
      D.transformed.castLength hsRank.symm
    have hlocalCast :=
      Beli2009BinaryReachable.castEdgeCount hsDiff.symm DR.reachable
    have hlocal : Beli2009BinaryReachable (K := K)
        (fun j ↦ bs.valueUnit j) (fun j ↦ c.valueUnit j) := by
      convert hlocalCast using 1 <;>
        funext j <;>
        simp only [bsExact, c, valueUnit_castLength_connectivity] <;>
        congr 1
    have hlocalZero : Fin.cast hsDiff s.localPivot =
        (0 : Fin ((N - i.1) + 1)) := by
      apply Fin.ext
      dsimp [s, BONG.GoodBONG.suffixPairLocalization,
        AlphaLocalizationIndex.localPivot]
      omega
    have hzeroLocal : Fin.cast hsDiff.symm
        (0 : Fin ((N - i.1) + 1)) = s.localPivot := by
      apply Fin.ext
      dsimp [s, BONG.GoodBONG.suffixPairLocalization,
        AlphaLocalizationIndex.localPivot]
      omega
    have hsegmentAlphas := bsExact.alpha_invariant D.transformed
    have hlocalZero' : Fin.cast (hsDiff.symm).symm s.localPivot =
        (0 : Fin ((N - i.1) + 1)) := by
      apply Fin.ext
      change i.1 - i.1 = 0
      omega
    have htransportAlpha : bsExact.alphaValue
        (0 : Fin ((N - i.1) + 1)) = bs.alphaValue s.localPivot := by
      calc
        bsExact.alphaValue (0 : Fin ((N - i.1) + 1)) =
            (bs.castLength
              (congrArg (fun k => k + 1) hsDiff)).alphaValue
                (0 : Fin ((N - i.1) + 1)) := rfl
        _ = bs.alphaValue (Fin.cast hsDiff.symm
            (0 : Fin ((N - i.1) + 1))) :=
          BONG.GoodBONG.alphaValue_castLength' bs hsDiff
            (0 : Fin ((N - i.1) + 1))
        _ = bs.alphaValue s.localPivot := congrArg bs.alphaValue hzeroLocal
    have hc : c.adjacentBinaryAlpha s.localPivot =
        (bs.alphaValue s.localPivot : WithTop ℚ) := by
      calc
        c.adjacentBinaryAlpha s.localPivot =
            D.transformed.adjacentBinaryAlpha
              (Fin.cast (hsDiff.symm).symm s.localPivot) :=
          D.transformed.adjacentBinaryAlpha_castLength
            hsDiff.symm s.localPivot
        _ = D.transformed.firstBinaryAlpha :=
          congrArg D.transformed.adjacentBinaryAlpha hlocalZero'
        _ = (D.transformed.alphaValue
            (0 : Fin ((N - i.1) + 1)) : WithTop ℚ) :=
          D.firstBinaryAlpha_eq
        _ = (bsExact.alphaValue
            (0 : Fin ((N - i.1) + 1)) : WithTop ℚ) :=
          congrArg (fun x : ℚ => (x : WithTop ℚ))
            (hsegmentAlphas (0 : Fin ((N - i.1) + 1))).symm
        _ = (bs.alphaValue s.localPivot : WithTop ℚ) := by
          exact congrArg (fun x : ℚ => (x : WithTop ℚ)) htransportAlpha
    rcases b.toBONG.beliLemma49_ii b.good ws c.toBONG c.good with ⟨R⟩
    let transformed : BONG.GoodBONG q L (N + 2) := ⟨R.bong, R.good⟩
    have hspivot : s.pivotFin = i := Eq.refl _
    have hinside := b.adjacentBinaryAlpha_eq_of_segmentReplacement s ws c R
    rw [hspivot] at hinside
    have hglobalAlphas := b.alpha_invariant transformed
    let htotal : N + 2 = s.start + (s.stop - s.start) + 1 := by
      dsimp [s, BONG.GoodBONG.suffixPairLocalization]
      omega
    have hglobalCast := reachable_of_suffixSegmentReplacement
      htotal b ws c R hlocal
    have hedge : s.start + (s.stop - s.start) = N + 1 := by
      dsimp [s, BONG.GoodBONG.suffixPairLocalization]
      omega
    have hglobalReindexed :=
      Beli2009BinaryReachable.castEdgeCount hedge hglobalCast
    have hglobal : Beli2009BinaryReachable (K := K)
        (fun j ↦ b.valueUnit j) (fun j ↦ transformed.valueUnit j) := by
      convert hglobalReindexed using 1 <;>
        funext j <;>
        congr 1
    exact ⟨{
      data := {
        transformed := transformed
        adjacentBinaryAlpha_eq := by
          calc
            transformed.adjacentBinaryAlpha i =
                c.adjacentBinaryAlpha s.localPivot := hinside
            _ = (bs.alphaValue s.localPivot : WithTop ℚ) := hc
            _ = (b.alphaValue i : WithTop ℚ) := hchosen.symm
            _ = (transformed.alphaValue i : WithTop ℚ) :=
              congrArg (fun x : ℚ => (x : WithTop ℚ)) (hglobalAlphas i)
      }
      reachable := hglobal
    }⟩

/-! ## Path-refined Section 9 normalization data -/

/-- If the literal adjacent binary block at a shifted boundary realizes the
global alpha, deleting the head preserves that alpha.  This is the
index-uniform form of the local calculation used after Corollary 8.11 in
Lemma 9.3. -/
theorem alphaValue_succ_eq_tail_of_adjacentBinaryAlpha_succ
    {N : Nat} (c : BONG.GoodBONG q L (N + 3))
    (p : Fin (N + 1))
    (hlocal : c.adjacentBinaryAlpha p.succ =
      (c.alphaValue p.succ : WithTop ℚ)) :
    c.alphaValue p.succ = c.tail.alphaValue p := by
  have hshift := c.alpha_shift_le_tail p
  have hhalf := c.tail.alpha_le_halfGapCandidate p
  rw [c.halfGapCandidate_tail] at hhalf
  have hleft := c.tail.alpha_le_leftDefectCandidate
    (i := p) (j := p) le_rfl
  rw [c.leftDefectCandidate_tail] at hleft
  have htailLocal :
      c.tail.alpha p ≤ c.adjacentBinaryAlpha p.succ := by
    unfold BONG.GoodBONG.adjacentBinaryAlpha
    exact le_min hhalf hleft
  rw [c.coe_alphaValue] at hlocal
  apply WithTop.coe_injective
  rw [c.coe_alphaValue, c.tail.coe_alphaValue]
  exact le_antisymm hshift (htailLocal.trans_eq hlocal)

/-- The source normalization used in the first branch of Lemma 9.3,
together with the actual adjacent-binary path producing it. -/
structure ReachableLemma93SourceTailNormalization
    {N : Nat} (b : BONG.GoodBONG q L (N + 4)) where
  data : b.Beli2019Lemma93SourceTailNormalization
  reachable : Beli2009BinaryReachable (K := K)
    (fun i => b.valueUnit i) (fun i => data.transformed.valueUnit i)

/-- Over a residue field with more than two elements, the source
normalization in Lemma 9.3 is supplied by the path-refined Corollary 8.11.
The single local equality then propagates to every later boundary. -/
theorem reachableLemma93SourceTailNormalization_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    {N : Nat} (b : BONG.GoodBONG q L (N + 4))
    (hresidueMore : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableLemma93SourceTailNormalization b) := by
  rcases reachableCorollary811_of_largeResidue b
      (1 : Fin (N + 3)) hresidueMore with ⟨D⟩
  have hbase :
      D.data.transformed.alphaValue (1 : Fin (N + 3)) =
        D.data.transformed.tail.alphaValue (0 : Fin (N + 2)) :=
    alphaValue_succ_eq_tail_of_adjacentBinaryAlpha_succ
      D.data.transformed (0 : Fin (N + 2)) (by
        simpa using D.data.adjacentBinaryAlpha_eq)
  refine ⟨{
    data := {
      transformed := D.data.transformed
      adjacentBinaryAlpha_eq := D.data.adjacentBinaryAlpha_eq
      alpha_shift_eq_tail := ?_
    }
    reachable := D.reachable
  }⟩
  intro i
  exact D.data.transformed.alphaValue_shift_eq_tail_of_base_eq
    (0 : Fin (N + 2)) i (Fin.zero_le i) hbase

/-- The rank-three Case 2 source-head normalization from Lemma 9.3,
together with the adjacent-binary path that produces it. -/
structure ReachableCaseTwoSourceHeadNormalizationRankThree
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 3) where
  data : BONG.GoodBONG.Beli2019Lemma93CaseTwoSourceHeadNormalizationRankThree a b
  reachable : Beli2009BinaryReachable (K := K)
    (fun i => b.valueUnit i) (fun i => data.transformed.valueUnit i)

/-- Over a residue field with more than two elements, the Case 2
normalization in the ternary base case is exactly the path-refined
Lemma 8.8 transformation. -/
theorem reachable_caseTwoSourceHeadNormalization_rankThree_of_largeResidue
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [BinaryNormGeneratorLocalLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 3)
    (hfirst : a.order (0 : Fin 3) = b.order (0 : Fin 3))
    (hcase : a.Beli2019Lemma93CaseTwoConditionRankThree b)
    (hresidueMore : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableCaseTwoSourceHeadNormalizationRankThree a b) := by
  let raw := BONG.GoodBONG.defectOrder (K := K)
    ((-1) * a.prefixProduct 3 * b.prefixProduct 1)
  have hrawLe : (b.alphaValue (0 : Fin 2) : WithTop ℚ) ≤ raw := by
    have hle := a.truncatedPrefixDefect_le_defect b (-1) 3 1
    exact hcase.1 ▸ hle
  by_cases hrawEq : raw = (b.alphaValue (0 : Fin 2) : WithTop ℚ)
  · exact ⟨{
      data := {
        transformed := b
        firstThirdRawDefect_eq := hrawEq
      }
      reachable := Relation.ReflTransGen.refl
    }⟩
  · have hstrictAlpha :=
      a.sourceFirstAlpha_lt_halfGap_of_caseTwo_rankThree b hfirst hcase
    have hnotExceptional : ¬b.Beli2019Lemma88Exceptional := by
      rintro ⟨hhalf, _⟩
      exact (ne_of_lt hstrictAlpha) hhalf
    rcases reachableLemma88_sufficiency_of_largeResidue b
        hnotExceptional hresidueMore with ⟨T⟩
    have hstrict : (b.alphaValue (0 : Fin 2) : WithTop ℚ) < raw :=
      lt_of_le_of_ne hrawLe (fun h => hrawEq h.symm)
    have hproduct :
        (-1 : Kˣ) * a.prefixProduct 3 *
              T.transform.transformed.prefixProduct 1 =
          T.transform.epsilon *
            ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
      rw [T.transform.prefixProduct_one_eq_rankThree]
      ac_rfl
    refine ⟨{
      data := {
        transformed := T.transform.transformed
        firstThirdRawDefect_eq := ?_
      }
      reachable := T.reachable
    }⟩
    rw [hproduct,
      BONG.GoodBONG.defectOrder_mul_eq_left_of_lt_right (K := K)
        (T.transform.epsilon_defect ▸ hstrict),
      T.transform.epsilon_defect]

/-- Lemma 9.2 together with the concrete adjacent-binary path producing
its selected good BONG.  The paper's statement only records the endpoint;
the extra field is what is needed to use Lemma 9.3 in a connectivity proof.
-/
structure ReachableLemma92Transform
    {N : Nat} (a : BONG.GoodBONG q L (N + 4)) where
  transform : a.Beli2019Lemma92Transform
  reachable : Beli2009BinaryReachable (K := K)
    (fun i => a.valueUnit i)
    (fun i => transform.transformed.valueUnit i)

/-- A self-tail agreement already supplied by a reachable good BONG gives
the path-refined form of Lemma 9.2 without any further choice. -/
noncomputable def reachableLemma92TransformOfSelfTailAgreement
    [GoodBONGClassificationLaws.{u, v, v} K]
    {N : Nat} (a c : BONG.GoodBONG q L (N + 4))
    (reachable : Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => c.valueUnit i))
    (hfirst : c.valueUnit (0 : Fin (N + 4)) =
      a.valueUnit (0 : Fin (N + 4)))
    (hlater : ∀ (i : Fin (N + 2)), 2 ≤ i.1 →
      c.alphaValue i.succ = c.tail.alphaValue i)
    (hearly : a.Lemma92EarlyAlternative →
      c.alphaValue (2 : Fin (N + 3)) =
        c.tail.alphaValue (1 : Fin (N + 2))) :
    ReachableLemma92Transform a where
  transform := BONG.GoodBONG.lemma92TransformOfSelfTailAgreement
    a c hfirst hlater hearly
  reachable := reachable

/-- The identity endpoint is the base case of the path-refined Lemma 9.2
construction. -/
noncomputable def reachableLemma92TransformIdentity
    [GoodBONGClassificationLaws.{u, v, v} K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 4))
    (hlater : ∀ (i : Fin (N + 2)), 2 ≤ i.1 →
      a.alphaValue i.succ = a.tail.alphaValue i)
    (hearly : a.Lemma92EarlyAlternative →
      a.alphaValue (2 : Fin (N + 3)) =
        a.tail.alphaValue (1 : Fin (N + 2))) :
    ReachableLemma92Transform a :=
  reachableLemma92TransformOfSelfTailAgreement a a
    (beli2009BinaryReachable_refl _) rfl hlater hearly

/-- The normalized pair of Lemma 9.3, augmented by paths from the two BONGs
with which the connectivity problem started. -/
structure ReachableLemma93NormalizedPair
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} {N : Nat}
    (a : BONG.GoodBONG q L (N + 4))
    (b : BONG.GoodBONG r M (N + 4)) where
  pair : BONG.GoodBONG.Beli2019Lemma93NormalizedPair a b
  targetReachable : Beli2009BinaryReachable (K := K)
    (fun i => a.valueUnit i)
    (fun i => pair.targetTransform.transformed.valueUnit i)
  sourceReachable : Beli2009BinaryReachable (K := K)
    (fun i => b.valueUnit i)
    (fun i => pair.sourceTransform.transformed.valueUnit i)

/-- Assemble the preceding path-refined pair from a reachable head choice
and two reachable Lemma 9.2 transforms. -/
noncomputable def ReachableLemma93NormalizedPair.ofTransforms
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} {N : Nat}
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    (a : BONG.GoodBONG q L (N + 4))
    (b : BONG.GoodBONG r M (N + 4))
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (c : BONG.GoodBONG q L (N + 4))
    (d : BONG.GoodBONG r M (N + 4))
    (hcFirst : c.valueUnit (0 : Fin (N + 4)) =
      d.valueUnit (0 : Fin (N + 4)))
    (hc : Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => c.valueUnit i))
    (hd : Beli2009BinaryReachable (K := K)
      (fun i => b.valueUnit i) (fun i => d.valueUnit i))
    (Ta : ReachableLemma92Transform c)
    (Tb : ReachableLemma92Transform d) :
    ReachableLemma93NormalizedPair a b where
  pair := BONG.GoodBONG.Beli2019Lemma93NormalizedPair.ofTransforms
    (classificationV := classificationV)
    (classificationW := classificationW)
    a b conditions c d hcFirst Ta.transform Tb.transform
  targetReachable := hc.trans Ta.reachable
  sourceReachable := hd.trans Tb.reachable

/-! ## Lifting a projected-tail path through an aligned head -/

/-- Once the two selected heads have equal value, an isometry from the
source projected lattice to the target projected lattice lets us compare the
two tails on one literal lattice.  A binary-transformation path between the
target tail and the transported source tail then lifts by `Fin.cons` to a
path between the two full BONG value sequences. -/
theorem reachable_of_headValue_eq_of_mappedTail_reachable
    {N : Nat} (c d : BONG.GoodBONG q L (N + 4))
    (hhead : c.valueUnit (0 : Fin (N + 4)) =
      d.valueUnit (0 : Fin (N + 4)))
    (f : Lattice.Isometry
      (q.orthogonalSpace d.toBONG.head d.toBONG.head_isAnisotropic)
      (q.orthogonalSpace c.toBONG.head c.toBONG.head_isAnisotropic)
      (L.projectedLattice q d.toBONG.head d.toBONG.head_isAnisotropic)
      (L.projectedLattice q c.toBONG.head c.toBONG.head_isAnisotropic))
    (htail : Beli2009BinaryReachable (K := K)
      (fun i => c.tail.valueUnit i)
      (fun i => (d.tail.mapLatticeIsometry f).valueUnit i)) :
    Beli2009BinaryReachable (K := K)
      (fun i => c.valueUnit i) (fun i => d.valueUnit i) := by
  have hlift := Beli2009BinaryReachable.cons
    (c.valueUnit (0 : Fin (N + 4))) htail
  rw [cons_tailValues_eq c] at hlift
  have htarget :
      Fin.cons (c.valueUnit (0 : Fin (N + 4)))
          (fun i => (d.tail.mapLatticeIsometry f).valueUnit i) =
        (fun i => d.valueUnit i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hhead
    · calc
        (d.tail.mapLatticeIsometry f).valueUnit j =
            d.tail.valueUnit j :=
          BONG.GoodBONG.valueUnit_mapLatticeIsometry f d.tail j
        _ = d.valueUnit j.succ := by
          apply Units.ext
          exact d.toBONG.value_tail j
  rw [htarget] at hlift
  exact hlift

/-- Lemma 9.3's lower-rank representation is an isometry in the present
same-lattice situation.  Equality of the selected head values cancels the
head summands in the projection-volume formula, while the two tail BONGs
give the required equality of ambient dimensions. -/
theorem orthogonalAmbient_of_equalValue_sameSpace
    (x y : V) (hx : q.IsAnisotropic x) (hy : q.IsAnisotropic y)
    (heq : q.quadratic x = q.quadratic y) :
    (q.orthogonalSpace x hx).Represents (q.orthogonalSpace y hy) := by
  have hexists : ∃ g : QuadraticSpace.Isometry q q,
      g.toLinearEquiv y = x := by
    let g := q.equalValueTransportIsometry y x hy hx heq.symm
    exact ⟨g, q.equalValueTransportIsometry_apply_left y x hy hx heq.symm⟩
  rcases hexists with ⟨g, hmap⟩
  subst x
  exact ⟨(g.orthogonalIsometry y hy).toRepresentation⟩

theorem normalizedPair_tail_isIsometric
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    {N : Nat} (a b : BONG.GoodBONG q L (N + 4))
    (ambient : q.Represents q)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (D : ReachableLemma93NormalizedPair a b)
    (C : BONG.GoodBONG.Beli2019Lemma93LowReverseCertificate a b D.pair) :
    Lattice.IsIsometric
      (q.orthogonalSpace D.pair.sourceTransform.transformed.toBONG.head
        D.pair.sourceTransform.transformed.toBONG.head_isAnisotropic)
      (q.orthogonalSpace D.pair.targetTransform.transformed.toBONG.head
        D.pair.targetTransform.transformed.toBONG.head_isAnisotropic)
      (L.projectedLattice q
        D.pair.sourceTransform.transformed.toBONG.head
        D.pair.sourceTransform.transformed.toBONG.head_isAnisotropic)
      (L.projectedLattice q
        D.pair.targetTransform.transformed.toBONG.head
        D.pair.targetTransform.transformed.toBONG.head_isAnisotropic) := by
  let input := D.pair.toLemma93Input
    (classificationV := classification) (classificationW := classification)
    a b ambient conditions C
  have htailConditions : RepresentationConditions
      D.pair.targetTransform.transformed.tail
      D.pair.sourceTransform.transformed.tail (Nat.le_refl (N + 2)) := by
    exact (input.headReduction
      (targetLaws := alpha) (sourceLaws := alpha)).tailConditions
  have hheadQuadratic :
      q.quadratic D.pair.targetTransform.transformed.toBONG.head =
        q.quadratic D.pair.sourceTransform.transformed.toBONG.head := by
    rw [← D.pair.targetTransform.transformed.toBONG.value_zero_eq_quadratic_head,
      ← D.pair.sourceTransform.transformed.toBONG.value_zero_eq_quadratic_head]
    exact D.pair.headValue_eq
  have horthogonalAmbient := orthogonalAmbient_of_equalValue_sameSpace
    D.pair.targetTransform.transformed.toBONG.head
    D.pair.sourceTransform.transformed.toBONG.head
    D.pair.targetTransform.transformed.toBONG.head_isAnisotropic
    D.pair.sourceTransform.transformed.toBONG.head_isAnisotropic
    hheadQuadratic
  letI : FiniteDimensional K
      (q.vectorOrthogonal
        D.pair.sourceTransform.transformed.toBONG.head) :=
    D.pair.sourceTransform.transformed.tail.toBONG.basis
      |>.finiteDimensional_of_finite
  letI : FiniteDimensional K
      (q.vectorOrthogonal
        D.pair.targetTransform.transformed.toBONG.head) :=
    D.pair.targetTransform.transformed.tail.toBONG.basis
      |>.finiteDimensional_of_finite
  have hrep : Lattice.Represents
      (q.orthogonalSpace
        D.pair.targetTransform.transformed.toBONG.head
        D.pair.targetTransform.transformed.toBONG.head_isAnisotropic)
      (q.orthogonalSpace
        D.pair.sourceTransform.transformed.toBONG.head
        D.pair.sourceTransform.transformed.toBONG.head_isAnisotropic)
      (L.projectedLattice q
        D.pair.targetTransform.transformed.toBONG.head
        D.pair.targetTransform.transformed.toBONG.head_isAnisotropic)
      (L.projectedLattice q
        D.pair.sourceTransform.transformed.toBONG.head
        D.pair.sourceTransform.transformed.toBONG.head_isAnisotropic) :=
    (beli2019Theorem21 (Nat.le_refl (N + 2)) horthogonalAmbient
      D.pair.targetTransform.transformed.tail
      D.pair.sourceTransform.transformed.tail).2 htailConditions
  have hfinrank : Module.finrank K
        (q.vectorOrthogonal
          D.pair.sourceTransform.transformed.toBONG.head) =
      Module.finrank K
        (q.vectorOrthogonal
          D.pair.targetTransform.transformed.toBONG.head) := by
    rw [← D.pair.sourceTransform.transformed.tail.toBONG.length_eq_finrank,
      ← D.pair.targetTransform.transformed.tail.toBONG.length_eq_finrank]
  have hsourceVolume := Lattice.volumeOrder_eq_ordUnit_add_projection
    q L D.pair.sourceTransform.transformed.toBONG.head
      D.pair.sourceTransform.transformed.toBONG.head_isNormGenerator
      D.pair.sourceTransform.transformed.toBONG.head_isAnisotropic
  have htargetVolume := Lattice.volumeOrder_eq_ordUnit_add_projection
    q L D.pair.targetTransform.transformed.toBONG.head
      D.pair.targetTransform.transformed.toBONG.head_isNormGenerator
      D.pair.targetTransform.transformed.toBONG.head_isAnisotropic
  have hheadOrder :
      ordUnit K (Units.mk0
        (q.quadratic D.pair.sourceTransform.transformed.toBONG.head)
        D.pair.sourceTransform.transformed.toBONG.head_isAnisotropic) =
      ordUnit K (Units.mk0
        (q.quadratic D.pair.targetTransform.transformed.toBONG.head)
        D.pair.targetTransform.transformed.toBONG.head_isAnisotropic) := by
    apply congrArg (ordUnit K)
    apply Units.ext
    exact hheadQuadratic.symm
  have hvolume :
      Lattice.volumeOrder
          (q.orthogonalSpace
            D.pair.sourceTransform.transformed.toBONG.head
            D.pair.sourceTransform.transformed.toBONG.head_isAnisotropic)
          (L.projectedLattice q
            D.pair.sourceTransform.transformed.toBONG.head
            D.pair.sourceTransform.transformed.toBONG.head_isAnisotropic) =
        Lattice.volumeOrder
          (q.orthogonalSpace
            D.pair.targetTransform.transformed.toBONG.head
            D.pair.targetTransform.transformed.toBONG.head_isAnisotropic)
          (L.projectedLattice q
            D.pair.targetTransform.transformed.toBONG.head
            D.pair.targetTransform.transformed.toBONG.head_isAnisotropic) := by
    omega
  exact Lattice.Represents.isIsometric_of_finrank_eq_of_volumeOrder_eq
    hrep hfinrank hvolume

/-- The complete Section 9 induction step after a path-refined normalized
pair has been constructed.  The only recursive input is connectivity for
the two good BONGs on the target projected lattice, whose rank is one less.
-/
theorem reachable_of_normalizedPair_of_tailConnectivity
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    {N : Nat} (a b : BONG.GoodBONG q L (N + 4))
    (ambient : q.Represents q)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (D : ReachableLemma93NormalizedPair a b)
    (C : BONG.GoodBONG.Beli2019Lemma93LowReverseCertificate a b D.pair)
    (tailConnectivity : ∀ x y : BONG.GoodBONG
      (q.orthogonalSpace D.pair.targetTransform.transformed.toBONG.head
        D.pair.targetTransform.transformed.toBONG.head_isAnisotropic)
      (L.projectedLattice q
        D.pair.targetTransform.transformed.toBONG.head
        D.pair.targetTransform.transformed.toBONG.head_isAnisotropic)
      (N + 3),
      Beli2009BinaryReachable (K := K)
        (fun i => x.valueUnit i) (fun i => y.valueUnit i)) :
    Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => b.valueUnit i) := by
  rcases normalizedPair_tail_isIsometric a b ambient conditions D C with ⟨f⟩
  have htail := tailConnectivity
    D.pair.targetTransform.transformed.tail
    (D.pair.sourceTransform.transformed.tail.mapLatticeIsometry f)
  have hhead :
      D.pair.targetTransform.transformed.valueUnit (0 : Fin (N + 4)) =
        D.pair.sourceTransform.transformed.valueUnit (0 : Fin (N + 4)) := by
    apply Units.ext
    exact D.pair.headValue_eq
  have hselected := reachable_of_headValue_eq_of_mappedTail_reachable
    D.pair.targetTransform.transformed
    D.pair.sourceTransform.transformed hhead f htail
  exact D.targetReachable.trans
    (hselected.trans (Beli2009BinaryReachable.symm D.sourceReachable))

/-! ## The four-step bridge for the remaining strict isotropic orientation -/

/-- Inversion in the second argument does not change a Hilbert symbol. -/
theorem hilbertSymbol_inv_right_eq_local
    [HilbertSymbolLaws K] (a b : Kˣ) :
    hilbertSymbol K a b⁻¹ = hilbertSymbol K a b := by
  rw [hilbertSymbol_comm K a b⁻¹,
    hilbertSymbol_inv_left_eq,
    hilbertSymbol_comm K b a]

/-- The alternating path `1→0→1→0` which resolves the opposite Hilbert
orientation in the strict isotropic ternary case.  The first two
multipliers are auxiliary.  The last two remove them while installing the
prescribed multipliers `eta` and `epsilon`.  Exact defects of the two
altered adjacent products make both dynamic binary alphas return to the
original global alphas. -/
theorem exists_rankThree_fourStep_scaling_of_dynamic
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 3)
    (epsilon : valuationUnitSubgroup K)
    (hepsilonFirst : hilbertSymbol K (epsilon : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (eta theta mu : valuationUnitSubgroup K)
    (hetaLast : hilbertSymbol K (eta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = -1)
    (hetaEpsilon : hilbertSymbol K (eta : Kˣ)
      (epsilon : Kˣ) = 1)
    (hthetaAlpha : a.adjacentBinaryAlpha (1 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
    (hthetaLast : hilbertSymbol K (theta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = 1)
    (hmuAlpha : rankThreeFirstBinaryAlphaAfterRightMultiplier
        a (theta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ))
    (hkappaAlpha : rankThreeLastBinaryAlphaAfterLeftMultiplier
        a (mu : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((eta / theta : valuationUnitSubgroup K) : Kˣ)))
    (hmuCombined : hilbertSymbol K
      ((eta : Kˣ) * a.adjacentProduct (0 : Fin 2)) (mu : Kˣ) = -1)
    (hbridge : hilbertSymbol K (theta : Kˣ) (mu : Kˣ) =
      hilbertSymbol K (a.adjacentProduct (0 : Fin 2)) (mu : Kˣ))
    (hnuAlpha : rankThreeFirstBinaryAlphaAfterRightMultiplier
        a (eta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((epsilon / mu : valuationUnitSubgroup K) : Kˣ))) :
    ∃ f : BONG.GoodBONG q L 3,
      (fun i => f.valueUnit i) =
        ![(epsilon : Kˣ) * a.valueUnit 0,
          (epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 1,
          (eta : Kˣ) * a.valueUnit 2] ∧
      Beli2009BinaryReachable (K := K)
        (fun i => a.valueUnit i) (fun i => f.valueUnit i) := by
  have hthetaGroup : valuationUnitClassHom K theta ∈
      beliNormGeneratorGroup K
        (a.valueUnit (2 : Fin 3) / a.valueUnit (1 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (1 : Fin 2) theta
    · exact hthetaAlpha
    · rw [hilbertSymbol_comm K]
      exact hthetaLast
  rcases exists_goodBONG_binaryTransformation_exact a (1 : Fin 2)
      theta hthetaGroup with ⟨c, hcValues⟩
  have hthetaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => a.valueUnit i) (fun i => c.valueUnit i) :=
    ⟨1, theta, hthetaGroup, hcValues⟩
  have hcFirstAdjacent : c.adjacentProduct (0 : Fin 2) =
      (theta : Kˣ) * a.adjacentProduct (0 : Fin 2) := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hcValues (0 : Fin 2).castSucc,
      congrFun hcValues (0 : Fin 2).succ]
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]
    exact mul_comm _ _
  have hcFirstAlpha : c.adjacentBinaryAlpha (0 : Fin 2) =
      rankThreeFirstBinaryAlphaAfterRightMultiplier a (theta : Kˣ) := by
    have horders := a.order_invariant c
    have horderZero : c.order (0 : Fin 2).castSucc =
        a.order (0 : Fin 2).castSucc :=
      (horders (0 : Fin 2).castSucc).symm
    have horderOne : c.order (0 : Fin 2).succ =
        a.order (0 : Fin 2).succ :=
      (horders (0 : Fin 2).succ).symm
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankThreeFirstBinaryAlphaAfterRightMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [horderOne, horderZero, hcFirstAdjacent]
  have hcFirstAlphaLe : c.adjacentBinaryAlpha (0 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) := by
    rw [hcFirstAlpha]
    exact hmuAlpha
  have hmuHilbert : hilbertSymbol K
      (c.adjacentProduct (0 : Fin 2)) (mu : Kˣ) = 1 := by
    rw [hcFirstAdjacent, hilbertSymbol_mul_left, hbridge,
      Int.units_mul_self]
  have hmuGroup : valuationUnitClassHom K mu ∈
      beliNormGeneratorGroup K
        (c.valueUnit (1 : Fin 3) / c.valueUnit (0 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      c (0 : Fin 2) mu hcFirstAlphaLe hmuHilbert
  rcases exists_goodBONG_binaryTransformation_exact c (0 : Fin 2)
      mu hmuGroup with ⟨d, hdValues⟩
  have hmuStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => c.valueUnit i) (fun i => d.valueUnit i) :=
    ⟨0, mu, hmuGroup, hdValues⟩
  have hdLastAdjacent : d.adjacentProduct (1 : Fin 2) =
      ((mu : Kˣ) * a.adjacentProduct (1 : Fin 2)) * (theta : Kˣ) ^ 2 := by
    have hdOne : d.valueUnit (1 : Fin 3) =
        (mu : Kˣ) * c.valueUnit (1 : Fin 3) := by
      rw [congrFun hdValues (1 : Fin 3)]
      rfl
    have hdTwo : d.valueUnit (2 : Fin 3) = c.valueUnit (2 : Fin 3) := by
      rw [congrFun hdValues (2 : Fin 3)]
      simp [beli2009BinaryTransformAt]
    have hcOne : c.valueUnit (1 : Fin 3) =
        (theta : Kˣ) * a.valueUnit (1 : Fin 3) := by
      rw [congrFun hcValues (1 : Fin 3)]
      rfl
    have hcTwo : c.valueUnit (2 : Fin 3) =
        (theta : Kˣ) * a.valueUnit (2 : Fin 3) := by
      rw [congrFun hcValues (2 : Fin 3)]
      rfl
    unfold BONG.GoodBONG.adjacentProduct
    change -(d.valueUnit (1 : Fin 3) * d.valueUnit (2 : Fin 3)) = _
    rw [hdOne, hdTwo, hcOne, hcTwo]
    apply Units.ext
    simp [pow_two]
    ring
  have hdLastAlpha : d.adjacentBinaryAlpha (1 : Fin 2) =
      rankThreeLastBinaryAlphaAfterLeftMultiplier a (mu : Kˣ) := by
    have horders := a.order_invariant d
    have horderOne : d.order (1 : Fin 2).castSucc =
        a.order (1 : Fin 2).castSucc :=
      (horders (1 : Fin 2).castSucc).symm
    have horderTwo : d.order (1 : Fin 2).succ =
        a.order (1 : Fin 2).succ :=
      (horders (1 : Fin 2).succ).symm
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankThreeLastBinaryAlphaAfterLeftMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [horderTwo, horderOne, hdLastAdjacent,
      BONG.GoodBONG.defectOrder_mul_square]
  let kappa : valuationUnitSubgroup K := eta / theta
  have hdLastAlphaLe : d.adjacentBinaryAlpha (1 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (kappa : Kˣ) := by
    rw [hdLastAlpha]
    simpa only [kappa] using hkappaAlpha
  have hmuEtaProduct : hilbertSymbol K (mu : Kˣ) (eta : Kˣ) *
      hilbertSymbol K (mu : Kˣ)
        (a.adjacentProduct (0 : Fin 2)) = -1 := by
    have h := hmuCombined
    rw [hilbertSymbol_comm K, hilbertSymbol_mul_right] at h
    exact h
  have hmuTheta : hilbertSymbol K (mu : Kˣ) (theta : Kˣ) =
      hilbertSymbol K (mu : Kˣ)
        (a.adjacentProduct (0 : Fin 2)) := by
    rw [hilbertSymbol_comm K (mu : Kˣ) (theta : Kˣ), hbridge,
      hilbertSymbol_comm K]
  have hmuKappa : hilbertSymbol K (mu : Kˣ) (kappa : Kˣ) = -1 := by
    change hilbertSymbol K (mu : Kˣ)
      ((eta : Kˣ) * (theta : Kˣ)⁻¹) = -1
    rw [hilbertSymbol_mul_right, hilbertSymbol_inv_right_eq_local,
      hmuTheta]
    exact hmuEtaProduct
  have hlastKappa : hilbertSymbol K
      (a.adjacentProduct (1 : Fin 2)) (kappa : Kˣ) = -1 := by
    change hilbertSymbol K (a.adjacentProduct (1 : Fin 2))
      ((eta : Kˣ) * (theta : Kˣ)⁻¹) = -1
    rw [hilbertSymbol_mul_right, hilbertSymbol_inv_right_eq_local,
      hilbertSymbol_comm K (a.adjacentProduct (1 : Fin 2)) (eta : Kˣ),
      hetaLast,
      hilbertSymbol_comm K (a.adjacentProduct (1 : Fin 2)) (theta : Kˣ),
      hthetaLast]
    norm_num
  have hkappaHilbert : hilbertSymbol K
      (d.adjacentProduct (1 : Fin 2)) (kappa : Kˣ) = 1 := by
    rw [hdLastAdjacent, hilbertSymbol_mul_square_left,
      hilbertSymbol_mul_left, hmuKappa, hlastKappa]
    norm_num
  have hkappaGroup : valuationUnitClassHom K kappa ∈
      beliNormGeneratorGroup K
        (d.valueUnit (2 : Fin 3) / d.valueUnit (1 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      d (1 : Fin 2) kappa hdLastAlphaLe hkappaHilbert
  rcases exists_goodBONG_binaryTransformation_exact d (1 : Fin 2)
      kappa hkappaGroup with ⟨e, heValues⟩
  have hkappaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => d.valueUnit i) (fun i => e.valueUnit i) :=
    ⟨1, kappa, hkappaGroup, heValues⟩
  have heFirstAdjacent : e.adjacentProduct (0 : Fin 2) =
      ((eta : Kˣ) * a.adjacentProduct (0 : Fin 2)) * (mu : Kˣ) ^ 2 := by
    have heZero : e.valueUnit (0 : Fin 3) = d.valueUnit (0 : Fin 3) := by
      rw [congrFun heValues (0 : Fin 3)]
      simp [beli2009BinaryTransformAt]
    have heOne : e.valueUnit (1 : Fin 3) =
        (kappa : Kˣ) * d.valueUnit (1 : Fin 3) := by
      rw [congrFun heValues (1 : Fin 3)]
      rfl
    have hdZero : d.valueUnit (0 : Fin 3) =
        (mu : Kˣ) * a.valueUnit (0 : Fin 3) := by
      calc
        d.valueUnit (0 : Fin 3) =
            (mu : Kˣ) * c.valueUnit (0 : Fin 3) := by
          rw [congrFun hdValues (0 : Fin 3)]
          rfl
        _ = (mu : Kˣ) * a.valueUnit (0 : Fin 3) := by
          rw [congrFun hcValues (0 : Fin 3)]
          simp [beli2009BinaryTransformAt]
    have hdOne : d.valueUnit (1 : Fin 3) =
        (mu : Kˣ) * (theta : Kˣ) * a.valueUnit (1 : Fin 3) := by
      calc
        d.valueUnit (1 : Fin 3) =
            (mu : Kˣ) * c.valueUnit (1 : Fin 3) := by
          rw [congrFun hdValues (1 : Fin 3)]
          rfl
        _ = (mu : Kˣ) * (theta : Kˣ) *
            a.valueUnit (1 : Fin 3) := by
          rw [congrFun hcValues (1 : Fin 3)]
          simp [beli2009BinaryTransformAt, mul_assoc]
    unfold BONG.GoodBONG.adjacentProduct
    have hcastZero : (Fin.castSucc (0 : Fin 2) : Fin 3) =
        (0 : Fin 3) := rfl
    have hsuccZero : (Fin.succ (0 : Fin 2) : Fin 3) =
        (1 : Fin 3) := rfl
    rw [hcastZero, hsuccZero]
    change -(e.valueUnit (0 : Fin 3) * e.valueUnit (1 : Fin 3)) = _
    rw [heZero, heOne, hdZero, hdOne]
    change -((mu : Kˣ) * a.valueUnit 0 *
      ((eta : Kˣ) * (theta : Kˣ)⁻¹ *
        ((mu : Kˣ) * (theta : Kˣ) * a.valueUnit 1))) = _
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val, BONG.GoodBONG.coe_valueUnit]
    field_simp
    <;> ring
  have heFirstAlpha : e.adjacentBinaryAlpha (0 : Fin 2) =
      rankThreeFirstBinaryAlphaAfterRightMultiplier a (eta : Kˣ) := by
    have horders := a.order_invariant e
    have horderZero : e.order (0 : Fin 2).castSucc =
        a.order (0 : Fin 2).castSucc :=
      (horders (0 : Fin 2).castSucc).symm
    have horderOne : e.order (0 : Fin 2).succ =
        a.order (0 : Fin 2).succ :=
      (horders (0 : Fin 2).succ).symm
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankThreeFirstBinaryAlphaAfterRightMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [horderOne, horderZero, heFirstAdjacent,
      BONG.GoodBONG.defectOrder_mul_square]
  let nu : valuationUnitSubgroup K := epsilon / mu
  have heFirstAlphaLe : e.adjacentBinaryAlpha (0 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (nu : Kˣ) := by
    rw [heFirstAlpha]
    simpa only [nu] using hnuAlpha
  have hcombinedEpsilon : hilbertSymbol K
      ((eta : Kˣ) * a.adjacentProduct (0 : Fin 2))
      (epsilon : Kˣ) = -1 := by
    have hfirstEpsilon : hilbertSymbol K
        (a.adjacentProduct (0 : Fin 2)) (epsilon : Kˣ) = -1 := by
      rw [hilbertSymbol_comm K]
      exact hepsilonFirst
    rw [hilbertSymbol_mul_left,
      show hilbertSymbol K (eta : Kˣ) (epsilon : Kˣ) = 1 by
        exact hetaEpsilon,
      hfirstEpsilon]
    norm_num
  have hcombinedNu : hilbertSymbol K
      ((eta : Kˣ) * a.adjacentProduct (0 : Fin 2)) (nu : Kˣ) = 1 := by
    change hilbertSymbol K
      ((eta : Kˣ) * a.adjacentProduct (0 : Fin 2))
      ((epsilon : Kˣ) * (mu : Kˣ)⁻¹) = 1
    rw [hilbertSymbol_mul_right, hilbertSymbol_inv_right_eq_local,
      hcombinedEpsilon, hmuCombined]
    norm_num
  have hnuHilbert : hilbertSymbol K
      (e.adjacentProduct (0 : Fin 2)) (nu : Kˣ) = 1 := by
    rw [heFirstAdjacent, hilbertSymbol_mul_square_left]
    exact hcombinedNu
  have hnuGroup : valuationUnitClassHom K nu ∈
      beliNormGeneratorGroup K
        (e.valueUnit (1 : Fin 3) / e.valueUnit (0 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      e (0 : Fin 2) nu heFirstAlphaLe hnuHilbert
  rcases exists_goodBONG_binaryTransformation_exact e (0 : Fin 2)
      nu hnuGroup with ⟨f, hfValues⟩
  have hnuStep : IsBeli2009BinaryTransformation (K := K)
      (fun i => e.valueUnit i) (fun i => f.valueUnit i) :=
    ⟨0, nu, hnuGroup, hfValues⟩
  have hfinalValues : (fun i => f.valueUnit i) =
      ![(epsilon : Kˣ) * a.valueUnit 0,
        (epsilon : Kˣ) * (eta : Kˣ) * a.valueUnit 1,
        (eta : Kˣ) * a.valueUnit 2] := by
    rw [hfValues, heValues, hdValues, hcValues]
    funext i
    fin_cases i <;>
      simp [beli2009BinaryTransformAt, nu, kappa, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm] <;> group <;>
      simp [zpow_neg_one, mul_assoc, mul_left_comm, mul_comm]
  exact ⟨f, hfinalValues,
    hthetaStep.reachable.trans
      (hmuStep.reachable.trans
        (hkappaStep.reachable.trans hnuStep.reachable))⟩

/-- Prescribed-first-value wrapper around the exact four-step scaling core.
This retains the interface used by the rank-three Lemma 8.14 proof while
exposing the full coefficient endpoint to higher-rank detours. -/
theorem reachableLemma814_rankThree_negative_of_fourStepBridge_dynamic
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (hepsilonFirst : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (eta theta mu : valuationUnitSubgroup K)
    (hetaLast : hilbertSymbol K (eta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = -1)
    (hetaEpsilon : hilbertSymbol K (eta : Kˣ)
      (a.lemma814Epsilon b) = 1)
    (hthetaAlpha : a.adjacentBinaryAlpha (1 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
    (hthetaLast : hilbertSymbol K (theta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = 1)
    (hmuAlpha : rankThreeFirstBinaryAlphaAfterRightMultiplier
        a (theta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ))
    (hkappaAlpha : rankThreeLastBinaryAlphaAfterLeftMultiplier
        a (mu : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((eta / theta : valuationUnitSubgroup K) : Kˣ)))
    (hmuCombined : hilbertSymbol K
      ((eta : Kˣ) * a.adjacentProduct (0 : Fin 2)) (mu : Kˣ) = -1)
    (hbridge : hilbertSymbol K (theta : Kˣ) (mu : Kˣ) =
      hilbertSymbol K (a.adjacentProduct (0 : Fin 2)) (mu : Kˣ))
    (hnuAlpha : rankThreeFirstBinaryAlphaAfterRightMultiplier
        a (eta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((⟨a.lemma814Epsilon b,
              a.lemma814Epsilon_isValuationUnit b horder⟩ :
            valuationUnitSubgroup K) / mu : valuationUnitSubgroup K) : Kˣ)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  let epsilon : valuationUnitSubgroup K :=
    ⟨a.lemma814Epsilon b, a.lemma814Epsilon_isValuationUnit b horder⟩
  have hepsilonFirst' : hilbertSymbol K (epsilon : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1 := by
    simpa only [epsilon, Subgroup.coe_mk] using hepsilonFirst
  have hetaEpsilon' : hilbertSymbol K (eta : Kˣ)
      (epsilon : Kˣ) = 1 := by
    simpa only [epsilon, Subgroup.coe_mk] using hetaEpsilon
  have hnuAlpha' : rankThreeFirstBinaryAlphaAfterRightMultiplier
        a (eta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((epsilon / mu : valuationUnitSubgroup K) : Kˣ)) := by
    simpa only [epsilon] using hnuAlpha
  rcases exists_rankThree_fourStep_scaling_of_dynamic
      a epsilon hepsilonFirst' eta theta mu hetaLast hetaEpsilon'
        hthetaAlpha hthetaLast hmuAlpha hkappaAlpha hmuCombined hbridge
        hnuAlpha' with
    ⟨f, hfValues, hreach⟩
  have hfHead : f.valueUnit (0 : Fin 3) = b.valueUnit (0 : Fin 1) := by
    calc
      f.valueUnit (0 : Fin 3) =
          (epsilon : Kˣ) * a.valueUnit (0 : Fin 3) := by
        simpa using congrFun hfValues (0 : Fin 3)
      _ = a.lemma814Epsilon b * a.valueUnit (0 : Fin 3) := by
        rfl
      _ = b.valueUnit (0 : Fin 1) :=
        a.lemma814Epsilon_mul_firstValue b
  exact ⟨{
    transform := {
      transformed := f
      firstValue_eq := hfHead
    }
    reachable := hreach
  }⟩

/-- Equal-outer specialization of the dynamic four-step bridge.  Remark 8.7
turns the two exact adjacent-product defects into the four dynamic alpha
bounds used by `reachableLemma814_rankThree_negative_of_fourStepBridge_dynamic`.
This wrapper preserves the original interface used by the isotropic proof. -/
theorem reachableLemma814_rankThree_negative_of_fourStepBridge
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hepsilonFirst : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (eta theta mu : valuationUnitSubgroup K)
    (hetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ))
    (hetaFirstProduct : BONG.GoodBONG.defectOrder (K := K)
        ((eta : Kˣ) * a.adjacentProduct (0 : Fin 2)) =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hetaLast : hilbertSymbol K (eta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = -1)
    (hetaEpsilon : hilbertSymbol K (eta : Kˣ)
      (a.lemma814Epsilon b) = 1)
    (hthetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ))
    (hthetaFirstProduct : BONG.GoodBONG.defectOrder (K := K)
        ((theta : Kˣ) * a.adjacentProduct (0 : Fin 2)) =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hthetaLast : hilbertSymbol K (theta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = 1)
    (hmuDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ))
    (hmuLastProduct : BONG.GoodBONG.defectOrder (K := K)
        ((mu : Kˣ) * a.adjacentProduct (1 : Fin 2)) =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hmuCombined : hilbertSymbol K
      ((eta : Kˣ) * a.adjacentProduct (0 : Fin 2)) (mu : Kˣ) = -1)
    (hbridge : hilbertSymbol K (theta : Kˣ) (mu : Kˣ) =
      hilbertSymbol K (a.adjacentProduct (0 : Fin 2)) (mu : Kˣ)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [BONG.GoodBONG.remark87PreviousValue,
      BONG.GoodBONG.remark87NextValue] using houter)
  have hfirstRelation :
      (((((a.order (1 : Fin 3) - a.order (0 : Fin 3) : Int) : ℚ)) :
          WithTop ℚ) +
        (a.alphaValue (1 : Fin 2) : WithTop ℚ)) =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    have h := hremark.previousAlpha_eq
    change a.alphaValue (0 : Fin 2) =
      ((a.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) +
        a.alphaValue (1 : Fin 2) at h
    have h' := congrArg (fun x : ℚ => (x : WithTop ℚ)) h
    rw [← houter] at h'
    simpa only [WithTop.coe_add, WithTop.coe_sub, Int.cast_sub,
      Int.cast_ofNat] using h'.symm
  have hlastRelation :
      (((((a.order (2 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ)) :
          WithTop ℚ) +
        (a.alphaValue (0 : Fin 2) : WithTop ℚ)) =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    have h := hremark.currentAlpha_eq
    change a.alphaValue (1 : Fin 2) =
      ((a.order (0 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ) +
        a.alphaValue (0 : Fin 2) at h
    have h' := congrArg (fun x : ℚ => (x : WithTop ℚ)) h
    rw [houter] at h'
    simpa only [WithTop.coe_add, WithTop.coe_sub, Int.cast_sub,
      Int.cast_ofNat] using h'.symm
  have hthetaAlpha : a.adjacentBinaryAlpha (1 : Fin 2) ≤
      BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) := by
    rw [show a.adjacentBinaryAlpha (1 : Fin 2) =
      a.lastBinaryAlpha by rfl, hlast]
    exact hthetaDepth
  have hmuAlpha : rankThreeFirstBinaryAlphaAfterRightMultiplier
      a (theta : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) := by
    unfold rankThreeFirstBinaryAlphaAfterRightMultiplier
    refine (min_le_right _ _).trans ?_
    rw [hthetaFirstProduct]
    exact hfirstRelation.le.trans hmuDepth
  let kappa : valuationUnitSubgroup K := eta / theta
  have hkappaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (kappa : Kˣ) := by
    have hthetaInvDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) ((theta : Kˣ)⁻¹) := by
      rw [BONG.GoodBONG.defectOrder_inv]
      exact hthetaDepth
    exact (le_min hetaDepth hthetaInvDepth).trans
      (BONG.GoodBONG.defectOrder_mul_ge_min
        (K := K) (eta : Kˣ) ((theta : Kˣ)⁻¹))
  have hkappaAlpha : rankThreeLastBinaryAlphaAfterLeftMultiplier
      a (mu : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K) (kappa : Kˣ) := by
    unfold rankThreeLastBinaryAlphaAfterLeftMultiplier
    refine (min_le_right _ _).trans ?_
    rw [hmuLastProduct]
    exact hlastRelation.le.trans hkappaDepth
  let epsilon : valuationUnitSubgroup K :=
    ⟨a.lemma814Epsilon b, a.lemma814Epsilon_isValuationUnit b horder⟩
  let nu : valuationUnitSubgroup K := epsilon / mu
  have hepsilonDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (epsilon : Kˣ) := by
    simpa only [epsilon, Subgroup.coe_mk] using
      a.alpha_le_lemma814EpsilonDefect b conditions
  have hmuInvDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) ((mu : Kˣ)⁻¹) := by
    rw [BONG.GoodBONG.defectOrder_inv]
    exact hmuDepth
  have hnuDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (nu : Kˣ) := by
    exact (le_min hepsilonDepth hmuInvDepth).trans
      (BONG.GoodBONG.defectOrder_mul_ge_min
        (K := K) (epsilon : Kˣ) ((mu : Kˣ)⁻¹))
  have hnuAlpha : rankThreeFirstBinaryAlphaAfterRightMultiplier
      a (eta : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K) (nu : Kˣ) := by
    unfold rankThreeFirstBinaryAlphaAfterRightMultiplier
    refine (min_le_right _ _).trans ?_
    rw [hetaFirstProduct]
    exact hfirstRelation.le.trans hnuDepth
  exact reachableLemma814_rankThree_negative_of_fourStepBridge_dynamic
    a b horder hepsilonFirst eta theta mu hetaLast hetaEpsilon
      hthetaAlpha hthetaLast hmuAlpha
      (by simpa only [kappa] using hkappaAlpha) hmuCombined hbridge
      (by simpa only [epsilon, nu] using hnuAlpha)

/-- A prescribed-head `0→1→0` bridge in fully dynamic form.  The first
multiplier is `epsilon*rho`, the middle multiplier is `eta`, and the last is
`rho⁻¹`.  Thus the auxiliary factors cancel and the final first value is
exactly `epsilon*a₀`.  This version does not assume that a preselected target
ternary BONG has a normalized literal edge. -/
theorem reachableLemma814_rankThree_negative_of_zeroOneZero_dynamic
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hepsilonFirst : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (eta rho : valuationUnitSubgroup K)
    (hetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ))
    (hetaLast : hilbertSymbol K (eta : Kˣ)
      (a.adjacentProduct (1 : Fin 2)) = -1)
    (hetaEpsilon : hilbertSymbol K (eta : Kˣ)
      (a.lemma814Epsilon b) = 1)
    (hrhoDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ))
    (hrhoEta : hilbertSymbol K (rho : Kˣ) (eta : Kˣ) = -1)
    (hrhoFirst : hilbertSymbol K (rho : Kˣ)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (hdynamicLast : rankThreeLastBinaryAlphaAfterLeftMultiplier
        a (a.lemma814Epsilon b * (rho : Kˣ)) ≤
      BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ))
    (hdynamicFirst : rankThreeFirstBinaryAlphaAfterRightMultiplier
        a (eta : Kˣ) ≤
      BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  let epsilon : valuationUnitSubgroup K :=
    ⟨a.lemma814Epsilon b, a.lemma814Epsilon_isValuationUnit b horder⟩
  let mu : valuationUnitSubgroup K := epsilon * rho
  let nu : valuationUnitSubgroup K := epsilon / mu
  have hdetour := ternaryDetour_hilbert_conditions
    (K := K) (a.adjacentProduct (0 : Fin 2))
      (a.adjacentProduct (1 : Fin 2))
      (epsilon : Kˣ) (eta : Kˣ) (rho : Kˣ)
      (by simpa only [epsilon, Subgroup.coe_mk] using hepsilonFirst)
      hetaLast
      (by rw [hilbertSymbol_comm K];
          simpa only [epsilon, Subgroup.coe_mk] using hetaEpsilon)
      hrhoEta hrhoFirst
  have hepsilonDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (epsilon : Kˣ) := by
    simpa only [epsilon, Subgroup.coe_mk] using
      a.alpha_le_lemma814EpsilonDefect b conditions
  have hmuDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) := by
    exact (le_min hepsilonDepth hrhoDepth).trans
      (BONG.GoodBONG.defectOrder_mul_ge_min
        (K := K) (epsilon : Kˣ) (rho : Kˣ))
  have hmuHilbert : hilbertSymbol K
      (a.adjacentProduct (0 : Fin 2)) (mu : Kˣ) = 1 := by
    rw [hilbertSymbol_comm K]
    simpa only [mu, Subgroup.coe_mul] using hdetour.1
  have hmuGroup : valuationUnitClassHom K mu ∈
      beliNormGeneratorGroup K
        (a.valueUnit (1 : Fin 3) / a.valueUnit (0 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (0 : Fin 2) mu
    · simpa only [BONG.GoodBONG.adjacentBinaryAlpha_zero, hfirst]
        using hmuDepth
    · exact hmuHilbert
  rcases exists_goodBONG_binaryTransformation_exact a (0 : Fin 2)
      mu hmuGroup with ⟨c, hcValues⟩
  have hmuStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ c.valueUnit i) :=
    ⟨0, mu, hmuGroup, hcValues⟩
  have hcLastAdjacent : c.adjacentProduct (1 : Fin 2) =
      (mu : Kˣ) * a.adjacentProduct (1 : Fin 2) := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hcValues (1 : Fin 2).castSucc,
      congrFun hcValues (1 : Fin 2).succ]
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]
  have hcLastAlpha : c.adjacentBinaryAlpha (1 : Fin 2) =
      rankThreeLastBinaryAlphaAfterLeftMultiplier
        a (a.lemma814Epsilon b * (rho : Kˣ)) := by
    have horders := a.order_invariant c
    have horderOne : c.order (1 : Fin 2).castSucc =
        a.order (1 : Fin 2).castSucc :=
      (horders (1 : Fin 2).castSucc).symm
    have horderTwo : c.order (1 : Fin 2).succ =
        a.order (1 : Fin 2).succ :=
      (horders (1 : Fin 2).succ).symm
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankThreeLastBinaryAlphaAfterLeftMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [horderTwo, horderOne, hcLastAdjacent]
    change _ = min _ (_ + BONG.GoodBONG.defectOrder (K := K)
      ((epsilon : Kˣ) * (rho : Kˣ) * a.adjacentProduct (1 : Fin 2)))
    simp only [mu, Subgroup.coe_mul, epsilon, Subgroup.coe_mk]
  have hetaHilbert : hilbertSymbol K
      (c.adjacentProduct (1 : Fin 2)) (eta : Kˣ) = 1 := by
    rw [hcLastAdjacent, hilbertSymbol_comm K]
    simpa only [mu, Subgroup.coe_mul] using hdetour.2.1
  have hetaGroup : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K
        (c.valueUnit (2 : Fin 3) / c.valueUnit (1 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      c (1 : Fin 2) eta
    · rw [hcLastAlpha]
      exact hdynamicLast
    · exact hetaHilbert
  rcases exists_goodBONG_binaryTransformation_exact c (1 : Fin 2)
      eta hetaGroup with ⟨d, hdValues⟩
  have hetaStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ c.valueUnit i) (fun i ↦ d.valueUnit i) :=
    ⟨1, eta, hetaGroup, hdValues⟩
  have hdFirstAdjacent : d.adjacentProduct (0 : Fin 2) =
      ((eta : Kˣ) * a.adjacentProduct (0 : Fin 2)) * (mu : Kˣ) ^ 2 := by
    have hdZero : d.valueUnit (0 : Fin 3) = c.valueUnit (0 : Fin 3) := by
      rw [congrFun hdValues (0 : Fin 3)]
      simp [beli2009BinaryTransformAt]
    have hdOne : d.valueUnit (1 : Fin 3) =
        (eta : Kˣ) * c.valueUnit (1 : Fin 3) := by
      rw [congrFun hdValues (1 : Fin 3)]
      rfl
    have hcZero : c.valueUnit (0 : Fin 3) =
        (mu : Kˣ) * a.valueUnit (0 : Fin 3) := by
      rw [congrFun hcValues (0 : Fin 3)]
      rfl
    have hcOne : c.valueUnit (1 : Fin 3) =
        (mu : Kˣ) * a.valueUnit (1 : Fin 3) := by
      rw [congrFun hcValues (1 : Fin 3)]
      rfl
    unfold BONG.GoodBONG.adjacentProduct
    change -(d.valueUnit (0 : Fin 3) * d.valueUnit (1 : Fin 3)) = _
    rw [hdZero, hdOne, hcZero, hcOne]
    apply Units.ext
    simp [pow_two]
    ring
  have hdFirstAlpha : d.adjacentBinaryAlpha (0 : Fin 2) =
      rankThreeFirstBinaryAlphaAfterRightMultiplier a (eta : Kˣ) := by
    have horders := a.order_invariant d
    have horderZero : d.order (0 : Fin 2).castSucc =
        a.order (0 : Fin 2).castSucc :=
      (horders (0 : Fin 2).castSucc).symm
    have horderOne : d.order (0 : Fin 2).succ =
        a.order (0 : Fin 2).succ :=
      (horders (0 : Fin 2).succ).symm
    unfold BONG.GoodBONG.adjacentBinaryAlpha
      rankThreeFirstBinaryAlphaAfterRightMultiplier
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [horderOne, horderZero, hdFirstAdjacent,
      BONG.GoodBONG.defectOrder_mul_square]
  have hnuRho : (nu : Kˣ) = (rho : Kˣ)⁻¹ := by
    dsimp only [nu, mu, epsilon]
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hnuDepth : rankThreeFirstBinaryAlphaAfterRightMultiplier
      a (eta : Kˣ) ≤ BONG.GoodBONG.defectOrder (K := K) (nu : Kˣ) := by
    rw [hnuRho, BONG.GoodBONG.defectOrder_inv]
    exact hdynamicFirst
  have hnuHilbert : hilbertSymbol K
      (d.adjacentProduct (0 : Fin 2)) (nu : Kˣ) = 1 := by
    rw [hdFirstAdjacent, hilbertSymbol_mul_square_left, hnuRho,
      hilbertSymbol_comm K]
    exact hdetour.2.2
  have hnuGroup : valuationUnitClassHom K nu ∈
      beliNormGeneratorGroup K
        (d.valueUnit (1 : Fin 3) / d.valueUnit (0 : Fin 3)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      d (0 : Fin 2) nu
    · rw [hdFirstAlpha]
      exact hnuDepth
    · exact hnuHilbert
  rcases exists_goodBONG_binaryTransformation_exact d (0 : Fin 2)
      nu hnuGroup with ⟨f, hfValues⟩
  have hnuStep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ d.valueUnit i) (fun i ↦ f.valueUnit i) :=
    ⟨0, nu, hnuGroup, hfValues⟩
  have hfHead : f.valueUnit (0 : Fin 3) = b.valueUnit (0 : Fin 1) := by
    calc
      f.valueUnit (0 : Fin 3) = (nu : Kˣ) * d.valueUnit 0 := by
        rw [congrFun hfValues (0 : Fin 3)]
        rfl
      _ = (nu : Kˣ) * c.valueUnit 0 := by
        rw [congrFun hdValues (0 : Fin 3)]
        simp [beli2009BinaryTransformAt]
      _ = (nu : Kˣ) * ((mu : Kˣ) * a.valueUnit 0) := by
        rw [congrFun hcValues (0 : Fin 3)]
        rfl
      _ = a.lemma814Epsilon b * a.valueUnit 0 := by
        rw [hnuRho]
        simp only [mu, Subgroup.coe_mul, epsilon, Subgroup.coe_mk]
        calc
          (rho : Kˣ)⁻¹ *
                (a.lemma814Epsilon b * (rho : Kˣ) * a.valueUnit 0) =
              a.lemma814Epsilon b * ((rho : Kˣ)⁻¹ * (rho : Kˣ)) *
                a.valueUnit 0 := by ac_rfl
          _ = a.lemma814Epsilon b * a.valueUnit 0 := by simp
      _ = b.valueUnit (0 : Fin 1) :=
        a.lemma814Epsilon_mul_firstValue b
  exact ⟨{
    transform := {
      transformed := f
      firstValue_eq := hfHead
    }
    reachable := hmuStep.reachable.trans
      (hetaStep.reachable.trans hnuStep.reachable)
  }⟩

/-- A multiplier which does not deepen the first adjacent defect keeps the
dynamic first binary alpha below the original first global alpha. -/
theorem rankThreeFirstBinaryAlphaAfterRightMultiplier_le_firstAlpha_of_product_le
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 3)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hnotFirst : ¬a.AttainsHalfGap (0 : Fin 2))
    (theta : Kˣ)
    (hproduct : BONG.GoodBONG.defectOrder (K := K)
        (theta * a.adjacentProduct (0 : Fin 2)) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (0 : Fin 2))) :
    rankThreeFirstBinaryAlphaAfterRightMultiplier a theta ≤
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
  unfold rankThreeFirstBinaryAlphaAfterRightMultiplier
  refine (min_le_right _ _).trans ?_
  have hleft :=
    firstLeftDefectCandidate_eq_alpha_of_normalized_notHalfGap
      a hfirst hnotFirst
  calc
    (((a.order (1 : Fin 3) - a.order (0 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K)
          (theta * a.adjacentProduct (0 : Fin 2)) ≤
      (((a.order (1 : Fin 3) - a.order (0 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2)) := add_le_add_right hproduct _
    _ = (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
      simpa [BONG.GoodBONG.leftDefectCandidate,
        BONG.GoodBONG.adjacentDefect] using hleft

/-- The symmetric dynamic bound at the last edge. -/
theorem rankThreeLastBinaryAlphaAfterLeftMultiplier_le_secondAlpha_of_product_le
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 3)
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hnotLast : ¬a.AttainsHalfGap (1 : Fin 2))
    (mu : Kˣ)
    (hproduct : BONG.GoodBONG.defectOrder (K := K)
        (mu * a.adjacentProduct (1 : Fin 2)) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (1 : Fin 2))) :
    rankThreeLastBinaryAlphaAfterLeftMultiplier a mu ≤
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
  unfold rankThreeLastBinaryAlphaAfterLeftMultiplier
  refine (min_le_right _ _).trans ?_
  have hleft :=
    lastLeftDefectCandidate_eq_alpha_of_normalized_notHalfGap
      a hlast hnotLast
  calc
    (((a.order (2 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K)
          (mu * a.adjacentProduct (1 : Fin 2)) ≤
      (((a.order (2 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (1 : Fin 2)) := add_le_add_right hproduct _
    _ = (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
      simpa [BONG.GoodBONG.leftDefectCandidate,
        BONG.GoodBONG.adjacentDefect] using hleft

/-- Unequal outer orders with a last half-gap.  The complementary-defect
unit from the printed proof is strictly deeper than the first adjacent
class.  In its favorable Hilbert orientation it gives the direct dynamic
right-left bridge.  In the opposite orientation a first-alpha reference
and the two-character correction supply `rho`; the last half-gap makes the
middle dynamic bound automatic, yielding the prescribed-head
`0→1→0` bridge. -/
theorem reachableLemma814_rankThree_negative_of_unequalOuter_lastHalfGap
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (houter : a.Lemma814UnequalOuterBound b)
    (hlastHalf : a.AttainsHalfGap (1 : Fin 2))
    (hepsilonFirst : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  have hnotFirst : ¬a.AttainsHalfGap (0 : Fin 2) := by
    intro hfirstHalf
    exact (not_both_attainHalfGap_of_unequalOuter
      a b conditions houter hfirstHalf) hlastHalf
  have hsecondPositive :=
    a.secondAlpha_pos_of_lemma814UnequalOuterBound
      b conditions houter hepsilonFirst
  have hsumTop :=
    a.secondAlpha_add_fullDefect_le_twoE_of_unequalOuter b houter
  have hfullNotTop : a.truncatedPrefixDefect b (-1) 3 1 ≠ ⊤ := by
    intro htop
    rw [htop] at hsumTop
    have hfinite : (2 : WithTop ℚ) *
        ((ramificationIndex K : ℚ) : WithTop ℚ) ≠ ⊤ := by
      rw [show (2 : WithTop ℚ) *
          ((ramificationIndex K : ℚ) : WithTop ℚ) =
        ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) by norm_num]
      exact WithTop.coe_ne_top
    have hrightTop : (2 : WithTop ℚ) *
        ((ramificationIndex K : ℚ) : WithTop ℚ) = ⊤ :=
      top_unique (by simpa only [add_top] using hsumTop)
    exact hfinite hrightTop
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hfullNotTop
  have hzDefect : BONG.GoodBONG.defectOrder (K := K)
      (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) =
        (d : WithTop ℚ) := by
    calc
      BONG.GoodBONG.defectOrder (K := K)
          (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) =
          a.truncatedPrefixDefect b (-1) 3 1 :=
        (a.lemma814TernaryFullDefect_eq_epsilon_mul_secondAdjacent b).symm
      _ = (d : WithTop ℚ) := hd.symm
  have hdNonnegative : 0 ≤ d := by
    have hnonnegative := BONG.GoodBONG.defectOrder_nonneg
      (K := K) (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
    rw [hzDefect] at hnonnegative
    exact_mod_cast hnonnegative
  rw [← hd] at hsumTop
  have htwoE : (2 : WithTop ℚ) *
        ((ramificationIndex K : ℚ) : WithTop ℚ) =
      ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    norm_num
  rw [htwoE] at hsumTop
  have hsumRat : a.alphaValue (1 : Fin 2) + d ≤
      2 * (ramificationIndex K : ℚ) := by
    exact_mod_cast hsumTop
  have hdLt : d < 2 * (ramificationIndex K : ℚ) := by
    linarith
  rcases exists_complementaryDefect_hilbert_neg_of_nonnegative
      (K := K)
      (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
      d hzDefect hdNonnegative hdLt with
    ⟨etaRaw, hetaUnit, hetaDefect, hetaCombined⟩
  let eta : valuationUnitSubgroup K := ⟨etaRaw, hetaUnit⟩
  have hetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) := by
    rw [show ((eta : valuationUnitSubgroup K) : Kˣ) = etaRaw by rfl,
      hetaDefect]
    exact_mod_cast (show a.alphaValue (1 : Fin 2) ≤
        2 * (ramificationIndex K : ℚ) - d by linarith)
  have hfirstFull :=
    firstAlpha_le_fullDefect_of_lastHalfGap_unequalOuter
      a b conditions houter hlastHalf
  have hfirstD : a.alphaValue (0 : Fin 2) ≤ d := by
    rw [← hd] at hfirstFull
    exact_mod_cast hfirstFull
  have hfirstOdd := a.beli2009Lemma27_iv (0 : Fin 2) hnotFirst
  have hfirstNonnegative : 0 ≤ a.alphaValue (0 : Fin 2) :=
    (a.beli2009Lemma27_i (0 : Fin 2)).1
  have hfirstLt : a.alphaValue (0 : Fin 2) <
      2 * (ramificationIndex K : ℚ) := by
    linarith
  rcases DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      (a.alphaValue (0 : Fin 2)) hfirstOdd hfirstNonnegative hfirstLt with
    ⟨reference, hrefUnit, hrefDefect⟩
  have hsumEtaReferenceOrder :
      BONG.GoodBONG.defectOrder (K := K) etaRaw +
          BONG.GoodBONG.defectOrder (K := K) reference ≤
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hetaDefect, hrefDefect]
    exact_mod_cast (show
      (2 * (ramificationIndex K : ℚ) - d) +
          a.alphaValue (0 : Fin 2) ≤
        2 * (ramificationIndex K : ℚ) by linarith)
  have hsumEtaReference : quadraticDefect K etaRaw +
        quadraticDefect K reference ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞) :=
    quadraticDefect_add_le_twoE_of_defectOrder_add_le_twoE_enat
      etaRaw reference hsumEtaReferenceOrder
  have hepsilonUnit : IsValuationUnit K
      ((a.lemma814Epsilon b : Kˣ) : K) :=
    a.lemma814Epsilon_isValuationUnit b horder
  have hrefDepth : BONG.GoodBONG.defectOrder (K := K) reference ≤
      BONG.GoodBONG.defectOrder (K := K) (a.lemma814Epsilon b) := by
    rw [hrefDefect]
    exact a.alpha_le_lemma814EpsilonDefect b conditions
  have hA₀EtaLt : BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (0 : Fin 2)) <
      BONG.GoodBONG.defectOrder (K := K) etaRaw :=
    firstAdjacentDefectOrder_lt_complementary_of_unequalOuter
      a b houter hfirst hnotFirst d hd.symm etaRaw hetaDefect
  have hetaA₀ : BONG.GoodBONG.defectOrder (K := K)
      (etaRaw * a.adjacentProduct (0 : Fin 2)) =
        BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2)) :=
    BONG.GoodBONG.defectOrder_mul_eq_right_of_lt_left
      (K := K) hA₀EtaLt
  have hpair : hilbertSymbol K etaRaw (a.lemma814Epsilon b) *
        hilbertSymbol K etaRaw (a.adjacentProduct (1 : Fin 2)) = -1 := by
    calc
      hilbertSymbol K etaRaw (a.lemma814Epsilon b) *
            hilbertSymbol K etaRaw (a.adjacentProduct (1 : Fin 2)) =
          hilbertSymbol K etaRaw
            (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) := by
        rw [hilbertSymbol_mul_right]
      _ = -1 := hetaCombined
  rcases Int.units_eq_one_or
      (hilbertSymbol K etaRaw (a.adjacentProduct (1 : Fin 2))) with
    hetaLast | hetaLast
  · have hetaEpsilon : hilbertSymbol K etaRaw
        (a.lemma814Epsilon b) = -1 := by
      rw [hetaLast] at hpair
      simpa using hpair
    have hdynamic : rankThreeFirstBinaryAlphaAfterRightMultiplier
          a (eta : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K) (a.lemma814Epsilon b) := by
      have hlocal :=
        rankThreeFirstBinaryAlphaAfterRightMultiplier_le_firstAlpha_of_product_le
          a hfirst hnotFirst etaRaw hetaA₀.le
      exact hlocal.trans (a.alpha_le_lemma814EpsilonDefect b conditions)
    exact reachableLemma814_rankThree_negative_of_dynamicTheta
      a b horder conditions hlast hepsilonFirst eta hetaDepth
        (by simpa only [eta, Subgroup.coe_mk] using hetaLast)
        (by simpa only [eta, Subgroup.coe_mk] using hetaEpsilon)
        (by simpa only [eta, Subgroup.coe_mk] using hdynamic)
  · have hetaEpsilon : hilbertSymbol K etaRaw
        (a.lemma814Epsilon b) = 1 := by
      rw [hetaLast] at hpair
      have hcancel := congrArg (fun z : ℤˣ => (-1 : ℤˣ) * z) hpair
      simpa [mul_assoc] using hcancel
    rcases exists_valuationUnit_two_negative_correction
        (a.lemma814Epsilon b) etaRaw
        (a.adjacentProduct (0 : Fin 2)) reference
        hepsilonUnit hrefUnit hrefDepth hsumEtaReference
        (by rw [hilbertSymbol_comm K]; exact hetaEpsilon)
        hepsilonFirst with
      ⟨rhoRaw, hrhoUnit, hrhoDepthRaw, hrhoEta, hrhoFirst⟩
    let rho : valuationUnitSubgroup K := ⟨rhoRaw, hrhoUnit⟩
    have hrhoDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ) := by
      rw [← hrefDefect]
      simpa only [rho, Subgroup.coe_mk] using hrhoDepthRaw
    have hdynamicLast : rankThreeLastBinaryAlphaAfterLeftMultiplier
          a (a.lemma814Epsilon b * (rho : Kˣ)) ≤
        BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) := by
      unfold rankThreeLastBinaryAlphaAfterLeftMultiplier
      refine (min_le_left _ _).trans ?_
      calc
        a.halfGapCandidate (1 : Fin 2) =
            (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
          rw [← a.coe_halfGapValue]
          exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hlastHalf.symm
        _ ≤ BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) := hetaDepth
    have hdynamicFirst : rankThreeFirstBinaryAlphaAfterRightMultiplier
          a (eta : Kˣ) ≤
        BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ) := by
      have hlocal :=
        rankThreeFirstBinaryAlphaAfterRightMultiplier_le_firstAlpha_of_product_le
          a hfirst hnotFirst etaRaw hetaA₀.le
      exact hlocal.trans hrhoDepth
    exact reachableLemma814_rankThree_negative_of_zeroOneZero_dynamic
      a b horder conditions hfirst hepsilonFirst eta rho hetaDepth
        (by simpa only [eta, Subgroup.coe_mk] using hetaLast)
        (by simpa only [eta, Subgroup.coe_mk] using hetaEpsilon)
        hrhoDepth
        (by simpa only [rho, eta, Subgroup.coe_mk] using hrhoEta)
        (by simpa only [rho, Subgroup.coe_mk] using hrhoFirst)
        hdynamicLast hdynamicFirst

/-- Path-refined strict unequal-outer ternary case.  The easy orientation is
the right-left dynamic bridge.  In the opposite orientation, P1 leaves only
one possible cancellation boundary.  Off that boundary the elementary
two-character correction gives a `0→1→0` path.  On the boundary a
large-residue fixed-layer neighbour preserves the last adjacent defect; its
two Hilbert orientations are resolved respectively by the same three-step
path and by the fully dynamic four-step bridge. -/
theorem reachableLemma814_rankThree_negative_of_unequalOuter_strict_of_largeResidue
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (houter : a.Lemma814UnequalOuterBound b)
    (hnotFirst : ¬a.AttainsHalfGap (0 : Fin 2))
    (hnotLast : ¬a.AttainsHalfGap (1 : Fin 2))
    (hepsilonFirst : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  let A₀ : Kˣ := a.adjacentProduct (0 : Fin 2)
  let A₁ : Kˣ := a.adjacentProduct (1 : Fin 2)
  let epsilon : valuationUnitSubgroup K :=
    ⟨a.lemma814Epsilon b, a.lemma814Epsilon_isValuationUnit b horder⟩
  rcases exists_unequalOuter_strict_eta_of_largeResidue
      hres a b conditions houter hfirst hnotFirst hnotLast with
    ⟨etaRaw, hetaUnit, hetaDefect, hetaA₀Le, hetaCombined⟩
  let eta : valuationUnitSubgroup K := ⟨etaRaw, hetaUnit⟩
  have hepsilonUnit : IsValuationUnit K ((epsilon : Kˣ) : K) := by
    exact (epsilon : valuationUnitSubgroup K).property
  have hepsilonDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (epsilon : Kˣ) := by
    simpa only [epsilon, Subgroup.coe_mk] using
      a.alpha_le_lemma814EpsilonDefect b conditions
  have hfirstOdd := a.beli2009Lemma27_iv (0 : Fin 2) hnotFirst
  have hsecondOdd := a.beli2009Lemma27_iv (1 : Fin 2) hnotLast
  have hfirstNonnegative : 0 ≤ a.alphaValue (0 : Fin 2) :=
    (a.beli2009Lemma27_i (0 : Fin 2)).1
  have hsecondNonnegative : 0 ≤ a.alphaValue (1 : Fin 2) :=
    (a.beli2009Lemma27_i (1 : Fin 2)).1
  have hfirstPositive : 0 < a.alphaValue (0 : Fin 2) := by
    rcases hfirstOdd with ⟨z, hzOdd, hz⟩
    have hzNonnegative : 0 ≤ z := by
      rw [hz] at hfirstNonnegative
      exact_mod_cast hfirstNonnegative
    have hzPositive : 0 < z := by
      rcases hzOdd with ⟨m, hm⟩
      omega
    rw [hz]
    exact_mod_cast hzPositive
  have hsecondPositive : 0 < a.alphaValue (1 : Fin 2) := by
    rcases hsecondOdd with ⟨z, hzOdd, hz⟩
    have hzNonnegative : 0 ≤ z := by
      rw [hz] at hsecondNonnegative
      exact_mod_cast hsecondNonnegative
    have hzPositive : 0 < z := by
      rcases hzOdd with ⟨m, hm⟩
      omega
    rw [hz]
    exact_mod_cast hzPositive
  have halphaSum :=
    a.alphaSum_le_twoE_of_lemma814UnequalOuterBound b conditions houter
  have hfirstLt : a.alphaValue (0 : Fin 2) <
      2 * (ramificationIndex K : ℚ) := by
    linarith
  rcases DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      (a.alphaValue (0 : Fin 2)) hfirstOdd hfirstNonnegative hfirstLt with
    ⟨reference, hrefUnit, hrefDefect⟩
  have hsumOrder : BONG.GoodBONG.defectOrder (K := K) etaRaw +
        BONG.GoodBONG.defectOrder (K := K) reference ≤
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hetaDefect, hrefDefect]
    exact_mod_cast (show a.alphaValue (1 : Fin 2) +
        a.alphaValue (0 : Fin 2) ≤ 2 * (ramificationIndex K : ℚ) by
      simpa only [add_comm] using halphaSum)
  have hsumQuadratic : quadraticDefect K etaRaw +
        quadraticDefect K reference ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞) :=
    quadraticDefect_add_le_twoE_of_defectOrder_add_le_twoE_enat
      etaRaw reference hsumOrder
  have hpair : hilbertSymbol K etaRaw (a.lemma814Epsilon b) *
        hilbertSymbol K etaRaw A₁ = -1 := by
    calc
      hilbertSymbol K etaRaw (a.lemma814Epsilon b) *
            hilbertSymbol K etaRaw A₁ =
          hilbertSymbol K etaRaw (a.lemma814Epsilon b * A₁) := by
            rw [hilbertSymbol_mul_right]
      _ = hilbertSymbol K (a.lemma814Epsilon b * A₁) etaRaw :=
        hilbertSymbol_comm K _ _
      _ = -1 := by simpa only [A₁] using hetaCombined
  rcases Int.units_eq_one_or (hilbertSymbol K etaRaw A₁) with
      hetaLast | hetaLast
  · have hetaEpsilon : hilbertSymbol K etaRaw
        (a.lemma814Epsilon b) = -1 := by
      rw [hetaLast] at hpair
      simpa using hpair
    apply reachableLemma814_rankThree_negative_of_dynamicTheta
      a b horder conditions hlast hepsilonFirst eta
    · simpa only [eta, Subgroup.coe_mk] using hetaDefect.ge
    · simpa only [eta, Subgroup.coe_mk, A₁] using hetaLast
    · simpa only [eta, Subgroup.coe_mk] using hetaEpsilon
    · have hdynamic :=
        rankThreeFirstBinaryAlphaAfterRightMultiplier_le_firstAlpha_of_product_le
          a hfirst hnotFirst etaRaw (by simpa only [A₀] using hetaA₀Le)
      exact hdynamic.trans (by
        simpa only [epsilon, Subgroup.coe_mk] using hepsilonDepth)
  · have hetaEpsilon : hilbertSymbol K etaRaw
        (a.lemma814Epsilon b) = 1 := by
      rw [hetaLast] at hpair
      have h := hpair
      norm_num at h ⊢
      exact h
    have hA₁Le : BONG.GoodBONG.defectOrder (K := K) A₁ ≤
        (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
      simpa only [A₁] using
        secondAdjacentDefectOrder_le_firstAlpha_of_normalized_notHalfGap
          a hlast hnotLast
    by_cases hA₁Eq : BONG.GoodBONG.defectOrder (K := K) A₁ =
        (a.alphaValue (0 : Fin 2) : WithTop ℚ)
    · have hA₁RefOrder : BONG.GoodBONG.defectOrder (K := K) A₁ =
          BONG.GoodBONG.defectOrder (K := K) reference := by
        rw [hA₁Eq, hrefDefect]
      have hA₁Quadratic : quadraticDefect K A₁ =
          quadraticDefect K reference :=
        BONG.GoodBONG.quadraticDefect_eq_of_defectOrder_eq
          A₁ reference hA₁RefOrder
      have hA₁Finite : quadraticDefect K A₁ ≠ ⊤ := by
        rw [hA₁Quadratic]
        intro htop
        have htopOrder : BONG.GoodBONG.defectOrder (K := K) reference =
            ⊤ := by
          unfold BONG.GoodBONG.defectOrder
          rw [htop]
          rfl
        rw [hrefDefect] at htopOrder
        exact WithTop.coe_ne_top htopOrder
      have hA₁Nonzero : quadraticDefect K A₁ ≠ 0 := by
        rw [hA₁Quadratic]
        exact quadraticDefect_ne_zero_of_isValuationUnit reference hrefUnit
      have hA₁NotTwoE : quadraticDefect K A₁ ≠
          ((2 * ramificationIndex K : Nat) : ℕ∞) := by
        intro htwo
        have horderTwo : BONG.GoodBONG.defectOrder (K := K) A₁ =
            (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
          unfold BONG.GoodBONG.defectOrder
          rw [htwo]
          rfl
        rw [hA₁Eq] at horderTwo
        have halphaTwo : a.alphaValue (0 : Fin 2) =
            2 * (ramificationIndex K : ℚ) := by
          have h := WithTop.coe_eq_coe.mp horderTwo
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
        exact (ne_of_lt hfirstLt) halphaTwo
      have hadjacentSum :=
        unequalOuter_adjacentDefectOrder_sum_lt_twoE_of_normalized_notHalfGaps
          a b conditions houter hfirst hlast hnotFirst hnotLast
      have hfixedOrder :
          BONG.GoodBONG.defectOrder (K := K) (etaRaw * A₀) +
              BONG.GoodBONG.defectOrder (K := K) A₁ ≤
            (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
        exact (add_le_add_left (by simpa only [A₀] using hetaA₀Le) _).trans
          hadjacentSum.le
      have hfixedSum : quadraticDefect K (etaRaw * A₀) +
            quadraticDefect K A₁ ≤
          ((2 * ramificationIndex K : Nat) : ℕ∞) :=
        quadraticDefect_add_le_twoE_of_defectOrder_add_le_twoE_enat
          (etaRaw * A₀) A₁ hfixedOrder
      rcases exists_same_defect_product_hilbert_neg_one_of_largeResidue
          hres (etaRaw * A₀) A₁ hA₁Finite hA₁Nonzero hA₁NotTwoE
            hfixedSum with
        ⟨w, hwDefect, hA₁wDefect, hwCombined⟩
      have hwEven : Even (ordUnit K w) := by
        rcases Int.even_or_odd (ordUnit K w) with heven | hodd
        · exact heven
        · exact (hA₁Nonzero (by
            rw [← hwDefect]
            exact quadraticDefect_eq_zero_of_odd_ordUnit w hodd)).elim
      rcases BONG.GoodBONG.exists_valuationUnit_eq_mul_square_of_even_order
          w hwEven with ⟨muRaw, s, hmuUnit, hmuFactor⟩
      let mu : valuationUnitSubgroup K := ⟨muRaw, hmuUnit⟩
      have hmuQuadratic : quadraticDefect K muRaw =
          quadraticDefect K A₁ := by
        rw [hmuFactor, quadraticDefect_mul_square]
        exact hwDefect
      have hmuDefect : BONG.GoodBONG.defectOrder (K := K) muRaw =
          (a.alphaValue (0 : Fin 2) : WithTop ℚ) :=
        (defectOrder_eq_of_quadraticDefect_eq muRaw A₁ hmuQuadratic).trans
          hA₁Eq
      have hmuA₁Quadratic : quadraticDefect K (muRaw * A₁) =
          quadraticDefect K A₁ := by
        rw [hmuFactor]
        rw [show (w * s ^ 2) * A₁ = (A₁ * w) * s ^ 2 by ac_rfl,
          quadraticDefect_mul_square]
        exact hA₁wDefect
      have hmuA₁Order : BONG.GoodBONG.defectOrder (K := K)
          (muRaw * A₁) = BONG.GoodBONG.defectOrder (K := K) A₁ :=
        defectOrder_eq_of_quadraticDefect_eq (muRaw * A₁) A₁
          hmuA₁Quadratic
      have hmuCombined : hilbertSymbol K (etaRaw * A₀) muRaw = -1 := by
        rw [hmuFactor, hilbertSymbol_mul_square_right]
        exact hwCombined
      have hmuPair : hilbertSymbol K etaRaw muRaw *
          hilbertSymbol K A₀ muRaw = -1 := by
        simpa only [hilbertSymbol_mul_left] using hmuCombined
      rcases Int.units_eq_one_or (hilbertSymbol K etaRaw muRaw) with
          hetaMu | hetaMu
      · have hA₀Mu : hilbertSymbol K A₀ muRaw = -1 := by
          rw [hetaMu] at hmuPair
          simpa using hmuPair
        have hA₀Le : BONG.GoodBONG.defectOrder (K := K) A₀ ≤
            (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
          simpa only [A₀] using
            firstAdjacentDefectOrder_le_secondAlpha_of_normalized_notHalfGap
              a hfirst hnotFirst
        obtain ⟨thetaReference, hthetaReferenceUnit,
            halphaOneLeReference, hA₀LtReference,
            hmuReferenceSum, hmuA₁ReferenceSum⟩ :
            ∃ thetaReference : Kˣ,
              IsValuationUnit K (thetaReference : K) ∧
                (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
                  BONG.GoodBONG.defectOrder (K := K) thetaReference ∧
                BONG.GoodBONG.defectOrder (K := K) A₀ <
                  BONG.GoodBONG.defectOrder (K := K) thetaReference ∧
                quadraticDefect K muRaw + quadraticDefect K thetaReference ≤
                  ((2 * ramificationIndex K : Nat) : ℕ∞) ∧
                quadraticDefect K (muRaw * A₁) +
                    quadraticDefect K thetaReference ≤
                  ((2 * ramificationIndex K : Nat) : ℕ∞) := by
          by_cases hA₀Eq : BONG.GoodBONG.defectOrder (K := K) A₀ =
              (a.alphaValue (1 : Fin 2) : WithTop ℚ)
          · have hstrictOrder :
                BONG.GoodBONG.defectOrder (K := K) muRaw +
                    BONG.GoodBONG.defectOrder (K := K) etaRaw <
                  (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
              rw [hmuDefect, hetaDefect, ← hA₁Eq, ← hA₀Eq]
              simpa only [add_comm] using hadjacentSum
            have hstrictQuadratic :=
              quadraticDefect_add_lt_twoE_of_defectOrder_add_lt_twoE
                muRaw etaRaw hstrictOrder
            rcases
                DyadicHilbertDefectChoiceLaws.exists_higher_defect_negative_of_sum_lt
                  muRaw etaRaw hstrictQuadratic with
              ⟨c, hcDefect, hcHilbert⟩
            have hcNonzero : quadraticDefect K c ≠ 0 := by
              intro hcZero
              rw [hcZero] at hcDefect
              exact (not_lt_of_ge bot_le hcDefect)
            rcases exists_valuationUnit_same_defect_same_hilbert
                muRaw c hcNonzero with
              ⟨thetaReference, hthetaReferenceUnit,
                hthetaReferenceDefect, hthetaReferenceHilbert⟩
            have hetaReferenceLt : BONG.GoodBONG.defectOrder (K := K)
                etaRaw < BONG.GoodBONG.defectOrder (K := K)
                  thetaReference :=
              BONG.GoodBONG.defectOrder_lt_of_quadraticDefect_lt
                etaRaw thetaReference
                  (hcDefect.trans_eq hthetaReferenceDefect.symm)
            have hmuReferenceHilbert : hilbertSymbol K muRaw
                thetaReference = -1 :=
              hthetaReferenceHilbert.trans hcHilbert
            have hmuReferenceSum :=
              (beli2019Lemma82_i muRaw thetaReference).mp
                ⟨thetaReference, rfl, hmuReferenceHilbert⟩
            have hmuA₁ReferenceSum : quadraticDefect K (muRaw * A₁) +
                quadraticDefect K thetaReference ≤
                  ((2 * ramificationIndex K : Nat) : ℕ∞) := by
              rw [hmuA₁Quadratic]
              rw [← hmuQuadratic]
              exact hmuReferenceSum
            exact ⟨thetaReference, hthetaReferenceUnit,
              hetaDefect.ge.trans hetaReferenceLt.le,
              (hA₀Eq.trans hetaDefect.symm) ▸ hetaReferenceLt,
              hmuReferenceSum, hmuA₁ReferenceSum⟩
          · have hA₀LtEta : BONG.GoodBONG.defectOrder (K := K) A₀ <
                BONG.GoodBONG.defectOrder (K := K) etaRaw := by
              rw [hetaDefect]
              exact lt_of_le_of_ne hA₀Le hA₀Eq
            have hmuEtaSum : quadraticDefect K muRaw +
                quadraticDefect K etaRaw ≤
                  ((2 * ramificationIndex K : Nat) : ℕ∞) := by
              rw [hmuQuadratic, hA₁Quadratic]
              simpa only [add_comm] using hsumQuadratic
            have hmuA₁EtaSum : quadraticDefect K (muRaw * A₁) +
                quadraticDefect K etaRaw ≤
                  ((2 * ramificationIndex K : Nat) : ℕ∞) := by
              rw [hmuA₁Quadratic, hA₁Quadratic]
              simpa only [add_comm] using hsumQuadratic
            exact ⟨etaRaw, hetaUnit, hetaDefect.ge, hA₀LtEta,
              hmuEtaSum, hmuA₁EtaSum⟩
        rcases exists_valuationUnit_hilbert_neg_one_of_two_sums_le
            muRaw A₁ thetaReference hthetaReferenceUnit
              hmuReferenceSum hmuA₁ReferenceSum with
          ⟨thetaRaw, hthetaUnit, hthetaReferenceDepth,
            hmuTheta, hA₁Theta⟩
        let theta : valuationUnitSubgroup K := ⟨thetaRaw, hthetaUnit⟩
        have hthetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
            BONG.GoodBONG.defectOrder (K := K) thetaRaw :=
          halphaOneLeReference.trans hthetaReferenceDepth
        have hthetaA₀Order : BONG.GoodBONG.defectOrder (K := K)
            (thetaRaw * A₀) = BONG.GoodBONG.defectOrder (K := K) A₀ :=
          BONG.GoodBONG.defectOrder_mul_eq_right_of_lt_left
            (K := K) (hA₀LtReference.trans_le hthetaReferenceDepth)
        have hthetaAlpha : a.adjacentBinaryAlpha (1 : Fin 2) ≤
            BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) := by
          rw [show a.adjacentBinaryAlpha (1 : Fin 2) =
              a.lastBinaryAlpha by rfl, hlast]
          simpa only [theta, Subgroup.coe_mk] using hthetaDepth
        have hmuAlpha : rankThreeFirstBinaryAlphaAfterRightMultiplier
              a (theta : Kˣ) ≤
            BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) := by
          have hdynamic :=
            rankThreeFirstBinaryAlphaAfterRightMultiplier_le_firstAlpha_of_product_le
              a hfirst hnotFirst thetaRaw (by
                simpa only [A₀] using hthetaA₀Order.le)
          exact hdynamic.trans (by
            simpa only [mu, Subgroup.coe_mk] using hmuDefect.ge)
        have hkappaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
            BONG.GoodBONG.defectOrder (K := K)
              (((eta / theta : valuationUnitSubgroup K) : Kˣ)) := by
          change (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
            BONG.GoodBONG.defectOrder (K := K)
              ((etaRaw : Kˣ) * (thetaRaw : Kˣ)⁻¹)
          have hinvDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
              BONG.GoodBONG.defectOrder (K := K) thetaRaw⁻¹ := by
            rw [BONG.GoodBONG.defectOrder_inv]
            exact hthetaDepth
          exact (le_min hetaDefect.ge hinvDepth).trans
            (BONG.GoodBONG.defectOrder_mul_ge_min
              (K := K) etaRaw thetaRaw⁻¹)
        have hkappaAlpha : rankThreeLastBinaryAlphaAfterLeftMultiplier
              a (mu : Kˣ) ≤
            BONG.GoodBONG.defectOrder (K := K)
              (((eta / theta : valuationUnitSubgroup K) : Kˣ)) := by
          have hdynamic :=
            rankThreeLastBinaryAlphaAfterLeftMultiplier_le_secondAlpha_of_product_le
              a hlast hnotLast muRaw (by
                simpa only [A₁] using hmuA₁Order.le)
          exact hdynamic.trans hkappaDepth
        have hnuDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
            BONG.GoodBONG.defectOrder (K := K)
              (((epsilon / mu : valuationUnitSubgroup K) : Kˣ)) := by
          change (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
            BONG.GoodBONG.defectOrder (K := K)
              ((a.lemma814Epsilon b) * muRaw⁻¹)
          have hmuInvDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
              BONG.GoodBONG.defectOrder (K := K) muRaw⁻¹ := by
            rw [BONG.GoodBONG.defectOrder_inv, hmuDefect]
          exact (le_min (by
              simpa only [epsilon, Subgroup.coe_mk] using hepsilonDepth)
              hmuInvDepth).trans
            (BONG.GoodBONG.defectOrder_mul_ge_min
              (K := K) (a.lemma814Epsilon b) muRaw⁻¹)
        have hnuAlpha : rankThreeFirstBinaryAlphaAfterRightMultiplier
              a (eta : Kˣ) ≤
            BONG.GoodBONG.defectOrder (K := K)
              (((epsilon / mu : valuationUnitSubgroup K) : Kˣ)) := by
          have hdynamic :=
            rankThreeFirstBinaryAlphaAfterRightMultiplier_le_firstAlpha_of_product_le
              a hfirst hnotFirst etaRaw (by simpa only [A₀] using hetaA₀Le)
          exact hdynamic.trans hnuDepth
        have hbridge : hilbertSymbol K (theta : Kˣ) (mu : Kˣ) =
            hilbertSymbol K A₀ (mu : Kˣ) := by
          rw [hilbertSymbol_comm K]
          simpa only [theta, mu, Subgroup.coe_mk, hmuTheta, A₀, hA₀Mu]
        exact reachableLemma814_rankThree_negative_of_fourStepBridge_dynamic
          a b horder hepsilonFirst eta theta mu
            (by simpa only [eta, Subgroup.coe_mk, A₁] using hetaLast)
            (by simpa only [eta, Subgroup.coe_mk] using hetaEpsilon)
            hthetaAlpha
            (by rw [hilbertSymbol_comm K];
                simpa only [theta, Subgroup.coe_mk, A₁] using hA₁Theta)
            hmuAlpha hkappaAlpha
            (by simpa only [eta, mu, Subgroup.coe_mk, A₀] using hmuCombined)
            (by simpa only [A₀] using hbridge) hnuAlpha
      · have hA₀Mu : hilbertSymbol K A₀ muRaw = 1 := by
          rw [hetaMu] at hmuPair
          have h := hmuPair
          norm_num at h ⊢
          exact h
        let rho : valuationUnitSubgroup K := epsilon * mu
        have hrhoDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
            BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ) := by
          exact (le_min hepsilonDepth hmuDefect.ge).trans
            (BONG.GoodBONG.defectOrder_mul_ge_min
              (K := K) (epsilon : Kˣ) (mu : Kˣ))
        have hrhoEta : hilbertSymbol K (rho : Kˣ) (eta : Kˣ) = -1 := by
          simp only [rho, Subgroup.coe_mul, epsilon, eta, mu,
            Subgroup.coe_mk]
          rw [hilbertSymbol_mul_left,
            hilbertSymbol_comm K (a.lemma814Epsilon b) etaRaw,
            hetaEpsilon,
            hilbertSymbol_comm K muRaw etaRaw, hetaMu]
          norm_num
        have hrhoA₀ : hilbertSymbol K (rho : Kˣ) A₀ = -1 := by
          simp only [rho, Subgroup.coe_mul, epsilon, mu, Subgroup.coe_mk]
          rw [hilbertSymbol_mul_left]
          rw [show hilbertSymbol K (a.lemma814Epsilon b) A₀ = -1 by
            simpa only [A₀] using hepsilonFirst,
            hilbertSymbol_comm K muRaw A₀, hA₀Mu]
          norm_num
        have hscaledA₁ : BONG.GoodBONG.defectOrder (K := K)
              (a.lemma814Epsilon b * (rho : Kˣ) * A₁) =
            BONG.GoodBONG.defectOrder (K := K) (muRaw * A₁) := by
          simp only [rho, epsilon, mu, Subgroup.coe_mul, Subgroup.coe_mk]
          rw [show a.lemma814Epsilon b *
                (a.lemma814Epsilon b * muRaw) * A₁ =
              (muRaw * A₁) * (a.lemma814Epsilon b) ^ 2 by
                simp only [pow_two]; ac_rfl,
            BONG.GoodBONG.defectOrder_mul_square]
        have hdynamicLast : rankThreeLastBinaryAlphaAfterLeftMultiplier
              a (a.lemma814Epsilon b * (rho : Kˣ)) ≤
            BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) := by
          have hdynamic :=
            rankThreeLastBinaryAlphaAfterLeftMultiplier_le_secondAlpha_of_product_le
              a hlast hnotLast (a.lemma814Epsilon b * (rho : Kˣ))
                (by rw [hscaledA₁]; simpa only [A₁] using hmuA₁Order.le)
          exact hdynamic.trans (by
            simpa only [eta, Subgroup.coe_mk] using hetaDefect.ge)
        have hdynamicFirst : rankThreeFirstBinaryAlphaAfterRightMultiplier
              a (eta : Kˣ) ≤
            BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ) := by
          have hdynamic :=
            rankThreeFirstBinaryAlphaAfterRightMultiplier_le_firstAlpha_of_product_le
              a hfirst hnotFirst etaRaw (by simpa only [A₀] using hetaA₀Le)
          exact hdynamic.trans hrhoDepth
        exact reachableLemma814_rankThree_negative_of_zeroOneZero_dynamic
          a b horder conditions hfirst hepsilonFirst eta rho
            (by simpa only [eta, Subgroup.coe_mk] using hetaDefect.ge)
            (by simpa only [eta, Subgroup.coe_mk, A₁] using hetaLast)
            (by simpa only [eta, Subgroup.coe_mk] using hetaEpsilon)
            hrhoDepth hrhoEta (by simpa only [A₀] using hrhoA₀)
            hdynamicLast hdynamicFirst
    · have hA₁Lt : BONG.GoodBONG.defectOrder (K := K) A₁ <
          (a.alphaValue (0 : Fin 2) : WithTop ℚ) :=
        lt_of_le_of_ne hA₁Le hA₁Eq
      rcases exists_valuationUnit_two_negative_correction
          (epsilon : Kˣ) etaRaw A₀ reference hepsilonUnit hrefUnit
            (by rw [hrefDefect];
                simpa only [epsilon, Subgroup.coe_mk] using hepsilonDepth)
            hsumQuadratic
            (by rw [hilbertSymbol_comm K];
                simpa only [epsilon, Subgroup.coe_mk] using hetaEpsilon)
            (by simpa only [epsilon, Subgroup.coe_mk, A₀] using
              hepsilonFirst) with
        ⟨rhoRaw, hrhoUnit, hrhoDepth, hrhoEta, hrhoA₀⟩
      let rho : valuationUnitSubgroup K := ⟨rhoRaw, hrhoUnit⟩
      have hrhoAlphaDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
          BONG.GoodBONG.defectOrder (K := K) rhoRaw := by
        rw [← hrefDefect]
        exact hrhoDepth
      have hmuDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
          BONG.GoodBONG.defectOrder (K := K)
            (a.lemma814Epsilon b * rhoRaw) := by
        exact (le_min hepsilonDepth hrhoAlphaDepth).trans
          (BONG.GoodBONG.defectOrder_mul_ge_min
            (K := K) (a.lemma814Epsilon b) rhoRaw)
      have hmuA₁Order : BONG.GoodBONG.defectOrder (K := K)
          ((a.lemma814Epsilon b * rhoRaw) * A₁) =
            BONG.GoodBONG.defectOrder (K := K) A₁ :=
        BONG.GoodBONG.defectOrder_mul_eq_right_of_lt_left
          (K := K) (hA₁Lt.trans_le hmuDepth)
      have hdynamicLast : rankThreeLastBinaryAlphaAfterLeftMultiplier
            a (a.lemma814Epsilon b * (rho : Kˣ)) ≤
          BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) := by
        have hdynamic :=
          rankThreeLastBinaryAlphaAfterLeftMultiplier_le_secondAlpha_of_product_le
            a hlast hnotLast (a.lemma814Epsilon b * rhoRaw)
              (by simpa only [A₁] using hmuA₁Order.le)
        exact hdynamic.trans (by
          simpa only [eta, Subgroup.coe_mk] using hetaDefect.ge)
      have hdynamicFirst : rankThreeFirstBinaryAlphaAfterRightMultiplier
            a (eta : Kˣ) ≤
          BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ) := by
        have hdynamic :=
          rankThreeFirstBinaryAlphaAfterRightMultiplier_le_firstAlpha_of_product_le
            a hfirst hnotFirst etaRaw (by simpa only [A₀] using hetaA₀Le)
        exact hdynamic.trans (by
          simpa only [rho, Subgroup.coe_mk] using hrhoAlphaDepth)
      exact reachableLemma814_rankThree_negative_of_zeroOneZero_dynamic
        a b horder conditions hfirst hepsilonFirst eta rho
          (by simpa only [eta, Subgroup.coe_mk] using hetaDefect.ge)
          (by simpa only [eta, Subgroup.coe_mk, A₁] using hetaLast)
          (by simpa only [eta, Subgroup.coe_mk] using hetaEpsilon)
          (by simpa only [rho, Subgroup.coe_mk] using hrhoAlphaDepth)
          (by simpa only [rho, eta, Subgroup.coe_mk] using hrhoEta)
          (by simpa only [rho, Subgroup.coe_mk, A₀] using hrhoA₀)
          hdynamicLast hdynamicFirst

/-- Complete path-refined unequal-outer ternary branch.  The positive
Hilbert sign is the literal first binary move.  For the negative sign, the
two half-gap cases above and the strict branch exhaust all possibilities. -/
theorem reachableLemma814_rankThree_unequalOuter_of_largeResidue
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (houter : a.Lemma814UnequalOuterBound b) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases Int.units_eq_one_or
      (hilbertSymbol K (a.lemma814Epsilon b)
        (a.adjacentProduct (0 : Fin 2))) with
    hpositive | hnegative
  · exact reachableLemma814_binaryBranch
      a b horder conditions hfirst hpositive
  · by_cases hfirstHalf : a.AttainsHalfGap (0 : Fin 2)
    · exact reachableLemma814_rankThree_negative_of_unequalOuter_firstHalfGap
        a b horder conditions hlast houter hfirstHalf hnegative
    · by_cases hlastHalf : a.AttainsHalfGap (1 : Fin 2)
      · exact reachableLemma814_rankThree_negative_of_unequalOuter_lastHalfGap
          a b horder conditions hfirst hlast houter hlastHalf hnegative
      · exact
          reachableLemma814_rankThree_negative_of_unequalOuter_strict_of_largeResidue
            hres a b horder conditions hfirst hlast houter hfirstHalf
              hlastHalf hnegative

/-- The opposite orientation left by the strict isotropic construction is not
an obstruction over a residue field with more than two elements.  The two
non-half-gap alphas are positive odd integers `k₀,k₁`, and Remark 8.7 gives
`k₀ + k₁ < 2e`.  A fixed-defect neighbour supplies the middle multiplier
`mu`.  According to its Hilbert sign on the first adjacent product, either
`theta = 1` works or a depth-`k₁+1` principal-layer choice supplies `theta`.
The preceding four-step bridge then installs the prescribed first value. -/
theorem reachableLemma814_rankThree_negative_of_isotropic_opposite_of_largeResidue
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hnotHalf : ¬a.AttainsHalfGap (0 : Fin 2))
    (hepsilonFirst : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (etaRaw : Kˣ)
    (hetaUnit : IsValuationUnit K (etaRaw : K))
    (hetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) etaRaw)
    (hetaFirstProduct : BONG.GoodBONG.defectOrder (K := K)
        (etaRaw * a.adjacentProduct (0 : Fin 2)) =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hetaLast : hilbertSymbol K etaRaw
      (a.adjacentProduct (1 : Fin 2)) = -1)
    (hetaEpsilon : hilbertSymbol K etaRaw
      (a.lemma814Epsilon b) = 1) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [BONG.GoodBONG.remark87PreviousValue,
      BONG.GoodBONG.remark87NextValue] using houter)
  have hsecondNotHalf :
      a.alphaValue (1 : Fin 2) ≠ a.halfGapValue (1 : Fin 2) := by
    intro hsecondHalf
    apply hnotHalf
    apply hremark.attainsHalfGap_iff.mpr
    exact hsecondHalf
  have hfirstOdd := a.beli2009Lemma27_iv (0 : Fin 2) hnotHalf
  have hsecondOdd := a.beli2009Lemma27_iv (1 : Fin 2) hsecondNotHalf
  have hfirstNonnegative : 0 ≤ a.alphaValue (0 : Fin 2) :=
    (a.beli2009Lemma27_i (0 : Fin 2)).1
  have hsecondNonnegative : 0 ≤ a.alphaValue (1 : Fin 2) :=
    (a.beli2009Lemma27_i (1 : Fin 2)).1
  rcases hfirstOdd with ⟨z₀, hz₀Odd, hz₀⟩
  rcases hsecondOdd with ⟨z₁, hz₁Odd, hz₁⟩
  have hz₀Nonnegative : 0 ≤ z₀ := by
    rw [hz₀] at hfirstNonnegative
    exact_mod_cast hfirstNonnegative
  have hz₁Nonnegative : 0 ≤ z₁ := by
    rw [hz₁] at hsecondNonnegative
    exact_mod_cast hsecondNonnegative
  let k₀ : Nat := z₀.toNat
  let k₁ : Nat := z₁.toNat
  have hk₀Int : (k₀ : Int) = z₀ := by
    simpa only [k₀] using Int.toNat_of_nonneg hz₀Nonnegative
  have hk₁Int : (k₁ : Int) = z₁ := by
    simpa only [k₁] using Int.toNat_of_nonneg hz₁Nonnegative
  have hfirstNat : a.alphaValue (0 : Fin 2) = (k₀ : ℚ) := by
    calc
      a.alphaValue (0 : Fin 2) = (z₀ : ℚ) := hz₀
      _ = (k₀ : ℚ) := by exact_mod_cast hk₀Int.symm
  have hsecondNat : a.alphaValue (1 : Fin 2) = (k₁ : ℚ) := by
    calc
      a.alphaValue (1 : Fin 2) = (z₁ : ℚ) := hz₁
      _ = (k₁ : ℚ) := by exact_mod_cast hk₁Int.symm
  have hk₀ : 0 < k₀ := by
    have hz₀Positive : 0 < z₀ := by
      rcases hz₀Odd with ⟨m, hm⟩
      omega
    exact_mod_cast (show 0 < (k₀ : Int) by
      simpa only [hk₀Int] using hz₀Positive)
  have hk₁ : 0 < k₁ := by
    have hz₁Positive : 0 < z₁ := by
      rcases hz₁Odd with ⟨m, hm⟩
      omega
    exact_mod_cast (show 0 < (k₁ : Int) by
      simpa only [hk₁Int] using hz₁Positive)
  have hsumNe : a.alphaValue (0 : Fin 2) +
        a.alphaValue (1 : Fin 2) ≠
      2 * (ramificationIndex K : ℚ) := by
    intro hsumEq
    apply hnotHalf
    apply hremark.alphaSum_eq_twoE_iff.mp
    simpa [BONG.GoodBONG.remark87PreviousAlpha,
      BONG.GoodBONG.remark87CurrentAlpha] using hsumEq
  have hsumLt : a.alphaValue (0 : Fin 2) +
        a.alphaValue (1 : Fin 2) <
      2 * (ramificationIndex K : ℚ) :=
    lt_of_le_of_ne (by
      simpa [BONG.GoodBONG.remark87PreviousAlpha,
        BONG.GoodBONG.remark87CurrentAlpha] using hremark.alphaSum_le_twoE)
      hsumNe
  have hkSumLt : k₀ + k₁ < 2 * ramificationIndex K := by
    exact_mod_cast (show (k₀ : ℚ) + (k₁ : ℚ) <
      2 * (ramificationIndex K : ℚ) by
        simpa only [← hfirstNat, ← hsecondNat] using hsumLt)
  have hkBudget : k₀ + (k₁ + 1) ≤ 2 * ramificationIndex K := by
    omega
  have hk₀Lt : k₀ < 2 * ramificationIndex K := by omega
  have hA₀DefectOrder :=
    firstAdjacentDefect_eq_secondAlpha_of_normalized_notHalfGap
      a houter hfirst hnotHalf
  have hA₁DefectOrder :=
    secondAdjacentDefect_eq_firstAlpha_of_normalized_notHalfGap
      a houter hlast hsecondNotHalf
  have hA₀DefectNat : BONG.GoodBONG.defectOrder (K := K)
      (a.adjacentProduct (0 : Fin 2)) =
        (((k₁ : Nat) : ℚ) : WithTop ℚ) := by
    rw [hA₀DefectOrder, hsecondNat]
  have hA₁DefectNat : BONG.GoodBONG.defectOrder (K := K)
      (a.adjacentProduct (1 : Fin 2)) =
        (((k₀ : Nat) : ℚ) : WithTop ℚ) := by
    rw [hA₁DefectOrder, hfirstNat]
  have hA₀Quadratic : quadraticDefect K
      (a.adjacentProduct (0 : Fin 2)) = (k₁ : ℕ∞) :=
    quadraticDefect_eq_natCast_of_defectOrder_eq_natCast
      (a.adjacentProduct (0 : Fin 2)) k₁ hA₀DefectNat
  have hA₁Quadratic : quadraticDefect K
      (a.adjacentProduct (1 : Fin 2)) = (k₀ : ℕ∞) :=
    quadraticDefect_eq_natCast_of_defectOrder_eq_natCast
      (a.adjacentProduct (1 : Fin 2)) k₀ hA₁DefectNat
  have hetaFirstQuadratic : quadraticDefect K
      (etaRaw * a.adjacentProduct (0 : Fin 2)) = (k₁ : ℕ∞) :=
    quadraticDefect_eq_natCast_of_defectOrder_eq_natCast
      (etaRaw * a.adjacentProduct (0 : Fin 2)) k₁ (by
        rw [hetaFirstProduct, hsecondNat])
  have hA₁Finite : quadraticDefect K
      (a.adjacentProduct (1 : Fin 2)) ≠ ⊤ := by
    rw [hA₁Quadratic]
    exact WithTop.coe_ne_top
  have hA₁Nonzero : quadraticDefect K
      (a.adjacentProduct (1 : Fin 2)) ≠ 0 := by
    rw [hA₁Quadratic]
    exact_mod_cast (ne_of_gt hk₀)
  have hA₁NotTwoE : quadraticDefect K
      (a.adjacentProduct (1 : Fin 2)) ≠
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    rw [hA₁Quadratic]
    exact_mod_cast (ne_of_lt hk₀Lt)
  have hetaA₁Sum : quadraticDefect K
        (etaRaw * a.adjacentProduct (0 : Fin 2)) +
      quadraticDefect K (a.adjacentProduct (1 : Fin 2)) ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    rw [hetaFirstQuadratic, hA₁Quadratic]
    exact_mod_cast (show k₁ + k₀ ≤ 2 * ramificationIndex K by omega)
  rcases exists_same_defect_product_hilbert_neg_one_of_largeResidue
      hres (etaRaw * a.adjacentProduct (0 : Fin 2))
        (a.adjacentProduct (1 : Fin 2)) hA₁Finite hA₁Nonzero
          hA₁NotTwoE hetaA₁Sum with
    ⟨w, hwDefect, hA₁wDefect, hwCombined⟩
  have hwEven : Even (ordUnit K w) := by
    rcases Int.even_or_odd (ordUnit K w) with heven | hodd
    · exact heven
    · have hwZero := quadraticDefect_eq_zero_of_odd_ordUnit w hodd
      have hk₀ENat : (k₀ : ℕ∞) ≠ 0 := by
        exact_mod_cast (ne_of_gt hk₀)
      apply (hk₀ENat ?_).elim
      rw [← hA₁Quadratic, ← hwDefect]
      exact hwZero
  rcases BONG.GoodBONG.exists_valuationUnit_eq_mul_square_of_even_order
      w hwEven with ⟨muRaw, s, hmuUnit, hmuFactor⟩
  let eta : valuationUnitSubgroup K := ⟨etaRaw, hetaUnit⟩
  let mu : valuationUnitSubgroup K := ⟨muRaw, hmuUnit⟩
  have hmuQuadratic : quadraticDefect K muRaw =
      quadraticDefect K (a.adjacentProduct (1 : Fin 2)) := by
    rw [hmuFactor, quadraticDefect_mul_square]
    exact hwDefect
  have hmuA₁Quadratic : quadraticDefect K
      (muRaw * a.adjacentProduct (1 : Fin 2)) =
        quadraticDefect K (a.adjacentProduct (1 : Fin 2)) := by
    rw [hmuFactor]
    rw [show (w * s ^ 2) * a.adjacentProduct (1 : Fin 2) =
      (a.adjacentProduct (1 : Fin 2) * w) * s ^ 2 by ac_rfl,
      quadraticDefect_mul_square]
    exact hA₁wDefect
  have hmuDefectOrder : BONG.GoodBONG.defectOrder (K := K) muRaw =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) :=
    (defectOrder_eq_of_quadraticDefect_eq muRaw
      (a.adjacentProduct (1 : Fin 2)) hmuQuadratic).trans hA₁DefectOrder
  have hmuDepth : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (mu : Kˣ) := by
    change (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) muRaw
    rw [hmuDefectOrder]
  have hmuLastProduct : BONG.GoodBONG.defectOrder (K := K)
        ((mu : Kˣ) * a.adjacentProduct (1 : Fin 2)) =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    simpa only [mu, Subgroup.coe_mk] using
      (defectOrder_eq_of_quadraticDefect_eq
        (muRaw * a.adjacentProduct (1 : Fin 2))
        (a.adjacentProduct (1 : Fin 2)) hmuA₁Quadratic).trans
          hA₁DefectOrder
  have hmuCombined : hilbertSymbol K
      ((eta : Kˣ) * a.adjacentProduct (0 : Fin 2)) (mu : Kˣ) = -1 := by
    change hilbertSymbol K
      (etaRaw * a.adjacentProduct (0 : Fin 2)) muRaw = -1
    rw [hmuFactor, hilbertSymbol_mul_square_right]
    exact hwCombined
  rcases Int.units_eq_one_or (hilbertSymbol K
      (a.adjacentProduct (0 : Fin 2)) (mu : Kˣ)) with
    hA₀mu | hA₀mu
  · let theta : valuationUnitSubgroup K := 1
    have hthetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) := by
      simp only [theta, One.one, Subgroup.coe_one]
      rw [BONG.GoodBONG.defectOrder_one]
      exact le_top
    have hthetaFirstProduct : BONG.GoodBONG.defectOrder (K := K)
          ((theta : Kˣ) * a.adjacentProduct (0 : Fin 2)) =
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
      simpa only [theta, One.one, Subgroup.coe_one, one_mul] using hA₀DefectOrder
    have hthetaLast : hilbertSymbol K (theta : Kˣ)
        (a.adjacentProduct (1 : Fin 2)) = 1 := by
      simpa only [theta, One.one, Subgroup.coe_one] using
        hilbertSymbol_one_left (K := K) (a.adjacentProduct (1 : Fin 2))
    have hbridge : hilbertSymbol K (theta : Kˣ) (mu : Kˣ) =
        hilbertSymbol K (a.adjacentProduct (0 : Fin 2)) (mu : Kˣ) := by
      rw [hA₀mu]
      simpa only [theta, One.one, Subgroup.coe_one] using
        hilbertSymbol_one_left (K := K) (mu : Kˣ)
    exact reachableLemma814_rankThree_negative_of_fourStepBridge
      a b horder conditions hlast houter hepsilonFirst eta theta mu
        (by simpa only [eta, Subgroup.coe_mk] using hetaDepth)
        (by simpa only [eta, Subgroup.coe_mk] using hetaFirstProduct)
        (by simpa only [eta, Subgroup.coe_mk] using hetaLast)
        (by simpa only [eta, Subgroup.coe_mk] using hetaEpsilon)
        hthetaDepth hthetaFirstProduct hthetaLast hmuDepth hmuLastProduct
          hmuCombined hbridge
  · have hmuQuadraticNat : quadraticDefect K (mu : Kˣ) = (k₀ : ℕ∞) := by
      simpa only [mu, Subgroup.coe_mk, hA₁Quadratic] using hmuQuadratic
    have hA₁muQuadraticNat : quadraticDefect K
        (a.adjacentProduct (1 : Fin 2) * (mu : Kˣ)) = (k₀ : ℕ∞) := by
      rw [mul_comm]
      simpa only [mu, Subgroup.coe_mk, hA₁Quadratic] using hmuA₁Quadratic
    have hmuSum : quadraticDefect K (mu : Kˣ) + (k₁ + 1 : ℕ∞) ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      rw [hmuQuadraticNat]
      exact_mod_cast hkBudget
    have hA₁muSum : quadraticDefect K
          (a.adjacentProduct (1 : Fin 2) * (mu : Kˣ)) +
        (k₁ + 1 : ℕ∞) ≤
          ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      rw [hA₁muQuadraticNat]
      exact_mod_cast hkBudget
    rcases exists_valuationUnit_depth_norm_hilbert_neg_one_of_sums_le
        (-(a.adjacentProduct (1 : Fin 2))) (mu : Kˣ) (k₁ + 1)
          (by omega) hmuSum (by simpa using hA₁muSum) with
      ⟨theta, hthetaDeep, hA₁Theta, hmuTheta⟩
    have hthetaDepth : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) := by
      rw [hsecondNat]
      exact (show (((k₁ : Nat) : ℚ) : WithTop ℚ) ≤
          ((((k₁ + 1 : Nat) : ℚ)) : WithTop ℚ) by exact_mod_cast (Nat.le_succ k₁)) |>.trans
        hthetaDeep
    have hA₀LtTheta : BONG.GoodBONG.defectOrder (K := K)
          (a.adjacentProduct (0 : Fin 2)) <
        BONG.GoodBONG.defectOrder (K := K) (theta : Kˣ) := by
      rw [hA₀DefectOrder, hsecondNat]
      exact (show (((k₁ : Nat) : ℚ) : WithTop ℚ) <
          ((((k₁ + 1 : Nat) : ℚ)) : WithTop ℚ) by exact_mod_cast (Nat.lt_succ_self k₁)) |>.trans_le
        hthetaDeep
    have hthetaFirstProduct : BONG.GoodBONG.defectOrder (K := K)
          ((theta : Kˣ) * a.adjacentProduct (0 : Fin 2)) =
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
      exact (BONG.GoodBONG.defectOrder_mul_eq_right_of_lt_left
        hA₀LtTheta).trans hA₀DefectOrder
    have hthetaLast : hilbertSymbol K (theta : Kˣ)
        (a.adjacentProduct (1 : Fin 2)) = 1 := by
      rw [hilbertSymbol_comm K]
      simpa using hA₁Theta
    have hbridge : hilbertSymbol K (theta : Kˣ) (mu : Kˣ) =
        hilbertSymbol K (a.adjacentProduct (0 : Fin 2)) (mu : Kˣ) := by
      rw [hilbertSymbol_comm K, hmuTheta, hA₀mu]
    exact reachableLemma814_rankThree_negative_of_fourStepBridge
      a b horder conditions hlast houter hepsilonFirst eta theta mu
        (by simpa only [eta, Subgroup.coe_mk] using hetaDepth)
        (by simpa only [eta, Subgroup.coe_mk] using hetaFirstProduct)
        (by simpa only [eta, Subgroup.coe_mk] using hetaLast)
        (by simpa only [eta, Subgroup.coe_mk] using hetaEpsilon)
        hthetaDepth hthetaFirstProduct hthetaLast hmuDepth hmuLastProduct
          hmuCombined hbridge

/-- Complete path-refined isotropic equal-outer ternary branch of Lemma 8.14.
The positive first Hilbert sign is the direct binary move.  With negative
sign, the half-gap case is the inverse-adjacent move; in the strict case the
paper's multiplier either has the favorable orientation or is resolved by
the four-step large-residue bridge. -/
theorem reachableLemma814_rankThree_isotropic_of_largeResidue
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hisotropic : a.Lemma814FirstThreeIsotropic) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases Int.units_eq_one_or
      (hilbertSymbol K (a.lemma814Epsilon b)
        (a.adjacentProduct (0 : Fin 2))) with hpositive | hnegative
  · exact reachableLemma814_binaryBranch
      a b horder conditions hfirst hpositive
  · by_cases hhalf : a.AttainsHalfGap (0 : Fin 2)
    · exact reachableLemma814_rankThree_negative_of_isotropic_halfGap
        a b horder conditions hlast houter hisotropic hhalf hnegative
    · rcases
        reachableLemma814_rankThree_negative_of_isotropic_notHalfGap_or_opposite
          hres a b horder conditions hlast houter hisotropic hhalf hnegative with
      hreached | ⟨eta, hetaUnit, hetaDepth, hetaProduct,
        hetaLast, hetaEpsilon⟩
      · exact hreached
      · exact
          reachableLemma814_rankThree_negative_of_isotropic_opposite_of_largeResidue
            hres a b horder conditions hfirst hlast houter hhalf hnegative
              eta hetaUnit hetaDepth hetaProduct hetaLast hetaEpsilon

/-- Complete path-refined rank-three Lemma 8.14 after both literal endpoint
alphas have been normalized.  Lemma 8.13 gives the exhaustive outer-order
split in the Hilbert-negative case; the preceding equal- and unequal-outer
connectivity theorems close every branch. -/
theorem reachableLemma814_rankThree_reduced_of_largeResidue
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hfirst : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ))
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases Int.units_eq_one_or
      (hilbertSymbol K (a.lemma814Epsilon b)
        (a.adjacentProduct (0 : Fin 2))) with
    hpositive | hnegative
  · exact reachableLemma814_binaryBranch
      a b horder conditions hfirst hpositive
  · rcases a.lemma814_outerCases_of_hilbert_neg_one
        b conditions hnegative with houter | houter
    · by_cases hisotropic : a.Lemma814FirstThreeIsotropic
      · exact reachableLemma814_rankThree_isotropic_of_largeResidue
          hres a b horder conditions hfirst hlast houter hisotropic
      · exact reachableLemma814_rankThree_anisotropic_of_largeResidue
          hres a b horder conditions hfirst hlast houter
            ((a.not_firstThreeIsotropic_iff_anisotropic).mp hisotropic)
            hnotExceptional
    · exact reachableLemma814_rankThree_unequalOuter_of_largeResidue
        hres a b horder conditions hfirst hlast houter

/-- Complete path-refined ternary Lemma 8.14.  The reachable left- and
right-endpoint Corollary 8.10 constructions first put both literal binary
edges in normal form.  Lemma 8.13 conditions and the exceptional predicate
are invariant under replacement by a good BONG of the same lattice, so the
reduced path theorem applies and its path concatenates with normalization. -/
theorem reachableLemma814_rankThree_of_largeResidue
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 3) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases reachableRankThreeDoubleNormalForm_of_largeResidue a hres with ⟨D⟩
  let c := D.transformed
  have horders : a.SameOrders c := a.order_invariant c
  have horder' : c.order (0 : Fin 3) = b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin 3)]
    exact horder
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classificationV)
    (classificationW := classificationW) c b horder conditions
  have hinvariant := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) c b
  have hnotExceptional' : ¬c.Beli2019Lemma814Exceptional b :=
    fun E => hnotExceptional (hinvariant.mpr E)
  rcases reachableLemma814_rankThree_reduced_of_largeResidue
      hres c b horder' hconditions D.firstBinaryAlpha_eq
        D.lastBinaryAlpha_eq hnotExceptional' with ⟨T⟩
  exact ⟨{
    transform := {
      transformed := T.transform.transformed
      firstValue_eq := T.transform.firstValue_eq
    }
    reachable := D.reachable.trans T.reachable
  }⟩

/-! ## The path-refined rank-three instance of Lemma 9.3 -/

/-- The matched-head package used in the ternary proof of Lemma 9.3,
augmented by the actual binary-transformation path from the original target
BONG. -/
structure ReachableLemma93MatchedPairRankThree
    (a c : BONG.GoodBONG q L 3) where
  pair : a.Beli2019Lemma93MatchedPairRankThree c
  reachable : Beli2009BinaryReachable (K := K)
    (fun i => a.valueUnit i) (fun i => pair.targetBONG.valueUnit i)

/-- In the same-lattice ternary situation, the path-refined Lemma 8.14
constructs the matched head required by Lemma 9.3.  Necessity for the
canonical unary prefix supplies the Lemma 8.13 hypotheses, while the fact
that the source BONG itself realizes that prefix rules out every exceptional
case. -/
theorem reachableLemma93MatchedPair_rankThree_of_largeResidue
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a c : BONG.GoodBONG q L 3)
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin 3))
    (selectedConditions : RepresentationConditions a c (Nat.le_refl 2)) :
    Nonempty (ReachableLemma93MatchedPairRankThree a c) := by
  have unaryConditions : a.Lemma813Conditions c.firstUnarySegment :=
    a.lemma813Conditions_firstUnarySegment_of_representation
      (sourceLaws := alpha) (targetLaws := alpha)
      (structuralV := structural)
      c hfirst (Lattice.represents_refl q L)
  have hnotExceptional :
      ¬a.Beli2019Lemma814Exceptional c.firstUnarySegment :=
    not_lemma814Exceptional_firstUnarySegment_of_sameLattice a c
  rcases reachableLemma814_rankThree_of_largeResidue
      hres a c.firstUnarySegment
        (hfirst.trans c.firstUnarySegment_order_zero.symm)
        unaryConditions hnotExceptional with ⟨T⟩
  have transformedConditions : RepresentationConditions
      T.transform.transformed c (Nat.le_refl 2) :=
    (a.representationConditions_changeBONG_iff
      (classificationV := classification)
      (classificationW := classification)
      T.transform.transformed c c (Nat.le_refl 2)).mp selectedConditions
  have hheadUnit : T.transform.transformed.valueUnit (0 : Fin 3) =
      c.valueUnit (0 : Fin 3) :=
    T.transform.firstValue_eq.trans c.firstUnarySegment_valueUnit_zero
  have hhead : T.transform.transformed.value 0 = c.value 0 := by
    simpa only [BONG.GoodBONG.coe_valueUnit] using congrArg Units.val hheadUnit
  have hfirst' : T.transform.transformed.order (0 : Fin 3) =
      c.order (0 : Fin 3) := by
    unfold BONG.GoodBONG.order
    rw [T.transform.transformed.toBONG.order_eq_ordUnit,
      c.toBONG.order_eq_ordUnit]
    simpa only [BONG.GoodBONG.valueUnit] using congrArg (ordUnit K) hheadUnit
  exact ⟨{
    pair := {
      targetBONG := T.transform.transformed
      selectedConditions := transformedConditions
      headValue_eq := hhead
      secondOrder_le :=
        T.transform.transformed.secondOrder_le_of_firstOrder_eq c
          transformedConditions.orderCondition hfirst'
    }
    reachable := T.reachable
  }⟩

/-- The full ternary recursive input of Lemma 9.3 together with paths from
the two original BONGs to the selected target and source BONGs. -/
structure ReachableLemma93InputRankThree
    (a b : BONG.GoodBONG q L 3) where
  targetBONG : BONG.GoodBONG q L 3
  sourceBONG : BONG.GoodBONG q L 3
  selectedConditions :
    RepresentationConditions targetBONG sourceBONG (Nat.le_refl 2)
  headValue_eq : targetBONG.value 0 = sourceBONG.value 0
  secondOrder_le :
    targetBONG.order (1 : Fin 3) ≤ sourceBONG.order (1 : Fin 3)
  essentialAlpha_eq : ∀ i : RepresentationIndex 2 2,
    (targetBONG.tail.IsCurrentEssential sourceBONG.tail i ∨
      targetBONG.tail.IsNextEssential sourceBONG.tail i) →
    targetBONG.tail.representationAlpha sourceBONG.tail i =
      targetBONG.representationAlpha sourceBONG i.tailShift
  targetReachable : Beli2009BinaryReachable (K := K)
    (fun i => a.valueUnit i) (fun i => targetBONG.valueUnit i)
  sourceReachable : Beli2009BinaryReachable (K := K)
    (fun i => b.valueUnit i) (fun i => sourceBONG.valueUnit i)

/-- Forget the path fields and recover the literal recursive input used by
the paper-facing statement of Lemma 9.3. -/
noncomputable def ReachableLemma93InputRankThree.toLemma93Input
    {a b : BONG.GoodBONG q L 3}
    (D : ReachableLemma93InputRankThree a b)
    (ambient : q.Represents q)
    (conditions : RepresentationConditions a b (Nat.le_refl 2)) :
    Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl 2)
        ambient conditions) where
  tailIndex := 1
  targetIndex_eq := rfl
  sourceIndex_eq := rfl
  targetBONG := D.targetBONG
  sourceBONG := D.sourceBONG
  selectedConditions := D.selectedConditions
  headValue_eq := D.headValue_eq
  secondOrder_le := D.secondOrder_le
  essentialAlpha_eq := D.essentialAlpha_eq

/-- Path-refined rank-three Lemma 9.3 in the same-lattice case.  The proof
retains the paper's three numerical alternatives.  In the third branch the
source-head normalization is the reachable form of Lemma 8.8; all target
head selections use the complete path-refined ternary Lemma 8.14. -/
theorem reachableLemma93Input_rankThree_of_largeResidue
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a b : BONG.GoodBONG q L 3)
    (hfirst : a.order (0 : Fin 3) = b.order (0 : Fin 3))
    (ambient : q.Represents q)
    (conditions : RepresentationConditions a b (Nat.le_refl 2)) :
    Nonempty (ReachableLemma93InputRankThree a b) := by
  let d := a.truncatedPrefixDefect b (-1) 3 1
  let beta : WithTop ℚ := (b.alphaValue (0 : Fin 2) : WithTop ℚ)
  let threshold : WithTop ℚ :=
    ((((b.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) / 2 +
      (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
  have hdBeta : d ≤ beta := by
    have hcap := a.truncatedPrefixDefect_le_rightCap b (-1) 3 1
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    have hzero : (⟨1 - 1, by omega⟩ : Fin 2) = (0 : Fin 2) := by
      apply Fin.ext
      rfl
    rw [hzero] at hcap
    exact hcap
  by_cases hstrict : d < beta
  · rcases reachableLemma93MatchedPair_rankThree_of_largeResidue
        hres a b hfirst conditions with ⟨P⟩
    have hdefectInvariant := a.truncatedPrefixDefect_invariant
      (classificationV := classification) (classificationW := classification)
      (prefixChangeV := prefixChange) (prefixChangeW := prefixChange)
      P.pair.targetBONG b b (-1) 3 1
    have hstrictSelected :
        P.pair.targetBONG.truncatedPrefixDefect b (-1) 3 1 <
          (b.alphaValue (0 : Fin 2) : WithTop ℚ) := by
      rw [← hdefectInvariant]
      exact hstrict
    have hdefect :=
      P.pair.targetBONG.firstThirdDefect_eq_tail_of_lt_betaOne_rankThree
        b P.pair.headValue_eq hstrictSelected
    have halpha :=
      P.pair.targetBONG.essentialAlpha_eq_rankThree_of_firstThirdDefect_eq_tail
        b P.pair.headValue_eq hdefect
    exact ⟨{
      targetBONG := P.pair.targetBONG
      sourceBONG := b
      selectedConditions := P.pair.selectedConditions
      headValue_eq := P.pair.headValue_eq
      secondOrder_le := P.pair.secondOrder_le
      essentialAlpha_eq := halpha
      targetReachable := P.reachable
      sourceReachable := beli2009BinaryReachable_refl _
    }⟩
  · have hdbeta : d = beta :=
      le_antisymm hdBeta (le_of_not_gt hstrict)
    by_cases hlarge : threshold ≤ d
    · rcases reachableLemma93MatchedPair_rankThree_of_largeResidue
          hres a b hfirst conditions with ⟨P⟩
      have htargetOrders : a.SameOrders P.pair.targetBONG :=
        a.order_invariant P.pair.targetBONG
      have hfirstSelected : P.pair.targetBONG.order (0 : Fin 3) =
          b.order (0 : Fin 3) :=
        (htargetOrders (0 : Fin 3)).symm.trans hfirst
      have hdefectInvariant := a.truncatedPrefixDefect_invariant
        (classificationV := classification)
        (classificationW := classification)
        (prefixChangeV := prefixChange) (prefixChangeW := prefixChange)
        P.pair.targetBONG b b (-1) 3 1
      have hlargeSelected :
          ((((b.order (1 : Fin 3) -
              P.pair.targetBONG.order (2 : Fin 3) : Int) : ℚ) / 2 +
            (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
          P.pair.targetBONG.truncatedPrefixDefect b (-1) 3 1 := by
        rw [← htargetOrders (2 : Fin 3), ← hdefectInvariant]
        exact hlarge
      have halpha :=
        P.pair.targetBONG.essentialAlpha_eq_rankThree_of_largeDefect
          b P.pair.headValue_eq hfirstSelected hlargeSelected
      exact ⟨{
        targetBONG := P.pair.targetBONG
        sourceBONG := b
        selectedConditions := P.pair.selectedConditions
        headValue_eq := P.pair.headValue_eq
        secondOrder_le := P.pair.secondOrder_le
        essentialAlpha_eq := halpha
        targetReachable := P.reachable
        sourceReachable := beli2009BinaryReachable_refl _
      }⟩
    · have hcase : a.Beli2019Lemma93CaseTwoConditionRankThree b :=
        ⟨hdbeta, lt_of_not_ge hlarge⟩
      rcases reachable_caseTwoSourceHeadNormalization_rankThree_of_largeResidue
          a b hfirst hcase hres with ⟨H⟩
      have hsourceOrders : b.SameOrders H.data.transformed :=
        b.order_invariant H.data.transformed
      have hsourceAlphas : b.SameAlphas H.data.transformed :=
        b.alpha_invariant H.data.transformed
      have hfirstSelected : a.order (0 : Fin 3) =
          H.data.transformed.order (0 : Fin 3) :=
        hfirst.trans (hsourceOrders (0 : Fin 3))
      have selectedConditions :
          RepresentationConditions a H.data.transformed (Nat.le_refl 2) :=
        (a.representationConditions_changeBONG_iff
          (classificationV := classification)
          (classificationW := classification)
          a b H.data.transformed (Nat.le_refl 2)).mp conditions
      rcases reachableLemma93MatchedPair_rankThree_of_largeResidue
          hres a H.data.transformed hfirstSelected selectedConditions with ⟨P⟩
      have hrawTarget := BONG.GoodBONG.firstThirdRawDefect_changeTarget_rankThree
        a P.pair.targetBONG H.data.transformed
      have hrawSelected : BONG.GoodBONG.defectOrder (K := K)
          ((-1) * P.pair.targetBONG.prefixProduct 3 *
            H.data.transformed.prefixProduct 1) =
          (H.data.transformed.alphaValue (0 : Fin 2) : WithTop ℚ) :=
        (hrawTarget.trans H.data.firstThirdRawDefect_eq).trans
          (congrArg (fun x : ℚ => (x : WithTop ℚ))
            (hsourceAlphas (0 : Fin 2)))
      have hdefect :=
        P.pair.targetBONG.firstThirdDefect_eq_tail_of_raw_eq_betaOne_rankThree
          H.data.transformed P.pair.headValue_eq hrawSelected
      have halpha :=
        P.pair.targetBONG.essentialAlpha_eq_rankThree_of_firstThirdDefect_eq_tail
          H.data.transformed P.pair.headValue_eq hdefect
      exact ⟨{
        targetBONG := P.pair.targetBONG
        sourceBONG := H.data.transformed
        selectedConditions := P.pair.selectedConditions
        headValue_eq := P.pair.headValue_eq
        secondOrder_le := P.pair.secondOrder_le
        essentialAlpha_eq := halpha
        targetReachable := P.reachable
        sourceReachable := H.reachable
      }⟩

/-- The two projected binary lattices selected by the path-refined ternary
Lemma 9.3 are isometric.  Theorem 2.1 gives the integral representation;
equal tail ranks and the projection-volume identity upgrade it to an
isometry. -/
theorem reachableLemma93InputRankThree_tail_isIsometric
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    {a b : BONG.GoodBONG q L 3}
    (D : ReachableLemma93InputRankThree a b) :
    Lattice.IsIsometric
      (q.orthogonalSpace D.sourceBONG.toBONG.head
        D.sourceBONG.toBONG.head_isAnisotropic)
      (q.orthogonalSpace D.targetBONG.toBONG.head
        D.targetBONG.toBONG.head_isAnisotropic)
      (L.projectedLattice q D.sourceBONG.toBONG.head
        D.sourceBONG.toBONG.head_isAnisotropic)
      (L.projectedLattice q D.targetBONG.toBONG.head
        D.targetBONG.toBONG.head_isAnisotropic) := by
  have htailConditions : RepresentationConditions
      D.targetBONG.tail D.sourceBONG.tail (Nat.le_refl 1) :=
    D.targetBONG.representationConditions_tail
      (targetLaws := alpha) (sourceLaws := alpha)
      D.sourceBONG D.selectedConditions D.headValue_eq D.secondOrder_le
        D.essentialAlpha_eq
  have hheadQuadratic :
      q.quadratic D.targetBONG.toBONG.head =
        q.quadratic D.sourceBONG.toBONG.head := by
    rw [← D.targetBONG.toBONG.value_zero_eq_quadratic_head,
      ← D.sourceBONG.toBONG.value_zero_eq_quadratic_head]
    exact D.headValue_eq
  have horthogonalAmbient := orthogonalAmbient_of_equalValue_sameSpace
    D.targetBONG.toBONG.head D.sourceBONG.toBONG.head
    D.targetBONG.toBONG.head_isAnisotropic
    D.sourceBONG.toBONG.head_isAnisotropic hheadQuadratic
  letI : FiniteDimensional K
      (q.vectorOrthogonal D.sourceBONG.toBONG.head) :=
    D.sourceBONG.tail.toBONG.basis.finiteDimensional_of_finite
  letI : FiniteDimensional K
      (q.vectorOrthogonal D.targetBONG.toBONG.head) :=
    D.targetBONG.tail.toBONG.basis.finiteDimensional_of_finite
  have hrep : Lattice.Represents
      (q.orthogonalSpace D.targetBONG.toBONG.head
        D.targetBONG.toBONG.head_isAnisotropic)
      (q.orthogonalSpace D.sourceBONG.toBONG.head
        D.sourceBONG.toBONG.head_isAnisotropic)
      (L.projectedLattice q D.targetBONG.toBONG.head
        D.targetBONG.toBONG.head_isAnisotropic)
      (L.projectedLattice q D.sourceBONG.toBONG.head
        D.sourceBONG.toBONG.head_isAnisotropic) :=
    (beli2019Theorem21 (Nat.le_refl 1) horthogonalAmbient
      D.targetBONG.tail D.sourceBONG.tail).2 htailConditions
  have hfinrank : Module.finrank K
        (q.vectorOrthogonal D.sourceBONG.toBONG.head) =
      Module.finrank K
        (q.vectorOrthogonal D.targetBONG.toBONG.head) := by
    rw [← D.sourceBONG.tail.toBONG.length_eq_finrank,
      ← D.targetBONG.tail.toBONG.length_eq_finrank]
  have hsourceVolume := Lattice.volumeOrder_eq_ordUnit_add_projection
    q L D.sourceBONG.toBONG.head
      D.sourceBONG.toBONG.head_isNormGenerator
      D.sourceBONG.toBONG.head_isAnisotropic
  have htargetVolume := Lattice.volumeOrder_eq_ordUnit_add_projection
    q L D.targetBONG.toBONG.head
      D.targetBONG.toBONG.head_isNormGenerator
      D.targetBONG.toBONG.head_isAnisotropic
  have hheadOrder :
      ordUnit K (Units.mk0 (q.quadratic D.sourceBONG.toBONG.head)
        D.sourceBONG.toBONG.head_isAnisotropic) =
      ordUnit K (Units.mk0 (q.quadratic D.targetBONG.toBONG.head)
        D.targetBONG.toBONG.head_isAnisotropic) := by
    apply congrArg (ordUnit K)
    apply Units.ext
    exact hheadQuadratic.symm
  have hvolume :
      Lattice.volumeOrder
          (q.orthogonalSpace D.sourceBONG.toBONG.head
            D.sourceBONG.toBONG.head_isAnisotropic)
          (L.projectedLattice q D.sourceBONG.toBONG.head
            D.sourceBONG.toBONG.head_isAnisotropic) =
        Lattice.volumeOrder
          (q.orthogonalSpace D.targetBONG.toBONG.head
            D.targetBONG.toBONG.head_isAnisotropic)
          (L.projectedLattice q D.targetBONG.toBONG.head
            D.targetBONG.toBONG.head_isAnisotropic) := by
    omega
  exact Lattice.Represents.isIsometric_of_finrank_eq_of_volumeOrder_eq
    hrep hfinrank hvolume

/-- Every two ternary good BONGs of the same lattice are connected by the
binary transformations from Beli's final remark when the residue field has
more than two elements.  This is the complete induction base needed for
the arbitrary-rank Section 9 argument. -/
theorem reachable_rankThree_of_largeResidue
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a b : BONG.GoodBONG q L 3) :
    Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => b.valueUnit i) := by
  let ambient : q.Represents q := QuadraticSpace.represents_refl q
  have conditions : RepresentationConditions a b (Nat.le_refl 2) :=
    beli2019_necessity (sourceLaws := alpha) (targetLaws := alpha)
      a b (Nat.le_refl 2) (Lattice.represents_refl q L)
  have horders : a.SameOrders b := a.order_invariant b
  rcases reachableLemma93Input_rankThree_of_largeResidue
      hres a b (horders (0 : Fin 3)) ambient conditions with ⟨D⟩
  rcases reachableLemma93InputRankThree_tail_isIsometric D with ⟨f⟩
  have htail := reachable_rankTwo D.targetBONG.tail
    (D.sourceBONG.tail.mapLatticeIsometry f)
  have hhead : D.targetBONG.valueUnit (0 : Fin 3) =
      D.sourceBONG.valueUnit (0 : Fin 3) := by
    apply Units.ext
    exact D.headValue_eq
  have hselected := reachable_of_headValue_eq_of_mappedTail_reachable_rankThree
    D.targetBONG D.sourceBONG hhead f htail
  exact D.targetReachable.trans
    (hselected.trans (Beli2009BinaryReachable.symm D.sourceReachable))

/-! ## Lifting the ternary path into an initial segment -/

/-- Reindex a binary-transformation path along an equality of finite
lengths. -/
theorem Beli2009BinaryReachable.castLength
    {m n : Nat} (h : m = n) {x y : Fin (m + 1) → Kˣ}
    (R : Beli2009BinaryReachable (K := K) x y) :
    Beli2009BinaryReachable (K := K)
      (fun i : Fin (n + 1) => x (Fin.cast (congrArg (· + 1) h).symm i))
      (fun i : Fin (n + 1) => y (Fin.cast (congrArg (· + 1) h).symm i)) := by
  subst n
  simpa using R

/-- A reachable prescribed-first-value change on an initial ternary segment
lifts to the ambient good BONG by Beli (2003), Lemma 4.9(ii). -/
theorem reachablePrescribedFirstValueTransform_of_firstThreeSegment
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [BeliLemma49Laws.{u, v} K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 3))
    (b : BONG.GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (T : ReachablePrescribedFirstValueTransform
      (segment.toGoodBONG a.good) b) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases a.toBONG.beliLemma49_ii a.good segment
      T.transform.transformed.toBONG T.transform.transformed.good with
    ⟨replacement⟩
  let transformed : BONG.GoodBONG q L (N + 3) :=
    ⟨replacement.bong, replacement.good⟩
  have hinside := replacement.inside_eq (0 : Fin 3)
  have hfirst : transformed.valueUnit (0 : Fin (N + 3)) =
      T.transform.transformed.valueUnit (0 : Fin 3) := by
    apply Units.ext
    change replacement.bong.value 0 = T.transform.transformed.toBONG.value 0
    rw [← replacement.bong.quadratic_ambientVector,
      ← T.transform.transformed.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector 0) =
      q.quadratic (T.transform.transformed.toBONG.ambientVector 0 : V)
    exact congrArg q.quadratic hinside
  have hreachCast := reachable_of_prefixSegmentReplacement
    (n := N + 3) (M := 2) (S := N) (by omega)
    a segment T.transform.transformed replacement T.reachable
  have hreindexed := Beli2009BinaryReachable.castLength
    (show 2 + N = N + 2 by omega) hreachCast
  have hreach : Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => transformed.valueUnit i) := by
    simpa [transformed] using hreindexed
  exact ⟨{
    transform := {
      transformed := transformed
      firstValue_eq := hfirst.trans T.transform.firstValue_eq
    }
    reachable := hreach
  }⟩

/-- A reachable prescribed-first-value change on an initial quaternary
segment lifts to the ambient good BONG by Beli (2003), Lemma 4.9(ii). -/
theorem reachablePrescribedFirstValueTransform_of_firstFourSegment
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [BeliLemma49Laws.{u, v} K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 4))
    (b : BONG.GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 4 (by omega))
    (T : ReachablePrescribedFirstValueTransform
      (segment.toGoodBONG a.good) b) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases a.toBONG.beliLemma49_ii a.good segment
      T.transform.transformed.toBONG T.transform.transformed.good with
    ⟨replacement⟩
  let transformed : BONG.GoodBONG q L (N + 4) :=
    ⟨replacement.bong, replacement.good⟩
  have hinside := replacement.inside_eq (0 : Fin 4)
  have hfirst : transformed.valueUnit (0 : Fin (N + 4)) =
      T.transform.transformed.valueUnit (0 : Fin 4) := by
    apply Units.ext
    change replacement.bong.value 0 = T.transform.transformed.toBONG.value 0
    rw [← replacement.bong.quadratic_ambientVector,
      ← T.transform.transformed.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector 0) =
      q.quadratic (T.transform.transformed.toBONG.ambientVector 0 : V)
    exact congrArg q.quadratic hinside
  have hreachCast := reachable_of_prefixSegmentReplacement
    (n := N + 4) (M := 3) (S := N) (by omega)
    a segment T.transform.transformed replacement T.reachable
  have hreindexed := Beli2009BinaryReachable.castLength
    (show 3 + N = N + 3 by omega) hreachCast
  have hreach : Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => transformed.valueUnit i) := by
    simpa [transformed] using hreindexed
  exact ⟨{
    transform := {
      transformed := transformed
      firstValue_eq := hfirst.trans T.transform.firstValue_eq
    }
    reachable := hreach
  }⟩

/-- Path-refined form of the common rank-reduction step in Lemma 8.14:
once an initial ternary segment satisfies the local hypotheses, solve it by
the complete ternary path theorem and reinsert it into the ambient BONG. -/
theorem reachableLemma814_of_safeFirstThreeSegment_of_largeResidue
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 3))
    (b : BONG.GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (horder : (segment.toGoodBONG a.good).order (0 : Fin 3) =
      b.order (0 : Fin 1))
    (conditions : (segment.toGoodBONG a.good).Lemma813Conditions b)
    (hnotExceptional :
      ¬(segment.toGoodBONG a.good).Beli2019Lemma814Exceptional b)
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases reachableLemma814_rankThree_of_largeResidue hres
      (segment.toGoodBONG a.good) b horder conditions hnotExceptional with ⟨T⟩
  exact reachablePrescribedFirstValueTransform_of_firstThreeSegment
    a b segment T

/-- Ambient-order variant of the preceding rank-reduction step. -/
theorem reachableLemma814_of_safeFirstThreeSegment_of_ambientOrder
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 3))
    (b : BONG.GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (horder : a.order (0 : Fin (N + 3)) = b.order (0 : Fin 1))
    (conditions : (segment.toGoodBONG a.good).Lemma813Conditions b)
    (hnotExceptional :
      ¬(segment.toGoodBONG a.good).Beli2019Lemma814Exceptional b)
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  have hsegmentOrder : (segment.toGoodBONG a.good).order (0 : Fin 3) =
      a.order (0 : Fin (N + 3)) := by
    change segment.bong.order 0 = a.toBONG.order 0
    simpa [BONG.SegmentWitness.sourceIndex] using segment.order_eq (0 : Fin 3)
  exact reachableLemma814_of_safeFirstThreeSegment_of_largeResidue
    a b segment (hsegmentOrder.trans horder) conditions hnotExceptional hres

/-! ## Path-refined quaternary branches of Lemma 8.14 -/

/-- A final-pair Lemma 8.8 scaling together with the binary path which
produces the ambient rank-four BONG. -/
structure ReachableLemma814LastPairScalingData
    (a : BONG.GoodBONG q L 4) where
  data : a.Beli2019Lemma814LastPairScalingData
  reachable : Beli2009BinaryReachable (K := K)
    (fun i => a.valueUnit i) (fun i => data.transformed.valueUnit i)

/-- Reinsert a reachable final binary transformation and lift its path
through Lemma 4.9(ii). -/
theorem reachableLastPairScalingData_of_transform
    [GoodBONGClassificationLaws.{u, v, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 2 2 (by omega))
    (T : ReachableFirstValueTransform (segment.toGoodBONG a.good))
    (halpha : (segment.toGoodBONG a.good).alphaValue (0 : Fin 1) =
      a.alphaValue (2 : Fin 3)) :
    Nonempty (ReachableLemma814LastPairScalingData a) := by
  let s := segment.toGoodBONG a.good
  rcases a.toBONG.beliLemma49_ii a.good segment
      T.transform.transformed.toBONG T.transform.transformed.good with
    ⟨replacement⟩
  let transformed : BONG.GoodBONG q L 4 :=
    ⟨replacement.bong, replacement.good⟩
  have beforeValue_eq (i : Fin 4) (hi : i.1 < 2) :
      transformed.valueUnit i = a.valueUnit i := by
    apply Units.ext
    change replacement.bong.value i = a.toBONG.value i
    rw [← replacement.bong.quadratic_ambientVector,
      ← a.toBONG.quadratic_ambientVector]
    exact congrArg q.quadratic (replacement.before_eq i hi)
  have hthirdLocal : transformed.valueUnit (2 : Fin 4) =
      T.transform.transformed.valueUnit (0 : Fin 2) := by
    apply Units.ext
    change replacement.bong.value 2 =
      T.transform.transformed.toBONG.value 0
    rw [← replacement.bong.quadratic_ambientVector,
      ← T.transform.transformed.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector 2) =
      q.quadratic (T.transform.transformed.toBONG.ambientVector 0 : V)
    have hinside := replacement.inside_eq (0 : Fin 2)
    simpa using congrArg q.quadratic hinside
  have hsegmentFirst : s.valueUnit (0 : Fin 2) =
      a.valueUnit (2 : Fin 4) := by
    change segment.bong.valueUnit 0 = a.toBONG.valueUnit 2
    simp [BONG.SegmentWitness.sourceIndex]
  let D : a.Beli2019Lemma814LastPairScalingData := {
    epsilon := T.transform.epsilon
    epsilon_isValuationUnit := T.transform.epsilon_isValuationUnit
    epsilon_defect := T.transform.epsilon_defect.trans
      (congrArg (fun x : ℚ => (x : WithTop ℚ)) halpha)
    transformed := transformed
    firstValue_eq := beforeValue_eq (0 : Fin 4) (by omega)
    secondValue_eq := beforeValue_eq (1 : Fin 4) (by omega)
    thirdValue_eq := hthirdLocal.trans <| T.transform.firstValue_eq.trans <|
      congrArg (T.transform.epsilon * ·) hsegmentFirst
  }
  have hglobal := reachable_of_suffixSegmentReplacement
    (n := 4) (P := 2) (M := 1) rfl a segment
      T.transform.transformed replacement T.reachable
  have hreach : Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => D.transformed.valueUnit i) := by
    simpa [D, transformed] using hglobal
  exact ⟨⟨D, hreach⟩⟩

/-- Reachable version of the successful last-pair scaling in the strict
alpha-sum branch. -/
theorem reachable_rankFour_lastPairScaling_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ))
    (hstrict : a.alphaValue (2 : Fin 3) <
      a.halfGapValue (2 : Fin 3))
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableLemma814LastPairScalingData a) := by
  let segment := a.toBONG.segmentWitness 2 2 (by omega)
  let s := segment.toGoodBONG a.good
  have halpha : s.alphaValue (0 : Fin 1) =
      a.alphaValue (2 : Fin 3) :=
    BONG.GoodBONG.rankFour_lastPairAlpha_eq_of_lastBinaryAlpha
      a segment hlast
  have hhalf : s.halfGapValue (0 : Fin 1) =
      a.halfGapValue (2 : Fin 3) :=
    BONG.GoodBONG.rankFour_lastPairHalfGap_eq a segment
  have hlocalStrict : s.alphaValue (0 : Fin 1) <
      s.halfGapValue (0 : Fin 1) := by
    rw [halpha, hhalf]
    exact hstrict
  have hnotExceptional : ¬s.Beli2019Lemma88Exceptional := by
    rintro ⟨hattains, _⟩
    exact (ne_of_lt hlocalStrict) hattains
  rcases reachableLemma88_sufficiency_of_largeResidue s
      hnotExceptional hres with ⟨T⟩
  exact reachableLastPairScalingData_of_transform a segment T halpha

/-- In the strict upper alpha-sum branch, the production proof already
reduces to the initial ternary segment.  Replacing its terminal invocation
of Lemma 8.14 by the reachable ternary theorem retains the complete binary
path. -/
theorem reachableLemma814_rankFour_alphaSum_gt_of_largeResidue
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hsum : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  let segment := a.toBONG.segmentWitness 0 3 (by omega)
  have hnotLocal :=
    BONG.GoodBONG.rankFour_notExceptional_firstThree_of_alphaSum_gt
      a b segment houter hbinary hsum hnotExceptional
  have hconditions := BONG.GoodBONG.rankFour_firstThreeConditions
    a b segment houter hbinary conditions hnotLocal
  exact reachableLemma814_of_safeFirstThreeSegment_of_ambientOrder
    a b segment horder hconditions hnotLocal hres

/-- Reachable quaternary lower-sum branch when the final literal binary
alpha has already been normalized to the third global alpha.  This is the
part of Beli's case (b) which also applies when the two alternating order
pairs are equal; no strict `R₂ < R₄` hypothesis is needed once the literal
last alpha equality is supplied. -/
theorem reachableLemma814_rankFour_alphaSum_lt_of_first_ge_of_lastBinaryAlpha
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) <
      2 * (ramificationIndex K : ℚ))
    (hfirstGe : a.alphaValue (2 : Fin 3) ≤
      a.alphaValue (0 : Fin 3)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  let oldSegment := a.toBONG.segmentWitness 0 3 (by omega)
  by_cases hlocal :
      ((oldSegment.toGoodBONG a.good).alphaValue (1 : Fin 2) : WithTop ℚ) +
          (oldSegment.toGoodBONG a.good).lemma814FirstThirdCappedDefect b <
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ)
  · have hnotLocal := BONG.GoodBONG.rankThree_notExceptional_of_defectSum_lt
      (oldSegment.toGoodBONG a.good) b hlocal
    have hlocalConditions := BONG.GoodBONG.rankFour_firstThreeConditions
      a b oldSegment houter hbinary conditions hnotLocal
    exact reachableLemma814_of_safeFirstThreeSegment_of_ambientOrder
      a b oldSegment horder hlocalConditions hnotLocal hres
  · have hlarge :
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) ≤
          (oldSegment.toGoodBONG a.good).alphaValue (1 : Fin 2) +
            (oldSegment.toGoodBONG a.good).lemma814FirstThirdCappedDefect b :=
      le_of_not_gt hlocal
    have hrawLocal :=
      BONG.GoodBONG.rankFour_thirdAlpha_lt_firstThreeDefect_of_alphaSum_lt
        a b oldSegment houter hbinary hsum hlarge
    have hraw : (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
        BONG.GoodBONG.defectOrder (K := K)
          ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
      rw [← BONG.GoodBONG.rankFour_firstThreeDefect_eq_raw
        a b oldSegment]
      exact hrawLocal
    have hstrict :=
      BONG.GoodBONG.rankFour_thirdAlpha_lt_halfGap_of_alphaSum_lt a hsum
    rcases reachable_rankFour_lastPairScaling_of_largeResidue
        a hlast hstrict hres with ⟨RD⟩
    let D := RD.data
    let changed := D.transformed
    let newSegment := changed.toBONG.segmentWitness 0 3 (by omega)
    have hnewDefect :
        (newSegment.toGoodBONG changed.good).lemma814FirstThirdCappedDefect b =
          (a.alphaValue (2 : Fin 3) : WithTop ℚ) :=
      D.firstThreeDefect_eq b newSegment hraw
    have horders := a.order_invariant changed
    have halphas := a.alpha_invariant changed
    have hchangedOrder : changed.order (0 : Fin 4) =
        b.order (0 : Fin 1) := by
      rw [← horders (0 : Fin 4)]
      exact horder
    have hchangedOuter : changed.order (0 : Fin 4) =
        changed.order (2 : Fin 4) := by
      rw [← horders (0 : Fin 4), ← horders (2 : Fin 4)]
      exact houter
    have hchangedBinary : changed.firstBinaryAlpha =
        (changed.alphaValue (0 : Fin 3) : WithTop ℚ) := by
      calc
        changed.firstBinaryAlpha = a.firstBinaryAlpha := D.firstBinaryAlpha_eq
        _ = (a.alphaValue (0 : Fin 3) : WithTop ℚ) := hbinary
        _ = (changed.alphaValue (0 : Fin 3) : WithTop ℚ) :=
          congrArg (fun x : ℚ => (x : WithTop ℚ))
            (halphas (0 : Fin 3))
    have hchangedConditions := a.lemma813Conditions_changeTargetBONG
      (classificationV := classification)
      (classificationW := classification) changed b horder conditions
    have hprefix := BONG.GoodBONG.rankFour_prefixAlphas_eq_of_firstBinaryAlpha
      changed newSegment hchangedOuter hchangedBinary
    have hnewLocal :
        ((newSegment.toGoodBONG changed.good).alphaValue (1 : Fin 2) :
            WithTop ℚ) +
            (newSegment.toGoodBONG changed.good).lemma814FirstThirdCappedDefect b <
          (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) := by
      rw [hprefix.2, hnewDefect, ← halphas (1 : Fin 3)]
      exact_mod_cast hsum
    have hnotNew := BONG.GoodBONG.rankThree_notExceptional_of_defectSum_lt
      (newSegment.toGoodBONG changed.good) b hnewLocal
    have hnewConditions :=
      BONG.GoodBONG.rankFour_firstThreeConditions_of_prefixAlphas
        changed b newSegment hchangedOuter hprefix hchangedConditions hnotNew
    rcases reachableLemma814_of_safeFirstThreeSegment_of_ambientOrder
        changed b newSegment hchangedOrder hnewConditions hnotNew hres with ⟨T⟩
    exact ⟨{
      transform := {
        transformed := T.transform.transformed
        firstValue_eq := T.transform.firstValue_eq
      }
      reachable := RD.reachable.trans T.reachable
    }⟩

/-- Reachable quaternary lower-sum branch with `alpha₁ ≥ alpha₃` and
strictly increasing second/fourth orders.  Corollary 8.10 is first realized by
an explicit binary path; the strict order comparison then identifies the
literal last binary alpha, so the preceding terminal theorem applies. -/
theorem reachableLemma814_rankFour_alphaSum_lt_of_first_ge
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) <
      2 * (ramificationIndex K : ℚ))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hfirstGe : a.alphaValue (2 : Fin 3) ≤
      a.alphaValue (0 : Fin 3)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases reachableLemma814FirstNormalForm_of_largeResidue
      a b horder conditions hnotExceptional hres with ⟨F⟩
  let c := F.data.transformed
  have horders : a.SameOrders c := a.order_invariant c
  have halphas : a.SameAlphas c := a.alpha_invariant c
  have houter' : c.order (0 : Fin 4) = c.order (2 : Fin 4) := by
    rw [← horders (0 : Fin 4), ← horders (2 : Fin 4)]
    exact houter
  have hsum' : c.alphaValue (1 : Fin 3) + c.alphaValue (2 : Fin 3) <
      2 * (ramificationIndex K : ℚ) := by
    rw [← halphas (1 : Fin 3), ← halphas (2 : Fin 3)]
    exact hsum
  have hsecondFourth' : c.order (1 : Fin 4) < c.order (3 : Fin 4) := by
    rw [← horders (1 : Fin 4), ← horders (3 : Fin 4)]
    exact hsecondFourth
  have hfirstGe' : c.alphaValue (2 : Fin 3) ≤
      c.alphaValue (0 : Fin 3) := by
    rw [← halphas (2 : Fin 3), ← halphas (0 : Fin 3)]
    exact hfirstGe
  have hlast : c.lastBinaryAlpha =
      (c.alphaValue (2 : Fin 3) : WithTop ℚ) :=
    BONG.GoodBONG.rankFour_lastBinaryAlpha_eq_of_alphaSum_lt_of_first_ge
      c houter' hsecondFourth' hfirstGe'
  rcases reachableLemma814_rankFour_alphaSum_lt_of_first_ge_of_lastBinaryAlpha
      hres c b F.data.firstOrder_eq F.data.conditions houter'
        F.data.firstBinaryAlpha_eq hlast hsum' hfirstGe' with ⟨T⟩
  exact ⟨{
    transform := {
      transformed := T.transform.transformed
      firstValue_eq := T.transform.firstValue_eq
    }
    reachable := F.reachable.trans T.reachable
  }⟩

/-- Reachable terminal form of the quaternary lower-sum branch
`alpha₁ < alpha₃`, assuming that the last literal binary alpha is already
the third global alpha. -/
theorem reachableLemma814_rankFour_alphaSum_lt_of_first_lt_of_lastBinaryAlpha
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) <
      2 * (ramificationIndex K : ℚ))
    (hfirstLt : a.alphaValue (0 : Fin 3) <
      a.alphaValue (2 : Fin 3))
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  let oldFirst := a.toBONG.segmentWitness 0 3 (by omega)
  let oldLast := a.toBONG.segmentWitness 2 2 (by omega)
  have holdPrefix := BONG.GoodBONG.rankFour_prefixAlphas_eq_of_first_lt_third
    a oldFirst oldLast houter hfirstLt
  by_cases hlocal :
      ((oldFirst.toGoodBONG a.good).alphaValue (1 : Fin 2) : WithTop ℚ) +
          (oldFirst.toGoodBONG a.good).lemma814FirstThirdCappedDefect b <
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ)
  · have hnotLocal := BONG.GoodBONG.rankThree_notExceptional_of_defectSum_lt
      (oldFirst.toGoodBONG a.good) b hlocal
    have hconditions :=
      BONG.GoodBONG.rankFour_firstThreeConditions_of_prefixAlphas
        a b oldFirst houter holdPrefix conditions hnotLocal
    exact reachableLemma814_of_safeFirstThreeSegment_of_ambientOrder
      a b oldFirst horder hconditions hnotLocal hres
  · have hlarge :
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) ≤
          (oldFirst.toGoodBONG a.good).alphaValue (1 : Fin 2) +
            (oldFirst.toGoodBONG a.good).lemma814FirstThirdCappedDefect b :=
      le_of_not_gt hlocal
    have hrawLocal :=
      BONG.GoodBONG.rankFour_thirdAlpha_lt_firstThreeDefect_of_secondAlpha_eq
        a b oldFirst holdPrefix.2 hsum hlarge
    have hraw : (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
        BONG.GoodBONG.defectOrder (K := K)
          ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
      rw [← BONG.GoodBONG.rankFour_firstThreeDefect_eq_raw
        a b oldFirst]
      exact hrawLocal
    have hstrict :=
      BONG.GoodBONG.rankFour_thirdAlpha_lt_halfGap_of_alphaSum_lt a hsum
    rcases reachable_rankFour_lastPairScaling_of_largeResidue
        a hlast hstrict hres with ⟨RD⟩
    let D := RD.data
    let changed := D.transformed
    let newFirst := changed.toBONG.segmentWitness 0 3 (by omega)
    let newLast := changed.toBONG.segmentWitness 2 2 (by omega)
    have hnewDefect :
        (newFirst.toGoodBONG changed.good).lemma814FirstThirdCappedDefect b =
          (a.alphaValue (2 : Fin 3) : WithTop ℚ) :=
      D.firstThreeDefect_eq b newFirst hraw
    have horders := a.order_invariant changed
    have halphas := a.alpha_invariant changed
    have hchangedOrder : changed.order (0 : Fin 4) =
        b.order (0 : Fin 1) := by
      rw [← horders (0 : Fin 4)]
      exact horder
    have hchangedOuter : changed.order (0 : Fin 4) =
        changed.order (2 : Fin 4) := by
      rw [← horders (0 : Fin 4), ← horders (2 : Fin 4)]
      exact houter
    have hchangedFirstLt : changed.alphaValue (0 : Fin 3) <
        changed.alphaValue (2 : Fin 3) := by
      rw [← halphas (0 : Fin 3), ← halphas (2 : Fin 3)]
      exact hfirstLt
    have hchangedConditions := a.lemma813Conditions_changeTargetBONG
      (classificationV := classification)
      (classificationW := classification) changed b horder conditions
    have hnewPrefix :=
      BONG.GoodBONG.rankFour_prefixAlphas_eq_of_first_lt_third
        changed newFirst newLast hchangedOuter hchangedFirstLt
    have hnewLocal :
        ((newFirst.toGoodBONG changed.good).alphaValue (1 : Fin 2) :
            WithTop ℚ) +
            (newFirst.toGoodBONG changed.good).lemma814FirstThirdCappedDefect b <
          (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) := by
      rw [hnewPrefix.2, hnewDefect, ← halphas (1 : Fin 3)]
      exact_mod_cast hsum
    have hnotNew := BONG.GoodBONG.rankThree_notExceptional_of_defectSum_lt
      (newFirst.toGoodBONG changed.good) b hnewLocal
    have hnewConditions :=
      BONG.GoodBONG.rankFour_firstThreeConditions_of_prefixAlphas
        changed b newFirst hchangedOuter hnewPrefix hchangedConditions hnotNew
    rcases reachableLemma814_of_safeFirstThreeSegment_of_ambientOrder
        changed b newFirst hchangedOrder hnewConditions hnotNew hres with ⟨T⟩
    exact ⟨{
      transform := {
        transformed := T.transform.transformed
        firstValue_eq := T.transform.firstValue_eq
      }
      reachable := RD.reachable.trans T.reachable
    }⟩

/-- Complete reachable quaternary lower-sum branch `alpha₁ < alpha₃`.
If necessary, path-refined Corollary 8.11 first normalizes the final adjacent
binary pair. -/
theorem reachableLemma814_rankFour_alphaSum_lt_of_first_lt
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) <
      2 * (ramificationIndex K : ℚ))
    (hfirstLt : a.alphaValue (0 : Fin 3) <
      a.alphaValue (2 : Fin 3)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  by_cases hlast : a.lastBinaryAlpha =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ)
  · exact reachableLemma814_rankFour_alphaSum_lt_of_first_lt_of_lastBinaryAlpha
      hres a b horder conditions houter hsum hfirstLt hlast
  · rcases reachableCorollary811_of_largeResidue
        a (2 : Fin 3) hres with ⟨C⟩
    let changed := C.data.transformed
    have horders := a.order_invariant changed
    have halphas := a.alpha_invariant changed
    have hchangedOrder : changed.order (0 : Fin 4) =
        b.order (0 : Fin 1) := by
      rw [← horders (0 : Fin 4)]
      exact horder
    have hchangedOuter : changed.order (0 : Fin 4) =
        changed.order (2 : Fin 4) := by
      rw [← horders (0 : Fin 4), ← horders (2 : Fin 4)]
      exact houter
    have hchangedSum : changed.alphaValue (1 : Fin 3) +
        changed.alphaValue (2 : Fin 3) <
          2 * (ramificationIndex K : ℚ) := by
      rw [← halphas (1 : Fin 3), ← halphas (2 : Fin 3)]
      exact hsum
    have hchangedFirstLt : changed.alphaValue (0 : Fin 3) <
        changed.alphaValue (2 : Fin 3) := by
      rw [← halphas (0 : Fin 3), ← halphas (2 : Fin 3)]
      exact hfirstLt
    have hchangedConditions := a.lemma813Conditions_changeTargetBONG
      (classificationV := classification)
      (classificationW := classification) changed b horder conditions
    have hlastIndex : Fin.last 2 = (2 : Fin 3) := by
      apply Fin.ext
      rfl
    have hchangedLast : changed.lastBinaryAlpha =
        (changed.alphaValue (2 : Fin 3) : WithTop ℚ) := by
      unfold BONG.GoodBONG.lastBinaryAlpha
      rw [hlastIndex]
      exact C.data.adjacentBinaryAlpha_eq
    rcases reachableLemma814_rankFour_alphaSum_lt_of_first_lt_of_lastBinaryAlpha
        hres changed b hchangedOrder hchangedConditions hchangedOuter
          hchangedSum hchangedFirstLt hchangedLast with ⟨T⟩
    exact ⟨{
      transform := {
        transformed := T.transform.transformed
        firstValue_eq := T.transform.firstValue_eq
      }
      reachable := C.reachable.trans T.reachable
    }⟩

/-- Complete reachable quaternary strict lower-sum branch. -/
theorem reachableLemma814_rankFour_alphaSum_lt
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) <
      2 * (ramificationIndex K : ℚ))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  by_cases hfirstGe : a.alphaValue (2 : Fin 3) ≤
      a.alphaValue (0 : Fin 3)
  · exact reachableLemma814_rankFour_alphaSum_lt_of_first_ge
      hres a b horder conditions hnotExceptional houter hsum hsecondFourth
        hfirstGe
  · have hfirstLt : a.alphaValue (0 : Fin 3) <
        a.alphaValue (2 : Fin 3) := lt_of_not_ge hfirstGe
    exact reachableLemma814_rankFour_alphaSum_lt_of_first_lt
      hres a b horder conditions houter hsum hfirstLt

/-- Complete reachable quaternary strict upper-sum branch.  The initial
Corollary 8.10 normalization is retained as part of the final path. -/
theorem reachableLemma814_rankFour_alphaSum_gt
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsum : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases reachableLemma814FirstNormalForm_of_largeResidue
      a b horder conditions hnotExceptional hres with ⟨F⟩
  let c := F.data.transformed
  have horders : a.SameOrders c := a.order_invariant c
  have halphas : a.SameAlphas c := a.alpha_invariant c
  have houter' : c.order (0 : Fin 4) = c.order (2 : Fin 4) := by
    rw [← horders (0 : Fin 4), ← horders (2 : Fin 4)]
    exact houter
  have hsum' : 2 * (ramificationIndex K : ℚ) <
      c.alphaValue (1 : Fin 3) + c.alphaValue (2 : Fin 3) := by
    rw [← halphas (1 : Fin 3), ← halphas (2 : Fin 3)]
    exact hsum
  rcases reachableLemma814_rankFour_alphaSum_gt_of_largeResidue
      hres c b F.data.firstOrder_eq F.data.conditions F.data.notExceptional
        houter' F.data.firstBinaryAlpha_eq hsum' with ⟨T⟩
  exact ⟨{
    transform := {
      transformed := T.transform.transformed
      firstValue_eq := T.transform.firstValue_eq
    }
    reachable := F.reachable.trans T.reachable
  }⟩

/-! ## The path-refined preliminary quaternary boundary normalization -/

/-- A scaling of the final ternary segment, together with the binary path
realizing the induced ambient rank-four change. -/
structure ReachableLemma814FirstAdjacentScalingData
    (a : BONG.GoodBONG q L 4) where
  data : a.Beli2019Lemma814FirstAdjacentScalingData
  reachable : Beli2009BinaryReachable (K := K)
    (fun i => a.valueUnit i) (fun i => data.transformed.valueUnit i)

/-- Insert a prescribed first-value transform of the final ternary segment
and retain an explicit binary path.  Ternary connectivity supplies the local
path; Beli (2003), Lemma 4.9(ii), lifts it into the ambient rank-four BONG. -/
theorem reachableFirstAdjacentScalingData_of_transform
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 1 3 (by omega))
    (T : (segment.toGoodBONG a.good).Beli2019FirstValueTransform)
    (halpha : (segment.toGoodBONG a.good).alphaValue (0 : Fin 2) =
      a.alphaValue (1 : Fin 3))
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    ∃ R : ReachableLemma814FirstAdjacentScalingData a,
      R.data.epsilon = T.epsilon := by
  let s := segment.toGoodBONG a.good
  rcases a.toBONG.beliLemma49_ii a.good segment
      T.transformed.toBONG T.transformed.good with ⟨replacement⟩
  let transformed : BONG.GoodBONG q L 4 :=
    ⟨replacement.bong, replacement.good⟩
  have hfirst : transformed.valueUnit (0 : Fin 4) =
      a.valueUnit (0 : Fin 4) := by
    apply Units.ext
    change replacement.bong.value 0 = a.toBONG.value 0
    rw [← replacement.bong.quadratic_ambientVector,
      ← a.toBONG.quadratic_ambientVector]
    exact congrArg q.quadratic
      (replacement.before_eq (0 : Fin 4) (by omega))
  have hsecondLocal : transformed.valueUnit (1 : Fin 4) =
      T.transformed.valueUnit (0 : Fin 3) := by
    apply Units.ext
    change replacement.bong.value 1 = T.transformed.toBONG.value 0
    rw [← replacement.bong.quadratic_ambientVector,
      ← T.transformed.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector 1) =
      q.quadratic (T.transformed.toBONG.ambientVector 0 : V)
    simpa using congrArg q.quadratic (replacement.inside_eq (0 : Fin 3))
  have hsegmentFirst : s.valueUnit (0 : Fin 3) =
      a.valueUnit (1 : Fin 4) := by
    change segment.bong.valueUnit 0 = a.toBONG.valueUnit 1
    simp [BONG.SegmentWitness.sourceIndex]
  let D : a.Beli2019Lemma814FirstAdjacentScalingData := {
    epsilon := T.epsilon
    epsilon_isValuationUnit := T.epsilon_isValuationUnit
    epsilon_defect := T.epsilon_defect.trans <|
      congrArg (fun x : ℚ => (x : WithTop ℚ)) halpha
    transformed := transformed
    firstValue_eq := hfirst
    secondValue_eq := hsecondLocal.trans <| T.firstValue_eq.trans <|
      congrArg (T.epsilon * ·) hsegmentFirst
  }
  have hlocal : Beli2009BinaryReachable (K := K)
      (fun i => s.valueUnit i) (fun i => T.transformed.valueUnit i) :=
    reachable_rankThree_of_largeResidue hres s T.transformed
  have hglobal := reachable_of_suffixSegmentReplacement
    (n := 4) (P := 1) (M := 2) rfl a segment T.transformed replacement hlocal
  have hreach : Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => D.transformed.valueUnit i) := by
    simpa [D, transformed] using hglobal
  exact ⟨⟨D, hreach⟩, rfl⟩

/-- The preliminary first-adjacent normalization together with its actual
binary-transformation path. -/
structure ReachableLemma814FirstAdjacentNormalizationData
    (a : BONG.GoodBONG q L 4) where
  data : a.Beli2019Lemma814FirstAdjacentNormalizationData
  reachable : Beli2009BinaryReachable (K := K)
    (fun i => a.valueUnit i) (fun i => data.transformed.valueUnit i)

/-- Package a reachable final-ternary scaling once its new first adjacent
defect is known to be strict. -/
theorem reachableFirstAdjacentNormalizationData_of_scaling
    (a : BONG.GoodBONG q L 4)
    (R : ReachableLemma814FirstAdjacentScalingData a)
    (hstrict :
      (R.data.transformed.alphaValue (1 : Fin 3) : WithTop ℚ) <
        R.data.transformed.adjacentDefect (0 : Fin 3)) :
    Nonempty (ReachableLemma814FirstAdjacentNormalizationData a) :=
  ⟨{
    data := {
      transformed := R.data.transformed
      firstAdjacent_strict := hstrict
    }
    reachable := R.reachable
  }⟩

/-- A multiplier in the middle binary norm-generator group gives a single
ambient binary step at index one.  A strict defect of its product with the
old first adjacent class is therefore a reachable preliminary boundary
normalization. -/
theorem reachableFirstAdjacentNormalization_of_multiplier
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 4) (ε : Kˣ)
    (hbinary : a.adjacentBinaryAlpha (1 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hunit : IsValuationUnit K (ε : K))
    (hdefect : BONG.GoodBONG.defectOrder (K := K) ε =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hhilbert : hilbertSymbol K ε (a.adjacentProduct (1 : Fin 3)) = 1)
    (hstrictProduct : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      BONG.GoodBONG.defectOrder (K := K)
        (ε * a.adjacentProduct (0 : Fin 3))) :
    Nonempty (ReachableLemma814FirstAdjacentNormalizationData a) := by
  have hgroup : valuationUnitClassHom K ⟨ε, hunit⟩ ∈
      beliNormGeneratorGroup K
        (a.valueUnit (2 : Fin 4) / a.valueUnit (1 : Fin 4)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (1 : Fin 3) ⟨ε, hunit⟩
    · change a.adjacentBinaryAlpha (1 : Fin 3) ≤
        BONG.GoodBONG.defectOrder (K := K) ε
      rw [hbinary, hdefect]
    · change hilbertSymbol K (a.adjacentProduct (1 : Fin 3)) ε = 1
      rw [hilbertSymbol_comm K]
      exact hhilbert
  rcases exists_goodBONG_binaryTransformation_exact a (1 : Fin 3)
      ⟨ε, hunit⟩ hgroup with ⟨c, hvalues⟩
  have hstep : IsBeli2009BinaryTransformation (K := K)
      (fun i => a.valueUnit i) (fun i => c.valueUnit i) :=
    ⟨1, ⟨ε, hunit⟩, hgroup, hvalues⟩
  have hproduct : c.adjacentProduct (0 : Fin 3) =
      ε * a.adjacentProduct (0 : Fin 3) := by
    unfold BONG.GoodBONG.adjacentProduct
    rw [congrFun hvalues (0 : Fin 3).castSucc,
      congrFun hvalues (0 : Fin 3).succ]
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]
  have halphas := a.alpha_invariant c
  have hstrict : (c.alphaValue (1 : Fin 3) : WithTop ℚ) <
      c.adjacentDefect (0 : Fin 3) := by
    rw [← halphas (1 : Fin 3)]
    unfold BONG.GoodBONG.adjacentDefect
    rw [hproduct]
    exact hstrictProduct
  exact ⟨{
    data := {
      transformed := c
      firstAdjacent_strict := hstrict
    }
    reachable := hstep.reachable
  }⟩

/-- Reachable positive-Hilbert branch of the preliminary quaternary boundary
normalization.  Removing a square from the first adjacent class gives a
valuation-unit multiplier; the resulting index-one binary move makes that
adjacent product a square. -/
theorem reachableFirstAdjacentNormalization_of_hilbert_one
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hbinary : a.adjacentBinaryAlpha (1 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hnot : ¬(a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3))
    (hhilbert : hilbertSymbol K (a.adjacentProduct (0 : Fin 3))
      (a.adjacentProduct (1 : Fin 3)) = 1) :
    Nonempty (ReachableLemma814FirstAdjacentNormalizationData a) := by
  let x := a.adjacentProduct (0 : Fin 3)
  let y := a.adjacentProduct (1 : Fin 3)
  have hxEven : Even (ordUnit K x) := by
    simpa only [x] using
      BONG.GoodBONG.rankFour_firstAdjacentOrder_even a houter
  rcases BONG.exists_valuationUnit_multiplier_isSquare x hxEven with
    ⟨ε, hεUnit, hεxSquare, hεDefectRaw⟩
  have hxDefect : BONG.GoodBONG.defectOrder (K := K) x =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    have h :=
      BONG.GoodBONG.rankFour_firstAdjacentDefect_eq_secondAlpha_of_not_lt
        a houter hnot
    simpa only [BONG.GoodBONG.adjacentDefect, x] using h
  have hεDefect : BONG.GoodBONG.defectOrder (K := K) ε =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    unfold BONG.GoodBONG.defectOrder
    rw [hεDefectRaw]
    exact hxDefect
  have hεHilbert : hilbertSymbol K ε y = 1 := by
    calc
      hilbertSymbol K ε y = hilbertSymbol K x y :=
        hilbertSymbol_eq_of_isSquare_mul_left hεxSquare
      _ = 1 := by simpa only [x, y] using hhilbert
  have hstrictProduct : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      BONG.GoodBONG.defectOrder (K := K)
        (ε * a.adjacentProduct (0 : Fin 3)) := by
    rw [show a.adjacentProduct (0 : Fin 3) = x by rfl,
      BONG.GoodBONG.defectOrder_eq_top_of_isSquare hεxSquare]
    exact WithTop.coe_lt_top _
  exact reachableFirstAdjacentNormalization_of_multiplier
    a ε hbinary hεUnit hεDefect
      (by simpa only [y] using hεHilbert) hstrictProduct

/-- Reachable negative-Hilbert branch when the final alpha attains its
half-gap.  The complementary-defect construction produces a multiplier in
the middle binary norm group whose product with the first adjacent class has
strictly larger defect; hence one explicit index-one move suffices. -/
theorem reachableFirstAdjacentNormalization_of_third_eq_of_hilbert_neg
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hbinary : a.adjacentBinaryAlpha (1 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hnot : ¬(a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3))
    (hthird : a.alphaValue (2 : Fin 3) =
      a.halfGapValue (2 : Fin 3))
    (hhilbert : hilbertSymbol K (a.adjacentProduct (0 : Fin 3))
      (a.adjacentProduct (1 : Fin 3)) = -1) :
    Nonempty (ReachableLemma814FirstAdjacentNormalizationData a) := by
  let x := a.adjacentProduct (0 : Fin 3)
  let p := a.adjacentProduct (1 : Fin 3)
  have hxEven : Even (ordUnit K x) := by
    simpa only [x] using
      BONG.GoodBONG.rankFour_firstAdjacentOrder_even a houter
  have hxDefect : BONG.GoodBONG.defectOrder (K := K) x =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    have h :=
      BONG.GoodBONG.rankFour_firstAdjacentDefect_eq_secondAlpha_of_not_lt
        a houter hnot
    simpa only [BONG.GoodBONG.adjacentDefect, x] using h
  have hpDefect : BONG.GoodBONG.defectOrder (K := K) p =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
    have h :=
      BONG.GoodBONG.rankFour_middleAdjacentDefect_eq_firstAlpha_of_third_eq_halfGap
        a houter hsecondFourth hsum hbinary hthird
    simpa only [BONG.GoodBONG.adjacentDefect, p] using h
  have hboundaryAlpha := a.rankFour_boundaryAlphaData
    houter hsecondFourth hsum
  have hfirstNonnegative : 0 ≤ a.alphaValue (0 : Fin 3) :=
    (a.beli2009Lemma27_i (0 : Fin 3)).1
  rcases BONG.exists_complementaryDefect_hilbert_neg_of_nonnegative
      (K := K) p (a.alphaValue (0 : Fin 3)) hpDefect hfirstNonnegative
        hboundaryAlpha.first_lt_twoE with
    ⟨w, hwUnit, hwDefect, hwHilbert⟩
  have hwEven : Even (ordUnit K w) := by
    have hwOrder : ordUnit K w = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K w).1 hwUnit
    rw [hwOrder]
    exact ⟨0, by simp⟩
  have hwNonzero : quadraticDefect K w ≠ 0 :=
    BONG.quadraticDefect_ne_zero_of_even_ordUnit w hwEven
  rcases BONG.exists_valuationUnit_multiplier_same_defect_same_hilbert
      p x w hxEven hwNonzero with
    ⟨ε, hεUnit, hεxDefectRaw, hεxHilbertRaw⟩
  let high : ℚ :=
    2 * (ramificationIndex K : ℚ) - a.alphaValue (0 : Fin 3)
  have hεxDefect : BONG.GoodBONG.defectOrder (K := K) (ε * x) =
      (high : WithTop ℚ) := by
    have hwDefect' := hwDefect
    unfold BONG.GoodBONG.defectOrder at hwDefect'
    unfold BONG.GoodBONG.defectOrder
    rw [hεxDefectRaw]
    simpa only [high] using hwDefect'
  have hmiddleStrict : a.alphaValue (1 : Fin 3) <
      a.halfGapValue (1 : Fin 3) := by
    unfold BONG.GoodBONG.halfGapValue BONG.GoodBONG.orderGap at hthird ⊢
    push_cast at hthird ⊢
    have hsecondFourthQ : (a.order (1 : Fin 4) : ℚ) <
        a.order (3 : Fin 4) := by
      exact_mod_cast hsecondFourth
    linarith
  have hfirstSecondLt :
      a.alphaValue (0 : Fin 3) + a.alphaValue (1 : Fin 3) <
        2 * (ramificationIndex K : ℚ) := by
    have hrelation :=
      (a.beli2019Remark87 (0 : Fin 2) houter).currentAlpha_eq
    change a.alphaValue (1 : Fin 3) =
        ((a.order (0 : Fin 4) - a.order (1 : Fin 4) : Int) : ℚ) +
          a.alphaValue (0 : Fin 3) at hrelation
    unfold BONG.GoodBONG.halfGapValue BONG.GoodBONG.orderGap at hmiddleStrict
    push_cast at hmiddleStrict hrelation ⊢
    have houterQ : (a.order (0 : Fin 4) : ℚ) =
        a.order (2 : Fin 4) := by
      exact_mod_cast houter
    linarith
  have hhighGtSecond : a.alphaValue (1 : Fin 3) < high := by
    dsimp only [high]
    linarith
  have hxLtProduct : BONG.GoodBONG.defectOrder (K := K) x <
      BONG.GoodBONG.defectOrder (K := K) (ε * x) := by
    rw [hxDefect, hεxDefect]
    exact_mod_cast hhighGtSecond
  have hεSameDefect : BONG.GoodBONG.defectOrder (K := K) ε =
      BONG.GoodBONG.defectOrder (K := K) x := by
    by_contra hne
    have hproduct := BONG.GoodBONG.defectOrder_mul_eq_min_of_ne
      (K := K) hne
    have hle : BONG.GoodBONG.defectOrder (K := K) (ε * x) ≤
        BONG.GoodBONG.defectOrder (K := K) x := by
      rw [hproduct]
      exact min_le_right _ _
    exact (not_lt_of_ge hle hxLtProduct)
  have hεDefect : BONG.GoodBONG.defectOrder (K := K) ε =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) :=
    hεSameDefect.trans hxDefect
  have hpεx : hilbertSymbol K p (ε * x) = -1 := by
    calc
      hilbertSymbol K p (ε * x) = hilbertSymbol K p w := hεxHilbertRaw
      _ = hilbertSymbol K w p := hilbertSymbol_comm K p w
      _ = -1 := hwHilbert
  have hpε : hilbertSymbol K p ε = 1 := by
    rw [hilbertSymbol_mul_right, hilbertSymbol_comm K p x] at hpεx
    rw [show hilbertSymbol K x p = -1 by simpa only [x, p] using hhilbert]
      at hpεx
    simpa using hpεx
  have hεHilbert : hilbertSymbol K ε p = 1 := by
    rw [hilbertSymbol_comm K ε p]
    exact hpε
  exact reachableFirstAdjacentNormalization_of_multiplier
    a ε hbinary hεUnit hεDefect
      (by simpa only [p] using hεHilbert) (by
        rw [← hxDefect]
        simpa only [x] using hxLtProduct)

/-- Reachable negative-Hilbert branch when the final alpha is strictly below
its half-gap.  The paper's two-parameter ternary scaling is connected by the
already proved ternary large-residue theorem and then lifted into rank four. -/
theorem reachableFirstAdjacentNormalization_of_third_lt_of_hilbert_neg
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hbinary : a.adjacentBinaryAlpha (1 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hnot : ¬(a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3))
    (hthird : a.alphaValue (2 : Fin 3) <
      a.halfGapValue (2 : Fin 3))
    (hhilbert : hilbertSymbol K (a.adjacentProduct (0 : Fin 3))
      (a.adjacentProduct (1 : Fin 3)) = -1)
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableLemma814FirstAdjacentNormalizationData a) := by
  let x := a.adjacentProduct (0 : Fin 3)
  let p := a.adjacentProduct (1 : Fin 3)
  let z := a.adjacentProduct (2 : Fin 3)
  have hxEven : Even (ordUnit K x) := by
    simpa only [x] using
      BONG.GoodBONG.rankFour_firstAdjacentOrder_even a houter
  rcases BONG.exists_valuationUnit_multiplier_isSquare x hxEven with
    ⟨ε, hεUnit, hεxSquare, hεDefectRaw⟩
  have hxDefect : BONG.GoodBONG.defectOrder (K := K) x =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    have h :=
      BONG.GoodBONG.rankFour_firstAdjacentDefect_eq_secondAlpha_of_not_lt
        a houter hnot
    simpa only [BONG.GoodBONG.adjacentDefect, x] using h
  have hεDefect : BONG.GoodBONG.defectOrder (K := K) ε =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    unfold BONG.GoodBONG.defectOrder
    rw [hεDefectRaw]
    exact hxDefect
  have hεHilbert : hilbertSymbol K ε p = -1 := by
    calc
      hilbertSymbol K ε p = hilbertSymbol K x p :=
        hilbertSymbol_eq_of_isSquare_mul_left hεxSquare
      _ = -1 := by simpa only [x, p] using hhilbert
  let segment := a.toBONG.segmentWitness 1 3 (by omega)
  let s := segment.toGoodBONG a.good
  have hlocalFirst :=
    BONG.GoodBONG.rankFour_lastThree_firstAlpha_eq_of_adjacentBinaryAlpha
      a segment hbinary
  have hlocalSecond :=
    BONG.GoodBONG.rankFour_lastThree_secondAlpha_eq_of_boundary
      a segment hsum
  let d : ℚ :=
    ((a.order (2 : Fin 4) - a.order (3 : Fin 4) : Int) : ℚ) +
      a.alphaValue (2 : Fin 3)
  have hzDefect : BONG.GoodBONG.defectOrder (K := K) z =
      (d : WithTop ℚ) := by
    have hlast := BONG.GoodBONG.rankFour_boundary_lastBinaryAlpha_eq a hsum
    have hraw :=
      BONG.GoodBONG.rankFour_lastAdjacentDefect_eq_of_thirdAlpha_lt_halfGap
        a hlast hthird
    simpa only [BONG.GoodBONG.adjacentDefect, z, d] using hraw
  have hdLtSecond : d < a.alphaValue (1 : Fin 3) := by
    dsimp only [d]
    unfold BONG.GoodBONG.halfGapValue BONG.GoodBONG.orderGap at hthird
    push_cast at hthird ⊢
    linarith
  have hzLtEpsilon : BONG.GoodBONG.defectOrder (K := K) z <
      BONG.GoodBONG.defectOrder (K := K) ε := by
    rw [hzDefect, hεDefect]
    exact_mod_cast hdLtSecond
  have hεzDefect : BONG.GoodBONG.defectOrder (K := K) (ε * z) =
      (d : WithTop ℚ) := by
    rw [BONG.GoodBONG.defectOrder_mul_eq_right_of_lt_left hzLtEpsilon,
      hzDefect]
  have hdNonnegative : 0 ≤ d := by
    have hnonnegative :=
      BONG.GoodBONG.defectOrder_nonneg (K := K) (ε * z)
    rw [hεzDefect] at hnonnegative
    exact_mod_cast hnonnegative
  have hboundaryAlpha := a.rankFour_boundaryAlphaData
    houter hsecondFourth hsum
  have hdLtTwoE : d < 2 * (ramificationIndex K : ℚ) :=
    hdLtSecond.trans hboundaryAlpha.second_lt_twoE
  rcases BONG.exists_complementaryDefect_hilbert_neg_of_nonnegative
      (K := K) (ε * z) d hεzDefect hdNonnegative hdLtTwoE with
    ⟨η, hηUnit, hηDefect, hηHilbert⟩
  have hηLowerRat : a.alphaValue (2 : Fin 3) ≤
      2 * (ramificationIndex K : ℚ) - d := by
    dsimp only [d]
    unfold BONG.GoodBONG.halfGapValue BONG.GoodBONG.orderGap at hthird
    push_cast at hthird ⊢
    linarith
  have hηDefectBound : (s.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) η := by
    rw [hlocalSecond, hηDefect]
    exact_mod_cast hηLowerRat
  have hεDefectBound : (s.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) ε := by
    rw [hlocalFirst.1, hεDefect]
  have hεLocal : hilbertSymbol K ε
      (s.adjacentProduct (0 : Fin 2)) = -1 := by
    rw [BONG.GoodBONG.rankFour_lastThree_firstAdjacentProduct_eq a segment]
    exact hεHilbert
  have hηLocal : hilbertSymbol K η
      (ε * s.adjacentProduct (1 : Fin 2)) = -1 := by
    rw [BONG.GoodBONG.rankFour_lastThree_secondAdjacentProduct_eq a segment]
    simpa only [z] using hηHilbert
  have hadjacent := BONG.GoodBONG.ternaryScaled_adjacentHilbert_eq_of_neg
    s ε η hεLocal hηLocal
  have hproperty : s.toBONG.HasPropertyA := by
    intro i hi
    fin_cases i
    · change s.order (0 : Fin 3) < s.order (2 : Fin 3)
      have horder0 : s.order (0 : Fin 3) = a.order (1 : Fin 4) := by
        change segment.bong.order 0 = a.toBONG.order 1
        simp [BONG.SegmentWitness.sourceIndex]
      have horder2 : s.order (2 : Fin 3) = a.order (3 : Fin 4) := by
        change segment.bong.order 2 = a.toBONG.order 3
        simp [BONG.SegmentWitness.sourceIndex]
      rw [horder0, horder2]
      exact hsecondFourth
    · norm_num at hi
    · norm_num at hi
  have hAlphaSum : s.alphaValue (0 : Fin 2) + s.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) := by
    rw [hlocalFirst.1, hlocalSecond, hsum]
  rcases s.exists_goodBONG_ternaryScaled_of_propertyA ε η hεUnit hηUnit
      hεDefectBound hηDefectBound hadjacent hproperty hAlphaSum with
    ⟨localTransformed, hfirst⟩
  let T : s.Beli2019FirstValueTransform := {
    epsilon := ε
    epsilon_isValuationUnit := hεUnit
    epsilon_defect := hεDefect.trans <|
      congrArg (fun t : ℚ => (t : WithTop ℚ)) hlocalFirst.1.symm
    transformed := localTransformed
    firstValue_eq := hfirst
  }
  rcases reachableFirstAdjacentScalingData_of_transform
      a segment T hlocalFirst.1 hres with ⟨R, hRε⟩
  have halphas := a.alpha_invariant R.data.transformed
  have hstrict :
      (R.data.transformed.alphaValue (1 : Fin 3) : WithTop ℚ) <
        R.data.transformed.adjacentDefect (0 : Fin 3) := by
    rw [← halphas (1 : Fin 3), R.data.firstAdjacentDefect_eq, hRε,
      BONG.GoodBONG.defectOrder_eq_top_of_isSquare hεxSquare]
    exact WithTop.coe_lt_top _
  exact reachableFirstAdjacentNormalizationData_of_scaling a R hstrict

/-- Reachable completion of the preliminary boundary normalization once the
middle literal binary alpha is the ambient second alpha. -/
theorem reachableFirstAdjacentNormalization_of_middleBinary
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hbinary : a.adjacentBinaryAlpha (1 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableLemma814FirstAdjacentNormalizationData a) := by
  by_cases hstrict : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3)
  · exact ⟨{
      data := {
        transformed := a
        firstAdjacent_strict := hstrict
      }
      reachable := .refl
    }⟩
  · let x := a.adjacentProduct (0 : Fin 3)
    let p := a.adjacentProduct (1 : Fin 3)
    rcases Int.units_eq_one_or (hilbertSymbol K x p) with hhilbert | hhilbert
    · apply reachableFirstAdjacentNormalization_of_hilbert_one
        a houter hbinary hstrict
      simpa only [x, p] using hhilbert
    · rcases lt_or_eq_of_le
          (a.alphaValue_le_halfGapValue (2 : Fin 3)) with hthird | hthird
      · apply reachableFirstAdjacentNormalization_of_third_lt_of_hilbert_neg
          a houter hsecondFourth hsum hbinary hstrict hthird
            (by simpa only [x, p] using hhilbert) hres
      · apply reachableFirstAdjacentNormalization_of_third_eq_of_hilbert_neg
          a houter hsecondFourth hsum hbinary hstrict hthird
        simpa only [x, p] using hhilbert

/-- Path-refined preliminary normalization for the complete quaternary
equality boundary.  Corollary 8.11 first normalizes the middle adjacent pair;
the preceding theorem then makes the first raw adjacent defect strict. -/
theorem reachableFirstAdjacentNormalization
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableLemma814FirstAdjacentNormalizationData a) := by
  rcases reachableCorollary811_of_largeResidue
      a (1 : Fin 3) hres with ⟨C⟩
  let changed := C.data.transformed
  have horders := a.order_invariant changed
  have halphas := a.alpha_invariant changed
  have houter' : changed.order (0 : Fin 4) =
      changed.order (2 : Fin 4) := by
    rw [← horders (0 : Fin 4), ← horders (2 : Fin 4)]
    exact houter
  have hsecondFourth' : changed.order (1 : Fin 4) <
      changed.order (3 : Fin 4) := by
    rw [← horders (1 : Fin 4), ← horders (3 : Fin 4)]
    exact hsecondFourth
  have hsum' : changed.alphaValue (1 : Fin 3) +
      changed.alphaValue (2 : Fin 3) =
        2 * (ramificationIndex K : ℚ) := by
    rw [← halphas (1 : Fin 3), ← halphas (2 : Fin 3)]
    exact hsum
  rcases reachableFirstAdjacentNormalization_of_middleBinary
      changed houter' hsecondFourth' hsum'
        C.data.adjacentBinaryAlpha_eq hres with ⟨D⟩
  exact ⟨{
    data := {
      transformed := D.data.transformed
      firstAdjacent_strict := D.data.firstAdjacent_strict
    }
    reachable := C.reachable.trans D.reachable
  }⟩

/-- Reachable successful final-pair scaling on the quaternary equality
boundary. -/
theorem reachableBoundaryLastPairScaling_of_notExceptional
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hnotExceptional :
      let segment := a.toBONG.segmentWitness 2 2 (by omega)
      ¬(segment.toGoodBONG a.good).Beli2019Lemma88Exceptional)
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableLemma814LastPairScalingData a) := by
  let segment := a.toBONG.segmentWitness 2 2 (by omega)
  let s := segment.toGoodBONG a.good
  have hlast := BONG.GoodBONG.rankFour_boundary_lastBinaryAlpha_eq a hsum
  have halpha : s.alphaValue (0 : Fin 1) =
      a.alphaValue (2 : Fin 3) :=
    BONG.GoodBONG.rankFour_lastPairAlpha_eq_of_lastBinaryAlpha
      a segment hlast
  have hnot : ¬s.Beli2019Lemma88Exceptional := by
    simpa only [segment, s] using hnotExceptional
  rcases reachableLemma88_sufficiency_of_largeResidue
      s hnot hres with ⟨T⟩
  exact reachableLastPairScalingData_of_transform a segment T halpha

/-- Reachable quaternary equality-boundary proof after the preliminary strict
first-adjacent normalization.  Over a residue field with more than two
elements the exceptional final binary alternative is impossible; if the
initial ternary segment is unsafe, the reachable final-pair Lemma 8.8 move
makes it safe. -/
theorem reachableLemma814_rankFour_boundary_of_firstAdjacent
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hfirstAdjacent : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3))
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  let oldSegment := a.toBONG.segmentWitness
    (BONG.GoodBONG.prefixPairLocalization (N := 2) (1 : Fin 3)).start
    (BONG.GoodBONG.prefixPairLocalization (N := 2) (1 : Fin 3)).length
    (BONG.GoodBONG.prefixPairLocalization (N := 2) (1 : Fin 3)).bound
  let old := oldSegment.toGoodBONG a.good
  have holdPrefix := BONG.GoodBONG.rankFour_boundary_prefixAlphas_eq
    a oldSegment houter hsum
  by_cases hnotOld : ¬old.Beli2019Lemma814Exceptional b
  · have holdConditions :=
      BONG.GoodBONG.rankFour_firstThreeConditions_of_prefixAlphas
        a b oldSegment houter holdPrefix conditions hnotOld
    exact reachableLemma814_of_safeFirstThreeSegment_of_ambientOrder
      a b oldSegment horder holdConditions hnotOld hres
  · have holdExceptional : old.Beli2019Lemma814Exceptional b :=
      Classical.byContradiction hnotOld
    let lastSegment := a.toBONG.segmentWitness 2 2 (by omega)
    have hnotLast :
        ¬(lastSegment.toGoodBONG a.good).Beli2019Lemma88Exceptional := by
      intro E
      have D := BONG.GoodBONG.rankFour_boundary_lastPairExceptionData
        a houter hsecondFourth hsum (by simpa only [lastSegment] using E)
      exact D.residueTwo hres
    rcases reachableBoundaryLastPairScaling_of_notExceptional
        a hsum (by simpa only [lastSegment] using hnotLast) hres with ⟨RD⟩
    let D := RD.data
    let changed := D.transformed
    let newSegment := changed.toBONG.segmentWitness
      (BONG.GoodBONG.prefixPairLocalization (N := 2) (1 : Fin 3)).start
      (BONG.GoodBONG.prefixPairLocalization (N := 2) (1 : Fin 3)).length
      (BONG.GoodBONG.prefixPairLocalization (N := 2) (1 : Fin 3)).bound
    let new := newSegment.toGoodBONG changed.good
    have hnotNew : ¬new.Beli2019Lemma814Exceptional b := by
      apply BONG.GoodBONG.rankFour_boundary_notExceptional_firstThree_after_scaling
        a b D oldSegment newSegment houter hsum hfirstAdjacent
      exact holdExceptional
    have horders := a.order_invariant changed
    have halphas := a.alpha_invariant changed
    have hchangedOrder : changed.order (0 : Fin 4) =
        b.order (0 : Fin 1) := by
      rw [← horders (0 : Fin 4)]
      exact horder
    have hchangedOuter : changed.order (0 : Fin 4) =
        changed.order (2 : Fin 4) := by
      rw [← horders (0 : Fin 4), ← horders (2 : Fin 4)]
      exact houter
    have hchangedSum : changed.alphaValue (1 : Fin 3) +
        changed.alphaValue (2 : Fin 3) =
          2 * (ramificationIndex K : ℚ) := by
      rw [← halphas (1 : Fin 3), ← halphas (2 : Fin 3)]
      exact hsum
    have hnewPrefix := BONG.GoodBONG.rankFour_boundary_prefixAlphas_eq
      changed newSegment hchangedOuter hchangedSum
    have hchangedConditions := a.lemma813Conditions_changeTargetBONG
      (classificationV := classification)
      (classificationW := classification) changed b horder conditions
    have hnewConditions :=
      BONG.GoodBONG.rankFour_firstThreeConditions_of_prefixAlphas
        changed b newSegment hchangedOuter hnewPrefix hchangedConditions hnotNew
    rcases reachableLemma814_of_safeFirstThreeSegment_of_ambientOrder
        changed b newSegment hchangedOrder hnewConditions hnotNew hres with ⟨T⟩
    exact ⟨{
      transform := {
        transformed := T.transform.transformed
        firstValue_eq := T.transform.firstValue_eq
      }
      reachable := RD.reachable.trans T.reachable
    }⟩

/-- Complete path-refined quaternary equality boundary. -/
theorem reachableLemma814_rankFour_boundary
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases reachableFirstAdjacentNormalization
      a houter hsecondFourth hsum hres with ⟨D⟩
  let changed := D.data.transformed
  have horders := a.order_invariant changed
  have halphas := a.alpha_invariant changed
  have horder' : changed.order (0 : Fin 4) = b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin 4)]
    exact horder
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classification)
    (classificationW := classification) changed b horder conditions
  have hinvariant := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classification)
    (classificationW := classification)
    (prefixChangeV := prefixChange)
    (prefixChangeW := prefixChange) changed b
  have hnotExceptional' : ¬changed.Beli2019Lemma814Exceptional b :=
    fun E => hnotExceptional (hinvariant.mpr E)
  have houter' : changed.order (0 : Fin 4) =
      changed.order (2 : Fin 4) := by
    rw [← horders (0 : Fin 4), ← horders (2 : Fin 4)]
    exact houter
  have hsecondFourth' : changed.order (1 : Fin 4) <
      changed.order (3 : Fin 4) := by
    rw [← horders (1 : Fin 4), ← horders (3 : Fin 4)]
    exact hsecondFourth
  have hsum' : changed.alphaValue (1 : Fin 3) +
      changed.alphaValue (2 : Fin 3) =
        2 * (ramificationIndex K : ℚ) := by
    rw [← halphas (1 : Fin 3), ← halphas (2 : Fin 3)]
    exact hsum
  rcases reachableLemma814_rankFour_boundary_of_firstAdjacent
      changed b horder' hconditions houter' hsecondFourth' hsum'
        D.data.firstAdjacent_strict hres with ⟨T⟩
  exact ⟨{
    transform := {
      transformed := T.transform.transformed
      firstValue_eq := T.transform.firstValue_eq
    }
    reachable := D.reachable.trans T.reachable
  }⟩

/-- Complete path-refined rank-four branch when the first and third orders
are equal and the second order is strictly below the fourth. -/
theorem reachableLemma814_rankFour_strictSecondFourth
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases lt_trichotomy
      (a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3))
      (2 * (ramificationIndex K : ℚ)) with hbelow | hequal | habove
  · exact reachableLemma814_rankFour_alphaSum_lt
      hres a b horder conditions hnotExceptional houter hbelow hsecondFourth
  · exact reachableLemma814_rankFour_boundary
      a b horder conditions hnotExceptional houter hsecondFourth hequal hres
  · exact reachableLemma814_rankFour_alphaSum_gt
      hres a b horder conditions hnotExceptional houter habove

/-! ## The path-refined doubly alternating quaternary endpoint -/

/-- Once the literal first binary alpha has been normalized, a positive
Hilbert sign makes the prescribed first-value change one genuine adjacent
binary transformation.  This is the easy half of the doubly alternating
rank-four endpoint. -/
theorem reachablePrescribedFirstValue_rankFour_of_firstBinaryAlpha_le_of_hilbert_one
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (hbinary : a.firstBinaryAlpha ≤
      BONG.GoodBONG.defectOrder (K := K) (a.lemma814Epsilon b))
    (hhilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 3)) = 1) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  let epsilon := a.lemma814Epsilon b
  have hepsilonUnit : IsValuationUnit K (epsilon : K) :=
    a.lemma814Epsilon_isValuationUnit b horder
  have hgroup : valuationUnitClassHom K ⟨epsilon, hepsilonUnit⟩ ∈
      beliNormGeneratorGroup K
        (a.valueUnit (1 : Fin 4) / a.valueUnit (0 : Fin 4)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (0 : Fin 3) ⟨epsilon, hepsilonUnit⟩
    · change a.firstBinaryAlpha ≤
        BONG.GoodBONG.defectOrder (K := K) epsilon
      exact hbinary
    · change hilbertSymbol K (a.adjacentProduct (0 : Fin 3)) epsilon = 1
      rw [hilbertSymbol_comm K]
      exact hhilbert
  rcases exists_goodBONG_binaryTransformation_exact a (0 : Fin 3)
      ⟨epsilon, hepsilonUnit⟩ hgroup with ⟨c, hvalues⟩
  have hstep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ c.valueUnit i) :=
    ⟨0, ⟨epsilon, hepsilonUnit⟩, hgroup, hvalues⟩
  have hfirst : c.valueUnit (0 : Fin 4) = b.valueUnit (0 : Fin 1) := by
    calc
      c.valueUnit (0 : Fin 4) = epsilon * a.valueUnit (0 : Fin 4) := by
        rw [congrFun hvalues (0 : Fin 4)]
        simp [beli2009BinaryTransformAt]
      _ = b.valueUnit (0 : Fin 1) := a.lemma814Epsilon_mul_firstValue b
  exact ⟨{
    transform := {
      transformed := c
      firstValue_eq := hfirst
    }
    reachable := hstep.reachable
  }⟩

/-- Equality with the ambient first alpha supplies the preceding literal
binary bound from the Lemma 8.13 defect condition. -/
theorem reachablePrescribedFirstValue_rankFour_of_firstBinaryAlpha_of_hilbert_one
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hhilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 3)) = 1) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  apply reachablePrescribedFirstValue_rankFour_of_firstBinaryAlpha_le_of_hilbert_one
    a b horder
  · rw [hbinary]
    exact a.alpha_le_lemma814EpsilonDefect b conditions
  · exact hhilbert

/-- A legal middle-edge move which preserves the first adjacent defect and
flips the prescribed Hilbert character reduces the negative branch to the
preceding positive branch.  This is the path-level form of the elementary
`1 → 0` bridge used at the doubly alternating quaternary endpoint. -/
theorem reachablePrescribedFirstValue_rankFour_of_middleFlip
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (rho : valuationUnitSubgroup K)
    (hrhoDepth : a.adjacentBinaryAlpha (1 : Fin 3) ≤
      BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ))
    (hrhoMiddle : hilbertSymbol K (rho : Kˣ)
      (a.adjacentProduct (1 : Fin 3)) = 1)
    (hfirstDefect : BONG.GoodBONG.defectOrder (K := K)
        ((rho : Kˣ) * a.adjacentProduct (0 : Fin 3)) =
      BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (0 : Fin 3)))
    (hrhoEpsilon : hilbertSymbol K (rho : Kˣ)
      (a.lemma814Epsilon b) = -1)
    (hepsilonFirst : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 3)) = -1) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  have hrhoGroup : valuationUnitClassHom K rho ∈
      beliNormGeneratorGroup K
        (a.valueUnit (2 : Fin 4) / a.valueUnit (1 : Fin 4)) := by
    apply valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (1 : Fin 3) rho hrhoDepth
    rw [hilbertSymbol_comm K]
    exact hrhoMiddle
  rcases exists_goodBONG_binaryTransformation_exact a (1 : Fin 3)
      rho hrhoGroup with ⟨c, hvalues⟩
  have hstep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ c.valueUnit i) :=
    ⟨1, rho, hrhoGroup, hvalues⟩
  have horders := a.order_invariant c
  have hhead : c.valueUnit (0 : Fin 4) = a.valueUnit (0 : Fin 4) := by
    rw [congrFun hvalues (0 : Fin 4)]
    simp [beli2009BinaryTransformAt]
  have hepsilon : c.lemma814Epsilon b = a.lemma814Epsilon b := by
    unfold BONG.GoodBONG.lemma814Epsilon
    rw [hhead]
  have hfirstProduct : c.adjacentProduct (0 : Fin 3) =
      (rho : Kˣ) * a.adjacentProduct (0 : Fin 3) := by
    have hvalueZero := congrFun hvalues (0 : Fin 3).castSucc
    have hvalueOne := congrFun hvalues (0 : Fin 3).succ
    unfold BONG.GoodBONG.adjacentProduct
    rw [hvalueZero, hvalueOne]
    simp [beli2009BinaryTransformAt, mul_assoc, mul_left_comm, mul_comm]
  have hfirstBinary : c.firstBinaryAlpha = a.firstBinaryAlpha := by
    have horderZero := horders (0 : Fin 3).castSucc
    have horderOne := horders (0 : Fin 3).succ
    unfold BONG.GoodBONG.firstBinaryAlpha
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [← horderZero, ← horderOne, hfirstProduct, hfirstDefect]
  have hbinaryBound : c.firstBinaryAlpha ≤
      BONG.GoodBONG.defectOrder (K := K) (c.lemma814Epsilon b) := by
    rw [hfirstBinary, hbinary, hepsilon]
    exact a.alpha_le_lemma814EpsilonDefect b conditions
  have hpositive : hilbertSymbol K (c.lemma814Epsilon b)
      (c.adjacentProduct (0 : Fin 3)) = 1 := by
    rw [hepsilon, hfirstProduct, hilbertSymbol_mul_right,
      hilbertSymbol_comm K (a.lemma814Epsilon b) (rho : Kˣ),
      hrhoEpsilon, hepsilonFirst]
    norm_num
  have horder' : c.order (0 : Fin 4) = b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin 4)]
    exact horder
  rcases
      reachablePrescribedFirstValue_rankFour_of_firstBinaryAlpha_le_of_hilbert_one
        c b horder' hbinaryBound hpositive with ⟨T⟩
  exact ⟨{
    transform := {
      transformed := T.transform.transformed
      firstValue_eq := T.transform.firstValue_eq
    }
    reachable := hstep.reachable.trans T.reachable
  }⟩

/-- The large-residue fixed-layer choice supplies the middle flip whenever
the first ternary block is anisotropic and the literal middle binary alpha
is no deeper than the first adjacent defect. -/
theorem reachablePrescribedFirstValue_rankFour_of_anisotropicMiddleNeighbor
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hmiddleLe : a.adjacentBinaryAlpha (1 : Fin 3) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (0 : Fin 3)))
    (hfirstEven : Even (ordUnit K (a.adjacentProduct (0 : Fin 3))))
    (hfirstFinite : quadraticDefect K
      (a.adjacentProduct (0 : Fin 3)) ≠ ⊤)
    (hfirstNonzero : quadraticDefect K
      (a.adjacentProduct (0 : Fin 3)) ≠ 0)
    (hfirstNotTwoE : quadraticDefect K
        (a.adjacentProduct (0 : Fin 3)) ≠
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hsum : quadraticDefect K
          (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 3)) +
        quadraticDefect K (a.adjacentProduct (0 : Fin 3)) ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hepsilonFirst : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 3)) = -1)
    (hfirstMiddle : hilbertSymbol K
      (a.adjacentProduct (0 : Fin 3))
      (a.adjacentProduct (1 : Fin 3)) = -1) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases exists_valuationUnit_anisotropic_detour_neighbor
      hres (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 3))
      (a.adjacentProduct (1 : Fin 3))
      hfirstEven hfirstFinite hfirstNonzero hfirstNotTwoE hsum
      hepsilonFirst hfirstMiddle with
    ⟨rhoRaw, hrhoUnit, hrhoDepthRaw, hrhoProduct,
      hrhoMiddle, hrhoEpsilon⟩
  let rho : valuationUnitSubgroup K := ⟨rhoRaw, hrhoUnit⟩
  have hrhoDepth : a.adjacentBinaryAlpha (1 : Fin 3) ≤
      BONG.GoodBONG.defectOrder (K := K) (rho : Kˣ) :=
    hmiddleLe.trans (by
      simpa only [rho, Subgroup.coe_mk] using hrhoDepthRaw)
  have hpreserve : BONG.GoodBONG.defectOrder (K := K)
        ((rho : Kˣ) * a.adjacentProduct (0 : Fin 3)) =
      BONG.GoodBONG.defectOrder (K := K)
        (a.adjacentProduct (0 : Fin 3)) :=
    defectOrder_eq_of_quadraticDefect_eq _ _ (by
      simpa only [rho, Subgroup.coe_mk] using hrhoProduct)
  exact reachablePrescribedFirstValue_rankFour_of_middleFlip
    a b horder conditions hbinary rho hrhoDepth
      (by simpa only [rho, Subgroup.coe_mk] using hrhoMiddle)
      hpreserve
      (by simpa only [rho, Subgroup.coe_mk] using hrhoEpsilon)
      hepsilonFirst

/-- Normalizing the right endpoint of the initial ternary segment preserves
the already normalized first binary edge.  After reinsertion, the first and
middle literal binary alphas therefore realize the first two ambient alphas.
The last two scalar values are unchanged, a fact used by the subsequent
last-edge preprocessing in the alternating rank-four branch. -/
structure ReachableRankFourInitialThreeRightNormalForm
    (a : BONG.GoodBONG q L 4) where
  transformed : BONG.GoodBONG q L 4
  firstBinaryAlpha_eq : transformed.firstBinaryAlpha =
    (transformed.alphaValue (0 : Fin 3) : WithTop ℚ)
  middleBinaryAlpha_eq : transformed.adjacentBinaryAlpha (1 : Fin 3) =
    (transformed.alphaValue (1 : Fin 3) : WithTop ℚ)
  thirdValue_eq : transformed.valueUnit (2 : Fin 4) =
    a.valueUnit (2 : Fin 4)
  fourthValue_eq : transformed.valueUnit (3 : Fin 4) =
    a.valueUnit (3 : Fin 4)
  reachable : Beli2009BinaryReachable (K := K)
    (fun i ↦ a.valueUnit i) (fun i ↦ transformed.valueUnit i)

/-- Lift the right-endpoint Corollary 8.10 normal form of the initial ternary
segment into an alternating rank-four BONG.  The local last-value equality
fixes the local first literal alpha, while Lemma 4.9(ii) makes the local path
an ambient binary-transformation path. -/
theorem reachableRankFourInitialThreeRightNormalForm_of_largeResidue
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableRankFourInitialThreeRightNormalForm a) := by
  let segment := a.toBONG.segmentWitness 0 3 (by omega)
  let s := segment.toGoodBONG a.good
  rcases reachableCorollary810_right_of_largeResidue s hres with ⟨R⟩
  let c := R.data.transformed
  rcases a.toBONG.beliLemma49_ii a.good segment c.toBONG c.good with
    ⟨replacement⟩
  let changed : BONG.GoodBONG q L 4 :=
    ⟨replacement.bong, replacement.good⟩
  have hlocalLast : c.valueUnit (2 : Fin 3) = s.valueUnit (2 : Fin 3) := by
    simpa [c] using R.data.lastValue_eq
  have hlocalFirst : c.firstBinaryAlpha = s.firstBinaryAlpha :=
    rankThree_firstBinaryAlpha_eq_of_lastValue_eq c s hlocalLast
  have hprefix := BONG.GoodBONG.rankFour_prefixAlphas_eq_of_firstBinaryAlpha
    a segment houter hbinary
  have hlocalAlphas := s.alpha_invariant c
  let p₀ := BONG.GoodBONG.rankFourFirstThreeFirstAlphaLocalization
  let p₁ := BONG.GoodBONG.prefixPairLocalization (N := 2) (1 : Fin 3)
  have hfirstInside : changed.adjacentBinaryAlpha (0 : Fin 3) =
      c.adjacentBinaryAlpha (0 : Fin 2) := by
    have h := a.adjacentBinaryAlpha_eq_of_segmentReplacement
      p₀ segment c replacement
    change changed.adjacentBinaryAlpha p₀.pivotFin =
      c.adjacentBinaryAlpha p₀.localPivot at h
    have hpivot : p₀.pivotFin = (0 : Fin 3) := by
      apply Fin.ext
      rfl
    have hlocal : p₀.localPivot = (0 : Fin 2) := by
      apply Fin.ext
      rfl
    rw [hpivot, hlocal] at h
    exact h
  have hmiddleInside : changed.adjacentBinaryAlpha (1 : Fin 3) =
      c.adjacentBinaryAlpha (1 : Fin 2) := by
    have h := a.adjacentBinaryAlpha_eq_of_segmentReplacement
      p₁ segment c replacement
    change changed.adjacentBinaryAlpha p₁.pivotFin =
      c.adjacentBinaryAlpha p₁.localPivot at h
    have hpivot : p₁.pivotFin = (1 : Fin 3) := by
      apply Fin.ext
      rfl
    have hlocal : p₁.localPivot = (1 : Fin 2) := by
      apply Fin.ext
      rfl
    rw [hpivot, hlocal] at h
    exact h
  have hglobalAlphas := a.alpha_invariant changed
  have hfirst : changed.firstBinaryAlpha =
      (changed.alphaValue (0 : Fin 3) : WithTop ℚ) := by
    calc
      changed.firstBinaryAlpha = c.firstBinaryAlpha := hfirstInside
      _ = s.firstBinaryAlpha := hlocalFirst
      _ = a.firstBinaryAlpha :=
        BONG.GoodBONG.rankFour_firstBinaryAlpha_eq_firstThree a segment
      _ = (a.alphaValue (0 : Fin 3) : WithTop ℚ) := hbinary
      _ = (changed.alphaValue (0 : Fin 3) : WithTop ℚ) :=
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) (hglobalAlphas 0)
  have hmiddle : changed.adjacentBinaryAlpha (1 : Fin 3) =
      (changed.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    calc
      changed.adjacentBinaryAlpha (1 : Fin 3) = c.lastBinaryAlpha :=
        hmiddleInside
      _ = (c.alphaValue (1 : Fin 2) : WithTop ℚ) :=
        R.data.lastBinaryAlpha_eq
      _ = (s.alphaValue (1 : Fin 2) : WithTop ℚ) :=
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) (hlocalAlphas 1).symm
      _ = (a.alphaValue (1 : Fin 3) : WithTop ℚ) :=
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hprefix.2
      _ = (changed.alphaValue (1 : Fin 3) : WithTop ℚ) :=
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) (hglobalAlphas 1)
  have hthirdInside := segmentReplacement_valueUnit_inside
    a segment c replacement (2 : Fin 3)
  have hsThird : s.valueUnit (2 : Fin 3) = a.valueUnit (2 : Fin 4) := by
    change segment.bong.valueUnit 2 = a.toBONG.valueUnit 2
    simp [BONG.SegmentWitness.sourceIndex]
  have hthird : changed.valueUnit (2 : Fin 4) =
      a.valueUnit (2 : Fin 4) := by
    exact hthirdInside.trans (hlocalLast.trans hsThird)
  have hfourth : changed.valueUnit (3 : Fin 4) =
      a.valueUnit (3 : Fin 4) := by
    exact segmentReplacement_valueUnit_after a segment c replacement
      (3 : Fin 4) (by omega)
  have hreachCast := reachable_of_prefixSegmentReplacement
    (n := 4) (M := 2) (S := 1) rfl a segment c replacement R.reachable
  have hreach : Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ changed.valueUnit i) := by
    simpa [changed] using hreachCast
  exact ⟨{
    transformed := changed
    firstBinaryAlpha_eq := hfirst
    middleBinaryAlpha_eq := hmiddle
    thirdValue_eq := hthird
    fourthValue_eq := hfourth
    reachable := hreach
  }⟩

/-- In a doubly alternating quaternary good BONG, the literal last binary
alpha lies below the defect complementary to the middle global alpha.  This
is the precise depth budget needed for a legal last-edge preprocessing move.
-/
theorem rankFour_lastBinaryAlpha_le_complement_secondAlpha_of_alternating
    [Beli2006AlphaLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (halternating : a.HasQuaternaryAlternatingOrders) :
    a.lastBinaryAlpha ≤
      ((2 * (ramificationIndex K : ℚ) -
        a.alphaValue (1 : Fin 3) : ℚ) : WithTop ℚ) := by
  have hfirstHalf := a.alphaValue_le_halfGapValue (0 : Fin 3)
  have hrelation := a.quaternaryAlternating_alpha_one_eq halternating
  have hhalf : a.halfGapValue (2 : Fin 3) ≤
      2 * (ramificationIndex K : ℚ) - a.alphaValue (1 : Fin 3) := by
    unfold BONG.GoodBONG.halfGapValue BONG.GoodBONG.orderGap at hfirstHalf hrelation
    unfold BONG.GoodBONG.halfGapValue BONG.GoodBONG.orderGap
    change a.alphaValue (0 : Fin 3) ≤
      ((a.order (1 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) at hfirstHalf
    change a.alphaValue (1 : Fin 3) =
      ((-(a.order (1 : Fin 4) - a.order (0 : Fin 4) : Int) : Int) : ℚ) +
        a.alphaValue (0 : Fin 3) at hrelation
    change ((a.order (3 : Fin 4) - a.order (2 : Fin 4) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) ≤
      2 * (ramificationIndex K : ℚ) - a.alphaValue (1 : Fin 3)
    rw [← halternating.1, ← halternating.2]
    push_cast at hfirstHalf hrelation ⊢
    linarith
  calc
    a.lastBinaryAlpha ≤ a.halfGapCandidate (2 : Fin 3) := by
      exact min_le_left _ _
    _ = (a.halfGapValue (2 : Fin 3) : WithTop ℚ) := rfl
    _ ≤ ((2 * (ramificationIndex K : ℚ) -
        a.alphaValue (1 : Fin 3) : ℚ) : WithTop ℚ) := by
      exact_mod_cast hhalf

/-- A defect order strictly below the dyadic endpoint cannot have quadratic
defect equal to the endpoint. -/
theorem quadraticDefect_ne_twoE_of_defectOrder_lt_twoE
    (x : Kˣ)
    (h : BONG.GoodBONG.defectOrder (K := K) x <
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) :
    quadraticDefect K x ≠ ((2 * ramificationIndex K : Nat) : ℕ∞) := by
  intro hx
  unfold BONG.GoodBONG.defectOrder at h
  rw [hx] at h
  exact (lt_irrefl _) h

/-- A locally exceptional anisotropic initial ternary block in an alternating
rank-four BONG supplies a legal last-edge multiplier at the complementary
middle-alpha depth.  Large residue degree lets Lemma 8.2(ii) impose the
positive tail Hilbert sign without changing that depth. -/
theorem exists_rankFour_alternating_exceptionA_lastMultiplier
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4)
    (b : BONG.GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (halternating : a.HasQuaternaryAlternatingOrders)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (A : (segment.toGoodBONG a.good).Beli2019Lemma814ExceptionA b)
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    ∃ eta : valuationUnitSubgroup K,
      a.lastBinaryAlpha ≤
          BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) ∧
        BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) =
          ((2 * (ramificationIndex K : ℚ) -
            a.alphaValue (1 : Fin 3) : ℚ) : WithTop ℚ) ∧
        hilbertSymbol K (a.adjacentProduct (2 : Fin 3)) (eta : Kˣ) = 1 := by
  let s := segment.toGoodBONG a.good
  have hprefix := BONG.GoodBONG.rankFour_prefixAlphas_eq_of_firstBinaryAlpha
    a segment halternating.1 hbinary
  have horder₀ : s.order (0 : Fin 3) = a.order (0 : Fin 4) := by
    change segment.bong.order 0 = a.toBONG.order 0
    simp [BONG.SegmentWitness.sourceIndex]
  have horder₂ : s.order (2 : Fin 3) = a.order (2 : Fin 4) := by
    change segment.bong.order 2 = a.toBONG.order 2
    simp [BONG.SegmentWitness.sourceIndex]
  have hlocalOuter : s.order (0 : Fin 3) = s.order (2 : Fin 3) := by
    rw [horder₀, horder₂, halternating.1]
  have hsecondOddLocal :=
    s.secondAlpha_isOddRationalInteger_of_equalOuter_anisotropic
      hlocalOuter A.firstThree_anisotropic
  have hsecondOdd : IsOddRationalInteger (a.alphaValue (1 : Fin 3)) := by
    rw [← hprefix.2]
    exact hsecondOddLocal
  have hsecondNonnegative : 0 ≤ a.alphaValue (1 : Fin 3) :=
    (a.beli2009Lemma27_i (1 : Fin 3)).1
  have hfirstNonnegative : 0 ≤ a.alphaValue (0 : Fin 3) :=
    (a.beli2009Lemma27_i (0 : Fin 3)).1
  have hsum := a.quaternaryAlternating_alphaSum_le_twoE halternating
  have hsecondLe : a.alphaValue (1 : Fin 3) ≤
      2 * (ramificationIndex K : ℚ) := by linarith
  have hsecondNe : a.alphaValue (1 : Fin 3) ≠
      2 * (ramificationIndex K : ℚ) := by
    intro hendpoint
    rcases hsecondOdd with ⟨z, hzOdd, hz⟩
    have hzEndpoint : z = 2 * (ramificationIndex K : Int) := by
      exact_mod_cast hz.symm.trans hendpoint
    rcases hzOdd with ⟨m, hm⟩
    omega
  have hsecondLt : a.alphaValue (1 : Fin 3) <
      2 * (ramificationIndex K : ℚ) :=
    lt_of_le_of_ne hsecondLe hsecondNe
  have hsecondPos : 0 < a.alphaValue (1 : Fin 3) :=
    BONG.GoodBONG.oddRationalInteger_pos_of_nonnegative
      hsecondOdd hsecondNonnegative
  rcases DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      (a.alphaValue (1 : Fin 3)) hsecondOdd hsecondNonnegative hsecondLt with
    ⟨reference, hrefUnit, hrefDefect⟩
  rcases BONG.exists_complementaryDefect_hilbert_neg reference
      (a.alphaValue (1 : Fin 3)) hrefDefect hsecondPos hsecondLt with
    ⟨eta₀, heta₀Unit, heta₀Defect, _heta₀Hilbert⟩
  have hcomplementPos : 0 < 2 * (ramificationIndex K : ℚ) -
      a.alphaValue (1 : Fin 3) := by linarith
  have hcomplementLt : 2 * (ramificationIndex K : ℚ) -
      a.alphaValue (1 : Fin 3) < 2 * (ramificationIndex K : ℚ) := by
    linarith
  have heta₀OrderLt : BONG.GoodBONG.defectOrder (K := K) eta₀ <
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [heta₀Defect]
    exact_mod_cast hcomplementLt
  have heta₀Nonzero : quadraticDefect K eta₀ ≠ 0 :=
    quadraticDefect_ne_zero_of_isValuationUnit eta₀ heta₀Unit
  have heta₀NotTwoE : quadraticDefect K eta₀ ≠
      ((2 * ramificationIndex K : Nat) : ℕ∞) :=
    quadraticDefect_ne_twoE_of_defectOrder_lt_twoE eta₀ heta₀OrderLt
  have hnotPair : ¬BONG.IsZeroTwoEDefectPair
      (K := K) (a.adjacentProduct (2 : Fin 3)) eta₀ := by
    rintro (⟨_, heta₀Endpoint⟩ | ⟨_, heta₀Zero⟩)
    · exact heta₀NotTwoE heta₀Endpoint
    · exact heta₀Nonzero heta₀Zero
  rcases BONG.beli2019Lemma82_ii_unit hres
      (a.adjacentProduct (2 : Fin 3)) eta₀ heta₀Unit hnotPair with
    ⟨etaRaw, hetaUnit, hetaQuadratic, hetaHilbert⟩
  let eta : valuationUnitSubgroup K := ⟨etaRaw, hetaUnit⟩
  have hetaDefect : BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) =
      ((2 * (ramificationIndex K : ℚ) -
        a.alphaValue (1 : Fin 3) : ℚ) : WithTop ℚ) := by
    change BONG.GoodBONG.defectOrder (K := K) etaRaw = _
    exact (BONG.defectOrder_eq_of_quadraticDefect_eq
      etaRaw eta₀ hetaQuadratic).trans heta₀Defect
  refine ⟨eta, ?_, hetaDefect, ?_⟩
  · exact (rankFour_lastBinaryAlpha_le_complement_secondAlpha_of_alternating
      a halternating).trans_eq hetaDefect.symm
  · simpa only [eta, Subgroup.coe_mk] using hetaHilbert

/-- In the alternating rank-four branch, a locally exceptional initial
ternary block is repaired by one legal transformation of the final binary
edge.  Its complementary-depth multiplier lowers the uncapped first-three
defect to `2e - alpha₁`; the new ternary block is therefore nonexceptional
and the complete reachable ternary Lemma 8.14 finishes the construction. -/
theorem reachablePrescribedFirstValue_rankFour_of_alternating_localExceptionA
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (halternating : a.HasQuaternaryAlternatingOrders)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (A : (segment.toGoodBONG a.good).Beli2019Lemma814ExceptionA b)
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases exists_rankFour_alternating_exceptionA_lastMultiplier
      a b segment halternating hbinary A hres with
    ⟨eta, hetaDepth, hetaDefect, hetaHilbert⟩
  have hetaGroup : valuationUnitClassHom K eta ∈
      beliNormGeneratorGroup K
        (a.valueUnit (3 : Fin 4) / a.valueUnit (2 : Fin 4)) := by
    exact valuationUnitClass_mem_normGenerator_of_adjacentAlpha_le_hilbert
      a (2 : Fin 3) eta hetaDepth hetaHilbert
  rcases exists_goodBONG_binaryTransformation_exact a (2 : Fin 3)
      eta hetaGroup with ⟨c, hvalues⟩
  have hstep : IsBeli2009BinaryTransformation (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ c.valueUnit i) :=
    ⟨2, eta, hetaGroup, hvalues⟩
  have hvalue₀ : c.valueUnit (0 : Fin 4) = a.valueUnit (0 : Fin 4) := by
    rw [congrFun hvalues (0 : Fin 4)]
    simp [beli2009BinaryTransformAt]
  have hvalue₁ : c.valueUnit (1 : Fin 4) = a.valueUnit (1 : Fin 4) := by
    rw [congrFun hvalues (1 : Fin 4)]
    simp [beli2009BinaryTransformAt]
  have hvalue₂ : c.valueUnit (2 : Fin 4) =
      (eta : Kˣ) * a.valueUnit (2 : Fin 4) := by
    rw [congrFun hvalues (2 : Fin 4)]
    simp [beli2009BinaryTransformAt]
  have horders := a.order_invariant c
  have halphas := a.alpha_invariant c
  have hfirstProduct : c.adjacentProduct (0 : Fin 3) =
      a.adjacentProduct (0 : Fin 3) := by
    unfold BONG.GoodBONG.adjacentProduct
    change -(c.valueUnit (0 : Fin 4) * c.valueUnit (1 : Fin 4)) =
      -(a.valueUnit (0 : Fin 4) * a.valueUnit (1 : Fin 4))
    rw [hvalue₀, hvalue₁]
  have hfirstBinary : c.firstBinaryAlpha = a.firstBinaryAlpha := by
    have horderZero := horders (0 : Fin 3).castSucc
    have horderOne := horders (0 : Fin 3).succ
    unfold BONG.GoodBONG.firstBinaryAlpha
      BONG.GoodBONG.halfGapCandidate
      BONG.GoodBONG.leftDefectCandidate
      BONG.GoodBONG.adjacentDefect
    rw [← horderZero, ← horderOne, hfirstProduct]
  have hbinary' : c.firstBinaryAlpha =
      (c.alphaValue (0 : Fin 3) : WithTop ℚ) := by
    calc
      c.firstBinaryAlpha = a.firstBinaryAlpha := hfirstBinary
      _ = (a.alphaValue (0 : Fin 3) : WithTop ℚ) := hbinary
      _ = (c.alphaValue (0 : Fin 3) : WithTop ℚ) :=
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) (halphas 0)
  have houter' : c.order (0 : Fin 4) = c.order (2 : Fin 4) := by
    rw [← horders (0 : Fin 4), ← horders (2 : Fin 4)]
    exact halternating.1
  have horder' : c.order (0 : Fin 4) = b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin 4)]
    exact horder
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classification)
    (classificationW := classification) c b horder conditions
  let newSegment := c.toBONG.segmentWitness 0 3 (by omega)
  let s := segment.toGoodBONG a.good
  let new := newSegment.toGoodBONG c.good
  have holdPrefix := BONG.GoodBONG.rankFour_prefixAlphas_eq_of_firstBinaryAlpha
    a segment halternating.1 hbinary
  have hnewPrefix := BONG.GoodBONG.rankFour_prefixAlphas_eq_of_firstBinaryAlpha
    c newSegment houter' hbinary'
  have hprefixProduct : c.prefixProduct 3 =
      (eta : Kˣ) * a.prefixProduct 3 := by
    unfold BONG.GoodBONG.prefixProduct
    rw [c.toBONG.prefixProduct_succ 2 (by omega),
      c.toBONG.prefixProduct_succ 1 (by omega),
      c.toBONG.prefixProduct_succ 0 (by omega),
      a.toBONG.prefixProduct_succ 2 (by omega),
      a.toBONG.prefixProduct_succ 1 (by omega),
      a.toBONG.prefixProduct_succ 0 (by omega)]
    simp only [BONG.prefixProduct_zero, one_mul]
    have hz : (⟨0, by omega⟩ : Fin 4) = (0 : Fin 4) := by
      apply Fin.ext
      rfl
    have ho : (⟨1, by omega⟩ : Fin 4) = (1 : Fin 4) := by
      apply Fin.ext
      rfl
    have ht : (⟨2, by omega⟩ : Fin 4) = (2 : Fin 4) := by
      apply Fin.ext
      rfl
    change c.valueUnit ⟨0, by omega⟩ * c.valueUnit ⟨1, by omega⟩ *
        c.valueUnit ⟨2, by omega⟩ =
      (eta : Kˣ) *
        (a.valueUnit ⟨0, by omega⟩ * a.valueUnit ⟨1, by omega⟩ *
          a.valueUnit ⟨2, by omega⟩)
    rw [hz, ho, ht, hvalue₀, hvalue₁, hvalue₂]
    ac_rfl
  let oldRaw : Kˣ := (-1) * a.prefixProduct 3 * b.prefixProduct 1
  let newRaw : Kˣ := (-1) * c.prefixProduct 3 * b.prefixProduct 1
  have hrawFactor : newRaw = (eta : Kˣ) * oldRaw := by
    dsimp only [newRaw, oldRaw]
    rw [hprefixProduct]
    ac_rfl
  have holdDefect := BONG.GoodBONG.rankFour_firstThreeDefect_eq_raw
    a b segment
  have holdStrict :
      (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) <
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
          BONG.GoodBONG.defectOrder (K := K) oldRaw := by
    simpa only [s, oldRaw, holdPrefix.2, holdDefect] using A.defectSum_strict
  have hcomplementTop :
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
          ((2 * (ramificationIndex K : ℚ) -
            a.alphaValue (1 : Fin 3) : ℚ) : WithTop ℚ) =
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) := by
    exact_mod_cast (show a.alphaValue (1 : Fin 3) +
      (2 * (ramificationIndex K : ℚ) - a.alphaValue (1 : Fin 3)) =
        2 * (ramificationIndex K : ℚ) by ring)
  have hcomplementLtOld :
      ((2 * (ramificationIndex K : ℚ) -
        a.alphaValue (1 : Fin 3) : ℚ) : WithTop ℚ) <
        BONG.GoodBONG.defectOrder (K := K) oldRaw := by
    apply (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp
    rw [hcomplementTop]
    exact holdStrict
  have hnewRawDefect : BONG.GoodBONG.defectOrder (K := K) newRaw =
      ((2 * (ramificationIndex K : ℚ) -
        a.alphaValue (1 : Fin 3) : ℚ) : WithTop ℚ) := by
    rw [hrawFactor,
      BONG.GoodBONG.defectOrder_mul_eq_left_of_lt_right
        (hetaDefect ▸ hcomplementLtOld), hetaDefect]
  have hnewDefect : new.lemma814FirstThirdCappedDefect b =
      ((2 * (ramificationIndex K : ℚ) -
        a.alphaValue (1 : Fin 3) : ℚ) : WithTop ℚ) := by
    rw [BONG.GoodBONG.rankFour_firstThreeDefect_eq_raw c b newSegment]
    exact hnewRawDefect
  have hnewSum :
      (new.alphaValue (1 : Fin 2) : WithTop ℚ) +
          new.lemma814FirstThirdCappedDefect b =
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) := by
    rw [hnewDefect, hnewPrefix.2, ← halphas (1 : Fin 3)]
    exact hcomplementTop
  have hnotNew : ¬new.Beli2019Lemma814Exceptional b := by
    rintro (A' | B' | C')
    · exact (ne_of_gt A'.defectSum_strict) hnewSum
    · exact B'.residueTwo hres
    · exact BONG.GoodBONG.not_lemma814ExceptionC_of_rank_three new b C'
  have hnewConditions :=
    BONG.GoodBONG.rankFour_firstThreeConditions_of_prefixAlphas
      c b newSegment houter' hnewPrefix hconditions hnotNew
  rcases reachableLemma814_of_safeFirstThreeSegment_of_ambientOrder
      c b newSegment horder' hnewConditions hnotNew hres with ⟨T⟩
  exact ⟨{
    transform := {
      transformed := T.transform.transformed
      firstValue_eq := T.transform.firstValue_eq
    }
    reachable := hstep.reachable.trans T.reachable
  }⟩

/-- Complete normalized doubly alternating rank-four endpoint.  The initial
ternary segment is either already nonexceptional, or its only possible
exception over a residue field of cardinality greater than two is exception
A; the latter is removed by the complementary-depth last-edge move above. -/
theorem reachablePrescribedFirstValue_rankFour_alternating_of_firstBinaryAlpha
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (halternating : a.HasQuaternaryAlternatingOrders)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  let segment := a.toBONG.segmentWitness 0 3 (by omega)
  have hprefix := BONG.GoodBONG.rankFour_prefixAlphas_eq_of_firstBinaryAlpha
    a segment halternating.1 hbinary
  by_cases hnotLocal :
      ¬(segment.toGoodBONG a.good).Beli2019Lemma814Exceptional b
  · have hlocalConditions :=
      BONG.GoodBONG.rankFour_firstThreeConditions_of_prefixAlphas
        a b segment halternating.1 hprefix conditions hnotLocal
    exact reachableLemma814_of_safeFirstThreeSegment_of_ambientOrder
      a b segment horder hlocalConditions hnotLocal hres
  · have hlocal :
        (segment.toGoodBONG a.good).Beli2019Lemma814Exceptional b :=
      Classical.byContradiction hnotLocal
    rcases hlocal with A | B | C
    · exact
        reachablePrescribedFirstValue_rankFour_of_alternating_localExceptionA
          a b segment horder conditions halternating hbinary A hres
    · exact False.elim (B.residueTwo hres)
    · exact False.elim
        (BONG.GoodBONG.not_lemma814ExceptionC_of_rank_three
          (segment.toGoodBONG a.good) b C)

/-- Complete path-refined doubly alternating rank-four endpoint.  Corollary
8.10 first normalizes the literal first binary alpha; order invariance keeps
the alternating pattern, after which the normalized theorem applies. -/
theorem reachablePrescribedFirstValue_rankFour_alternating
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (halternating : a.HasQuaternaryAlternatingOrders)
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases reachableCorollary810_of_largeResidue a hres with ⟨C⟩
  let changed := C.data.transformed
  have horders := a.order_invariant changed
  have horder' : changed.order (0 : Fin 4) = b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin 4)]
    exact horder
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classification)
    (classificationW := classification) changed b horder conditions
  have halternating' : changed.HasQuaternaryAlternatingOrders := by
    constructor
    · rw [← horders (0 : Fin 4), ← horders (2 : Fin 4)]
      exact halternating.1
    · rw [← horders (1 : Fin 4), ← horders (3 : Fin 4)]
      exact halternating.2
  rcases
      reachablePrescribedFirstValue_rankFour_alternating_of_firstBinaryAlpha
        changed b horder' hconditions halternating'
          C.data.firstBinaryAlpha_eq hres with ⟨T⟩
  exact ⟨{
    transform := {
      transformed := T.transform.transformed
      firstValue_eq := T.transform.firstValue_eq
    }
    reachable := C.reachable.trans T.reachable
  }⟩

/-! ## Path-refined unequal-outer normal forms -/

/-- Reduction (II) in the unequal-outer proof, augmented by the complete
binary path from the original ambient BONG. -/
structure ReachableLemma814SecondNormalForm
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    {N : Nat} (a : BONG.GoodBONG q L (N + 4))
    (b : BONG.GoodBONG r M 1) where
  data : a.Beli2019Lemma814SecondNormalForm b
  reachable : Beli2009BinaryReachable (K := K)
    (fun i ↦ a.valueUnit i) (fun i ↦ data.transformed.valueUnit i)

/-- Corollary 8.10 on the projected tail, lifted by `Fin.cons`, gives the
path-refined second normal form. -/
theorem reachableLemma814SecondNormalForm_of_largeResidue
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 4))
    (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 4)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ))
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableLemma814SecondNormalForm a b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases reachableCorollary810_of_largeResidue a.tail hres with ⟨C⟩
  let changed := a.replaceTailGood C.data.transformed
  have horders := a.order_invariant changed
  have halphas := a.alpha_invariant changed
  have hfirstValue : changed.valueUnit (0 : Fin (N + 4)) =
      a.valueUnit (0 : Fin (N + 4)) := by
    apply Units.ext
    change (a.replaceTailGood C.data.transformed).toBONG.value 0 =
      a.toBONG.value 0
    rw [(a.replaceTailGood C.data.transformed).toBONG.value_zero_eq_quadratic_head,
      a.toBONG.value_zero_eq_quadratic_head, a.replaceTailGood_head]
  have hsecondValue : changed.valueUnit (1 : Fin (N + 4)) =
      a.valueUnit (1 : Fin (N + 4)) := by
    calc
      changed.valueUnit (1 : Fin (N + 4)) =
          changed.tail.valueUnit (0 : Fin (N + 3)) := by
        symm
        simpa using changed.valueUnit_goodTail (0 : Fin (N + 3))
      _ = C.data.transformed.valueUnit (0 : Fin (N + 3)) := by rfl
      _ = a.tail.valueUnit (0 : Fin (N + 3)) := C.data.headValue_eq
      _ = a.valueUnit (1 : Fin (N + 4)) := by
        simpa using a.valueUnit_goodTail (0 : Fin (N + 3))
  have hadjacent : changed.adjacentDefect (0 : Fin (N + 3)) =
      a.adjacentDefect (0 : Fin (N + 3)) := by
    unfold BONG.GoodBONG.adjacentDefect BONG.GoodBONG.adjacentProduct
    rw [show changed.valueUnit (0 : Fin (N + 3)).castSucc =
          a.valueUnit (0 : Fin (N + 3)).castSucc by simpa using hfirstValue,
      show changed.valueUnit (0 : Fin (N + 3)).succ =
          a.valueUnit (0 : Fin (N + 3)).succ by simpa using hsecondValue]
  have hfirstBinarySame : changed.firstBinaryAlpha = a.firstBinaryAlpha := by
    unfold BONG.GoodBONG.firstBinaryAlpha
      BONG.GoodBONG.halfGapCandidate BONG.GoodBONG.leftDefectCandidate
    rw [← horders (0 : Fin (N + 3)).castSucc,
      ← horders (0 : Fin (N + 3)).succ, hadjacent]
  have hbinaryChanged : changed.firstBinaryAlpha =
      (changed.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := by
    calc
      changed.firstBinaryAlpha = a.firstBinaryAlpha := hfirstBinarySame
      _ = (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := hbinary
      _ = (changed.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) :=
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) (halphas 0)
  have htailChanged : changed.tail.firstBinaryAlpha =
      (changed.tail.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
    change C.data.transformed.firstBinaryAlpha =
      (C.data.transformed.alphaValue (0 : Fin (N + 2)) : WithTop ℚ)
    exact C.data.firstBinaryAlpha_eq
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classificationV)
    (classificationW := classificationW) changed b horder conditions
  have hinvariant := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) changed b
  let D : a.Beli2019Lemma814SecondNormalForm b := {
    transformed := changed
    firstOrder_eq := by
      rw [← horders (0 : Fin (N + 4))]
      exact horder
    firstBinaryAlpha_eq := hbinaryChanged
    tailFirstBinaryAlpha_eq := htailChanged
    initialThreeFirstAlpha_eq :=
      changed.lemma814InitialThree_firstAlpha_eq hbinaryChanged
    initialThreeSecondAlpha_eq :=
      changed.lemma814InitialThree_secondAlpha_eq_of_tailFirstBinaryAlpha
        htailChanged
    conditions := hconditions
    notExceptional := fun E ↦ hnotExceptional (hinvariant.mpr E)
  }
  have hlift := Beli2009BinaryReachable.cons
    (a.valueUnit (0 : Fin (N + 4))) C.reachable
  rw [cons_tailValues_eq a] at hlift
  have htarget :
      Fin.cons (a.valueUnit (0 : Fin (N + 4)))
          (fun i ↦ C.data.transformed.valueUnit i) =
        (fun i ↦ changed.valueUnit i) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact hfirstValue.symm
    · apply Units.ext
      change C.data.transformed.toBONG.value j = changed.toBONG.value j.succ
      rw [← changed.toBONG.value_tail j]
      rfl
  rw [htarget] at hlift
  exact ⟨⟨D, hlift⟩⟩

/-- Direct path-refined unequal-outer subcase: once the uncapped first-three
defect is no larger than the third alpha, the initial ternary theorem applies
and Lemma 4.9(ii) lifts its path. -/
theorem reachableLemma814_higherRankUnequal_of_raw_le_thirdAlpha
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 4))
    (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 4)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ))
    (hbound : a.Lemma814UnequalOuterBound b)
    (hraw : BONG.GoodBONG.defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * b.prefixProduct 1) ≤
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ))
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  have halpha := a.lemma814InitialThree_firstAlpha_eq hbinary
  have hrawBound := a.lemma814InitialThreeRawBound_of_raw_le_thirdAlpha
    b hbound hraw
  have hlocalBound := a.lemma814InitialThree_unequalOuterBound
    b halpha hbound.1 hrawBound
  have hconditions := a.lemma814InitialThree_conditions_of_unequalOuterBound
    b halpha conditions hlocalBound
  have hnotExceptional :=
    a.lemma814InitialThree_notExceptional_of_unequalOuterBound b hlocalBound
  exact reachableLemma814_of_safeFirstThreeSegment_of_ambientOrder
    a b a.lemma814InitialThreeSegment horder hconditions hnotExceptional hres

/-- Third-adjacent Corollary 8.11 normal form together with the actual
ambient adjacent-binary path. -/
structure ReachableLemma814ThirdAdjacentNormalForm
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    {N : Nat} (a : BONG.GoodBONG q L (N + 4))
    (b : BONG.GoodBONG r M 1) where
  data : a.Beli2019Lemma814ThirdAdjacentNormalForm b
  reachable : Beli2009BinaryReachable (K := K)
    (fun i ↦ a.valueUnit i) (fun i ↦ data.transformed.valueUnit i)

theorem reachableLemma814ThirdAdjacentNormalForm_of_largeResidue
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 4))
    (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 4)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (hfirst : a.lemma814InitialThree.alphaValue (0 : Fin 2) =
      a.alphaValue (0 : Fin (N + 3)))
    (hsecond : a.lemma814InitialThree.alphaValue (1 : Fin 2) =
      a.alphaValue (1 : Fin (N + 3)))
    (houter : a.order (0 : Fin (N + 4)) <
      a.order (2 : Fin (N + 4)))
    (hraw : (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) <
      BONG.GoodBONG.defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * b.prefixProduct 1))
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableLemma814ThirdAdjacentNormalForm a b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  have hstrict :=
    a.lemma814_firstEndpoint_strict_of_thirdAlpha_lt_rawDefect b conditions
      hfirst hsecond houter hraw
  rcases reachableCorollary811_of_largeResidue a
      (2 : Fin (N + 3)) hres with ⟨C⟩
  let changed := C.data.transformed
  have horders := a.order_invariant changed
  have halphas := a.alpha_invariant changed
  have hstrict' :
      (changed.order (0 : Fin (N + 4)) : ℚ) +
          changed.alphaValue (0 : Fin (N + 3)) <
        (changed.order (1 : Fin (N + 4)) : ℚ) +
          changed.alphaValue (1 : Fin (N + 3)) := by
    rw [← horders (0 : Fin (N + 4)), ← halphas (0 : Fin (N + 3)),
      ← horders (1 : Fin (N + 4)), ← halphas (1 : Fin (N + 3))]
    exact hstrict
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classificationV)
    (classificationW := classificationW) changed b horder conditions
  have hinvariant := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) changed b
  exact ⟨{
    data := {
      transformed := changed
      firstOrder_eq := by
        rw [← horders (0 : Fin (N + 4))]
        exact horder
      firstBinaryAlpha_eq :=
        changed.firstBinaryAlpha_eq_alpha_of_firstEndpoint_strict hstrict'
      thirdBinaryAlpha_eq := C.data.adjacentBinaryAlpha_eq
      outer_lt := by
        rw [← horders (0 : Fin (N + 4)),
          ← horders (2 : Fin (N + 4))]
        exact houter
      firstEndpoint_strict := hstrict'
      conditions := hconditions
      notExceptional := fun E ↦ hnotExceptional (hinvariant.mpr E)
    }
    reachable := C.reachable
  }⟩

/-- A suffix scaling in the unequal-outer argument, retaining its lifted
ambient binary path. -/
structure ReachableLemma814UnequalTailScalingData
    {N : Nat} (a : BONG.GoodBONG q L (N + 4)) where
  data : a.Beli2019Lemma814UnequalTailScalingData
  reachable : Beli2009BinaryReachable (K := K)
    (fun i ↦ a.valueUnit i) (fun i ↦ data.transformed.valueUnit i)

/-- In the strict third-alpha branch, path-refined Lemma 8.8 on the suffix
and Lemma 4.9(ii) produce the required ambient tail scaling. -/
theorem reachableLemma814UnequalTailScalingData_of_thirdAlpha_lt_halfGap
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 4))
    (hbinary : a.adjacentBinaryAlpha (2 : Fin (N + 3)) =
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ))
    (hstrict : a.alphaValue (2 : Fin (N + 3)) <
      a.halfGapValue (2 : Fin (N + 3)))
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableLemma814UnequalTailScalingData a) := by
  have halpha := a.lemma814UnequalTail_alpha_zero_eq_thirdAlpha hbinary
  have hhalf := a.lemma814UnequalTail_halfGapValue_zero_eq
  have htailStrict : a.lemma814UnequalTail.alphaValue (0 : Fin (N + 1)) <
      a.lemma814UnequalTail.halfGapValue (0 : Fin (N + 1)) := by
    rw [halpha, hhalf]
    exact hstrict
  have htailNotExceptional :
      ¬a.lemma814UnequalTail.Beli2019Lemma88Exceptional := by
    rintro ⟨hattains, _⟩
    exact (ne_of_lt htailStrict) hattains
  rcases reachableLemma88_sufficiency_of_largeResidue
      a.lemma814UnequalTail htailNotExceptional hres with ⟨T⟩
  rcases a.toBONG.beliLemma49_ii a.good a.lemma814UnequalTailSegment
      T.transform.transformed.toBONG T.transform.transformed.good with
    ⟨replacement⟩
  let transformed : BONG.GoodBONG q L (N + 4) :=
    ⟨replacement.bong, replacement.good⟩
  have beforeValue_eq (i : Fin (N + 4)) (hi : i.1 < 2) :
      transformed.valueUnit i = a.valueUnit i := by
    apply Units.ext
    change replacement.bong.value i = a.toBONG.value i
    rw [← replacement.bong.quadratic_ambientVector,
      ← a.toBONG.quadratic_ambientVector]
    exact congrArg q.quadratic (replacement.before_eq i hi)
  have hthirdLocal : transformed.valueUnit (2 : Fin (N + 4)) =
      T.transform.transformed.valueUnit (0 : Fin (N + 2)) := by
    apply Units.ext
    change replacement.bong.value 2 = T.transform.transformed.toBONG.value 0
    rw [← replacement.bong.quadratic_ambientVector,
      ← T.transform.transformed.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector 2) =
      q.quadratic (T.transform.transformed.toBONG.ambientVector 0 : V)
    exact congrArg q.quadratic (replacement.inside_eq (0 : Fin (N + 2)))
  have htailFirst : a.lemma814UnequalTail.valueUnit (0 : Fin (N + 2)) =
      a.valueUnit (2 : Fin (N + 4)) := by
    have h := a.lemma814UnequalTail_valueUnit_eq (0 : Fin (N + 2))
    convert h using 1
    congr 1
  let D : a.Beli2019Lemma814UnequalTailScalingData := {
    epsilon := T.transform.epsilon
    epsilon_isValuationUnit := T.transform.epsilon_isValuationUnit
    epsilon_defect := T.transform.epsilon_defect.trans <|
      congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) halpha
    transformed := transformed
    firstValue_eq := beforeValue_eq (0 : Fin (N + 4)) (by simp)
    secondValue_eq := beforeValue_eq (1 : Fin (N + 4)) (by simp)
    thirdValue_eq := hthirdLocal.trans <| T.transform.firstValue_eq.trans <|
      congrArg (T.transform.epsilon * ·) htailFirst
  }
  have hglobal := reachable_of_suffixSegmentReplacement
    (n := N + 4) (P := 2) (M := N + 1) (by omega)
      a a.lemma814UnequalTailSegment T.transform.transformed replacement
        T.reachable
  have hreindexed := Beli2009BinaryReachable.castLength
    (show 2 + (N + 1) = N + 3 by omega) hglobal
  have hreach : Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ D.transformed.valueUnit i) := by
    simpa [D, transformed] using hreindexed
  exact ⟨⟨D, hreach⟩⟩

/-- On the half-gap boundary, a nonexceptional binary pair `[a₃,a₄]`
supplies the same reachable ambient suffix scaling. -/
theorem reachableLemma814UnequalTailScalingData_of_thirdPair_notExceptional
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 4))
    (hbinary : a.adjacentBinaryAlpha (2 : Fin (N + 3)) =
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ))
    (hboundary : a.alphaValue (2 : Fin (N + 3)) =
      a.halfGapValue (2 : Fin (N + 3)))
    (hnotExceptional :
      ¬a.lemma814UnequalThirdPair.Beli2019Lemma88Exceptional)
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachableLemma814UnequalTailScalingData a) := by
  have halphaPair := a.lemma814UnequalThirdPair_alpha_eq_thirdAlpha hbinary
  have hpairHalf : a.lemma814UnequalThirdPair.AttainsHalfGap (0 : Fin 1) := by
    unfold BONG.GoodBONG.AttainsHalfGap
    rw [halphaPair, a.lemma814UnequalThirdPair_halfGap_eq]
    exact hboundary
  have hpairUnit : BONG.GoodBONG.IsValuationUnitDefect (K := K)
      (a.lemma814UnequalThirdPair.alphaValue (0 : Fin 1)) := by
    by_contra hA
    exact hnotExceptional ⟨hpairHalf, Or.inl hA⟩
  have halpha := a.lemma814UnequalTail_alpha_zero_eq_thirdAlpha hbinary
  have htailUnit : BONG.GoodBONG.IsValuationUnitDefect (K := K)
      (a.lemma814UnequalTail.alphaValue (0 : Fin (N + 1))) := by
    rw [halpha, ← halphaPair]
    exact hpairUnit
  have htailNotExceptional :
      ¬a.lemma814UnequalTail.Beli2019Lemma88Exceptional := by
    rintro ⟨_, hA | hB | hC⟩
    · exact hA htailUnit
    · rcases hB with ⟨B⟩
      exact B.residueTwo hres
    · rcases hC with ⟨C⟩
      exact C.residueTwo hres
  rcases reachableLemma88_sufficiency_of_largeResidue
      a.lemma814UnequalTail htailNotExceptional hres with ⟨T⟩
  rcases a.toBONG.beliLemma49_ii a.good a.lemma814UnequalTailSegment
      T.transform.transformed.toBONG T.transform.transformed.good with
    ⟨replacement⟩
  let transformed : BONG.GoodBONG q L (N + 4) :=
    ⟨replacement.bong, replacement.good⟩
  have beforeValue_eq (i : Fin (N + 4)) (hi : i.1 < 2) :
      transformed.valueUnit i = a.valueUnit i := by
    apply Units.ext
    change replacement.bong.value i = a.toBONG.value i
    rw [← replacement.bong.quadratic_ambientVector,
      ← a.toBONG.quadratic_ambientVector]
    exact congrArg q.quadratic (replacement.before_eq i hi)
  have hthirdLocal : transformed.valueUnit (2 : Fin (N + 4)) =
      T.transform.transformed.valueUnit (0 : Fin (N + 2)) := by
    apply Units.ext
    change replacement.bong.value 2 = T.transform.transformed.toBONG.value 0
    rw [← replacement.bong.quadratic_ambientVector,
      ← T.transform.transformed.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector 2) =
      q.quadratic (T.transform.transformed.toBONG.ambientVector 0 : V)
    exact congrArg q.quadratic (replacement.inside_eq (0 : Fin (N + 2)))
  have htailFirst : a.lemma814UnequalTail.valueUnit (0 : Fin (N + 2)) =
      a.valueUnit (2 : Fin (N + 4)) := by
    have h := a.lemma814UnequalTail_valueUnit_eq (0 : Fin (N + 2))
    convert h using 1
    congr 1
  let D : a.Beli2019Lemma814UnequalTailScalingData := {
    epsilon := T.transform.epsilon
    epsilon_isValuationUnit := T.transform.epsilon_isValuationUnit
    epsilon_defect := T.transform.epsilon_defect.trans <|
      congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) halpha
    transformed := transformed
    firstValue_eq := beforeValue_eq (0 : Fin (N + 4)) (by simp)
    secondValue_eq := beforeValue_eq (1 : Fin (N + 4)) (by simp)
    thirdValue_eq := hthirdLocal.trans <| T.transform.firstValue_eq.trans <|
      congrArg (T.transform.epsilon * ·) htailFirst
  }
  have hglobal := reachable_of_suffixSegmentReplacement
    (n := N + 4) (P := 2) (M := N + 1) (by omega)
      a a.lemma814UnequalTailSegment T.transform.transformed replacement
        T.reachable
  have hreindexed := Beli2009BinaryReachable.castLength
    (show 2 + (N + 1) = N + 3 by omega) hglobal
  have hreach : Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ D.transformed.valueUnit i) := by
    simpa [D, transformed] using hreindexed
  exact ⟨⟨D, hreach⟩⟩

/-- Any reachable suffix scaling whose multiplier has third-alpha defect
reduces the raw first-three defect to the direct ternary range. -/
theorem reachableLemma814_higherRankUnequal_of_tailScalingData
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 4))
    (b : BONG.GoodBONG r M 1)
    (H : a.Beli2019Lemma814UnequalHardData b)
    (D : ReachableLemma814UnequalTailScalingData
      H.normalForm.transformed)
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachablePrescribedFirstValueTransform
      H.normalForm.transformed b) := by
  let c := H.normalForm.transformed
  let changed := D.data.transformed
  have horders := c.order_invariant changed
  have halphas := c.alpha_invariant changed
  have horder' : changed.order (0 : Fin (N + 4)) =
      b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin (N + 4))]
    exact H.normalForm.firstOrder_eq
  have hstrictEndpoint :
      (changed.order (0 : Fin (N + 4)) : ℚ) +
          changed.alphaValue (0 : Fin (N + 3)) <
        (changed.order (1 : Fin (N + 4)) : ℚ) +
          changed.alphaValue (1 : Fin (N + 3)) := by
    rw [← horders (0 : Fin (N + 4)),
      ← halphas (0 : Fin (N + 3)),
      ← horders (1 : Fin (N + 4)),
      ← halphas (1 : Fin (N + 3))]
    exact H.normalForm.firstEndpoint_strict
  have hbinary :=
    changed.firstBinaryAlpha_eq_alpha_of_firstEndpoint_strict hstrictEndpoint
  have hconditions := c.lemma813Conditions_changeTargetBONG
    (classificationV := classification)
    (classificationW := classification) changed b
      H.normalForm.firstOrder_eq H.normalForm.conditions
  have hepsilon : changed.lemma814Epsilon b = c.lemma814Epsilon b := by
    unfold BONG.GoodBONG.lemma814Epsilon
    rw [D.data.firstValue_eq]
  have hadjacent : changed.adjacentProduct (0 : Fin (N + 3)) =
      c.adjacentProduct (0 : Fin (N + 3)) := by
    unfold BONG.GoodBONG.adjacentProduct
    have hfirst : changed.valueUnit (0 : Fin (N + 3)).castSucc =
        c.valueUnit (0 : Fin (N + 3)).castSucc := by
      change D.data.transformed.valueUnit (0 : Fin (N + 3)).castSucc =
        c.valueUnit (0 : Fin (N + 3)).castSucc
      convert D.data.firstValue_eq using 1 <;> congr 1
    have hsecond : changed.valueUnit (0 : Fin (N + 3)).succ =
        c.valueUnit (0 : Fin (N + 3)).succ := by
      change D.data.transformed.valueUnit (0 : Fin (N + 3)).succ =
        c.valueUnit (0 : Fin (N + 3)).succ
      convert D.data.secondValue_eq using 1 <;> congr 1
    rw [hfirst, hsecond]
  have hhilbert : hilbertSymbol K (changed.lemma814Epsilon b)
      (changed.adjacentProduct (0 : Fin (N + 3))) = -1 := by
    rw [hepsilon, hadjacent]
    exact H.hilbert_neg_one
  have houter : changed.order (0 : Fin (N + 4)) <
      changed.order (2 : Fin (N + 4)) := by
    rw [← horders (0 : Fin (N + 4)),
      ← horders (2 : Fin (N + 4))]
    exact H.normalForm.outer_lt
  have hbound : changed.Lemma814UnequalOuterBound b := by
    rcases changed.lemma814_outerCases_of_hilbert_neg_one b hconditions
        hhilbert with houterEq | hbound
    · exact (ne_of_lt houter houterEq).elim
    · exact hbound
  have hrawOld :=
    D.data.firstThreeRawDefect_eq_thirdAlpha_of_old_gt b
      H.thirdAlpha_lt_rawDefect
  have hraw : BONG.GoodBONG.defectOrder (K := K)
        ((-1) * changed.prefixProduct 3 * b.prefixProduct 1) =
      (changed.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) := by
    calc
      BONG.GoodBONG.defectOrder (K := K)
          ((-1) * changed.prefixProduct 3 * b.prefixProduct 1) =
          (c.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) := hrawOld
      _ = (changed.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) :=
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ))
          (halphas (2 : Fin (N + 3)))
  rcases reachableLemma814_higherRankUnequal_of_raw_le_thirdAlpha
      changed b horder' hconditions hbinary hbound hraw.le hres with ⟨T⟩
  exact ⟨{
    transform := {
      transformed := T.transform.transformed
      firstValue_eq := T.transform.firstValue_eq
    }
    reachable := D.reachable.trans T.reachable
  }⟩

/-- Over a residue field with more than two elements the hard unequal-outer
normal form always has a reachable suffix scaling.  The only residual binary
boundary exception would force the residue field to have two elements. -/
theorem reachableLemma814_higherRankUnequal_hard_of_largeResidue
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 4))
    (b : BONG.GoodBONG r M 1)
    (H : a.Beli2019Lemma814UnequalHardData b)
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachablePrescribedFirstValueTransform
      H.normalForm.transformed b) := by
  let c := H.normalForm.transformed
  rcases lt_or_eq_of_le
      (c.alphaValue_le_halfGapValue (2 : Fin (N + 3))) with
    hstrict | hboundary
  · rcases
        reachableLemma814UnequalTailScalingData_of_thirdAlpha_lt_halfGap
          c H.normalForm.thirdBinaryAlpha_eq hstrict hres with ⟨D⟩
    exact reachableLemma814_higherRankUnequal_of_tailScalingData
      a b H D hres
  · by_cases hpair :
        c.lemma814UnequalThirdPair.Beli2019Lemma88Exceptional
    · let E : a.Beli2019Lemma814UnequalBoundaryExceptionalData b := {
        hardData := H
        thirdAlpha_eq_halfGap := hboundary
        thirdPairExceptional := hpair
      }
      have P : BONG.GoodBONG.Beli2019Lemma814UnequalPairExceptionData c := by
        simpa only [E, c] using
          BONG.GoodBONG.lemma814UnequalBoundary_pairExceptionData a b E
      exact False.elim (P.residueTwo hres)
    · rcases
          reachableLemma814UnequalTailScalingData_of_thirdPair_notExceptional
            c H.normalForm.thirdBinaryAlpha_eq hboundary hpair hres with ⟨D⟩
      exact reachableLemma814_higherRankUnequal_of_tailScalingData
        a b H D hres

/-- Complete path-refined `R₁ < R₃` branch of Lemma 8.14 over a residue
field with more than two elements.  Both Corollary normalizations and every
suffix scaling are retained in the resulting binary path. -/
theorem reachableLemma814_higherRankUnequal_of_largeResidue
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 4))
    (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 4)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (houter : a.order (0 : Fin (N + 4)) <
      a.order (2 : Fin (N + 4)))
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases reachableLemma814FirstNormalForm_of_largeResidue
      (classificationV := classification) (classificationW := classification)
      (prefixChangeV := prefixChange) (prefixChangeW := prefixChange)
      a b horder conditions hnotExceptional hres with ⟨F⟩
  let c := F.data.transformed
  have hordersAC := a.order_invariant c
  have houterC : c.order (0 : Fin (N + 4)) <
      c.order (2 : Fin (N + 4)) := by
    rw [← hordersAC (0 : Fin (N + 4)),
      ← hordersAC (2 : Fin (N + 4))]
    exact houter
  rcases reachableLemma814SecondNormalForm_of_largeResidue
      (classificationV := classification) (classificationW := classification)
      (prefixChangeV := prefixChange) (prefixChangeW := prefixChange)
      c b F.data.firstOrder_eq F.data.conditions
        F.data.firstBinaryAlpha_eq F.data.notExceptional hres with ⟨S⟩
  let d := S.data.transformed
  have hordersCD := c.order_invariant d
  have houterD : d.order (0 : Fin (N + 4)) <
      d.order (2 : Fin (N + 4)) := by
    rw [← hordersCD (0 : Fin (N + 4)),
      ← hordersCD (2 : Fin (N + 4))]
    exact houterC
  have hprefix : Beli2009BinaryReachable (K := K)
      (fun i ↦ a.valueUnit i) (fun i ↦ d.valueUnit i) :=
    F.reachable.trans S.reachable
  rcases Int.units_eq_one_or
      (hilbertSymbol K (d.lemma814Epsilon b)
        (d.adjacentProduct (0 : Fin (N + 3)))) with hone | hneg
  · rcases reachableLemma814_binaryBranch d b S.data.firstOrder_eq
        S.data.conditions S.data.firstBinaryAlpha_eq hone with ⟨T⟩
    exact ⟨{
      transform := {
        transformed := T.transform.transformed
        firstValue_eq := T.transform.firstValue_eq
      }
      reachable := hprefix.trans T.reachable
    }⟩
  · rcases d.lemma814_outerCases_of_hilbert_neg_one b S.data.conditions
        hneg with houterEq | hbound
    · exact False.elim ((ne_of_lt houterD) houterEq)
    · by_cases hraw : BONG.GoodBONG.defectOrder (K := K)
          ((-1) * d.prefixProduct 3 * b.prefixProduct 1) ≤
        (d.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)
      · rcases reachableLemma814_higherRankUnequal_of_raw_le_thirdAlpha
            d b S.data.firstOrder_eq S.data.conditions
              S.data.firstBinaryAlpha_eq hbound hraw hres with ⟨T⟩
        exact ⟨{
          transform := {
            transformed := T.transform.transformed
            firstValue_eq := T.transform.firstValue_eq
          }
          reachable := hprefix.trans T.reachable
        }⟩
      · have hrawStrict :
            (d.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) <
              BONG.GoodBONG.defectOrder (K := K)
                ((-1) * d.prefixProduct 3 * b.prefixProduct 1) :=
          lt_of_not_ge hraw
        rcases reachableLemma814ThirdAdjacentNormalForm_of_largeResidue
            (classificationV := classification)
            (classificationW := classification)
            (prefixChangeV := prefixChange) (prefixChangeW := prefixChange)
            d b S.data.firstOrder_eq S.data.conditions S.data.notExceptional
              S.data.initialThreeFirstAlpha_eq
              S.data.initialThreeSecondAlpha_eq houterD hrawStrict hres with ⟨U⟩
        let e := U.data.transformed
        have hthrough : Beli2009BinaryReachable (K := K)
            (fun i ↦ a.valueUnit i) (fun i ↦ e.valueUnit i) :=
          hprefix.trans U.reachable
        rcases Int.units_eq_one_or
            (hilbertSymbol K (e.lemma814Epsilon b)
              (e.adjacentProduct (0 : Fin (N + 3)))) with hone' | hneg'
        · rcases reachableLemma814_binaryBranch e b U.data.firstOrder_eq
              U.data.conditions U.data.firstBinaryAlpha_eq hone' with ⟨T⟩
          exact ⟨{
            transform := {
              transformed := T.transform.transformed
              firstValue_eq := T.transform.firstValue_eq
            }
            reachable := hthrough.trans T.reachable
          }⟩
        · rcases e.lemma814_outerCases_of_hilbert_neg_one b
              U.data.conditions hneg' with houterEq' | hbound'
          · exact False.elim ((ne_of_lt U.data.outer_lt) houterEq')
          · by_cases hraw' : BONG.GoodBONG.defectOrder (K := K)
                ((-1) * e.prefixProduct 3 * b.prefixProduct 1) ≤
              (e.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)
            · rcases
                  reachableLemma814_higherRankUnequal_of_raw_le_thirdAlpha
                    e b U.data.firstOrder_eq U.data.conditions
                      U.data.firstBinaryAlpha_eq hbound' hraw' hres with ⟨T⟩
              exact ⟨{
                transform := {
                  transformed := T.transform.transformed
                  firstValue_eq := T.transform.firstValue_eq
                }
                reachable := hthrough.trans T.reachable
              }⟩
            · let H : d.Beli2019Lemma814UnequalHardData b := {
                normalForm := U.data
                hilbert_neg_one := hneg'
                unequalOuterBound := hbound'
                thirdAlpha_lt_rawDefect := lt_of_not_ge hraw'
              }
              rcases
                  reachableLemma814_higherRankUnequal_hard_of_largeResidue
                    d b H hres with ⟨T⟩
              exact ⟨{
                transform := {
                  transformed := T.transform.transformed
                  firstValue_eq := T.transform.firstValue_eq
                }
                reachable := hthrough.trans T.reachable
              }⟩

/-- Complete path-refined rank-four converse of Lemma 8.14 over a residue
field with more than two elements. -/
theorem reachableLemma814_rankFour_complete_of_largeResidue
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  have houterLe : a.order (0 : Fin 4) ≤ a.order (2 : Fin 4) :=
    a.good (0 : Fin 4) (by omega)
  rcases lt_or_eq_of_le houterLe with houter | houter
  · exact reachableLemma814_higherRankUnequal_of_largeResidue
      a b horder conditions hnotExceptional houter hres
  · have hsecondLe : a.order (1 : Fin 4) ≤ a.order (3 : Fin 4) :=
      a.good (1 : Fin 4) (by omega)
    rcases lt_or_eq_of_le hsecondLe with hsecond | hsecond
    · exact reachableLemma814_rankFour_strictSecondFourth
        a b horder conditions hnotExceptional houter hsecond hres
    · exact reachablePrescribedFirstValue_rankFour_alternating
        a b horder conditions ⟨houter, hsecond⟩ hres

/-- Complete path-refined converse of Lemma 8.14 in every rank at least
five.  Corollary 8.11 localizes the third alpha, after which the initial
quaternary segment satisfies the rank-four hypotheses.  Its local
exceptions (a) and (b) lift to ambient exceptions, while local exception
(c) is impossible over a residue field with more than two elements. -/
theorem reachableLemma814_higherRank_complete_of_largeResidue
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 5))
    (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 5)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  rcases reachableCorollary811_of_largeResidue a
      (⟨2, by omega⟩ : Fin (N + 4)) hres with ⟨C⟩
  let changed := C.data.transformed
  have horders := a.order_invariant changed
  have horder' : changed.order (0 : Fin (N + 5)) =
      b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin (N + 5))]
    exact horder
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classification)
    (classificationW := classification) changed b horder conditions
  have hinvariant := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classification)
    (classificationW := classification)
    (prefixChangeV := prefixChange)
    (prefixChangeW := prefixChange) changed b
  have hnotExceptional' : ¬changed.Beli2019Lemma814Exceptional b :=
    fun E ↦ hnotExceptional (hinvariant.mpr E)
  have hthirdBinary : changed.adjacentBinaryAlpha
      (⟨2, by omega⟩ : Fin (N + 4)) =
        (changed.alphaValue
          (⟨2, by omega⟩ : Fin (N + 4)) : WithTop ℚ) :=
    C.data.adjacentBinaryAlpha_eq
  have hlocalAlphas :=
    changed.lemma814InitialFour_alphas_eq (by omega) hthirdBinary
  have hlocalConditions :=
    changed.lemma814InitialFour_conditions b (by omega)
      hlocalAlphas hconditions
  have hnotAB :=
    changed.lemma814InitialFour_not_exceptionAB b (by omega)
      hlocalAlphas hnotExceptional'
  have hlocalNotExceptional :
      ¬(changed.lemma814InitialFour (by omega)).Beli2019Lemma814Exceptional b := by
    rintro (A | B | D)
    · exact hnotAB.1 A
    · exact hnotAB.2 B
    · exact D.residueTwo hres
  have hlocalOrder : (changed.lemma814InitialFour (by omega)).order
      (0 : Fin 4) = b.order (0 : Fin 1) := by
    rw [changed.lemma814InitialFour_order_eq (by omega)]
    exact horder'
  rcases reachableLemma814_rankFour_complete_of_largeResidue
      (changed.lemma814InitialFour (by omega)) b hlocalOrder
        hlocalConditions hlocalNotExceptional hres with ⟨T⟩
  rcases reachablePrescribedFirstValueTransform_of_firstFourSegment
      changed b (changed.lemma814InitialFourSegment (by omega)) T with ⟨U⟩
  exact ⟨{
    transform := {
      transformed := U.transform.transformed
      firstValue_eq := U.transform.firstValue_eq
    }
    reachable := C.reachable.trans U.reachable
  }⟩

/-- Complete path-refined converse of Lemma 8.14 in every rank at least
three.  The three branches are the ternary theorem, the complete quaternary
theorem, and the uniform higher-rank reduction to the initial quaternary
segment. -/
theorem reachableLemma814_complete_of_largeResidue
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [prefixChange : Beli2006PrefixChangeLaws.{u, v} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFive : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFour : Beli2019SectionFourLaws.{u, v} K]
    [deep : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    {N : Nat} (a : BONG.GoodBONG q L (N + 3))
    (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 3)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) := by
  cases N with
  | zero =>
      exact reachableLemma814_rankThree_of_largeResidue
        hres a b horder conditions hnotExceptional
  | succ N =>
      cases N with
      | zero =>
          exact reachableLemma814_rankFour_complete_of_largeResidue
            a b horder conditions hnotExceptional hres
      | succ N =>
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
            (reachableLemma814_higherRank_complete_of_largeResidue
              (N := N) a b horder conditions hnotExceptional hres)

/-- The residual state after normalizing the first literal binary alpha and
finding that the prescribed multiplier has the negative Hilbert sign.  The
head is unchanged, so the original prescribed first value and all Lemma 8.13
data transport to this state. -/
structure ReachableLemma814FirstHilbertNegativeData
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1) where
  transformed : BONG.GoodBONG q L 4
  headValue_eq : transformed.valueUnit (0 : Fin 4) =
    a.valueUnit (0 : Fin 4)
  firstOrder_eq : transformed.order (0 : Fin 4) = b.order (0 : Fin 1)
  conditions : transformed.Lemma813Conditions b
  firstBinaryAlpha_eq : transformed.firstBinaryAlpha =
    (transformed.alphaValue (0 : Fin 3) : WithTop ℚ)
  epsilonHilbert_neg : hilbertSymbol K (transformed.lemma814Epsilon b)
    (transformed.adjacentProduct (0 : Fin 3)) = -1
  reachable : Beli2009BinaryReachable (K := K)
    (fun i ↦ a.valueUnit i) (fun i ↦ transformed.valueUnit i)

/-- Corollary 8.10 reduces the prescribed-first-value problem to one
adjacent move unless the normalized first binary pair has negative Hilbert
sign.  The latter alternative is retained with the complete path and all
transported hypotheses for the remaining alternating argument. -/
theorem reachablePrescribedFirstValue_or_firstHilbertNegative_of_largeResidue
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty (ReachablePrescribedFirstValueTransform a b) ∨
      Nonempty (ReachableLemma814FirstHilbertNegativeData a b) := by
  rcases reachableCorollary810_of_largeResidue a hres with ⟨C⟩
  let changed := C.data.transformed
  have horders := a.order_invariant changed
  have horder' : changed.order (0 : Fin 4) = b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin 4)]
    exact horder
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classification)
    (classificationW := classification) changed b horder conditions
  rcases Int.units_eq_one_or
      (hilbertSymbol K (changed.lemma814Epsilon b)
        (changed.adjacentProduct (0 : Fin 3))) with hpositive | hnegative
  · left
    rcases reachablePrescribedFirstValue_rankFour_of_firstBinaryAlpha_of_hilbert_one
        changed b horder' hconditions C.data.firstBinaryAlpha_eq hpositive with
      ⟨T⟩
    exact ⟨{
      transform := {
        transformed := T.transform.transformed
        firstValue_eq := T.transform.firstValue_eq
      }
      reachable := C.reachable.trans T.reachable
    }⟩
  · right
    exact ⟨{
      transformed := changed
      headValue_eq := C.data.headValue_eq
      firstOrder_eq := horder'
      conditions := hconditions
      firstBinaryAlpha_eq := C.data.firstBinaryAlpha_eq
      epsilonHilbert_neg := hnegative
      reachable := C.reachable
    }⟩

end Beli2009FinalRemarksProof.LargeResidueConnectivity

end Bong
