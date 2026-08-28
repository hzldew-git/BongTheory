/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716ExceptionalRepresentation
import Bong.Bong.AlternatingEndpointTowerRepresentation
import Bong.Bong.Beli2019Lemma75EndpointClass
import Bong.Bong.BinaryEndpointProduct
import Bong.Bong.DiagonalBinaryRepresentation
import Bong.Dyadic.UnramifiedNorm

/-!
# Beli (2019), Lemma 7.16: the type-I geometric obstruction

The boundary case `s = 2` is the first geometric contradiction in the
paper.  The initial binary source prefix is the norm plane of the
distinguished unramified quadratic extension.  A comparison coefficient
whose order is one larger therefore cannot be represented by it.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L N : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]
variable [laws : DyadicDiscriminantClassLaws K]
variable [DyadicUnramifiedNormLaws K]
variable [HilbertSymbolLaws K]

omit [Beli2006AlphaLaws.{u, v} K] [DyadicUnramifiedNormLaws K]
  [HilbertSymbolLaws K] in
/-- The first signed binary determinant belongs to the distinguished
unramified discriminant square class. -/
theorem lemma716_initialSignedProduct_mul_discriminant_isSquare
    (a : GoodBONG q L (n + 3))
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K))) :
    IsSquare (-(a.valueUnit (0 : Fin (n + 3)) *
      a.valueUnit (1 : Fin (n + 3))) * laws.discriminantUnit) := by
  let first : Kˣ := a.valueUnit (0 : Fin (n + 3))
  let second : Kˣ := a.valueUnit (1 : Fin (n + 3))
  have hclass : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (negativeQuarterUnit K * laws.discriminantUnit) := by
    simpa only [lemma712DiscriminantParameter] using hdiscriminant
  have hparameter :=
    isSquare_neg_mul_discriminant_of_endpointClass hclass
  have hproduct : -(first * second) =
      (-(a.toBONG.adjacentParameter (0 : Fin (n + 3)) (by simp))) *
        first ^ 2 := by
    unfold BONG.adjacentParameter
    apply Units.ext
    simp only [first, second, GoodBONG.valueUnit, Units.val_neg,
      Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero (a.toBONG.valueUnit 0)]
    rfl
  rw [hproduct]
  have hreorder :
      ((-(a.toBONG.adjacentParameter (0 : Fin (n + 3)) (by simp))) *
          first ^ 2) * laws.discriminantUnit =
        (-(a.toBONG.adjacentParameter (0 : Fin (n + 3)) (by simp)) *
          laws.discriminantUnit) * first ^ 2 := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hreorder]
  exact hparameter.mul ⟨first, by simp [pow_two]⟩

omit [Beli2006AlphaLaws.{u, v} K] in
/-- A type-I failure at the minimal endpoint `s = 2` contradicts the odd
valuation of the represented unary coefficient. -/
theorem lemma716_typeI_failureProfile_false_of_two
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int)
    (hfirst : a.order 0 = R)
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (P : Beli2019Lemma716TypeIFailureProfile c R 2 (by omega) (by omega))
    (hrep : DiagonalRepresents
      (c.prefixValues 1 (by omega))
      (a.prefixValues 2 (by omega))) : False := by
  let a₀ : Kˣ := a.valueUnit (0 : Fin (n + 3))
  let a₁ : Kˣ := a.valueUnit (1 : Fin (n + 3))
  let c₀ : Kˣ := c.valueUnit (0 : Fin (n + 3))
  have hclass : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (negativeQuarterUnit K * laws.discriminantUnit) := by
    simpa only [lemma712DiscriminantParameter] using hdiscriminant
  have hsigned : IsSquare (-(a₀ * a₁) * laws.discriminantUnit) := by
    have hparameter :=
      isSquare_neg_mul_discriminant_of_endpointClass hclass
    have hproduct : -(a₀ * a₁) =
        (-(a.toBONG.adjacentParameter (0 : Fin (n + 3)) (by simp))) *
          a₀ ^ 2 := by
      unfold BONG.adjacentParameter
      apply Units.ext
      simp only [a₀, a₁, GoodBONG.valueUnit, Units.val_neg, Units.val_mul,
        Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
      field_simp [Units.ne_zero (a.toBONG.valueUnit 0)]
      rfl
    rw [hproduct]
    have hreorder :
        ((-(a.toBONG.adjacentParameter (0 : Fin (n + 3)) (by simp))) *
            a₀ ^ 2) * laws.discriminantUnit =
          (-(a.toBONG.adjacentParameter (0 : Fin (n + 3)) (by simp)) *
            laws.discriminantUnit) * a₀ ^ 2 := by
      apply Units.ext
      simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    rw [hreorder]
    exact hparameter.mul ⟨a₀, by simp [pow_two]⟩
  have hrepUnits : DiagonalRepresents
      (fun _ : Fin 1 => (c₀ : K))
      (Fin.cons (a₀ : K) (fun _ : Fin 1 => (a₁ : K))) := by
    convert hrep using 1
    · funext i
      fin_cases i
      rfl
    · funext i
      fin_cases i <;> rfl
  have hhilbert : hilbertSymbol K (c₀ * a₀⁻¹) (-(a₀ * a₁)) = 1 :=
    (DiagonalRepresents.unary_binary_iff_hilbertSymbol_one a₀ a₁ c₀).mp
      hrepUnits
  have hhilbert' : hilbertSymbol K laws.discriminantUnit (c₀ * a₀⁻¹) = 1 := by
    have hsame := hilbertSymbol_eq_discriminant_of_isSquare_mul_discriminant
      (K := K) (b := c₀ * a₀⁻¹) hsigned
    rw [hilbertSymbol_comm K (c₀ * a₀⁻¹) (-(a₀ * a₁))] at hhilbert
    rw [hsame] at hhilbert
    exact hhilbert
  have heven : Even (ordUnit K (c₀ * a₀⁻¹)) :=
    (hilbertSymbol_discriminant_eq_one_iff_even_order (c₀ * a₀⁻¹)).mp
      hhilbert'
  have hratioOrder : ordUnit K (c₀ * a₀⁻¹) = 1 := by
    rw [ordUnit_mul, ordUnit_inv]
    change c.order 0 - a.order 0 = 1
    rw [P.first, hfirst]
    omega
  rw [hratioOrder] at heven
  rcases heven with ⟨k, hk⟩
  omega

/-- For `s > 2`, Lemma 7.5 turns both length-`s - 2` blocks into
equal-scale endpoint towers.  The generic tower reduction then leaves the
same impossible odd-order unary representation as in the case `s = 2`. -/
theorem lemma716_typeI_failureProfile_false_of_gt_two
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (P : Beli2019Lemma716TypeIFailureProfile c R s D.two_le D.le_rank)
    (hs : 2 < s)
    (hrep : DiagonalRepresents
      (c.prefixValues (s - 1) (by
        have := D.le_rank
        omega))
      (a.prefixValues s D.le_rank)) : False := by
  rcases D.even with ⟨d, hd⟩
  let pairs := d - 1
  have hpairsPos : 0 < pairs := by
    dsimp only [pairs]
    omega
  have hsEq : s = 2 * pairs + 2 := by
    dsimp only [pairs]
    omega
  have D' : Lemma714StoppingData a R (2 * pairs + 2) := by
    rw [← hsEq]
    exact D
  have hRank : 2 * pairs + 2 ≤ n + 3 := D'.le_rank
  have P' : Beli2019Lemma716TypeIFailureProfile c R (2 * pairs + 2)
      D'.two_le D'.le_rank := by
    exact hsEq ▸ P
  have hrepEq : DiagonalRepresents
      (c.prefixValues (2 * pairs + 1) (by
        have := D'.le_rank
        omega))
      (a.prefixValues (2 * pairs + 2) D'.le_rank) := by
    exact prefixRepresents_cast c a (by omega) hsEq hrep
  let initial : Fin 2 → Kˣ := a.prefixValueUnits 2 (by
    have := D'.le_rank
    omega)
  let source : Fin (2 * pairs) → Kˣ := fun i =>
    a.valueUnit ⟨i.val + 2, by
      have := D'.le_rank
      omega⟩
  let comparison : Fin (2 * pairs) → Kˣ :=
    c.prefixValueUnits (2 * pairs) (by
      have := D'.le_rank
      omega)
  let extra : Kˣ := c.valueUnit ⟨2 * pairs, by
    have := D'.le_rank
    omega⟩
  let sourceFirst : Fin (n + 2) := ⟨2, by
    have := D'.le_rank
    omega⟩
  let sourceLast : Fin (n + 2) := ⟨2 * pairs, by
    have := D'.le_rank
    omega⟩
  have hsourceFirstLast : sourceFirst ≤ sourceLast := by
    exact Fin.mk_le_mk.mpr (by omega)
  have hsourceSegmentEven : Even (sourceLast.val - sourceFirst.val) := by
    exact ⟨pairs - 1, by simp only [sourceLast, sourceFirst]; omega⟩
  have hsFour : 4 ≤ 2 * pairs + 2 := by omega
  have hplateau := a.beli2019Lemma714_i R (2 * pairs + 2)
    D'.toLemma714MinimalityData hsFour hthird
  have hsourceInitial : a.order sourceFirst.castSucc = R + 1 := by
    simpa only [sourceFirst, Fin.castSucc_mk] using
      hplateau.high_positions 2 (by omega) (by omega) (by simp)
  have hsourceTerminal : a.order sourceLast.succ =
      R + 1 - 2 * (ramificationIndex K : Int) := by
    have h := hplateau.low_positions (2 * pairs + 1)
      (by omega) (by omega) (by
        exact ⟨pairs, by omega⟩)
    have hindex : sourceLast.succ =
        (⟨2 * pairs + 1, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      rfl
    rw [hindex, h]
    ring
  let sourceArithmetic := a.beli2019Lemma75_arithmetic
    sourceFirst sourceLast (R + 1) hsourceFirstLast hsourceSegmentEven
      hsourceInitial hsourceTerminal
  let comparisonFirst : Fin (n + 2) := ⟨0, by
    have := D'.le_rank
    omega⟩
  let comparisonLast : Fin (n + 2) := ⟨2 * pairs - 2, by
    have := D'.le_rank
    omega⟩
  have hcomparisonFirstLast : comparisonFirst ≤ comparisonLast := by
    exact Fin.mk_le_mk.mpr (by omega)
  have hcomparisonSegmentEven :
      Even (comparisonLast.val - comparisonFirst.val) := by
    exact ⟨pairs - 1, by
      simp only [comparisonLast, comparisonFirst, Nat.sub_zero]
      omega⟩
  have hcomparisonInitial : c.order comparisonFirst.castSucc = R + 1 := by
    change c.order (0 : Fin (n + 3)) = R + 1
    exact P'.first
  have hcomparisonTerminal : c.order comparisonLast.succ =
      R + 1 - 2 * (ramificationIndex K : Int) := by
    have hindex : comparisonLast.succ =
        (⟨2 * pairs - 1, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      simp only [comparisonLast, Fin.val_succ]
      omega
    rw [hindex]
    have hlowIndex : (⟨2 * pairs - 1, by omega⟩ : Fin (n + 3)) =
        ⟨(2 * pairs + 2) - 3, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [hlowIndex, P'.low (by omega)]
    ring
  let comparisonArithmetic := c.beli2019Lemma75_arithmetic
    comparisonFirst comparisonLast (R + 1) hcomparisonFirstLast
      hcomparisonSegmentEven hcomparisonInitial hcomparisonTerminal
  have hsourceClasses : AlternatingEndpointPairClasses source := by
    intro t
    let k : Fin (n + 2) := ⟨2 + 2 * t.val, by omega⟩
    have hsourceFirstK : sourceFirst ≤ k := by
      exact Fin.mk_le_mk.mpr (by omega)
    have hkSourceLast : k ≤ sourceLast := by
      exact Fin.mk_le_mk.mpr (by omega)
    have hkEven : Even (k.val - sourceFirst.val) := by
      exact ⟨t.val, by simp only [k, sourceFirst]; omega⟩
    have hclasses := a.beli2019Lemma75_pairBlock_endpointClass
      sourceFirst sourceLast k (R + 1) hsourceFirstLast
        hsourceSegmentEven hsourceInitial hsourceTerminal
        hsourceFirstK hkSourceLast hkEven
    have hpair := a.toBONG.adjacentSignedProduct_endpoint_cases
      k.castSucc (Nat.succ_lt_succ k.isLt) hclasses
    simpa only [source, GoodBONG.valueUnit, k, Fin.castSucc_mk, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using hpair
  have hcomparisonClasses : AlternatingEndpointPairClasses comparison := by
    intro t
    let k : Fin (n + 2) := ⟨2 * t.val, by omega⟩
    have hcomparisonFirstK : comparisonFirst ≤ k := Fin.zero_le k
    have hkComparisonLast : k ≤ comparisonLast := by
      exact Fin.mk_le_mk.mpr (by omega)
    have hkEven : Even (k.val - comparisonFirst.val) := by
      exact ⟨t.val, by
        simp only [k, comparisonFirst, Nat.sub_zero]
        omega⟩
    have hclasses := c.beli2019Lemma75_pairBlock_endpointClass
      comparisonFirst comparisonLast k (R + 1) hcomparisonFirstLast
        hcomparisonSegmentEven hcomparisonInitial hcomparisonTerminal
        hcomparisonFirstK hkComparisonLast hkEven
    have hpair := c.toBONG.adjacentSignedProduct_endpoint_cases
      k.castSucc (Nat.succ_lt_succ k.isLt) hclasses
    simpa only [comparison, prefixValueUnits, GoodBONG.valueUnit, k,
      Fin.castSucc_mk] using hpair
  have hextraOrder : ordUnit K extra = R + 1 := by
    calc
      ordUnit K extra = c.order ⟨2 * pairs, by omega⟩ := by
        exact (c.toBONG.order_eq_ordUnit _).symm
      _ = R + 1 := P'.high
  have hsourceOrders : ∀ t : Fin pairs,
      ordUnit K (source ⟨2 * t.val, by omega⟩) = ordUnit K extra := by
    intro t
    let k : Fin (n + 2) := ⟨2 + 2 * t.val, by omega⟩
    have hkOrder := sourceArithmetic.even_order k
      (Fin.mk_le_mk.mpr (by omega)) (Fin.mk_le_mk.mpr (by omega))
      ⟨t.val, by simp only [k, sourceFirst]; omega⟩
    calc
      ordUnit K (source ⟨2 * t.val, by omega⟩) = a.order k.castSucc := by
        simpa only [source, k, GoodBONG.valueUnit, Fin.castSucc_mk,
          GoodBONG.order, Nat.add_comm] using
            (a.toBONG.order_eq_ordUnit k.castSucc).symm
      _ = R + 1 := hkOrder
      _ = ordUnit K extra := hextraOrder.symm
  have hcomparisonOrders : ∀ t : Fin pairs,
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = ordUnit K extra := by
    intro t
    let k : Fin (n + 2) := ⟨2 * t.val, by omega⟩
    have hkOrder := comparisonArithmetic.even_order k
      (Fin.zero_le k) (Fin.mk_le_mk.mpr (by omega))
      ⟨t.val, by
        simp only [k, comparisonFirst, Nat.sub_zero]
        omega⟩
    calc
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = c.order k.castSucc := by
        simpa only [comparison, prefixValueUnits, GoodBONG.valueUnit, k,
          GoodBONG.order, Fin.castSucc_mk] using
            (c.toBONG.order_eq_ordUnit k.castSucc).symm
      _ = R + 1 := hkOrder
      _ = ordUnit K extra := hextraOrder.symm
  have hinitial : IsSquare
      (-(initial 0 * initial 1) * laws.discriminantUnit) := by
    have hzero : initial 0 = a.valueUnit (0 : Fin (n + 3)) := by
      unfold initial prefixValueUnits
      congr
    have hone : initial 1 = a.valueUnit (1 : Fin (n + 3)) := by
      unfold initial prefixValueUnits
      congr
    rw [hzero, hone]
    exact a.lemma716_initialSignedProduct_mul_discriminant_isSquare hdiscriminant
  have hodd : Odd (ordUnit K (extra * (initial 0)⁻¹)) := by
    rw [ordUnit_mul, ordUnit_inv, hextraOrder]
    change Odd ((R + 1) - a.order 0)
    rw [hfirst]
    exact ⟨0, by omega⟩
  have hnot := alternatingEndpointTower_unaryExtensionExclusion
    initial source comparison extra hinitial hsourceClasses hcomparisonClasses
      hsourceOrders hcomparisonOrders hodd
  apply hnot
  have hrep' : DiagonalRepresents
      (c.prefixValues (2 * pairs + 1) (by
        have := D'.le_rank
        omega))
      (a.prefixValues (2 + 2 * pairs) (by
        have := D'.le_rank
        omega)) :=
    prefixRepresents_cast c a rfl (by omega) hrepEq
  have hcomparisonCoefficients :
      diagonalUnitCoefficients (Fin.snoc comparison extra) =
        c.prefixValues (2 * pairs + 1) (by omega) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [comparison, extra, diagonalUnitCoefficients, prefixValues,
        GoodBONG.valueUnit, GoodBONG.value]
    · simp [comparison, diagonalUnitCoefficients, prefixValues,
        prefixValueUnits, GoodBONG.valueUnit, GoodBONG.value]
  have hsourceCoefficients :
      diagonalUnitCoefficients (Fin.append initial source) =
        a.prefixValues (2 + 2 * pairs) (by omega) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [initial, diagonalUnitCoefficients, prefixValues,
        prefixValueUnits, GoodBONG.valueUnit, GoodBONG.value]
    · simp [source, diagonalUnitCoefficients, prefixValues,
        GoodBONG.valueUnit, GoodBONG.value, Nat.add_comm]
  rw [hcomparisonCoefficients, hsourceCoefficients]
  exact hrep'

/-- Every rigid type-I failure profile is impossible.  The proof separates
the binary endpoint `s = 2` from the longer alternating-tower cancellation
used in the paper. -/
theorem lemma716_typeI_failureProfile_false
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (P : Beli2019Lemma716TypeIFailureProfile c R s D.two_le D.le_rank)
    (hrep : DiagonalRepresents
      (c.prefixValues (s - 1) (by
        have := D.le_rank
        omega))
      (a.prefixValues s D.le_rank)) : False := by
  rcases D.two_le.lt_or_eq with hs | hs
  · exact a.lemma716_typeI_failureProfile_false_of_gt_two c R s D hfirst
      hthird hdiscriminant P hs hrep
  · subst s
    exact a.lemma716_typeI_failureProfile_false_of_two c R hfirst
      hdiscriminant P hrep

end BONG.GoodBONG

end Bong
