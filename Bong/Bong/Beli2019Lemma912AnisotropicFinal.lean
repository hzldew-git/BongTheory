/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912AnisotropicPropagation

/-!
# Beli (2019), Lemma 9.12: final anisotropic descent boundary

This file closes the bottom boundary of the anisotropic scalar-failure
argument.  It proves the two initial mixed-prefix defect bounds have strict
sum greater than `2e`, and combines that boundary with the propagated
intermediate bounds to contradict anisotropy by prefix descent.
-/

namespace Bong

open Dyadic

universe u v w z


namespace BONG.GoodBONG.Beli2019Lemma910Data

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {Q : Lattice K U} {N : Nat}

theorem initialComparisonDefect_ge_failureThreshold
    [Beli2006AlphaLaws.{u, w} K]
    {R₁ R₂ A₁ : Int}
    (target : GoodBONG q L (N + 3))
    (c : GoodBONG r M (N + 3))
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (O : Beli2019Lemma912FailureAlternatingOrders target c R₁ R₂ i)
    (P : Beli2019Lemma912ComparisonFirstAlphaProfile c A₁)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K) :
    (((failureThreshold (K := K) A₁ 1 : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) (-c.prefixProduct 2) := by
  have hlocal := c.order_sub_add_alpha_le_adjacentDefect
    (0 : Fin (N + 2))
  rw [← c.defectOrder_prefixPair_eq_adjacentDefect
    (0 : Fin (N + 2))] at hlocal
  have hzero : c.order (0 : Fin (N + 3)) = R₁ :=
    O.comparison_even (0 : Fin (N + 3))
      (by change 0 + 1 ≤ i.val; omega) (by norm_num)
  have hone : c.order (1 : Fin (N + 3)) = R₂ + 2 :=
    O.comparison_odd (1 : Fin (N + 3))
      (by change 1 + 1 ≤ i.val; omega) (by norm_num)
  have hlower :
      (((((c.order (0 : Fin (N + 3)) - c.order (1 : Fin (N + 3)) : Int) : ℚ) +
          c.alphaValue (0 : Fin (N + 2)) : ℚ)) : WithTop ℚ) =
        (((failureThreshold (K := K) A₁ 1 : Int) : ℚ) : WithTop ℚ) := by
    apply WithTop.coe_eq_coe.mpr
    rw [hzero, hone, P.alpha_eq,
      failureThreshold_of_odd (K := K) A₁ 1 (by norm_num)]
    push_cast at hformula ⊢
    linarith
  have hzeroCast : (0 : Fin (N + 2)).castSucc =
      (0 : Fin (N + 3)) := rfl
  have hzeroSucc : (0 : Fin (N + 2)).succ =
      (1 : Fin (N + 3)) := rfl
  have hlocal' :
      (((((c.order (0 : Fin (N + 3)) - c.order (1 : Fin (N + 3)) : Int) : ℚ) +
          c.alphaValue (0 : Fin (N + 2)) : ℚ)) : WithTop ℚ) ≤
        defectOrder (K := K) (-c.prefixProduct 2) := by
    simpa only [hzeroCast, hzeroSucc, Fin.val_zero, Nat.zero_add,
      GoodBONG.prefixProduct, BONG.prefixProduct_zero, mul_one,
      neg_one_mul] using hlocal
  rw [hlower] at hlocal'
  exact hlocal'

theorem initialShiftedDefect_ge_failureThreshold
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, w} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (S : Beli2019Lemma912SourceAlphaAlternation
      (a.castLength hlength) A₁ i)
    (C : Beli2019Lemma912ComparisonAlphaAlternation c A₁ i)
    (T : Beli2019Lemma912TopMixedDefectBounds
      (a.castLength hlength) c A₁ i) :
    (((failureThreshold (K := K) A₁ 0 : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K)
        ((-1 : Kˣ) * (a.castLength hlength).prefixProduct 3 *
          c.prefixProduct 1) := by
  have h := shiftedMixedDefect_ge_failureThreshold
    (sourceLaws := sourceLaws) (comparisonLaws := comparisonLaws)
    a c D E horders hlength i O S C T 2 (by omega) hiTwo
  simpa only [Nat.reduceSubDiff, Nat.reduceAdd] using h

theorem initialShiftedMixedProduct_order_even
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (horderParity : Int.ModEq 2 R₁ R₂) :
    Even (ordUnit K
      ((-1 : Kˣ) * (a.castLength hlength).prefixProduct 3 *
        c.prefixProduct 1)) := by
  let source := a.castLength hlength
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hnegOne : ordUnit K (-1 : Kˣ) = 0 := by
    rw [ordUnit_neg, hone]
  have horder : ordUnit K
      ((-1 : Kˣ) * source.prefixProduct 3 * c.prefixProduct 1) =
        source.order (0 : Fin (N + 3)) +
          source.order (1 : Fin (N + 3)) +
          source.order (2 : Fin (N + 3)) +
          c.order (0 : Fin (N + 3)) := by
    rw [ordUnit_mul, ordUnit_mul, hnegOne, zero_add,
      source.ordUnit_prefixProduct_eq_orderSequence_prefixSum 3 (by omega),
      c.ordUnit_prefixProduct_eq_orderSequence_prefixSum 1 (by omega),
      source.orderSequence.prefixSum_succ 2,
      source.orderSequence.prefixSum_succ 1,
      source.orderSequence.prefixSum_one,
      c.orderSequence.prefixSum_one,
      BeliOrderSequence.entryOrZero_of_lt,
      BeliOrderSequence.entryOrZero_of_lt,
      BeliOrderSequence.entryOrZero_of_lt,
      BeliOrderSequence.entryOrZero_of_lt]
    rfl
  let zero : Fin 3 := ⟨0, by omega⟩
  let one : Fin 3 := ⟨1, by omega⟩
  let two : Fin 3 := ⟨2, by omega⟩
  have hs0 : source.order (⟨0, by omega⟩ : Fin (N + 3)) = R₁ := by
    rw [GoodBONG.order_castLength]
    have hindex : (⟨0, by omega⟩ : Fin (3 + N)) = Fin.castAdd N zero := by
      apply Fin.ext
      rfl
    rw [hindex, horders zero]
    rfl
  have hs1 : source.order (⟨1, by omega⟩ : Fin (N + 3)) = R₂ := by
    rw [GoodBONG.order_castLength]
    have hindex : (⟨1, by omega⟩ : Fin (3 + N)) = Fin.castAdd N one := by
      apply Fin.ext
      rfl
    rw [hindex, horders one]
    rfl
  have hs2 : source.order (⟨2, by omega⟩ : Fin (N + 3)) = R₁ := by
    rw [GoodBONG.order_castLength]
    have hindex : (⟨2, by omega⟩ : Fin (3 + N)) = Fin.castAdd N two := by
      apply Fin.ext
      rfl
    rw [hindex, horders two]
    rfl
  have hs0' : source.order (0 : Fin (N + 3)) = R₁ := by
    rw [show (0 : Fin (N + 3)) = (⟨0, by omega⟩ : Fin (N + 3)) by
      apply Fin.ext
      rfl]
    exact hs0
  have hs1' : source.order (1 : Fin (N + 3)) = R₂ := by
    rw [show (1 : Fin (N + 3)) = (⟨1, by omega⟩ : Fin (N + 3)) by
      apply Fin.ext
      rfl]
    exact hs1
  have hs2' : source.order (2 : Fin (N + 3)) = R₁ := by
    rw [show (2 : Fin (N + 3)) = (⟨2, by omega⟩ : Fin (N + 3)) by
      apply Fin.ext
      rfl]
    exact hs2
  have hc0 : c.order (0 : Fin (N + 3)) = R₁ :=
    O.comparison_even (0 : Fin (N + 3))
      (by change 0 + 1 ≤ i.val; omega) (by norm_num)
  have hdiffEven : Even (R₂ - R₁) := by
    rw [Int.modEq_iff_dvd] at horderParity
    rcases horderParity with ⟨t, ht⟩
    exact ⟨t, by omega⟩
  rcases hdiffEven with ⟨t, ht⟩
  rw [horder, hs0', hs1', hs2', hc0]
  refine ⟨2 * R₁ + t, ?_⟩
  omega

theorem initialComparisonProduct_order_even
    {R₁ R₂ : Int}
    (target : GoodBONG q L (N + 3))
    (c : GoodBONG r M (N + 3))
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (O : Beli2019Lemma912FailureAlternatingOrders target c R₁ R₂ i)
    (horderParity : Int.ModEq 2 R₁ R₂) :
    Even (ordUnit K (-c.prefixProduct 2)) := by
  have horder : ordUnit K (-c.prefixProduct 2) =
      c.order (0 : Fin (N + 3)) + c.order (1 : Fin (N + 3)) := by
    rw [ordUnit_neg,
      c.ordUnit_prefixProduct_eq_orderSequence_prefixSum 2 (by omega),
      c.orderSequence.prefixSum_succ 1,
      c.orderSequence.prefixSum_one,
      BeliOrderSequence.entryOrZero_of_lt,
      BeliOrderSequence.entryOrZero_of_lt]
    rfl
  have hc0 : c.order (0 : Fin (N + 3)) = R₁ :=
    O.comparison_even (0 : Fin (N + 3))
      (by change 0 + 1 ≤ i.val; omega) (by norm_num)
  have hc1 : c.order (1 : Fin (N + 3)) = R₂ + 2 :=
    O.comparison_odd (1 : Fin (N + 3))
      (by change 1 + 1 ≤ i.val; omega) (by norm_num)
  rw [horder, hc0, hc1]
  simpa only [add_assoc] using
    baselineAdjacentSum_even_of_modEq horderParity

theorem initialDefectSum_strict
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, w} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (P : Beli2019Lemma912ComparisonFirstAlphaProfile c A₁)
    (S : Beli2019Lemma912SourceAlphaAlternation
      (a.castLength hlength) A₁ i)
    (C : Beli2019Lemma912ComparisonAlphaAlternation c A₁ i)
    (T : Beli2019Lemma912TopMixedDefectBounds
      (a.castLength hlength) c A₁ i)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K)
    (horderParity : Int.ModEq 2 R₁ R₂) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
      defectOrder (K := K) (-c.prefixProduct 2) +
        defectOrder (K := K)
          ((-1 : Kˣ) * (a.castLength hlength).prefixProduct 3 *
            c.prefixProduct 1) := by
  let source := a.castLength hlength
  let first := failureThreshold (K := K) A₁ 1
  let second := failureThreshold (K := K) A₁ 0
  have hcomparisonWeak := initialComparisonDefect_ge_failureThreshold
    (K := K) (R₁ := R₁) (R₂ := R₂)
    (E.bong.castLength hlength) c i hiTwo O P hformula
  have hshiftedWeak := initialShiftedDefect_ge_failureThreshold
    (sourceLaws := sourceLaws) (comparisonLaws := comparisonLaws)
    a c D E horders hlength i hiTwo O S C T
  have hcomparisonOrderEven := initialComparisonProduct_order_even
    (K := K) (E.bong.castLength hlength) c i hiTwo O
      horderParity
  have hshiftedOrderEven := initialShiftedMixedProduct_order_even
    (K := K) a c D E horders hlength i hiTwo O horderParity
  have hcomparisonStrict := evenThreshold_lt_defectOrder_of_le
    (K := K) (-c.prefixProduct 2) first
    (failureThreshold_even P 1)
    (failureThreshold_lt_twoE P 1)
    hcomparisonOrderEven (by simpa only [first] using hcomparisonWeak)
  have hshiftedStrict := evenThreshold_lt_defectOrder_of_le
    (K := K)
    ((-1 : Kˣ) * source.prefixProduct 3 * c.prefixProduct 1) second
    (failureThreshold_even P 0)
    (failureThreshold_lt_twoE P 0)
    hshiftedOrderEven (by simpa only [second, source] using hshiftedWeak)
  have hsumInt : first + second =
      2 * (ramificationIndex K : Int) := by
    have h := failureThreshold_add_next (K := K) A₁ 0
    have h' : second + first =
        2 * (ramificationIndex K : Int) := by
      dsimp only [second, first]
      simpa only [Nat.zero_add] using h
    omega
  have hsumQ : (((2 * ramificationIndex K : Nat) : ℚ)) =
      ((first : Int) : ℚ) + ((second : Int) : ℚ) := by
    exact_mod_cast hsumInt.symm
  have hadd := WithTop.add_lt_add hcomparisonStrict hshiftedStrict
  rw [← WithTop.coe_add, ← hsumQ] at hadd
  exact hadd

theorem false_of_anisotropic_of_topPrefixRepresentation
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, w} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hanisotropic :
      (a.castLength hlength).Lemma814FirstThreeAnisotropic)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (P : Beli2019Lemma912ComparisonFirstAlphaProfile c A₁)
    (S : Beli2019Lemma912SourceAlphaAlternation
      (a.castLength hlength) A₁ i)
    (C : Beli2019Lemma912ComparisonAlphaAlternation c A₁ i)
    (T : Beli2019Lemma912TopMixedDefectBounds
      (a.castLength hlength) c A₁ i)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K)
    (horderParity : Int.ModEq 2 R₁ R₂)
    (htop : DiagonalRepresents
      (c.prefixValues i.val (by have := i.lt_large; omega))
      ((a.castLength hlength).prefixValues (i.val + 1)
        (by have := i.lt_large; omega))) :
    False := by
  let source := a.castLength hlength
  have hsteps : ∀ k : Nat, 2 < k → k ≤ i.val →
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
            (source.prefixProduct k * c.prefixProduct k) +
          defectOrder (K := K)
            (-source.prefixProduct (k + 1) * c.prefixProduct (k - 1)) := by
    intro k hkThree hki
    exact mixedDefectSum_strict
      (sourceLaws := sourceLaws) (comparisonLaws := comparisonLaws)
      a c D E horders hlength i O P S C T horderParity
        k (by omega) hki
  have hfinal := initialDefectSum_strict
    (sourceLaws := sourceLaws) (comparisonLaws := comparisonLaws)
    a c D E horders hlength i hiTwo O P S C T hformula
      horderParity
  exact false_of_anisotropic_of_prefixDescentBounds
    source c hanisotropic i.val hiTwo (by have := i.lt_large; omega)
      (by simpa only [source] using htop) hsteps
      (by simpa only [source] using hfinal)

end BONG.GoodBONG.Beli2019Lemma910Data

end Bong
