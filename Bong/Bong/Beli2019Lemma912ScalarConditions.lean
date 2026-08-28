/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912Construction
import Bong.Bong.Beli2019AuxiliaryAlphaBounds
import Bong.Bong.Beli2019RepresentationSourceHalfGap
import Bong.Bong.Beli2019CappedIntegrality
import Bong.Bong.Beli2019EvenClassMultiplier

/-!
# Beli (2019), Lemma 9.12: scalar inequalities in three type-I branches

This file proves the two scalar inequalities required by the type-I claim
for the equal-first-alpha, strict-below-half-gap, and isotropic-half-gap
branches. It also records the parity and rounding lemmas used by the strict
branch. The remaining anisotropic half-gap branch is treated separately.
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
  {M : Lattice K V} {P : Lattice K W} {Q : Lattice K U}
  {N : Nat}

/-- The later scalar inequalities in the below-half-gap branch. -/
theorem laterScalar_of_belowHalfGap
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ (A₁ + 2))
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (hdefectSource :
      (a.castLength hlength).RepresentationDefectCondition c)
    (hfirstAlpha : (a.castLength hlength).alphaValue
      (0 : Fin (N + 2)) = (A₁ : ℚ)) :
    ∀ i : RepresentationIndex (N + 3) (N + 3), 2 ≤ i.val →
      ((E.bong.castLength hlength).representationAlphaValue c i :
          WithTop ℚ) ≤
        (((((E.bong.castLength hlength).order
              ⟨i.val, i.lt_large⟩ -
            (E.bong.castLength hlength).order
              (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          ((A₁ + 2 : Int) : ℚ) : ℚ) : WithTop ℚ) := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  intro i hi
  have hcomparison := E.representationAlphaValue_le_source
    a c D horders hlength hdefectSourceTarget i hi
  have hsourceAlphaTop :=
    source.representationAlpha_le_leftAlpha c hdefectSource i
  have hsourceAlpha : source.representationAlphaValue c i ≤
      source.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ := by
    rw [← source.coe_representationAlphaValue c i] at hsourceAlphaTop
    exact WithTop.coe_le_coe.mp hsourceAlphaTop
  have hendpoint := source.alphaRightEndpoint_antitone
    (show (0 : Fin (N + 2)) ≤
        ⟨i.val - 1, by have := i.lt_large; omega⟩ by
      change 0 ≤ i.val - 1
      omega)
  have hsourceOne : source.order
      (⟨1, by omega⟩ : Fin (N + 3)) = R₂ := by
    rw [show source = a.castLength hlength by rfl,
      GoodBONG.order_castLength]
    have hindex : (⟨1, by omega⟩ : Fin (3 + N)) =
        Fin.castAdd N (1 : Fin 3) := by
      apply Fin.ext
      rfl
    rw [hindex, horders (1 : Fin 3)]
    rfl
  have hsourceCurrent : source.order ⟨i.val, i.lt_large⟩ =
      target.order ⟨i.val, i.lt_large⟩ :=
    (E.order_castLength_eq_source_of_two_le
      a D horders hlength ⟨i.val, i.lt_large⟩ hi).symm
  have htargetOne : target.order
      (⟨1, by omega⟩ : Fin (N + 3)) = R₂ + 2 := by
    have h := E.order_castLength_prefix a D hlength (1 : Fin 3)
    rw [D.order_one] at h
    change target.order _ = R₂ + 2 at h
    rw [show (⟨1, by omega⟩ : Fin (N + 3)) =
      ⟨(1 : Fin 3).val, by omega⟩ by
        apply Fin.ext
        simp]
    exact h
  have halphaBound : source.alphaValue
      ⟨i.val - 1, by have := i.lt_large; omega⟩ ≤
        ((source.order ⟨i.val, i.lt_large⟩ - R₂ : Int) : ℚ) +
          (A₁ : ℚ) := by
    unfold alphaRightEndpoint at hendpoint
    have hzeroSucc : (0 : Fin (N + 2)).succ =
        (⟨1, by omega⟩ : Fin (N + 3)) := by rfl
    have hcurrentSucc :
        (⟨i.val - 1, by have := i.lt_large; omega⟩ :
          Fin (N + 2)).succ = ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hzeroSucc, hcurrentSucc, hfirstAlpha, hsourceOne] at hendpoint
    push_cast at hendpoint ⊢
    linarith
  have hq : target.representationAlphaValue c i ≤
      ((target.order ⟨i.val, i.lt_large⟩ -
          target.order (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
        ((A₁ + 2 : Int) : ℚ) := by
    calc
      target.representationAlphaValue c i ≤
          source.representationAlphaValue c i := hcomparison
      _ ≤ source.alphaValue
          ⟨i.val - 1, by have := i.lt_large; omega⟩ := hsourceAlpha
      _ ≤ ((source.order ⟨i.val, i.lt_large⟩ - R₂ : Int) : ℚ) +
          (A₁ : ℚ) := halphaBound
      _ = ((target.order ⟨i.val, i.lt_large⟩ -
          target.order (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          ((A₁ + 2 : Int) : ℚ) := by
        rw [← hsourceCurrent, htargetOne]
        push_cast
        ring
  exact_mod_cast hq

/-- The later scalar inequalities in the equal-first-alpha branch. -/
theorem laterScalar_of_equalSecondLarge
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (hsourceSecond : R₂ + 2 ≤
      c.order (⟨1, by omega⟩ : Fin (N + 3)))
    (htargetFirstAlpha : c.alphaValue
      (0 : Fin (N + 2)) = (A₁ : ℚ)) :
    ∀ i : RepresentationIndex (N + 3) (N + 3), 2 ≤ i.val →
      ((E.bong.castLength hlength).representationAlphaValue c i :
          WithTop ℚ) ≤
        (((((E.bong.castLength hlength).order
              ⟨i.val, i.lt_large⟩ -
            (E.bong.castLength hlength).order
              (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          (A₁ : ℚ) : ℚ) : WithTop ℚ) := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  intro i hi
  have hcomparison := E.representationAlphaValue_le_source
    a c D horders hlength hdefectSourceTarget i hi
  have hprimaryTop := (source.representationAlpha_le_prime c i).trans
    (source.representationAlphaPrime_le_primaryRightCap c i)
  have hcapPos : 0 < i.val - 1 := by omega
  have hcapBound : i.val - 1 < N + 3 := by
    have := i.lt_large
    omega
  rw [c.prefixAlphaCap_of_internal hcapPos hcapBound] at hprimaryTop
  have hcapIndex :
      (⟨i.val - 1 - 1, by have := i.lt_large; omega⟩ : Fin (N + 2)) =
        ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
    apply Fin.ext
    simp only [Nat.sub_sub, Nat.reduceAdd]
  rw [hcapIndex, ← source.coe_representationAlphaValue c i] at hprimaryTop
  have hprimary : source.representationAlphaValue c i ≤
      ((source.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) +
        c.alphaValue ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
    exact_mod_cast hprimaryTop
  let current : Fin (N + 2) :=
    ⟨i.val - 2, by have := i.lt_large; omega⟩
  have hendpoint : c.alphaRightEndpoint current ≤
      c.alphaRightEndpoint (0 : Fin (N + 2)) := by
    letI : Beli2006AlphaLaws.{u, z} K := targetLaws
    exact c.alphaRightEndpoint_antitone
      (show (0 : Fin (N + 2)) ≤ current by
        change 0 ≤ i.val - 2
        omega)
  have hcurrentSucc : current.succ =
      (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    simp [current]
    omega
  have hzeroSucc : (0 : Fin (N + 2)).succ =
      (⟨1, by omega⟩ : Fin (N + 3)) := by rfl
  have hendpointBound :
      -(c.order ⟨i.val - 1, by have := i.le_small; omega⟩ : ℚ) +
          c.alphaValue ⟨i.val - 2, by have := i.lt_large; omega⟩ ≤
        -(c.order (⟨1, by omega⟩ : Fin (N + 3)) : ℚ) +
          (A₁ : ℚ) := by
    unfold alphaRightEndpoint at hendpoint
    rw [hcurrentSucc, hzeroSucc, htargetFirstAlpha] at hendpoint
    simpa only [current] using hendpoint
  have hsourceCurrent : source.order ⟨i.val, i.lt_large⟩ =
      target.order ⟨i.val, i.lt_large⟩ :=
    (E.order_castLength_eq_source_of_two_le
      a D horders hlength ⟨i.val, i.lt_large⟩ hi).symm
  have htargetOne : target.order
      (⟨1, by omega⟩ : Fin (N + 3)) = R₂ + 2 := by
    have h := E.order_castLength_prefix a D hlength (1 : Fin 3)
    rw [D.order_one] at h
    change target.order _ = R₂ + 2 at h
    rw [show (⟨1, by omega⟩ : Fin (N + 3)) =
      ⟨(1 : Fin 3).val, by omega⟩ by
        apply Fin.ext
        simp]
    exact h
  have hq : target.representationAlphaValue c i ≤
      ((target.order ⟨i.val, i.lt_large⟩ -
          target.order (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
        (A₁ : ℚ) := by
    calc
      target.representationAlphaValue c i ≤
          source.representationAlphaValue c i := hcomparison
      _ ≤ ((source.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) +
          c.alphaValue ⟨i.val - 2, by have := i.lt_large; omega⟩ := hprimary
      _ ≤ (source.order ⟨i.val, i.lt_large⟩ : ℚ) -
          (c.order (⟨1, by omega⟩ : Fin (N + 3)) : ℚ) +
          (A₁ : ℚ) := by
        push_cast
        linarith [hendpointBound]
      _ ≤ (source.order ⟨i.val, i.lt_large⟩ : ℚ) -
          ((R₂ + 2 : Int) : ℚ) + (A₁ : ℚ) := by
        have hint : source.order ⟨i.val, i.lt_large⟩ -
              c.order (⟨1, by omega⟩ : Fin (N + 3)) + A₁ ≤
            source.order ⟨i.val, i.lt_large⟩ - (R₂ + 2) + A₁ := by
          omega
        exact_mod_cast hint
      _ = ((target.order ⟨i.val, i.lt_large⟩ -
          target.order (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          (A₁ : ℚ) := by
        rw [← hsourceCurrent, htargetOne]
        push_cast
        ring
  exact_mod_cast hq

/-- A raw defect strictly above an integer is at least the next integer. -/
theorem intCast_add_one_le_defectOrder_of_lt
    (x : Kˣ) (A : Int)
    (hstrict : (((A : ℚ) : WithTop ℚ) < defectOrder (K := K) x)) :
    ((((A + 1 : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) x) := by
  rcases defectOrder_eq_top_or_isWithTopRationalInteger
      (K := K) x with htop | ⟨z, hz⟩
  · rw [htop]
    exact le_top
  · rw [hz] at hstrict ⊢
    apply WithTop.coe_le_coe.mpr
    have hAz : A < z := by
      exact_mod_cast WithTop.coe_lt_coe.mp hstrict
    exact_mod_cast (show A + 1 ≤ z by omega)

/-- An even-order square class with odd integral defect depth skips the
next even integer. -/
theorem intCast_add_two_le_defectOrder_of_odd_of_even_ordUnit
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    (x : Kˣ) (A : Int) (hAodd : Odd A)
    (hxEven : Even (ordUnit K x))
    (hstrict : (((A : ℚ) : WithTop ℚ) < defectOrder (K := K) x))
    (hTwoE : A + 2 ≤ 2 * (ramificationIndex K : Int)) :
    ((((A + 2 : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) x) := by
  by_cases htop : defectOrder (K := K) x = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hd] at hstrict ⊢
    apply WithTop.coe_le_coe.mpr
    by_contra hnot
    have hAd : (A : ℚ) < d := WithTop.coe_lt_coe.mp hstrict
    have hdUpper : d < ((A + 2 : Int) : ℚ) := lt_of_not_ge hnot
    have hTwoEQ : ((A + 2 : Int) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) := by
      exact_mod_cast hTwoE
    have hdTwoE : d < 2 * (ramificationIndex K : ℚ) :=
      hdUpper.trans_le hTwoEQ
    have hdOdd := isOddRationalInteger_of_even_ordUnit_of_defectOrder_eq
      x d hxEven hd.symm hdTwoE
    rcases hdOdd with ⟨z, hzOdd, hdz⟩
    have hAz : A < z := by
      exact_mod_cast (show (A : ℚ) < (z : ℚ) by
        simpa only [← hdz] using hAd)
    have hzUpper : z < A + 2 := by
      exact_mod_cast (show (z : ℚ) < ((A + 2 : Int) : ℚ) by
        simpa only [← hdz] using hdUpper)
    rcases hAodd with ⟨p, hp⟩
    rcases hzOdd with ⟨q, hq⟩
    omega

/-- In the residual profile, the signed full raw product has even
valuation. -/
theorem fullRawOrder_even
    (a : GoodBONG q M (N + 5))
    (c : GoodBONG s Q (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5))) :
    Even (ordUnit K
      ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1)) := by
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hnegOne : ordUnit K (-1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (-1 : Kˣ) (-1)
    have hmul : (-1 : Kˣ) * (-1) = 1 := by norm_num
    rw [hmul, hone] at h
    omega
  have horder : ordUnit K
      ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1) =
        a.order (0 : Fin (N + 5)) +
          a.order (1 : Fin (N + 5)) +
          a.order (2 : Fin (N + 5)) +
          c.order (0 : Fin (N + 5)) := by
    rw [ordUnit_mul, ordUnit_mul, hnegOne, zero_add,
      a.ordUnit_prefixProduct_eq_orderSequence_prefixSum 3 (by omega),
      c.ordUnit_prefixProduct_eq_orderSequence_prefixSum 1 (by omega),
      a.orderSequence.prefixSum_succ 2,
      a.orderSequence.prefixSum_succ 1,
      a.orderSequence.prefixSum_one,
      c.orderSequence.prefixSum_one,
      BeliOrderSequence.entryOrZero_of_lt,
      BeliOrderSequence.entryOrZero_of_lt,
      BeliOrderSequence.entryOrZero_of_lt,
      BeliOrderSequence.entryOrZero_of_lt]
    rfl
  rcases profile.firstGap_even with ⟨z, hz⟩
  rw [horder, ← hfirst, ← profile.firstThird_eq]
  refine ⟨2 * a.order (0 : Fin (N + 5)) + z, ?_⟩
  unfold orderGap at hz
  have hzeroSucc : (0 : Fin (N + 4)).succ =
      (1 : Fin (N + 5)) := by rfl
  have hzeroCast : (0 : Fin (N + 4)).castSucc =
      (0 : Fin (N + 5)) := by rfl
  rw [hzeroSucc, hzeroCast] at hz
  omega

/-- The first scalar inequality in the strict below-half-gap branch. -/
theorem firstScalar_of_belowHalfGap
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [targetParity : Beli2009AlphaParityLaws.{u, z} K]
    {A₁ : Int}
    (a : GoodBONG q M (N + 5))
    (c : GoodBONG s Q (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (data : Beli2019Lemma912TypeIBetaData a c A₁ (A₁ + 2))
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hstrict : (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1)
    (hbelow : a.alphaValue (0 : Fin (N + 4)) <
      a.halfGapValue (0 : Fin (N + 4))) :
    ((((A₁ + 2 : Int) : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect c (-1) 3 1) := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  letI : Beli2009AlphaParityLaws.{u, v} K := sourceParity
  have hAoddRational :=
    a.beli2019Lemma912_firstAlpha_odd_of_below_halfGap hbelow
  have hAodd : Odd A₁ := by
    rcases hAoddRational with ⟨z, hzOdd, hz⟩
    have hAz : A₁ = z := by
      exact_mod_cast data.firstAlpha.symm.trans hz
    simpa only [hAz] using hzOdd
  have hgapSharp :=
    a.beli2019Lemma912_firstGap_le_twoE_sub_four_of_below_halfGap
      c profile hbelow
  rcases a.halfGapValue_isRationalInteger_of_even
      (0 : Fin (N + 4)) profile.firstGap_even with ⟨H, hH⟩
  have hAH : A₁ < H := by
    exact_mod_cast (show (A₁ : ℚ) < (H : ℚ) by
      simpa only [← data.firstAlpha, ← hH] using hbelow)
  have hHBoundQ : (H : ℚ) ≤
      2 * (ramificationIndex K : ℚ) - 2 := by
    have hgapQ : (a.orderGap (0 : Fin (N + 4)) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) - 4 := by
      exact_mod_cast hgapSharp
    rw [← hH]
    unfold halfGapValue
    linarith
  have hHBound : H ≤ 2 * (ramificationIndex K : Int) - 2 := by
    exact_mod_cast hHBoundQ
  have hTwoE : A₁ + 2 ≤
      2 * (ramificationIndex K : Int) := by
    omega
  let x : Kˣ := (-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1
  have hxEven : Even (ordUnit K x) := by
    simpa only [x] using fullRawOrder_even a c profile hfirst
  have hrawStrict : (((A₁ : ℚ) : WithTop ℚ) <
      defectOrder (K := K) x) := by
    rw [← data.firstAlpha]
    exact hstrict.trans_le
      (a.truncatedPrefixDefect_le_defect c (-1) 3 1)
  have hraw : ((((A₁ + 2 : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) x) :=
    intCast_add_two_le_defectOrder_of_odd_of_even_ordUnit
      x A₁ hAodd hxEven hrawStrict hTwoE
  have hleft : ((((A₁ + 2 : Int) : ℚ) : WithTop ℚ) ≤
      a.prefixAlphaCap 3) := by
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
    exact_mod_cast data.betaThird
  have hrightStrict : (A₁ : ℚ) <
      c.alphaValue (0 : Fin (N + 4)) := by
    have htop := hstrict.trans_le
      (a.truncatedPrefixDefect_le_rightCap c (-1) 3 1)
    rw [data.firstAlpha,
      c.prefixAlphaCap_of_internal (by omega) (by omega)] at htop
    exact WithTop.coe_lt_coe.mp htop
  have hsourceHalfStep : ((A₁ + 1 : Int) : ℚ) ≤
      a.halfGapValue (0 : Fin (N + 4)) := by
    have hstep : A₁ + 1 ≤ H := by omega
    rw [hH]
    exact_mod_cast hstep
  have hhalfShift : a.halfGapValue (0 : Fin (N + 4)) + 1 ≤
      c.halfGapValue (0 : Fin (N + 4)) := by
    change (((a.order (1 : Fin (N + 5)) -
        a.order (0 : Fin (N + 5)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ)) + 1 ≤
      (((c.order (1 : Fin (N + 5)) -
        c.order (0 : Fin (N + 5)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ))
    have horderQ : (a.order (1 : Fin (N + 5)) : ℚ) + 2 ≤
        (c.order (1 : Fin (N + 5)) : ℚ) := by
      exact_mod_cast data.orderBounds.sourceSecondOrder
    have hfirstQ : (a.order (0 : Fin (N + 5)) : ℚ) =
        (c.order (0 : Fin (N + 5)) : ℚ) := by
      exact_mod_cast hfirst
    push_cast at ⊢
    linarith
  have hrightHalf : ((A₁ + 2 : Int) : ℚ) ≤
      c.halfGapValue (0 : Fin (N + 4)) := by
    push_cast at hsourceHalfStep ⊢
    linarith [hsourceHalfStep, hhalfShift]
  have hrightQ : ((A₁ + 2 : Int) : ℚ) ≤
      c.alphaValue (0 : Fin (N + 4)) := by
    letI : Beli2006AlphaLaws.{u, z} K := targetLaws
    letI : Beli2009AlphaParityLaws.{u, z} K := targetParity
    exact c.intCast_add_two_le_alphaValue_of_odd_of_lt_of_halfGap_le
      (0 : Fin (N + 4)) A₁ hAodd hrightStrict hrightHalf
  have hright : ((((A₁ + 2 : Int) : ℚ) : WithTop ℚ) ≤
      c.prefixAlphaCap 1) := by
    rw [c.prefixAlphaCap_of_internal (by omega) (by omega)]
    exact_mod_cast hrightQ
  unfold truncatedPrefixDefect
  simpa only [x] using le_min hraw (le_min hleft hright)

/-- The first scalar inequality in the isotropic half-gap branch. -/
theorem firstScalar_of_halfGapIsotropic
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [targetParity : Beli2009AlphaParityLaws.{u, z} K]
    {A₁ : Int}
    (a : GoodBONG q M (N + 5))
    (c : GoodBONG s Q (N + 5))
    (data : Beli2019Lemma912TypeIBetaData a c A₁ (A₁ + 1))
    (hstrict : (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1)
    (hbetaTwoE : A₁ + 1 ≤ 2 * (ramificationIndex K : Int)) :
    ((((A₁ + 1 : Int) : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect c (-1) 3 1) := by
  have hrawStrict : (((A₁ : ℚ) : WithTop ℚ) <
      defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1)) := by
    rw [← data.firstAlpha]
    exact hstrict.trans_le
      (a.truncatedPrefixDefect_le_defect c (-1) 3 1)
  have hraw := intCast_add_one_le_defectOrder_of_lt
    ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1) A₁ hrawStrict
  have hleft : ((((A₁ + 1 : Int) : ℚ) : WithTop ℚ) ≤
      a.prefixAlphaCap 3) := by
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
    exact_mod_cast data.betaThird
  have hrightStrict : (A₁ : ℚ) <
      c.alphaValue (0 : Fin (N + 4)) := by
    have htop := hstrict.trans_le
      (a.truncatedPrefixDefect_le_rightCap c (-1) 3 1)
    rw [data.firstAlpha,
      c.prefixAlphaCap_of_internal (by omega) (by omega)] at htop
    exact WithTop.coe_lt_coe.mp htop
  have hrightQ : ((A₁ + 1 : Int) : ℚ) ≤
      c.alphaValue (0 : Fin (N + 4)) := by
    letI : Beli2006AlphaLaws.{u, z} K := targetLaws
    letI : Beli2009AlphaParityLaws.{u, z} K := targetParity
    exact c.intCast_add_one_le_alphaValue_of_lt_of_le_twoE
      (0 : Fin (N + 4)) A₁ hbetaTwoE hrightStrict
  have hright : ((((A₁ + 1 : Int) : ℚ) : WithTop ℚ) ≤
      c.prefixAlphaCap 1) := by
    rw [c.prefixAlphaCap_of_internal (by omega) (by omega)]
    exact_mod_cast hrightQ
  unfold truncatedPrefixDefect
  exact le_min hraw (le_min hleft hright)

/-- The later scalar inequalities in the isotropic half-gap branch. -/
theorem laterScalar_of_halfGapIsotropic
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization
      (q := r) R₁ (R₂ + 2) R₁ (A₁ + 1))
    (E : Beli2019Lemma910Data a D)
    (hlength : 3 + N = N + 3)
    (horderTarget :
      (E.bong.castLength hlength).RepresentationOrderCondition c le_rfl)
    (hhalfFormula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K) :
    ∀ i : RepresentationIndex (N + 3) (N + 3), 2 ≤ i.val →
      ((E.bong.castLength hlength).representationAlphaValue c i :
          WithTop ℚ) ≤
        (((((E.bong.castLength hlength).order
              ⟨i.val, i.lt_large⟩ -
            (E.bong.castLength hlength).order
              (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          ((A₁ + 1 : Int) : ℚ) : ℚ) : WithTop ℚ) := by
  let target := E.bong.castLength hlength
  intro i hi
  have halpha : target.representationAlphaValue c i ≤
      target.halfGapValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ := by
    letI : Beli2006AlphaLaws.{u, z} K := targetLaws
    exact target.representationAlphaValue_le_sourceHalfGapValue_of_orderCondition
      c horderTarget i
  let current : Fin (N + 2) :=
    ⟨i.val - 1, by have := i.lt_large; omega⟩
  have hpair : target.adjacentOrderSum (0 : Fin (N + 2)) ≤
      target.adjacentOrderSum current := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    exact target.adjacentOrderSum_monotone
      (show (0 : Fin (N + 2)) ≤ current by
        change 0 ≤ i.val - 1
        omega)
  have hzeroCast : (0 : Fin (N + 2)).castSucc =
      (⟨0, by omega⟩ : Fin (N + 3)) := by rfl
  have hzeroSucc : (0 : Fin (N + 2)).succ =
      (⟨1, by omega⟩ : Fin (N + 3)) := by rfl
  have hcurrentCast : current.castSucc =
      (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have hcurrentSucc : current.succ =
      (⟨i.val, i.lt_large⟩ : Fin (N + 3)) := by
    apply Fin.ext
    simp [current]
    omega
  unfold adjacentOrderSum at hpair
  rw [hzeroCast, hzeroSucc, hcurrentCast, hcurrentSucc] at hpair
  have htargetZero : target.order
      (⟨0, by omega⟩ : Fin (N + 3)) = R₁ := by
    have h := E.order_castLength_prefix a D hlength (0 : Fin 3)
    rw [D.order_zero] at h
    change target.order _ = R₁ at h
    rw [show (⟨0, by omega⟩ : Fin (N + 3)) =
      ⟨(0 : Fin 3).val, by omega⟩ by
        apply Fin.ext
        simp]
    exact h
  have htargetOne : target.order
      (⟨1, by omega⟩ : Fin (N + 3)) = R₂ + 2 := by
    have h := E.order_castLength_prefix a D hlength (1 : Fin 3)
    rw [D.order_one] at h
    change target.order _ = R₂ + 2 at h
    rw [show (⟨1, by omega⟩ : Fin (N + 3)) =
      ⟨(1 : Fin 3).val, by omega⟩ by
        apply Fin.ext
        simp]
    exact h
  have hhalfBound : target.halfGapValue current ≤
      ((target.order ⟨i.val, i.lt_large⟩ -
          target.order (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
        ((A₁ + 1 : Int) : ℚ) := by
    unfold halfGapValue orderGap
    rw [hcurrentSucc, hcurrentCast]
    rw [htargetZero, htargetOne] at hpair
    rw [htargetOne]
    have hpairQ : (R₁ : ℚ) + ((R₂ + 2 : Int) : ℚ) ≤
        (target.order
          (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (N + 3)) : ℚ) +
          (target.order ⟨i.val, i.lt_large⟩ : ℚ) := by
      exact_mod_cast hpair
    push_cast at hpairQ hhalfFormula ⊢
    linarith [hpairQ]
  have hq : target.representationAlphaValue c i ≤
      ((target.order ⟨i.val, i.lt_large⟩ -
          target.order (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
        ((A₁ + 1 : Int) : ℚ) := by
    exact halpha.trans (by simpa only [current] using hhalfBound)
  exact_mod_cast hq

/-- Complete scalar package for the strict below-half-gap branch, in the
rank convention of Lemma 9.12. -/
theorem typeIScalarConditions_of_belowHalfGap
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [targetParity : Beli2009AlphaParityLaws.{u, z} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (N + 5))
    (c : GoodBONG s Q (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (data : Beli2019Lemma912TypeIBetaData a c A₁ (A₁ + 2))
    (D : Beli2019Lemma99Realization
      (q := r) R₁ (R₂ + 2) R₁ (A₁ + 2))
    (hsourceOrders : ∀ i : Fin 3,
      a.order (⟨i.1, by omega⟩ : Fin (N + 5)) =
        ![R₁, R₂, R₁] i)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hstrict : (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1)
    (hbelow : a.alphaValue (0 : Fin (N + 4)) <
      a.halfGapValue (0 : Fin (N + 4)))
    (E : Beli2019Lemma910Data
      (a.castLength (show N + 5 = 3 + (N + 2) by omega)) D)
    (hdefectSourceTarget : a.RepresentationDefectCondition
      (E.bong.castLength
        (show 3 + (N + 2) = (N + 2) + 3 by omega)))
    (hdefectSource : a.RepresentationDefectCondition c) :
    E.TypeIScalarConditions
      (a.castLength (show N + 5 = 3 + (N + 2) by omega)) c D
        (show 3 + (N + 2) = (N + 2) + 3 by omega) := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  letI : Beli2009AlphaParityLaws.{u, v} K := sourceParity
  let hambient : N + 5 = 3 + (N + 2) := by omega
  let hlength : 3 + (N + 2) = (N + 2) + 3 := by omega
  let ambient := a.castLength hambient
  have hambientOrders : ∀ i : Fin 3,
      ambient.order (Fin.castAdd (N + 2) i) = ![R₁, R₂, R₁] i := by
    intro i
    rw [show ambient = a.castLength hambient by rfl,
      GoodBONG.order_castLength]
    exact hsourceOrders i
  have hfirstScalar := firstScalar_of_belowHalfGap
    (sourceLaws := sourceLaws) (sourceParity := sourceParity)
    (targetLaws := targetLaws) (targetParity := targetParity)
    a c profile data hfirst hstrict hbelow
  have hfirstScalar' : ((((A₁ + 2 : Int) : ℚ) : WithTop ℚ) ≤
      (ambient.castLength hlength).truncatedPrefixDefect c (-1) 3 1) := by
    simpa only [ambient, castLength_castLength] using hfirstScalar
  have hdefectSourceTarget' :
      (ambient.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength) := by
    have hambientBack : ambient.castLength hlength = a := by
      exact castLength_castLength a hambient hlength
    rw [hambientBack]
    have htarget : E.bong.castLength hlength =
        E.bong.castLength
          (show 3 + (N + 2) = (N + 2) + 3 by omega) := by
      congr
    rw [htarget]
    exact hdefectSourceTarget
  have hdefectSource' :
      (ambient.castLength hlength).RepresentationDefectCondition c := by
    simpa only [ambient, castLength_castLength] using hdefectSource
  have hfirstAlpha : (ambient.castLength hlength).alphaValue
      (0 : Fin (N + 4)) = (A₁ : ℚ) := by
    simpa only [ambient, castLength_castLength] using data.firstAlpha
  change E.TypeIScalarConditions ambient c D hlength
  refine ⟨hfirstScalar', ?_⟩
  exact E.laterScalar_of_belowHalfGap
    (sourceLaws := sourceLaws) ambient c D hambientOrders hlength
      hdefectSourceTarget' hdefectSource' hfirstAlpha

/-- Complete scalar package for the equal-first-alpha, second-alpha-large
branch, in the rank convention of Lemma 9.12. -/
theorem typeIScalarConditions_of_equalSecondLarge
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (N + 5))
    (c : GoodBONG s Q (N + 5))
    (data : Beli2019Lemma912TypeIBetaData a c A₁ A₁)
    (D : Beli2019Lemma99Realization
      (q := r) R₁ (R₂ + 2) R₁ A₁)
    (hsourceOrders : ∀ i : Fin 3,
      a.order (⟨i.1, by omega⟩ : Fin (N + 5)) =
        ![R₁, R₂, R₁] i)
    (hfull : a.truncatedPrefixDefect c (-1) 3 1 =
      (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ))
    (hfirstAlpha : a.alphaValue (0 : Fin (N + 4)) =
      c.alphaValue (0 : Fin (N + 4)))
    (E : Beli2019Lemma910Data
      (a.castLength (show N + 5 = 3 + (N + 2) by omega)) D)
    (hdefectSourceTarget : a.RepresentationDefectCondition
      (E.bong.castLength
        (show 3 + (N + 2) = (N + 2) + 3 by omega))) :
    E.TypeIScalarConditions
      (a.castLength (show N + 5 = 3 + (N + 2) by omega)) c D
        (show 3 + (N + 2) = (N + 2) + 3 by omega) := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  let hambient : N + 5 = 3 + (N + 2) := by omega
  let hlength : 3 + (N + 2) = (N + 2) + 3 := by omega
  let ambient := a.castLength hambient
  have hambientOrders : ∀ i : Fin 3,
      ambient.order (Fin.castAdd (N + 2) i) = ![R₁, R₂, R₁] i := by
    intro i
    rw [show ambient = a.castLength hambient by rfl,
      GoodBONG.order_castLength]
    exact hsourceOrders i
  have hfirstScalar : (((A₁ : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect c (-1) 3 1) := by
    rw [hfull, data.firstAlpha]
  have hfirstScalar' : (((A₁ : ℚ) : WithTop ℚ) ≤
      (ambient.castLength hlength).truncatedPrefixDefect c (-1) 3 1) := by
    simpa only [ambient, castLength_castLength] using hfirstScalar
  have hdefectSourceTarget' :
      (ambient.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength) := by
    have hambientBack : ambient.castLength hlength = a := by
      exact castLength_castLength a hambient hlength
    rw [hambientBack]
    have htarget : E.bong.castLength hlength =
        E.bong.castLength
          (show 3 + (N + 2) = (N + 2) + 3 by omega) := by
      congr
    rw [htarget]
    exact hdefectSourceTarget
  have hsourceSecond : R₂ + 2 ≤
      c.order (⟨1, by omega⟩ : Fin (N + 5)) := by
    have hR₂ : a.order (1 : Fin (N + 5)) = R₂ := by
      simpa using hsourceOrders (1 : Fin 3)
    rw [show (⟨1, by omega⟩ : Fin (N + 5)) =
      (1 : Fin (N + 5)) by
        apply Fin.ext
        simp]
    simpa only [hR₂] using data.orderBounds.sourceSecondOrder
  have htargetFirstAlpha : c.alphaValue (0 : Fin (N + 4)) =
      (A₁ : ℚ) := hfirstAlpha.symm.trans data.firstAlpha
  change E.TypeIScalarConditions ambient c D hlength
  refine ⟨hfirstScalar', ?_⟩
  exact E.laterScalar_of_equalSecondLarge
    (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      ambient c D hambientOrders hlength hdefectSourceTarget'
        hsourceSecond htargetFirstAlpha

/-- Complete scalar package for the isotropic half-gap branch, in the rank
convention of Lemma 9.12. -/
theorem typeIScalarConditions_of_halfGapIsotropic
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [targetParity : Beli2009AlphaParityLaws.{u, z} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (N + 5))
    (c : GoodBONG s Q (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (data : Beli2019Lemma912TypeIBetaData a c A₁ (A₁ + 1))
    (D : Beli2019Lemma99Realization
      (q := r) R₁ (R₂ + 2) R₁ (A₁ + 1))
    (hsourceOrders : ∀ i : Fin 3,
      a.order (⟨i.1, by omega⟩ : Fin (N + 5)) =
        ![R₁, R₂, R₁] i)
    (hstrict : (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1)
    (hhalf : a.alphaValue (0 : Fin (N + 4)) =
      a.halfGapValue (0 : Fin (N + 4)))
    (E : Beli2019Lemma910Data
      (a.castLength (show N + 5 = 3 + (N + 2) by omega)) D)
    (horderTarget :
      (E.bong.castLength
        (show 3 + (N + 2) = (N + 2) + 3 by omega)).RepresentationOrderCondition
          c le_rfl) :
    E.TypeIScalarConditions
      (a.castLength (show N + 5 = 3 + (N + 2) by omega)) c D
        (show 3 + (N + 2) = (N + 2) + 3 by omega) := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  let hambient : N + 5 = 3 + (N + 2) := by omega
  let hlength : 3 + (N + 2) = (N + 2) + 3 := by omega
  let ambient := a.castLength hambient
  have hR₁ : a.order (0 : Fin (N + 5)) = R₁ := by
    simpa using hsourceOrders (0 : Fin 3)
  have hR₂ : a.order (1 : Fin (N + 5)) = R₂ := by
    simpa using hsourceOrders (1 : Fin 3)
  have hhalfFormula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    calc
      (A₁ : ℚ) = a.alphaValue (0 : Fin (N + 4)) :=
        data.firstAlpha.symm
      _ = a.halfGapValue (0 : Fin (N + 4)) := hhalf
      _ = ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
        unfold halfGapValue orderGap
        change (((a.order (1 : Fin (N + 5)) -
          a.order (0 : Fin (N + 5)) : Int) : ℚ) / 2 +
            (ramificationIndex K : ℚ)) = _
        rw [hR₁, hR₂]
  have hbetaTwoE : A₁ + 1 ≤
      2 * (ramificationIndex K : Int) := by
    have hbound := profile.firstGap_le_twoE_sub_two
    have hboundQ : (a.orderGap (0 : Fin (N + 4)) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) - 2 := by
      exact_mod_cast hbound
    have hhalfFormulaSource := hhalf
    rw [data.firstAlpha] at hhalfFormulaSource
    unfold halfGapValue at hhalfFormulaSource
    have hcast : ((A₁ + 1 : Int) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) := by
      push_cast at hhalfFormulaSource ⊢
      linarith [hboundQ]
    exact_mod_cast hcast
  have hfirstScalar := firstScalar_of_halfGapIsotropic
    (targetLaws := targetLaws) (targetParity := targetParity)
      a c data hstrict hbetaTwoE
  have hfirstScalar' : ((((A₁ + 1 : Int) : ℚ) : WithTop ℚ) ≤
      (ambient.castLength hlength).truncatedPrefixDefect c (-1) 3 1) := by
    simpa only [ambient, castLength_castLength] using hfirstScalar
  have horderTarget' :
      (E.bong.castLength hlength).RepresentationOrderCondition c le_rfl := by
    have htarget : E.bong.castLength hlength =
        E.bong.castLength
          (show 3 + (N + 2) = (N + 2) + 3 by omega) := by
      congr
    rw [htarget]
    exact horderTarget
  change E.TypeIScalarConditions ambient c D hlength
  refine ⟨hfirstScalar', ?_⟩
  exact E.laterScalar_of_halfGapIsotropic
    (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      ambient c D hlength horderTarget' hhalfFormula

end BONG.GoodBONG.Beli2019Lemma910Data

end Bong
