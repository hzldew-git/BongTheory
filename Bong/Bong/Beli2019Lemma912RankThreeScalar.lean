/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912RankThreeLemma99
import Bong.Bong.Beli2019Lemma912ScalarConditions
import Bong.Bong.Beli2019Lemma912AnisotropicAssembly

/-!
# Beli (2019), Lemma 9.12: ternary type-I scalar inequalities

At rank three the source prefix of length three is the full lattice.  Its
alpha cap is therefore infinity.  This endpoint identity replaces the
fourth-coordinate estimate used in the higher-rank proof of the first scalar
inequality.  The later scalar estimates were already proved uniformly in the
tail length and are instantiated here with tail length zero.
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

/-- The signed raw product in the ternary residual profile has even order. -/
theorem fullRawOrder_even_rankThree
    (a : GoodBONG q M 3) (c : GoodBONG s Q 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c)
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin 3)) :
    Even (ordUnit K ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1)) := by
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
        a.order (0 : Fin 3) + a.order (1 : Fin 3) +
          a.order (2 : Fin 3) + c.order (0 : Fin 3) := by
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
  refine ⟨2 * a.order (0 : Fin 3) + z, ?_⟩
  unfold orderGap at hz
  have hsucc : (0 : Fin 2).succ = (1 : Fin 3) := by rfl
  have hcast : (0 : Fin 2).castSucc = (0 : Fin 3) := by rfl
  rw [hsucc, hcast] at hz
  omega

/-- Odd integral alpha values cannot make a one-step jump before their
half-gap. -/
private theorem intCast_add_two_le_alphaValue_of_odd_of_lt_of_halfGap_le_rankThree
    [Beli2006AlphaLaws.{u, z} K]
    [Beli2009AlphaParityLaws.{u, z} K]
    (c : GoodBONG s Q 3) (i : Fin 2) (z₀ : Int)
    (hzOdd : Odd z₀) (hlt : (z₀ : ℚ) < c.alphaValue i)
    (hhalf : ((z₀ + 2 : Int) : ℚ) ≤ c.halfGapValue i) :
    ((z₀ + 2 : Int) : ℚ) ≤ c.alphaValue i := by
  by_cases heq : c.alphaValue i = c.halfGapValue i
  · rw [heq]
    exact hhalf
  · rcases c.beli2009Lemma27_iv i heq with ⟨w, hwOdd, hw⟩
    have hzw : z₀ < w := by
      exact_mod_cast (show (z₀ : ℚ) < (w : ℚ) by simpa only [← hw] using hlt)
    rcases hzOdd with ⟨p, hp⟩
    rcases hwOdd with ⟨t, ht⟩
    have hstep : z₀ + 2 ≤ w := by omega
    rw [hw]
    exact_mod_cast hstep

set_option maxHeartbeats 3000000 in
-- The ternary scalar proof normalizes several `WithTop` defect inequalities.
/-- First scalar inequality in the ternary below-half-gap branch. -/
theorem firstScalar_of_belowHalfGap_rankThree
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [targetParity : Beli2009AlphaParityLaws.{u, z} K]
    {A₁ : Int}
    (a : GoodBONG q M 3) (c : GoodBONG s Q 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c)
    (data : Beli2019Lemma912TypeIBetaDataRankThree a c A₁ (A₁ + 2))
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin 3))
    (hstrict : (a.alphaValue (0 : Fin 2) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1)
    (hbelow : a.alphaValue (0 : Fin 2) < a.halfGapValue (0 : Fin 2)) :
    ((((A₁ + 2 : Int) : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect c (-1) 3 1) := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  letI : Beli2009AlphaParityLaws.{u, v} K := sourceParity
  have hAoddRational :=
    a.beli2019Lemma912_firstAlpha_odd_of_below_halfGap_rankThree hbelow
  have hAodd : Odd A₁ := by
    rcases hAoddRational with ⟨z, hzOdd, hz⟩
    have hAz : A₁ = z := by exact_mod_cast data.firstAlpha.symm.trans hz
    simpa only [hAz] using hzOdd
  have hgapSharp :=
    a.beli2019Lemma912_firstGap_le_twoE_sub_four_of_below_halfGap_rankThree
      c profile hbelow
  rcases a.halfGapValue_isRationalInteger_of_even
      (0 : Fin 2) profile.firstGap_even with ⟨H, hH⟩
  have hAH : A₁ < H := by
    exact_mod_cast (show (A₁ : ℚ) < (H : ℚ) by
      simpa only [← data.firstAlpha, ← hH] using hbelow)
  have hHBoundQ : (H : ℚ) ≤ 2 * (ramificationIndex K : ℚ) - 2 := by
    have hgapQ : (a.orderGap (0 : Fin 2) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) - 4 := by exact_mod_cast hgapSharp
    rw [← hH]
    unfold halfGapValue
    linarith
  have hHBound : H ≤ 2 * (ramificationIndex K : Int) - 2 := by
    exact_mod_cast hHBoundQ
  have hTwoE : A₁ + 2 ≤ 2 * (ramificationIndex K : Int) := by omega
  let x : Kˣ := (-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1
  have hxEven : Even (ordUnit K x) := by
    simpa only [x] using fullRawOrder_even_rankThree a c profile hfirst
  have hrawStrict : (((A₁ : ℚ) : WithTop ℚ) < defectOrder (K := K) x) := by
    rw [← data.firstAlpha]
    exact hstrict.trans_le (a.truncatedPrefixDefect_le_defect c (-1) 3 1)
  have hraw : ((((A₁ + 2 : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) x) :=
    intCast_add_two_le_defectOrder_of_odd_of_even_ordUnit
      x A₁ hAodd hxEven hrawStrict hTwoE
  have hleft : ((((A₁ + 2 : Int) : ℚ) : WithTop ℚ) ≤
      a.prefixAlphaCap 3) := by
    rw [show 3 = 2 + 1 by omega, a.prefixAlphaCap_last]
    exact le_top
  have hrightStrict : (A₁ : ℚ) < c.alphaValue (0 : Fin 2) := by
    have htop := hstrict.trans_le
      (a.truncatedPrefixDefect_le_rightCap c (-1) 3 1)
    rw [data.firstAlpha,
      c.prefixAlphaCap_of_internal (by omega) (by omega)] at htop
    exact WithTop.coe_lt_coe.mp htop
  have hsourceHalfStep : ((A₁ + 1 : Int) : ℚ) ≤
      a.halfGapValue (0 : Fin 2) := by
    have hstep : A₁ + 1 ≤ H := by omega
    rw [hH]
    exact_mod_cast hstep
  have hhalfShift : a.halfGapValue (0 : Fin 2) + 1 ≤
      c.halfGapValue (0 : Fin 2) := by
    unfold halfGapValue orderGap
    have hsucc : (0 : Fin 2).succ = (1 : Fin 3) := by rfl
    have hcast : (0 : Fin 2).castSucc = (0 : Fin 3) := by rfl
    rw [hsucc, hcast]
    have horderQ : (a.order (1 : Fin 3) : ℚ) + 2 ≤
        (c.order (1 : Fin 3) : ℚ) := by
      exact_mod_cast data.sourceSecondOrder
    have hfirstQ : (a.order (0 : Fin 3) : ℚ) =
        (c.order (0 : Fin 3) : ℚ) := by exact_mod_cast hfirst
    push_cast
    linarith
  have hrightHalf : ((A₁ + 2 : Int) : ℚ) ≤
      c.halfGapValue (0 : Fin 2) := by
    push_cast at hsourceHalfStep ⊢
    linarith [hsourceHalfStep, hhalfShift]
  have hrightQ : ((A₁ + 2 : Int) : ℚ) ≤
      c.alphaValue (0 : Fin 2) := by
    letI : Beli2006AlphaLaws.{u, z} K := targetLaws
    letI : Beli2009AlphaParityLaws.{u, z} K := targetParity
    exact intCast_add_two_le_alphaValue_of_odd_of_lt_of_halfGap_le_rankThree
      c (0 : Fin 2) A₁ hAodd hrightStrict hrightHalf
  have hright : ((((A₁ + 2 : Int) : ℚ) : WithTop ℚ) ≤
      c.prefixAlphaCap 1) := by
    rw [c.prefixAlphaCap_of_internal (by omega) (by omega)]
    exact_mod_cast hrightQ
  unfold truncatedPrefixDefect
  simpa only [x] using le_min hraw (le_min hleft hright)

/-- First scalar inequality at an isotropic ternary half-gap. -/
theorem firstScalar_of_halfGapIsotropic_rankThree
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [targetParity : Beli2009AlphaParityLaws.{u, z} K]
    {A₁ : Int}
    (a : GoodBONG q M 3) (c : GoodBONG s Q 3)
    (data : Beli2019Lemma912TypeIBetaDataRankThree a c A₁ (A₁ + 1))
    (hstrict : (a.alphaValue (0 : Fin 2) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1)
    (hbetaTwoE : A₁ + 1 ≤ 2 * (ramificationIndex K : Int)) :
    ((((A₁ + 1 : Int) : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect c (-1) 3 1) := by
  have hrawStrict : (((A₁ : ℚ) : WithTop ℚ) <
      defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1)) := by
    rw [← data.firstAlpha]
    exact hstrict.trans_le (a.truncatedPrefixDefect_le_defect c (-1) 3 1)
  have hraw := intCast_add_one_le_defectOrder_of_lt
    ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1) A₁ hrawStrict
  have hleft : ((((A₁ + 1 : Int) : ℚ) : WithTop ℚ) ≤
      a.prefixAlphaCap 3) := by
    rw [show 3 = 2 + 1 by omega, a.prefixAlphaCap_last]
    exact le_top
  have hrightStrict : (A₁ : ℚ) < c.alphaValue (0 : Fin 2) := by
    have htop := hstrict.trans_le
      (a.truncatedPrefixDefect_le_rightCap c (-1) 3 1)
    rw [data.firstAlpha,
      c.prefixAlphaCap_of_internal (by omega) (by omega)] at htop
    exact WithTop.coe_lt_coe.mp htop
  have hrightQ : ((A₁ + 1 : Int) : ℚ) ≤ c.alphaValue (0 : Fin 2) := by
    letI : Beli2006AlphaLaws.{u, z} K := targetLaws
    letI : Beli2009AlphaParityLaws.{u, z} K := targetParity
    exact c.intCast_add_one_le_alphaValue_of_lt_of_le_twoE
      (0 : Fin 2) A₁ hbetaTwoE hrightStrict
  have hright : ((((A₁ + 1 : Int) : ℚ) : WithTop ℚ) ≤
      c.prefixAlphaCap 1) := by
    rw [c.prefixAlphaCap_of_internal (by omega) (by omega)]
    exact_mod_cast hrightQ
  unfold truncatedPrefixDefect
  exact le_min hraw (le_min hleft hright)

/-- Complete ternary scalar package in the equal-alpha large-second-alpha
branch. -/
theorem typeIScalarConditions_of_equalSecondLarge_rankThree
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (3 + 0)) (c : GoodBONG s Q (0 + 3))
    (data : Beli2019Lemma912TypeIBetaDataRankThree a c A₁ A₁)
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data (N := 0) a D)
    (horders : ∀ i : Fin 3, a.order (Fin.castAdd 0 i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + 0 = 0 + 3)
    (hfull : a.truncatedPrefixDefect c (-1) 3 1 =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hfirstAlpha : a.alphaValue (0 : Fin 2) = c.alphaValue (0 : Fin 2))
    (hdefectSourceTarget : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength)) :
    E.TypeIScalarConditions a c D hlength := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  have haCast : a.castLength hlength = a := by
    cases hlength
    rfl
  refine ⟨?_, ?_⟩
  · rw [haCast, hfull, data.firstAlpha]
  · have htargetFirstAlpha : c.alphaValue (0 : Fin 2) = (A₁ : ℚ) :=
      hfirstAlpha.symm.trans data.firstAlpha
    have hR₂ : a.order (1 : Fin 3) = R₂ := by
      simpa using horders (1 : Fin 3)
    have hsourceSecond : R₂ + 2 ≤ c.order (1 : Fin 3) := by
      simpa only [hR₂] using data.sourceSecondOrder
    exact E.laterScalar_of_equalSecondLarge
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      a c D horders hlength hdefectSourceTarget
        hsourceSecond htargetFirstAlpha

/-- Complete ternary scalar package in the below-half-gap branch. -/
theorem typeIScalarConditions_of_belowHalfGap_rankThree
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [targetParity : Beli2009AlphaParityLaws.{u, z} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (3 + 0)) (c : GoodBONG s Q (0 + 3))
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c)
    (data : Beli2019Lemma912TypeIBetaDataRankThree a c A₁ (A₁ + 2))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ (A₁ + 2))
    (E : Beli2019Lemma910Data (N := 0) a D)
    (horders : ∀ i : Fin 3, a.order (Fin.castAdd 0 i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + 0 = 0 + 3)
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin 3))
    (hstrict : (a.alphaValue (0 : Fin 2) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1)
    (hbelow : a.alphaValue (0 : Fin 2) < a.halfGapValue (0 : Fin 2))
    (hdefectSourceTarget : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (hdefectSource : (a.castLength hlength).RepresentationDefectCondition c) :
    E.TypeIScalarConditions a c D hlength := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  have haCast : a.castLength hlength = a := by
    cases hlength
    rfl
  refine ⟨?_, ?_⟩
  · rw [haCast]
    exact firstScalar_of_belowHalfGap_rankThree
      (sourceLaws := sourceLaws) (sourceParity := sourceParity)
      (targetLaws := targetLaws) (targetParity := targetParity)
      a c profile data hfirst hstrict hbelow
  · have hfirstAlpha : (a.castLength hlength).alphaValue
        (0 : Fin 2) = (A₁ : ℚ) := by
      rw [haCast]
      exact data.firstAlpha
    exact E.laterScalar_of_belowHalfGap
      (sourceLaws := sourceLaws) a c D horders hlength
        hdefectSourceTarget hdefectSource hfirstAlpha

/-- Complete ternary scalar package at the isotropic half-gap. -/
theorem typeIScalarConditions_of_halfGapIsotropic_rankThree
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [targetParity : Beli2009AlphaParityLaws.{u, z} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (3 + 0)) (c : GoodBONG s Q (0 + 3))
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c)
    (data : Beli2019Lemma912TypeIBetaDataRankThree a c A₁ (A₁ + 1))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ (A₁ + 1))
    (E : Beli2019Lemma910Data (N := 0) a D)
    (horders : ∀ i : Fin 3, a.order (Fin.castAdd 0 i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + 0 = 0 + 3)
    (hstrict : (a.alphaValue (0 : Fin 2) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1)
    (hhalf : a.alphaValue (0 : Fin 2) = a.halfGapValue (0 : Fin 2))
    (horderTarget : (E.bong.castLength hlength).RepresentationOrderCondition
      c le_rfl) :
    E.TypeIScalarConditions a c D hlength := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  have haCast : a.castLength hlength = a := by
    cases hlength
    rfl
  have hR₁ : a.order (0 : Fin 3) = R₁ := by
    simpa using horders (0 : Fin 3)
  have hR₂ : a.order (1 : Fin 3) = R₂ := by
    simpa using horders (1 : Fin 3)
  have hhalfFormula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    calc
      (A₁ : ℚ) = a.alphaValue (0 : Fin 2) := data.firstAlpha.symm
      _ = a.halfGapValue (0 : Fin 2) := hhalf
      _ = ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
        unfold halfGapValue orderGap
        have hsucc : (0 : Fin 2).succ = (1 : Fin 3) := by rfl
        have hcast : (0 : Fin 2).castSucc = (0 : Fin 3) := by rfl
        rw [hsucc, hcast, hR₁, hR₂]
  have hbetaTwoE : A₁ + 1 ≤ 2 * (ramificationIndex K : Int) := by
    have hboundQ : (a.orderGap (0 : Fin 2) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) - 2 := by
      exact_mod_cast profile.firstGap_le_twoE_sub_two
    have hhalfSource := hhalf
    rw [data.firstAlpha] at hhalfSource
    unfold halfGapValue at hhalfSource
    have hcast : ((A₁ + 1 : Int) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) := by
      push_cast at hhalfSource ⊢
      linarith [hboundQ]
    exact_mod_cast hcast
  refine ⟨?_, ?_⟩
  · rw [haCast]
    exact firstScalar_of_halfGapIsotropic_rankThree
      (targetLaws := targetLaws) (targetParity := targetParity)
        a c data hstrict hbetaTwoE
  · exact E.laterScalar_of_halfGapIsotropic
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
        a c D hlength horderTarget hhalfFormula

/-- Complete ternary scalar package at an anisotropic half-gap away from the
exceptional `2e-2` endpoint.  This is the tail-length-zero specialization of
the scalar-failure propagation argument. -/
theorem typeIScalarConditions_of_halfGapAnisotropic_rankThree
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, z} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [comparisonParity : Beli2009AlphaParityLaws.{u, z} K]
    [structural : BONGStructuralLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (3 + 0)) (c : GoodBONG s Q (0 + 3))
    (C : Beli2019Lemma99Conditions a R₁ R₂ A₁)
    (data : Beli2019Lemma912TypeIBetaDataRankThree a c A₁ A₁)
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data (N := 0) a D)
    (horders : ∀ i : Fin 3, a.order (Fin.castAdd 0 i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + 0 = 0 + 3)
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin 3))
    (hstrict : (a.alphaValue (0 : Fin 2) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1)
    (hhalf : a.alphaValue (0 : Fin 2) = a.halfGapValue (0 : Fin 2))
    (hgapSharp : a.orderGap (0 : Fin 2) ≤
      2 * (ramificationIndex K : Int) - 4)
    (ambient : q.Represents s)
    (hsource : RepresentationConditions (a.castLength hlength) c le_rfl)
    (hdefectSourceTarget : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (horderTarget : (E.bong.castLength hlength).RepresentationOrderCondition
      c le_rfl)
    (hanisotropic : (a.castLength hlength).Lemma814FirstThreeAnisotropic) :
    E.TypeIScalarConditions a c D hlength := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  letI : Beli2009AlphaParityLaws.{u, v} K := sourceParity
  have hR₁ : a.order (0 : Fin 3) = R₁ := by
    simpa using horders (0 : Fin 3)
  have hR₂ : a.order (1 : Fin 3) = R₂ := by
    simpa using horders (1 : Fin 3)
  have hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    calc
      (A₁ : ℚ) = a.alphaValue (0 : Fin 2) := data.firstAlpha.symm
      _ = a.halfGapValue (0 : Fin 2) := hhalf
      _ = ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
        unfold halfGapValue orderGap
        have hsucc : (0 : Fin 2).succ = (1 : Fin 3) := by rfl
        have hcast : (0 : Fin 2).castSucc = (0 : Fin 3) := by rfl
        rw [hsucc, hcast, hR₁, hR₂]
  have hgapSharp' : R₂ - R₁ ≤
      2 * (ramificationIndex K : Int) - 4 := by
    unfold orderGap at hgapSharp
    have hsucc : (0 : Fin 2).succ = (1 : Fin 3) := by rfl
    have hcast : (0 : Fin 2).castSucc = (0 : Fin 3) := by rfl
    rw [hsucc, hcast, hR₁, hR₂] at hgapSharp
    exact hgapSharp
  have haCast : a.castLength hlength = a := by
    cases hlength
    rfl
  have hanisotropicA : a.Lemma814FirstThreeAnisotropic := by
    simpa only [haCast] using hanisotropic
  have hAodd : Odd A₁ := Int.not_even_iff_odd.mp (by
    intro hAeven
    exact a.not_firstThreeIsotropic_of_anisotropic hanisotropicA
      (C.evenBoundary hAeven).2)
  have hANonnegative : 0 ≤ A₁ :=
    (le_max_left 0 (R₂ - R₁)).trans C.lower
  have hcomparisonZero : c.order (0 : Fin 3) = R₁ :=
    hfirst.symm.trans hR₁
  have hcomparisonOne : R₂ + 2 ≤ c.order (1 : Fin 3) := by
    simpa only [hR₂] using data.sourceSecondOrder
  have hfirstStrict : (((A₁ : ℚ) : WithTop ℚ)) <
      (a.castLength hlength).truncatedPrefixDefect c (-1) 3 1 := by
    simpa only [haCast, data.firstAlpha] using hstrict
  exact E.typeIScalarConditions_of_halfGapAnisotropic_core
    (sourceLaws := sourceLaws) (comparisonLaws := comparisonLaws)
    (sourceParity := sourceParity) (comparisonParity := comparisonParity)
    (structural := structural)
    a c D horders hlength ambient hsource hdefectSourceTarget horderTarget
      hanisotropic hformula hgapSharp' C.orderParity hcomparisonZero
      hcomparisonOne hANonnegative hAodd hfirstStrict (by
        intro hzero
        omega)

/-- At the excluded ternary endpoint, strictness raises the capped defect
from `2e-1` to the exact Lemma 9.6 lower bound `2e`. -/
theorem lemma96DefectBound_of_anisotropicBoundary_rankThree
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [targetParity : Beli2009AlphaParityLaws.{u, z} K]
    {A₁ : Int}
    (a : GoodBONG q M 3) (c : GoodBONG s Q 3)
    (data : Beli2019Lemma912TypeIBetaDataRankThree a c A₁ A₁)
    (hgap : a.orderGap (0 : Fin 2) =
      2 * (ramificationIndex K : Int) - 2)
    (hhalf : a.alphaValue (0 : Fin 2) = a.halfGapValue (0 : Fin 2))
    (hstrict : (a.alphaValue (0 : Fin 2) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1) :
    a.Beli2019Lemma96DefectBound c := by
  have hAeq : A₁ + 1 = 2 * (ramificationIndex K : Int) := by
    have hformula := hhalf
    rw [data.firstAlpha] at hformula
    unfold halfGapValue at hformula
    rw [hgap] at hformula
    have hformulaQ : (A₁ : ℚ) =
        2 * (ramificationIndex K : ℚ) - 1 := by
      push_cast at hformula ⊢
      linarith
    exact_mod_cast (show (A₁ : ℚ) + 1 =
      2 * (ramificationIndex K : ℚ) by linarith [hformulaQ])
  let shiftedData : Beli2019Lemma912TypeIBetaDataRankThree
      a c A₁ (A₁ + 1) := {
    firstAlpha := data.firstAlpha
    betaLower := by omega
    betaUpper := by omega
    sourceSecondOrder := data.sourceSecondOrder }
  have hscalar := firstScalar_of_halfGapIsotropic_rankThree
    (targetLaws := targetLaws) (targetParity := targetParity)
      a c shiftedData hstrict (by omega)
  unfold Beli2019Lemma96DefectBound
  have hcast : ((((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) =
      ((((A₁ + 1 : Int) : ℚ) : WithTop ℚ)) := by
    rw [hAeq]
    norm_num
  rw [hcast]
  exact hscalar

end BONG.GoodBONG.Beli2019Lemma910Data

end Bong
