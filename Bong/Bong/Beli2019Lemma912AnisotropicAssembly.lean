/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912AnisotropicCentral

/-!
# Beli (2019), Lemma 9.12: anisotropic type-I assembly

This file assembles the scalar, parity, mixed-defect, and prefix-descent parts
of the anisotropic half-gap branch.  If a later type-I scalar inequality were
to fail, the resulting alternating order and alpha profiles would force a top
prefix representation and contradict anisotropy of the first three vectors.
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
  {L : Lattice K V} {M : Lattice K W} {Q : Lattice K U}
  {N : Nat}

/- In the anisotropic half-gap branch, all type-I scalar inequalities hold.

The source lattice, the comparison lattice, and the auxiliary realization of
Lemma 9.9 live in three independent quadratic spaces. -/
set_option maxHeartbeats 4000000 in
-- The proof assembles the full scalar-failure propagation and prefix descent.
theorem typeIScalarConditions_of_halfGapAnisotropic_core
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [comparisonParity : Beli2009AlphaParityLaws.{u, w} K]
    [structural : BONGStructuralLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (ambient : q.Represents r)
    (hsource : RepresentationConditions (a.castLength hlength) c le_rfl)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (horderTarget :
      (E.bong.castLength hlength).RepresentationOrderCondition c le_rfl)
    (hanisotropic :
      (a.castLength hlength).Lemma814FirstThreeAnisotropic)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K)
    (hgapSharp : R₂ - R₁ ≤ 2 * (ramificationIndex K : Int) - 4)
    (horderParity : Int.ModEq 2 R₁ R₂)
    (hcomparisonZero : c.order (0 : Fin (N + 3)) = R₁)
    (hcomparisonOne : R₂ + 2 ≤ c.order (1 : Fin (N + 3)))
    (hANonnegative : 0 ≤ A₁)
    (hAodd : Odd A₁)
    (hfirstStrict : (((A₁ : ℚ) : WithTop ℚ)) <
      (a.castLength hlength).truncatedPrefixDefect c (-1) 3 1)
    (hthirdStrict : ∀ hN : 0 < N, (A₁ : ℚ) <
      (a.castLength hlength).alphaValue
        (⟨2, by omega⟩ : Fin (N + 2))) :
    E.TypeIScalarConditions a c D hlength := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  have hsourcePrime : RepresentationConditionsPrime source c le_rfl := by
    exact RepresentationConditions.toPrime
      (sourceLaws := sourceLaws) (targetLaws := comparisonLaws) hsource
  have hcomparisonStrict : (A₁ : ℚ) <
      c.alphaValue (0 : Fin (N + 2)) := by
    have hcap := source.truncatedPrefixDefect_le_rightCap c (-1) 3 1
    rw [c.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    have hindex : (⟨1 - 1, by omega⟩ : Fin (N + 2)) =
        (0 : Fin (N + 2)) := rfl
    rw [hindex] at hcap
    exact WithTop.coe_lt_coe.mp (hfirstStrict.trans_le hcap)
  change E.TypeIScalarConditions a c D hlength
  refine ⟨hfirstStrict.le, ?_⟩
  intro i hiTwo
  apply le_of_not_gt
  intro hfailureTop
  have hfailure :
      (((target.order ⟨i.val, i.lt_large⟩ -
          target.order (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          (A₁ : ℚ)) < target.representationAlphaValue c i := by
    exact WithTop.coe_lt_coe.mp (by simpa only [target] using hfailureTop)
  have hbounds := @failureOrderBounds.{u, v, z, w}
    K _ _ _ _ _ V _ _ U _ _ W _ _ q s r L M N
    sourceLaws comparisonLaws R₁ R₂ A₁
    a c D E hlength horderTarget hformula i hiTwo hfailure
  have hsums := E.failureAdjacentSumEqualities
    (sourceLaws := sourceLaws) (sourceParity := sourceParity)
    (comparisonLaws := comparisonLaws)
    a c D horders hlength hdefectSourceTarget hsource.defectCondition
      hformula hgapSharp horderParity hcomparisonZero hcomparisonOne
      i hiTwo hfailure hbounds
  have hconsequences := E.failureConstantSumConsequences
    (sourceLaws := sourceLaws) (comparisonLaws := comparisonLaws)
    a c D hlength hcomparisonZero hcomparisonOne i hiTwo hsums
  have O := E.failureAlternatingOrders
    a c D hlength hcomparisonZero i hiTwo hconsequences
  have P := comparisonFirstAlphaProfile
    (comparisonLaws := comparisonLaws) (comparisonParity := comparisonParity)
    c hcomparisonZero hconsequences.comparisonOne_eq hformula hgapSharp
      hANonnegative hAodd hcomparisonStrict
  have C := comparisonAlphaAlternation
    target c i hconsequences O P hformula
  have S : Beli2019Lemma912SourceAlphaAlternation source A₁ i := by
    by_cases hiEq : i.val = 2
    · refine ⟨?_, ?_⟩
      · intro k hkTwo hki _
        omega
      · intro k hkTwo hki _
        omega
    · have hiThree : 3 ≤ i.val := by omega
      have hNpos : 0 < N := by
        have hilarge := i.lt_large
        omega
      have hprofile := E.sourceAlphaProfile
        (sourceLaws := sourceLaws) (sourceParity := sourceParity)
        a c D horders hlength i hiThree O P hformula
          (by simpa only [source] using hthirdStrict hNpos)
      exact E.sourceAlphaAlternation
        a c D horders hlength i hiThree O hprofile hformula
  have T := E.topMixedDefectBounds
    (sourceLaws := sourceLaws) (sourceParity := sourceParity)
    (comparisonLaws := comparisonLaws)
    (comparisonParity := comparisonParity)
    a c D horders hlength hdefectSourceTarget hsource.defectCondition
      i hiTwo hfailure O P hformula
  have hnext := E.nextEssential_of_failure
    (sourceLaws := sourceLaws) (comparisonLaws := comparisonLaws)
    (structural := structural)
    a c D horders hlength hdefectSourceTarget hsource.defectCondition
      i hiTwo hfailure O
  exact False.elim (E.false_of_anisotropic_of_failure
    (sourceLaws := sourceLaws) (comparisonLaws := comparisonLaws)
    (sourceParity := sourceParity)
    a c D horders hlength ambient hsourcePrime.centralRepresentations
      i hiTwo hanisotropic hnext O P S C T hformula horderParity)

/- The outer wrapper converts the rank convention of Lemma 9.12 to the
`3 + N` convention used by the scalar-failure descent. -/
set_option maxHeartbeats 4000000 in
-- Several casts are kept explicit so the three ambient spaces remain visible.
theorem typeIScalarConditions_of_halfGapAnisotropic
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [comparisonParity : Beli2009AlphaParityLaws.{u, w} K]
    [structural : BONGStructuralLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (reference : GoodBONG s Q 3)
    (C : Beli2019Lemma99Conditions reference R₁ R₂ A₁)
    (a : GoodBONG q L (N + 5))
    (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (data : Beli2019Lemma912TypeIBetaData a c A₁ A₁)
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (hsourceOrders : ∀ i : Fin 3,
      a.order (⟨i.1, by omega⟩ : Fin (N + 5)) = ![R₁, R₂, R₁] i)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hstrict : (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1)
    (hhalf : a.alphaValue (0 : Fin (N + 4)) =
      a.halfGapValue (0 : Fin (N + 4)))
    (hrefIsotropy : reference.Lemma814FirstThreeIsotropic ↔
      a.Lemma814FirstThreeIsotropic)
    (E : Beli2019Lemma910Data
      (a.castLength (show N + 5 = 3 + (N + 2) by omega)) D)
    (ambientRepresentation : q.Represents r)
    (hsource : RepresentationConditions a c le_rfl)
    (hdefectSourceTarget : a.RepresentationDefectCondition
      (E.bong.castLength
        (show 3 + (N + 2) = (N + 2) + 3 by omega)))
    (horderTarget :
      (E.bong.castLength
        (show 3 + (N + 2) = (N + 2) + 3 by omega)).RepresentationOrderCondition
          c le_rfl)
    (hanisotropic : a.Lemma814FirstThreeAnisotropic) :
    E.TypeIScalarConditions
      (a.castLength (show N + 5 = 3 + (N + 2) by omega)) c D
        (show 3 + (N + 2) = (N + 2) + 3 by omega) := by
  let hambient : N + 5 = 3 + (N + 2) := by omega
  let hlength : 3 + (N + 2) = (N + 2) + 3 := by omega
  let source := a.castLength hambient
  have hR₁ : a.order (0 : Fin (N + 5)) = R₁ := by
    simpa using hsourceOrders (0 : Fin 3)
  have hR₂ : a.order (1 : Fin (N + 5)) = R₂ := by
    simpa using hsourceOrders (1 : Fin 3)
  have hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    calc
      (A₁ : ℚ) = a.alphaValue (0 : Fin (N + 4)) := data.firstAlpha.symm
      _ = a.halfGapValue (0 : Fin (N + 4)) := hhalf
      _ = ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
        unfold halfGapValue orderGap
        change (((a.order (1 : Fin (N + 5)) -
          a.order (0 : Fin (N + 5)) : Int) : ℚ) / 2 +
            (ramificationIndex K : ℚ)) = _
        rw [hR₁, hR₂]
  have hgapSharp : R₂ - R₁ ≤
      2 * (ramificationIndex K : Int) - 4 := by
    have h :=
      a.beli2019Lemma912_firstGap_le_twoE_sub_four_of_strict_anisotropic
        (alphaV := sourceLaws) (parityV := sourceParity)
        (alphaW := comparisonLaws) (parityW := comparisonParity)
        c profile hstrict hhalf hanisotropic
    unfold orderGap at h
    change a.order (1 : Fin (N + 5)) - a.order (0 : Fin (N + 5)) ≤
      2 * (ramificationIndex K : Int) - 4 at h
    simpa only [hR₁, hR₂] using h
  have hrefAnisotropic : reference.Lemma814FirstThreeAnisotropic := by
    apply (reference.not_firstThreeIsotropic_iff_anisotropic).mp
    intro hrefIsotropic
    exact a.not_firstThreeIsotropic_of_anisotropic hanisotropic
      (hrefIsotropy.mp hrefIsotropic)
  have hAodd : Odd A₁ := Int.not_even_iff_odd.mp (by
    intro hAeven
    exact reference.not_firstThreeIsotropic_of_anisotropic hrefAnisotropic
      (C.evenBoundary hAeven).2)
  have hANonnegative : 0 ≤ A₁ :=
    (le_max_left 0 (R₂ - R₁)).trans C.lower
  have hcomparisonZero : c.order (0 : Fin (N + 5)) = R₁ :=
    hfirst.symm.trans hR₁
  have hcomparisonOne : R₂ + 2 ≤ c.order (1 : Fin (N + 5)) := by
    simpa only [hR₂] using data.orderBounds.sourceSecondOrder
  have hsourceOrders' : ∀ i : Fin 3,
      source.order (Fin.castAdd (N + 2) i) = ![R₁, R₂, R₁] i := by
    intro i
    rw [show source = a.castLength hambient by rfl, GoodBONG.order_castLength]
    exact hsourceOrders i
  have hsource' : RepresentationConditions (source.castLength hlength) c le_rfl := by
    simpa only [source, castLength_castLength] using hsource
  have hdefectSourceTarget' :
      (source.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength) := by
    have hsourceBack : source.castLength hlength = a := by
      exact castLength_castLength a hambient hlength
    rw [hsourceBack]
    have htarget : E.bong.castLength hlength = E.bong.castLength
        (show 3 + (N + 2) = (N + 2) + 3 by omega) := by congr
    rw [htarget]
    exact hdefectSourceTarget
  have horderTarget' :
      (E.bong.castLength hlength).RepresentationOrderCondition c le_rfl := by
    have htarget : E.bong.castLength hlength = E.bong.castLength
        (show 3 + (N + 2) = (N + 2) + 3 by omega) := by congr
    rw [htarget]
    exact horderTarget
  have hanisotropic' :
      (source.castLength hlength).Lemma814FirstThreeAnisotropic := by
    simpa only [source, castLength_castLength] using hanisotropic
  have hfirstStrict : (((A₁ : ℚ) : WithTop ℚ)) <
      (source.castLength hlength).truncatedPrefixDefect c (-1) 3 1 := by
    simpa only [source, castLength_castLength, data.firstAlpha] using hstrict
  have hthirdStrict : (A₁ : ℚ) <
      (source.castLength hlength).alphaValue
        (⟨2, by omega⟩ : Fin ((N + 2) + 2)) := by
    have hsourceBack : source.castLength hlength = a := by
      exact castLength_castLength a hambient hlength
    rw [hsourceBack]
    have h := a.beli2019Lemma912_firstAlpha_lt_thirdAlpha_of_fullDefect_strict
      c hstrict
    rw [data.firstAlpha] at h
    convert h using 1
    congr 1
  change E.TypeIScalarConditions source c D hlength
  exact E.typeIScalarConditions_of_halfGapAnisotropic_core
    (sourceLaws := sourceLaws) (comparisonLaws := comparisonLaws)
    (sourceParity := sourceParity) (comparisonParity := comparisonParity)
    (structural := structural)
    source c D hsourceOrders' hlength ambientRepresentation hsource'
      hdefectSourceTarget' horderTarget' hanisotropic' hformula hgapSharp
      C.orderParity hcomparisonZero hcomparisonOne hANonnegative hAodd
      hfirstStrict (fun _ => hthirdStrict)

end BONG.GoodBONG.Beli2019Lemma910Data

end Bong
