/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCTheorem72
import Bong.Bong.He2023ADCPublishedParameterDomain
import Bong.Bong.He2023ADCOddMaximalStructure
import Bong.Bong.UnaryBinaryModelRepresentation

/-!
# He (2025), Theorem 7.2 with the published finite parameters

This file converts the representative-independent classification into the
literal finite presentation printed in Theorem 7.2.  The even base parameter
lies in U minus {1, Delta} and the unary coefficient is one of epsilon or
epsilon times pi, with both parameters chosen from the same complete normalized
system of unit square-class representatives.
-/

namespace Bong

open Dyadic Module HeHuPublishedSquareClassIndex

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The literal base-parameter domain U minus {1, Delta} in Theorem 7.2. -/
structure HeADC2025Theorem72BaseIndex {I : Type u} (U : I → Kˣ) where
  index : I
  notOne : U index ≠ 1
  notDiscriminant :
    U index ≠
      (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit

namespace HeADC2025Theorem72BaseIndex

/-- The two literal exclusions recover the sharp-domain proof needed to
construct the second named maximal lattice. -/
theorem sharp {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (hDelta : ∃ i,
      U i = (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (b : HeADC2025Theorem72BaseIndex (K := K) U) :
    HeHuSharpDomain (U b.index) := by
  apply (heADCSharpDomain_publishedParameter_iff U hU hDelta
    (b.index, false)).2
  simpa using And.intro b.notOne b.notDiscriminant

end HeADC2025Theorem72BaseIndex

/-- The finite product family printed in Theorem 7.2.  The Boolean component
of p is the exponent k in {0,1} on the uniformizer. -/
def HeADC2025Theorem72PublishedProduct {I : Type u} [Fintype I]
    (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (hDelta : ∃ i,
      U i = (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (q : QuadraticSpace K V) (L : Lattice K V) (k : Nat) : Prop :=
  (∃ (b : HeADC2025Theorem72BaseIndex (K := K) U)
      (p : HeHuPublishedSquareClassIndex I),
    Lattice.IsIsometric q
      ((BONG.coefficientDiagonalSpace
        (heADCW1Even (k + 1) (U b.index))).orthogonalSum
        ((QuadraticSpace.line K).rescaleUnit (parameter U p))) L
      (Lattice.product (heADCN1Even (k + 1) (U b.index)).lattice
        (BONG.unaryModelLattice (K := K)))) ∨
  (∃ (b : HeADC2025Theorem72BaseIndex (K := K) U)
      (p : HeHuPublishedSquareClassIndex I),
    let hs := b.sharp U hU hDelta
    Lattice.IsIsometric q
      ((BONG.coefficientDiagonalSpace
        (heADCW2Even (k + 1) (U b.index)
          (Or.inr hs.notSquare))).orthogonalSum
        ((QuadraticSpace.line K).rescaleUnit (parameter U p))) L
      (Lattice.product
        (heADCN2Even (k + 1) (U b.index)
          (Or.inr hs.notSquare)).lattice
        (BONG.unaryModelLattice (K := K))))

/-- Every published unary parameter has order zero or one. -/
theorem heADC2025Theorem72_publishedParameterOrder {I : Type u}
    [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (p : HeHuPublishedSquareClassIndex I) :
    ordUnit K (parameter U p) = 0 ∨ ordUnit K (parameter U p) = 1 := by
  rcases p with ⟨i, parity⟩
  cases parity with
  | false =>
      left
      rw [parameter_unit]
      exact (isValuationUnit_iff_ordUnit_eq_zero K (U i)).1 (hU.isUnit i)
  | true =>
      right
      rw [parameter_uniformizer, ordUnit_mul,
        (isValuationUnit_iff_ordUnit_eq_zero K (U i)).1 (hU.isUnit i),
        ordUnit_uniformizerPowerUnit]
      norm_num

/-- A sharp square class has defect strictly below the discriminant endpoint. -/
theorem heADC2025Theorem72_defectLt_of_sharpDomain (c : Kˣ)
    (hc : HeHuSharpDomain c) :
    quadraticDefect K c <
      ((2 * ramificationIndex K : Nat) : ℕ∞) := by
  have hfinite : quadraticDefect K c ≠ ⊤ := by
    exact ((quadraticDefect_eq_top_iff_isSquare (K := K) c).not.mpr
      hc.notSquare)
  let d := (quadraticDefect K c).toNat
  have hdefect : quadraticDefect K c = (d : ℕ∞) := by
    simpa only [d] using (ENat.coe_toNat hfinite).symm
  have hdLe : d ≤ 2 * ramificationIndex K := by
    have H := quadraticDefect_le_two_mul_e_of_not_isSquare
      (K := K) hc.notSquare
    rw [hdefect] at H
    exact_mod_cast H
  have hdNe : d ≠ 2 * ramificationIndex K := by
    intro hd
    have hlarge : ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
        quadraticDefect K c := by
      rw [hdefect, hd]
    rcases isSquare_or_isSquare_div_discriminant_of_defect_ge_twoE
        c hlarge with hsquare | hdiscriminant
    · exact hc.notSquare hsquare
    · exact hc.notDiscriminantSquare hdiscriminant
  rw [hdefect]
  exact_mod_cast (lt_of_le_of_ne hdLe hdNe)

/-- A maximal lattice carrying the nonmaximal product order from Lemma 7.19
must lie in the unit-parameter second odd ambient column. -/
theorem heADC2025Theorem72_maximalProductAmbientSecond
    (k : Nat) (a : GoodBONG q L (2 * k + 5)) (d : Int)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (horder : a.order ⟨2 * k + 3, by omega⟩ = 1 - d)
    (hmaximal : Lattice.IsOMaximal q L) :
    ∃ epsilon : Kˣ, IsValuationUnit K (epsilon : K) ∧
      q.IsIsometric
        (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) epsilon)) := by
  obtain ⟨epsilon, hepsilon, hfirst | hsecond | hfirstPi | hsecondPi⟩ :=
    a.exists_heADCOddNormalizedAmbient (k + 1)
  · let ac := a.castLength
      (by omega : 2 * k + 5 = 1 + 2 * ((k + 1) + 1))
    have hisometric := Lattice.oMaximal_isIsometric_of_isometric
      hmaximal
      (heHuOMaximalLattice_isOMaximal (heADCW1Odd (k + 1) epsilon))
      hfirst
    have hprofile := (heADC2025Lemma412iPublished epsilon hepsilon
      (k + 1) ac hmaximal.isIntegral hfirst).1 hisometric
    have hboundary := hprofile ⟨2 * k + 3, by omega⟩
    rw [order_castLength] at hboundary
    have hodd : ¬Even (2 * k + 3) := by
      rintro ⟨z, hz⟩
      omega
    simp [heADCMaximalOrderProfile,
      show 2 * k + 3 < 2 * ((k + 1) + 1) by omega,
      hodd] at hboundary
    rw [horder] at hboundary
    omega
  · exact ⟨epsilon, hepsilon, hsecond⟩
  · let ac := a.castLength
      (by omega : 2 * k + 5 = 1 + 2 * ((k + 1) + 1))
    have hisometric := Lattice.oMaximal_isIsometric_of_isometric
      hmaximal
      (heHuOMaximalLattice_isOMaximal
        (heADCW1Odd (k + 1)
          (epsilon * uniformizerPowerUnit K 1)))
      hfirstPi
    have hprofile := (heADC2025Lemma412iiiFirstPublished epsilon
      hepsilon (k + 1) ac hmaximal.isIntegral hfirstPi).1 hisometric
    have hboundary := hprofile ⟨2 * k + 3, by omega⟩
    rw [order_castLength] at hboundary
    have hodd : ¬Even (2 * k + 3) := by
      rintro ⟨z, hz⟩
      omega
    simp [heADCMaximalOrderProfile,
      show 2 * k + 3 < 2 * ((k + 1) + 1) by omega,
      hodd] at hboundary
    rw [horder] at hboundary
    omega
  · let ac := a.castLength
      (by omega : 2 * k + 5 = 3 + 2 * (k + 1))
    have hisometric := Lattice.oMaximal_isIsometric_of_isometric
      hmaximal
      (heHuOMaximalLattice_isOMaximal
        (heADCW2Odd (k + 1)
          (epsilon * uniformizerPowerUnit K 1)))
      hsecondPi
    have hprofile := (heADC2025Lemma412iiiSecondPublished epsilon
      hepsilon (k + 1) ac hmaximal.isIntegral hsecondPi).1 hisometric
    have hboundary := hprofile ⟨2 * k + 3, by omega⟩
    rw [order_castLength] at hboundary
    simp [heADCMaximalOrderProfile,
      show ¬2 * k + 3 < 2 * (k + 1) by omega,
      show 2 * k + 3 - 2 * (k + 1) = 1 by omega] at hboundary
    rw [horder] at hboundary
    omega

/-- Normalize an order-zero-or-one coefficient to the literal published
form epsilon times pi^k, retaining a valuation-unit square multiplier. -/
theorem exists_publishedParameter_mul_unit_square_of_order_zero_or_one
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (c : Kˣ) (hc : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    ∃ (p : HeHuPublishedSquareClassIndex I) (s : Kˣ),
      IsValuationUnit K (s : K) ∧ c = parameter U p * s ^ 2 := by
  rcases hc with hzero | hone
  · have hcUnit : IsValuationUnit K (c : K) :=
      (isValuationUnit_iff_ordUnit_eq_zero K c).2 hzero
    obtain ⟨i, s, hsUnit, hcs⟩ := hU.complete c hcUnit
    exact ⟨(i, false), s, hsUnit, by simpa using hcs⟩
  · let epsilon := normalizedUnitPart K c
    have hepsilonUnit : IsValuationUnit K (epsilon : K) :=
      normalizedUnitPart_isValuationUnit K c
    obtain ⟨i, s, hsUnit, hepsilon⟩ := hU.complete epsilon hepsilonUnit
    refine ⟨(i, true), s, hsUnit, ?_⟩
    have hrecover : uniformizerPowerUnit K (1 : Int) * epsilon = c := by
      simpa only [epsilon, hone] using
        uniformizerPower_mul_normalizedUnitPart K c
    rw [← hrecover, hepsilon, parameter_uniformizer]
    simp only [pow_two]
    ac_rfl

/-- Square-normalizing the parameter preserves the first named even maximal
lattice, not merely its ambient quadratic space. -/
theorem heADC2025Theorem72_firstBaseIsometric_of_mul_square
    (k : Nat) (c d s : Kˣ) (h : c = d * s ^ 2) :
    Lattice.IsIsometric
      (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1) c))
      (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1) d))
      (heADCN1Even (k + 1) c).lattice
      (heADCN1Even (k + 1) d).lattice := by
  have hrep :=
    Lattice.QuadraticLatticeModel.heHuEvenFirst_represents_of_mul_square
      (k + 1) c d s h
  have hambient :=
    Lattice.QuadraticLatticeModel.heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
      (heADCW1Even (k + 1) c) (heADCW1Even (k + 1) d) hrep
  exact Lattice.oMaximal_isIsometric_of_isometric
    (heHuOMaximalLattice_isOMaximal (heADCW1Even (k + 1) c))
    (heHuOMaximalLattice_isOMaximal (heADCW1Even (k + 1) d)) hambient

/-- Square-normalizing the parameter preserves the second named even maximal
lattice on the sharp domain. -/
theorem heADC2025Theorem72_secondBaseIsometric_of_mul_square
    (k : Nat) (c d s : Kˣ) (hc : HeHuSharpDomain c)
    (hd : HeHuSharpDomain d) (h : c = d * s ^ 2) :
    Lattice.IsIsometric
      (BONG.coefficientDiagonalSpace
        (heADCW2Even (k + 1) c (Or.inr hc.notSquare)))
      (BONG.coefficientDiagonalSpace
        (heADCW2Even (k + 1) d (Or.inr hd.notSquare)))
      (heADCN2Even (k + 1) c (Or.inr hc.notSquare)).lattice
      (heADCN2Even (k + 1) d (Or.inr hd.notSquare)).lattice := by
  have hrep := heADCEvenSharpSpace_represents_of_mul_square true
    (k + 1) c d s hc hd h
  have hambient :=
    Lattice.QuadraticLatticeModel.heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
      (heADCW2Even (k + 1) c (Or.inr hc.notSquare))
      (heADCW2Even (k + 1) d (Or.inr hd.notSquare)) (by
        simpa only [heADCEvenSharpSpace, if_pos] using hrep)
  exact Lattice.oMaximal_isIsometric_of_isometric
    (heHuOMaximalLattice_isOMaximal
      (heADCW2Even (k + 1) c (Or.inr hc.notSquare)))
    (heHuOMaximalLattice_isOMaximal
      (heADCW2Even (k + 1) d (Or.inr hd.notSquare))) hambient

/-- A unit-square change preserves the second odd named maximal lattice. -/
theorem heADC2025Theorem72_secondOddIsometric_of_mul_square
    (k : Nat) (c d s : Kˣ) (h : c = d * s ^ 2) :
    Lattice.IsIsometric
      (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) c))
      (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) d))
      (heADCN2Odd (k + 1) c).lattice
      (heADCN2Odd (k + 1) d).lattice := by
  have hrep :=
    Lattice.QuadraticLatticeModel.heHuOddSecond_represents_of_mul_square
      (k + 1) c d s h
  have hambient :=
    Lattice.QuadraticLatticeModel.heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
      (heADCW2Odd (k + 1) c) (heADCW2Odd (k + 1) d) hrep
  exact Lattice.oMaximal_isIsometric_of_isometric
    (heHuOMaximalLattice_isOMaximal (heADCW2Odd (k + 1) c))
    (heHuOMaximalLattice_isOMaximal (heADCW2Odd (k + 1) d)) hambient

/-- The representative-independent and literal finite product families are
equivalent. -/
theorem heADC2025Theorem72Product_iff_published
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (hDelta : ∃ i,
      U i = (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (k : Nat) :
    HeADC2025Theorem72Product q L k ↔
      HeADC2025Theorem72PublishedProduct U hU hDelta q L k := by
  constructor
  · rintro (H | H)
    · obtain ⟨delta, line, hdelta, hlt, hline, hisometric⟩ := H
      have hdeltaSharp := heADC2025Lemma719_sharpDomain_of_defect_lt
        delta hdelta hlt
      obtain ⟨i, s, _hsUnit, hdeltaFactor⟩ := hU.complete delta hdelta
      have hUiSharp := heADCSharpDomain_of_mul_square delta (U i) s
        hdeltaSharp hdeltaFactor
      have hexclusions :=
        (heADCSharpDomain_publishedParameter_iff U hU hDelta
          (i, false)).1 hUiSharp
      let b : HeADC2025Theorem72BaseIndex (K := K) U :=
        ⟨i, by simpa using hexclusions.1,
          by simpa using hexclusions.2⟩
      obtain ⟨p, t, htUnit, hlineFactor⟩ :=
        exists_publishedParameter_mul_unit_square_of_order_zero_or_one
          U hU line hline
      obtain ⟨f⟩ := hisometric
      obtain ⟨g⟩ :=
        heADC2025Theorem72_firstBaseIsometric_of_mul_square
          k delta (U i) s hdeltaFactor
      let h := BONG.unaryModelIsometryOfValuationUnitSquare
        (parameter U p) line t htUnit hlineFactor
      left
      exact ⟨b, p, ⟨f.trans (g.orthogonalProductBasic h)⟩⟩
    · obtain ⟨delta, line, hdelta, hlt, hline, hisometric⟩ := H
      let D := heADC2025Lemma719_unitDefectData delta hdelta hlt
      obtain ⟨i, s, _hsUnit, hdeltaFactor⟩ := hU.complete delta hdelta
      have hUiSharp := heADCSharpDomain_of_mul_square delta (U i) s
        D.sharp hdeltaFactor
      have hexclusions :=
        (heADCSharpDomain_publishedParameter_iff U hU hDelta
          (i, false)).1 hUiSharp
      let b : HeADC2025Theorem72BaseIndex (K := K) U :=
        ⟨i, by simpa using hexclusions.1,
          by simpa using hexclusions.2⟩
      obtain ⟨p, t, htUnit, hlineFactor⟩ :=
        exists_publishedParameter_mul_unit_square_of_order_zero_or_one
          U hU line hline
      obtain ⟨f⟩ := hisometric
      obtain ⟨g⟩ :=
        heADC2025Theorem72_secondBaseIsometric_of_mul_square
          k delta (U i) s D.sharp hUiSharp hdeltaFactor
      let h := BONG.unaryModelIsometryOfValuationUnitSquare
        (parameter U p) line t htUnit hlineFactor
      right
      refine ⟨b, p, ?_⟩
      dsimp only
      exact ⟨f.trans (g.orthogonalProductBasic h)⟩
  · rintro (H | H)
    · obtain ⟨b, p, hisometric⟩ := H
      let hs := b.sharp U hU hDelta
      left
      exact ⟨U b.index, parameter U p, hU.isUnit b.index,
        heADC2025Theorem72_defectLt_of_sharpDomain (U b.index) hs,
        heADC2025Theorem72_publishedParameterOrder U hU p, hisometric⟩
    · obtain ⟨b, p, hisometric⟩ := H
      let hs := b.sharp U hU hDelta
      right
      refine ⟨U b.index, parameter U p, hU.isUnit b.index,
        heADC2025Theorem72_defectLt_of_sharpDomain (U b.index) hs,
        heADC2025Theorem72_publishedParameterOrder U hU p, ?_⟩
      simpa only [hs] using hisometric

/-- The overlap assertion in Theorem 7.2 before choosing unit
representatives: a maximal member of either displayed product family is a
second-column odd maximal lattice with unit parameter. -/
theorem HeADC2025Theorem72Product.isometricSecondUnit_of_isOMaximal
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) (H : HeADC2025Theorem72Product q L k)
    (hmaximal : Lattice.IsOMaximal q L) :
    ∃ i : I,
      Lattice.IsIsometric q
        (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) (U i))) L
        (heADCN2Odd (k + 1) (U i)).lattice := by
  rcases H with H | H
  · obtain ⟨delta, line, hdelta, hlt, hline, hisometric⟩ := H
    let D := heADC2025Lemma719_unitDefectData delta hdelta hlt
    have Hmodel := heADC2025Lemma719FirstNamedPublished k delta line
      hdelta hlt hline
    obtain ⟨full, _hADC, horder⟩ := Hmodel
    obtain ⟨f⟩ := hisometric
    have hmaximalModel := hmaximal.of_latticeIsometry f
    obtain ⟨epsilon, hepsilon, hambient⟩ :=
      heADC2025Theorem72_maximalProductAmbientSecond k full D.d
        D.ltTwoE horder hmaximalModel
    have htoEpsilon := Lattice.oMaximal_isIsometric_of_isometric
      hmaximalModel
      (heHuOMaximalLattice_isOMaximal
        (heADCW2Odd (k + 1) epsilon))
      hambient
    obtain ⟨i, s, _hsUnit, hepsilonFactor⟩ :=
      hU.complete epsilon hepsilon
    have hnormalize :=
      heADC2025Theorem72_secondOddIsometric_of_mul_square
        k epsilon (U i) s hepsilonFactor
    obtain ⟨g⟩ := htoEpsilon
    obtain ⟨h⟩ := hnormalize
    exact ⟨i, ⟨f.trans (g.trans h)⟩⟩
  · obtain ⟨delta, line, hdelta, hlt, hline, hisometric⟩ := H
    let D := heADC2025Lemma719_unitDefectData delta hdelta hlt
    have Hmodel := heADC2025Lemma719SecondNamedPublished k delta line
      hdelta hlt hline
    obtain ⟨full, _hADC, horder⟩ := Hmodel
    obtain ⟨f⟩ := hisometric
    have hmaximalModel := hmaximal.of_latticeIsometry f
    obtain ⟨epsilon, hepsilon, hambient⟩ :=
      heADC2025Theorem72_maximalProductAmbientSecond k full D.d
        D.ltTwoE horder hmaximalModel
    have htoEpsilon := Lattice.oMaximal_isIsometric_of_isometric
      hmaximalModel
      (heHuOMaximalLattice_isOMaximal
        (heADCW2Odd (k + 1) epsilon))
      hambient
    obtain ⟨i, s, _hsUnit, hepsilonFactor⟩ :=
      hU.complete epsilon hepsilon
    have hnormalize :=
      heADC2025Theorem72_secondOddIsometric_of_mul_square
        k epsilon (U i) s hepsilonFactor
    obtain ⟨g⟩ := htoEpsilon
    obtain ⟨h⟩ := hnormalize
    exact ⟨i, ⟨f.trans (g.trans h)⟩⟩

/-- The final sentence of the published Theorem 7.2: if a lattice is both
maximal and in the displayed finite product family, it is one of the
published second-column odd maximal lattices. -/
theorem heADC2025Theorem72Published_overlap
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (hDelta : ∃ i,
      U i = (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (k : Nat)
    (H : HeADC2025Theorem72PublishedProduct U hU hDelta q L k)
    (hmaximal : Lattice.IsOMaximal q L) :
    ∃ i : I,
      Lattice.IsIsometric q
        (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) (U i))) L
        (heADCN2Odd (k + 1) (U i)).lattice :=
  (((heADC2025Theorem72Product_iff_published U hU hDelta k).2 H).isometricSecondUnit_of_isOMaximal
    U hU k hmaximal)

/-- He (2025), Theorem 7.2 in the literal finite representative-system
form printed in the published paper. -/
theorem heADC2025Theorem72Published
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (hDelta : ∃ i,
      U i = (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (k : Nat) (a : GoodBONG q L (2 * k + 5)) :
    Lattice.IsNADC.{u, u, u} q L (2 * k + 3) ↔
      Lattice.IsOMaximal q L ∨
        HeADC2025Theorem72PublishedProduct U hU hDelta q L k := by
  rw [heADC2025Theorem72 k a,
    heADC2025Theorem72Product_iff_published U hU hDelta k]

end BONG.GoodBONG

end Bong
