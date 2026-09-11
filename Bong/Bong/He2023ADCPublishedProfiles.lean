/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCMaximalProfiles
import Bong.Bong.He2023ADCSectionFour
import Bong.Bong.HeHu2022Lemma511

/-!
# He (2025): maximal-order criteria on the published ambient spaces

The concrete maximal BONG models are connected to Definition 4.1 by
equal-rank diagonal representations and maximal-lattice uniqueness. These
bridges do not assume the identification of a concrete model with a named
`W` or `N` family.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The unary first-column space in Definition 4.1. There is no unary
second-column space. -/
abbrev heADCW1Unary (c : Kˣ) : Fin 1 → Kˣ := ![c]

/-- The chosen maximal lattice in the unary space from Definition 4.1. -/
noncomputable abbrev heADCN1Unary (c : Kˣ) := heHuOMaximalModel (heADCW1Unary c)

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- An equal-rank diagonal identification of the BONG values identifies the
actual ambient quadratic space, even when the ranks use different expressions. -/
theorem ambientIsometric_of_diagonalRepresents {n m : Nat}
    (b : GoodBONG r M n) (w : Fin m → Kˣ) (hdim : n = m)
    (hrep : DiagonalRepresents (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients w)) : r.IsIsometric (BONG.coefficientDiagonalSpace w) := by
  obtain ⟨f⟩ := (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    b.valueUnit w).2 hrep
  let g := f.toIsometryOfFinrankEq (by simpa only [finrank_fin_fun] using hdim)
  exact ⟨b.toBONG.exactDiagonalizationIsometry.trans g⟩

/-- Transport a proved concrete maximal profile to the chosen maximal
lattice on a specified published diagonal space. The diagonal identification
is an explicit intermediate lemma, discharged in the numbered endpoints. -/
theorem isIsometric_publishedModel_iff_orderProfile {t m : Nat}
    (b : GoodBONG r M (t + 1)) (hM : Lattice.IsOMaximal r M)
    (tail : Fin (t + 1) → Int) (htail : ∀ j, b.order j = tail j)
    (k : Nat) (w : Fin m → Kˣ) (hdim : (t + 1) + 2 * k = m)
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients (heHu2022Lemma310BONG b hM.isIntegral k).valueUnit)
      (diagonalUnitCoefficients w))
    (a : GoodBONG q L ((t + 1) + 2 * k)) (hL : Lattice.IsIntegral q L)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace w)) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace w) L (heHuOMaximalLattice w) ↔
      ∀ i, a.order i = heADCMaximalOrderProfile (K := K) k tail i := by
  let c := heHu2022Lemma310BONG b hM.isIntegral k
  have hspace := c.ambientIsometric_of_diagonalRepresents w hdim hrep
  obtain ⟨f⟩ := Lattice.oMaximal_isIsometric_of_isometric
    (hM.halfHyperbolicExtension k) (heHuOMaximalLattice_isOMaximal w) hspace
  have hcriterion := a.isIsometric_iff_orders_eq_of_isOMaximal
    (c.mapLatticeIsometry f) hL (heHuOMaximalLattice_isOMaximal w) ambient
  simpa only [order_mapLatticeIsometry, c,
    heADC2025Remark410 b hM.isIntegral k tail htail] using hcriterion

/-- The rank-one boundary of Lemma 4.12(i) and (iii), for the normalized
parameters of order zero or one. Both directions concern the chosen `N_1^1`. -/
theorem heADC2025Lemma412UnaryPublished (c : Kˣ)
    (hc0 : 0 ≤ ordUnit K c) (hc1 : ordUnit K c ≤ 1)
    (a : GoodBONG q L 1) (hL : Lattice.IsIntegral q L)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Unary c))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace (heADCW1Unary c))
        L (heADCN1Unary c).lattice ↔ a.order 0 = ordUnit K c := by
  let b := BONG.unaryModelGoodBONG c
  have hbIntegral := heHuIntegral_of_firstOrder_nonneg b (by
    simpa only [b, BONG.unaryModelGoodBONG_order] using hc0)
  have hbMaximal := heHuRankOne_isOMaximal_of_order_le_one b hbIntegral (by
    simpa only [b, BONG.unaryModelGoodBONG_order] using hc1)
  have hbOrders : ∀ j, b.order j = (![ordUnit K c] : Fin 1 → Int) j := by
    intro j
    fin_cases j
    exact BONG.unaryModelGoodBONG_order c
  have hvalues : b.valueUnit = heADCW1Unary c := by
    funext j
    fin_cases j
    exact BONG.unaryModelBONG_valueUnit c 0
  have hrep : DiagonalRepresents (diagonalUnitCoefficients
      (heHu2022Lemma310BONG b hbMaximal.isIntegral 0).valueUnit)
      (diagonalUnitCoefficients (heADCW1Unary c)) := by
    change DiagonalRepresents (diagonalUnitCoefficients b.valueUnit) _
    rw [hvalues]
    exact diagonalRepresents_refl _
  have hcriterion := isIsometric_publishedModel_iff_orderProfile b hbMaximal _ hbOrders
    0 (heADCW1Unary c) rfl hrep a hL ambient
  simpa [heADCN1Unary, heHuOMaximalModel, heADCMaximalOrderProfile,
    Fin.forall_fin_one] using hcriterion

/-- Lift a tail identification to the conventional tower, keeping the
source and target's arithmetically equal coordinate types explicit. -/
theorem heADCTower_represents {t : Nat} (b : GoodBONG r M (t + 1))
    (hM : Lattice.IsIntegral r M) (k : Nat) (tail : Fin (t + 1) → Kˣ)
    (htail : DiagonalRepresents (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients tail)) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heHu2022Lemma310BONG b hM k).valueUnit)
      (diagonalUnitCoefficients
        (Fin.append (AlternatingEndpointTower.standardHyperbolicEndpointTower (K := K) k)
          tail)) := by
  have hlift := heHuLemma45Lemma310_represents_tower b hM k tail htail
  have hcast := diagonalRepresents_heHuFinFamilyCast_both (K := K)
    (rfl : (t + 1) + 2 * k = (t + 1) + 2 * k)
    (by omega : (t + 1) + 2 * k = 2 * k + (t + 1)) _ _ hlift
  simpa only [heHuFinFamilyCast_trans, heHuFinFamilyCast_self] using hcast

/-- Any binary tail identified with `[1,-c]` lifts to the named even `W_1` family. -/
theorem heADCBinaryTower_represents_evenFirst (b : GoodBONG r M 2)
    (hM : Lattice.IsIntegral r M) (k : Nat) (c : Kˣ)
    (htail : DiagonalRepresents (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heHuBinaryFirst c))) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heHu2022Lemma310BONG b hM k).valueUnit)
      (diagonalUnitCoefficients (heADCW1Even k c)) := by
  rw [heADCW1Even, heHuEvenFirst_eq_towerModel]
  exact heADCTower_represents b hM k (heHuBinaryFirst c) htail

/-- Lemma 4.11(i), square first-column row on the actual `W_1/N_1` families. -/
theorem heADC2025Lemma411iOnePublished (k : Nat) (a : GoodBONG q L (2 + 2 * k))
    (hL : Lattice.IsIntegral q L)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even k (1 : Kˣ)))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace (heADCW1Even k (1 : Kˣ)))
        L (heADCN1Even k (1 : Kˣ)).lattice ↔
      ∀ i, a.order i = heADCMaximalOrderProfile (K := K) k
        ![0, -(2 * (ramificationIndex K : Int))] i := by
  let b := heHuHyperbolicHeadGoodBONG (K := K)
  have hM := heHu2022Proposition37EvenFirstOne (K := K) 0
  have hvalues : b.valueUnit = heHuLemma45HyperbolicBONGValues (K := K) 1 := by
    funext i
    fin_cases i <;> simp [b, heHuLemma45HyperbolicBONGValues]
  have htarget : AlternatingEndpointTower.standardHyperbolicEndpointTower (K := K) 1 =
      heHuBinaryFirst (1 : Kˣ) := by
    funext i
    fin_cases i <;> simp [AlternatingEndpointTower.standardHyperbolicEndpointTower,
      heHuBinaryFirst]
  have htail : DiagonalRepresents (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heHuBinaryFirst (1 : Kˣ))) := by
    rw [hvalues, ← htarget]
    exact heHuLemma45HyperbolicBONGValues_represents_standard 1
  apply isIsometric_publishedModel_iff_orderProfile b hM _ (fun j ↦ ?_) k _ (by omega)
    (heADCBinaryTower_represents_evenFirst b hM.isIntegral k 1 htail) a hL ambient
  fin_cases j <;> simp [b]

/-- Lemma 4.11(i), discriminant first-column row on the actual `W_1/N_1` families. -/
theorem heADC2025Lemma411iDeltaPublished (k : Nat) (a : GoodBONG q L (2 + 2 * k))
    (hL : Lattice.IsIntegral q L)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even k
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace (heADCW1Even k
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit))
        L (heADCN1Even k (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit).lattice ↔
      ∀ i, a.order i = heADCMaximalOrderProfile (K := K) k
        ![0, -(2 * (ramificationIndex K : Int))] i := by
  let b := heHuDiscriminantEndpointGoodBONG (K := K) 0
  have hM := heHu2022Proposition37EvenFirstDelta (K := K) 0
  have htarget : heHuDiscriminantEndpointStandardValues (K := K) 0 =
      heHuBinaryFirst (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit := by
    funext i
    fin_cases i <;> simp [heHuDiscriminantEndpointStandardValues,
      heHuBinaryFirst, uniformizerPowerUnit]
  have htail := heHuDiscriminantEndpointGoodBONG_diagonalRepresents_standard (K := K) 0
  rw [htarget] at htail
  apply isIsometric_publishedModel_iff_orderProfile b hM _ (fun j ↦ ?_) k _ (by omega)
    (heADCBinaryTower_represents_evenFirst b hM.isIntegral k _ htail) a hL ambient
  fin_cases j <;> simp [b]

/-- Lemma 4.11(ii), discriminant second-column row on `W_2/N_2`. -/
theorem heADC2025Lemma411iiDeltaPublished (k : Nat) (a : GoodBONG q L (2 + 2 * k))
    (hL : Lattice.IsIntegral q L)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Even k
      (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
      (heHuLemma43_evenSecondDefined (K := K) k)))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace (heADCW2Even k
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) k)))
        L (heADCN2Even k (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
          (heHuLemma43_evenSecondDefined (K := K) k)).lattice ↔
      ∀ i, a.order i = heADCMaximalOrderProfile (K := K) k
        ![1, 1 - 2 * (ramificationIndex K : Int)] i := by
  let b := heHuDiscriminantEndpointGoodBONG (K := K) 1
  have hM := heHu2022Proposition37EvenSecondDelta (K := K) 0
  have htarget : heHuDiscriminantEndpointStandardValues (K := K) 1 =
      heHuDiscriminantBinary
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit := by
    funext i
    fin_cases i <;> simp [heHuDiscriminantEndpointStandardValues,
      heHuDiscriminantBinary, heHuBinaryTwist, mul_comm]
  have htail := heHuDiscriminantEndpointGoodBONG_diagonalRepresents_standard (K := K) 1
  rw [htarget] at htail
  have hlift := heADCTower_represents b hM.isIntegral k _ htail
  rw [← heHuLemma43_evenSecond_eq_model (K := K) k] at hlift
  apply isIsometric_publishedModel_iff_orderProfile b hM _ (fun j ↦ ?_) k _ (by omega)
    hlift a hL ambient
  fin_cases j <;> simp [b]

/-- Lemma 4.11(ii), square second-column row, with the undefined binary
case excluded by the rank `4+2k`. -/
theorem heADC2025Lemma411iiOnePublished (k : Nat) (a : GoodBONG q L (4 + 2 * k))
    (hL : Lattice.IsIntegral q L)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace
      (heADCW2Even (k + 1) (1 : Kˣ) (Or.inl (by omega))))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace
        (heADCW2Even (k + 1) (1 : Kˣ) (Or.inl (by omega))))
        L (heADCN2Even (k + 1) (1 : Kˣ) (Or.inl (by omega))).lattice ↔
      ∀ i, a.order i = heADCMaximalOrderProfile (K := K) k
        ![0, -(2 * (ramificationIndex K : Int)), 1,
          1 - 2 * (ramificationIndex K : Int)] i := by
  let b := heHuLemma311EvenSecondOneTail (K := K)
  have hM := heHu2022Proposition37EvenSecondOne (K := K) 0
  have htail := Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
    b.valueUnit (heHuLemma311EvenSecondOneStandardValues (K := K))
    (heHuLemma311EvenSecondOneFactors (K := K))
    (heHuLemma311EvenSecondOneTail_eq_anisotropic_mul_square (K := K))
  rw [heHuLemma311EvenSecondOneStandardValues_eq_anisotropic] at htail
  have hlift := heADCTower_represents b hM.isIntegral k _ htail
  have hcast := diagonalRepresents_heHuFinFamilyCast_both (K := K)
    (rfl : 4 + 2 * k = 4 + 2 * k) (by omega : 2 * k + 4 = 2 * (k + 1) + 2) _ _ hlift
  have hmodel := heHuEvenSecond_succ_of_square (K := K) k 1 (Or.inl (by omega))
    (show IsSquare (1 : Kˣ) from ⟨1, by simp⟩)
  rw [← hmodel] at hcast
  exact isIsometric_publishedModel_iff_orderProfile b hM _
    heHuLemma311EvenSecondOneTail_order k _ (by omega) hcast a hL ambient

/-- Lemma 4.12(ii), with the actual `W_2` hypothesis and `N_2` conclusion
from Definition 4.1, in every allowed odd rank. -/
theorem heADC2025Lemma412iiPublishedOfKappa
    (δ κ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (hκ : IsValuationUnit K (κ : K))
    (hκDefect : defectOrder (K := K) κ = ((2 * (ramificationIndex K : ℚ) - 1) : WithTop ℚ))
    (k : Nat) (a : GoodBONG q L (3 + 2 * k)) (hL : Lattice.IsIntegral q L)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Odd k δ))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace (heADCW2Odd k δ))
        L (heADCN2Odd k δ).lattice ↔
      ∀ i, a.order i = heADCMaximalOrderProfile (K := K) k
        ![0, 2 - 2 * (ramificationIndex K : Int), 0] i := by
  letI : GoodBONGClassificationLaws.{u, u, u} K := goodBONGClassificationLawsProved K
  let b := heHuLemma311OddSecondUnitTail δ κ hδ hκ hκDefect
  have hM := heHu2022Proposition37OddSecondUnit δ κ hδ hκ hκDefect 0
  have hδEven : Even (ordUnit K δ) := by
    rw [(isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ]
    exact ⟨0, by omega⟩
  exact isIsometric_publishedModel_iff_orderProfile b hM _
    (heHuLemma311OddSecondUnitTail_order δ κ hδ hκ hκDefect) k
    (heADCW2Odd k δ) (by omega)
    (heHuLemma511LiftEvenTail_represents_oddSecond b hM.isIntegral δ hδEven k
      (heHuLemma311OddSecondUnitTail_represents_oddSecondTailEven δ κ hδ hκ hκDefect))
    a hL ambient

/-- A unit of defect `2e-1` exists over every field in the dyadic context.
It is proof data for the displayed ternary model, not an extra paper hypothesis. -/
theorem exists_unit_defectOrder_eq_twoE_sub_one :
    ∃ κ : Kˣ, IsValuationUnit K (κ : K) ∧
      defectOrder (K := K) κ = ((2 * (ramificationIndex K : ℚ) - 1) : WithTop ℚ) := by
  let d := 2 * ramificationIndex K - 1
  have he := ramificationIndex_pos (K := K)
  have hdpos : 0 < d := by dsimp only [d]; omega
  have hdodd : Odd d := ⟨ramificationIndex K - 1, by dsimp only [d]; omega⟩
  have hdlt : d < 2 * ramificationIndex K := by dsimp only [d]; omega
  obtain ⟨κ, hκ, hdefect⟩ := exists_unit_quadraticDefect_eq_odd (K := K) d hdpos hdodd hdlt
  refine ⟨κ, hκ, ?_⟩
  rw [Beli2009FinalRemarksProof.defectOrder_eq_natCast_of_quadraticDefect_eq
    (K := K) κ d hdefect]
  congr 1
  have hdNat : d + 1 = 2 * ramificationIndex K := by dsimp only [d]; omega
  have hdRat : (d : ℚ) + 1 = 2 * (ramificationIndex K : ℚ) := by exact_mod_cast hdNat
  norm_num only [Nat.cast_ofNat]
  linarith

/-- Lemma 4.12(ii) on the published `W_2/N_2` families, with no auxiliary
unit or unproved classification law in the theorem's assumptions. -/
theorem heADC2025Lemma412iiPublished
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K))
    (k : Nat) (a : GoodBONG q L (3 + 2 * k)) (hL : Lattice.IsIntegral q L)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Odd k δ))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace (heADCW2Odd k δ))
        L (heADCN2Odd k δ).lattice ↔
      ∀ i, a.order i = heADCMaximalOrderProfile (K := K) k
        ![0, 2 - 2 * (ramificationIndex K : Int), 0] i := by
  obtain ⟨κ, hκ, hdefect⟩ := exists_unit_defectOrder_eq_twoE_sub_one (K := K)
  exact heADC2025Lemma412iiPublishedOfKappa δ κ hδ hκ hdefect k a hL ambient

/-- Adjoining at least one hyperbolic plane to a unary BONG gives the
first odd-dimensional space from Definition 4.1. -/
theorem heADCUnaryTower_represents_oddFirst
    (c : Kˣ) (hIntegral : Lattice.IsIntegral (QuadraticSpace.rescaleUnit c
      (QuadraticSpace.line K)) (BONG.unaryModelLattice (K := K))) (k : Nat) :
    DiagonalRepresents (diagonalUnitCoefficients
      (heHu2022Lemma310BONG (BONG.unaryModelGoodBONG c) hIntegral (k + 1)).valueUnit)
      (diagonalUnitCoefficients (heADCW1Odd k c)) := by
  let b := BONG.unaryModelGoodBONG c
  let line : Fin 1 → Kˣ := Fin.cons c Fin.elim0
  have htail : DiagonalRepresents (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients line) := by
    have hvalues : b.valueUnit = line := by
      funext i
      fin_cases i
      exact BONG.unaryModelBONG_valueUnit c 0
    rw [hvalues]
    exact diagonalRepresents_refl _
  have hlift := heHuLemma45Lemma310_represents_tower b hIntegral (k + 1) line htail
  let raw := heHu2022Lemma310BONG b hIntegral (k + 1)
  let model := heHuFinFamilyCast (by omega : 2 * (k + 1) + 1 = 1 + 2 * (k + 1))
    (Fin.append (AlternatingEndpointTower.standardHyperbolicEndpointTower (K := K) (k + 1))
      line)
  have hcast := diagonalRepresents_heHuFinFamilyCast_both (K := K)
    (rfl : 1 + 2 * (k + 1) = 1 + 2 * (k + 1))
    (by omega : 1 + 2 * (k + 1) = 2 * k + 3) raw.valueUnit model hlift
  have htarget : heHuFinFamilyCast (by omega : 1 + 2 * (k + 1) = 2 * k + 3) model =
      heADCW1Odd k c := by
    simp only [model, heHuFinFamilyCast_trans]
    rw [← Fin.snoc_eq_append, heHuLemma43_snoc_standard_eq_oddFirst (K := K) k c]
    rfl
  rw [htarget] at hcast
  exact hcast

/-- Lemma 4.12(i), first column in odd ranks at least three, stated using
the actual `W_1` and `N_1` families. The unary case is separate. -/
theorem heADC2025Lemma412iPublished
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (k : Nat)
    (a : GoodBONG q L (1 + 2 * (k + 1))) (hL : Lattice.IsIntegral q L)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Odd k δ))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace (heADCW1Odd k δ))
        L (heADCN1Odd k δ).lattice ↔
      ∀ i, a.order i = heADCMaximalOrderProfile (K := K) (k + 1) ![0] i := by
  have hM := heHu2022Proposition37OddFirstUnit δ hδ 0
  apply isIsometric_publishedModel_iff_orderProfile (BONG.unaryModelGoodBONG δ) hM _
    (fun j ↦ ?_) (k + 1) _ (by omega)
    (heADCUnaryTower_represents_oddFirst δ hM.isIntegral k) a hL ambient
  fin_cases j
  simp [BONG.unaryModelGoodBONG_order, (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ]

/-- Lemma 4.12(iii), first column in odd ranks at least three. -/
theorem heADC2025Lemma412iiiFirstPublished
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (k : Nat)
    (a : GoodBONG q L (1 + 2 * (k + 1))) (hL : Lattice.IsIntegral q L)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace
      (heADCW1Odd k (δ * uniformizerPowerUnit K 1)))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace
        (heADCW1Odd k (δ * uniformizerPowerUnit K 1)))
        L (heADCN1Odd k (δ * uniformizerPowerUnit K 1)).lattice ↔
      ∀ i, a.order i = heADCMaximalOrderProfile (K := K) (k + 1) ![1] i := by
  have hM := heHu2022Proposition37OddFirstUnitUniformizer δ hδ 0
  apply isIsometric_publishedModel_iff_orderProfile
    (BONG.unaryModelGoodBONG (δ * uniformizerPowerUnit K 1)) hM _
    (fun j ↦ ?_) (k + 1) _ (by omega)
    (heADCUnaryTower_represents_oddFirst _ hM.isIntegral k) a hL ambient
  fin_cases j
  simp [BONG.unaryModelGoodBONG_order, ordUnit_mul, ordUnit_uniformizerPowerUnit,
    (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ]

/-- Lemma 4.12(iii), second column, with the published parameter `δπ`
and the chosen maximal lattice `N_2^(2k+3)(δπ)`. -/
theorem heADC2025Lemma412iiiSecondPublished
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (k : Nat)
    (a : GoodBONG q L (3 + 2 * k)) (hL : Lattice.IsIntegral q L)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace
      (heADCW2Odd k (δ * uniformizerPowerUnit K 1)))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace
        (heADCW2Odd k (δ * uniformizerPowerUnit K 1)))
        L (heADCN2Odd k (δ * uniformizerPowerUnit K 1)).lattice ↔
      ∀ i, a.order i = heADCMaximalOrderProfile (K := K) k
        ![0, -(2 * (ramificationIndex K : Int)), 1] i := by
  let b := heHuLemma311OddSecondUnitUniformizerTail δ hδ
  have hM := heHu2022Proposition37OddSecondUnitUniformizer δ hδ 0
  have hodd : ¬ Even (ordUnit K (δ * uniformizerPowerUnit K 1)) := by
    rw [ordUnit_mul, (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ,
      ordUnit_uniformizerPowerUnit]
    norm_num
  have htail := Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
    b.valueUnit (heHuOddSecondTailOdd (heHuLemma57Parameter δ))
    (heHuLemma57TargetFactors (K := K))
    (heHuLemma57TargetValues_eq_oddSecond_mul_square δ hδ)
  exact isIsometric_publishedModel_iff_orderProfile b hM _
    (heHuLemma311OddSecondUnitUniformizerTail_order δ hδ) k _ (by omega)
    (heHuLemma511LiftOddTail_represents_oddSecond b hM.isIntegral _ hodd k htail)
    a hL ambient

end BONG.GoodBONG

end Bong
