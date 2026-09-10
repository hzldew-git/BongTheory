/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma78
import Bong.Bong.He2022ClassicPublishedRepresentation

/-!
# He (2024), Lemma 7.9

The endpoint condition in Lemma 7.9 separates the two exceptional even
lattices.  This file first proves the numerical trigger in part (i), then
identifies the exact BONG prefixes with the literal rows used in part (ii),
and finally upgrades the prefix-space dichotomy to integral representation
and nonrepresentation as stated in part (iii).
-/

namespace Bong

open Dyadic BONG.GoodBONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

private theorem he2022Classic_discriminantUnit_order :
    ordUnit K (Dyadic.dyadicDiscriminantClassLawsProved
      (K := K)).discriminantUnit = 0 :=
  (isValuationUnit_iff_ordUnit_eq_zero K
    (Dyadic.dyadicDiscriminantClassLawsProved
      (K := K)).discriminantUnit).1
      (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminant_isValuationUnit

private theorem he2022Classic_one_order : ordUnit K (1 : Kˣ) = 0 := by
  have h := ordUnit_mul K (1 : Kˣ) 1
  simp only [mul_one] at h
  omega

/-- The exact exceptional target `H_1^n(1)`. -/
noncomputable def heClassicEvenHOneGoodBONG (pairs : Nat) :=
  heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl)
    (he2022Classic_one_order (K := K))

/-- The exact exceptional target `H_1^n(Delta)`. -/
noncomputable def heClassicEvenHDiscriminantGoodBONG (pairs : Nat) :=
  heClassicEvenHGoodBONG (K := K) pairs
    (Dyadic.dyadicDiscriminantClassLawsProved
      (K := K)).discriminantUnit
    (Or.inr rfl) (he2022Classic_discriminantUnit_order (K := K))

/-- Bundle the first literal `P(omega)` lattice. -/
noncomputable def heClassicEvenP1OmegaModel (pairs : Nat) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuExactModel
    (heClassicEvenP1 (K := K) pairs (heClassicOmega (K := K)))
    (heClassicEvenP1_adjacentAdmissible pairs _
      (heClassicOmega_order (K := K)))
    (heClassicEvenP1_weakTwoStep pairs _
      (heClassicOmega_order (K := K)))

/-- Bundle the second literal `P(omega)` lattice. -/
noncomputable def heClassicEvenP2OmegaModel (pairs : Nat) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuExactModel
    (heClassicEvenP2 (K := K) pairs (heClassicOmega (K := K))
      (heClassicOmegaSharp (K := K)))
    (heClassicEvenP2_adjacentAdmissible pairs _ _
      (heClassicOmega_order (K := K)) (by
        rw [heClassicOmegaSharp_order (K := K)]))
    (heClassicEvenP2_weakTwoStep pairs _ _
      (heClassicOmega_order (K := K)) (by
        rw [heClassicOmegaSharp_order (K := K)]))

/-- Bundle the exceptional target with determinant parameter one. -/
noncomputable def heClassicEvenHOneModel (pairs : Nat) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heClassicEvenHModel (K := K) pairs 1 (Or.inl rfl)
    (he2022Classic_one_order (K := K))

/-- Bundle the exceptional target with discriminant determinant parameter. -/
noncomputable def heClassicEvenHDiscriminantModel (pairs : Nat) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heClassicEvenHModel (K := K) pairs
    (Dyadic.dyadicDiscriminantClassLawsProved
      (K := K)).discriminantUnit
    (Or.inr rfl) (he2022Classic_discriminantUnit_order (K := K))

namespace BONG.GoodBONG

/-- Lemma 7.9(i), abstracted only over the literal all-zero/all-one `P`
profile and its signed full self-defect. -/
theorem he2022ClassicLemma79i_of_zero_one_fullDefect
    (pairs : Nat) (a : GoodBONG q L (2 * pairs + 4))
    (heOne : ramificationIndex K = 1)
    (hzero : forall k : Fin (2 * pairs + 4), a.order k = 0)
    (halpha : forall k : Fin (2 * pairs + 3), a.alphaValue k = 1)
    (hfull : a.truncatedPrefixDefect a ((-1 : Kˣ) ^ (pairs + 2))
      0 (2 * pairs + 4) = ⊤)
    (c : Kˣ)
    (hcClass : c = 1 ∨ c = (Dyadic.dyadicDiscriminantClassLawsProved
      (K := K)).discriminantUnit)
    (hcOrder : ordUnit K c = 0)
    (hParameter :
      (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) <=
        defectOrder (K := K) c) :
    let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
    a.centralDefectTrigger b (he2022ClassicLemma43Index pairs (by omega)) := by
  dsimp only
  have hJ1 : a.HeClassicJ1EPrime (2 * pairs + 2) (by omega) := by
    constructor
    · intro i
      exact hzero _
    · intro i
      exact halpha _
  apply a.he2022ClassicLemma43_H_trigger_of_twoE_le_capped
    pairs (by omega) hJ1 heOne c hcClass hcOrder
  · rw [hfull]
    exact le_top
  · exact hParameter

end BONG.GoodBONG

theorem heClassicEvenP1Omega_fullSelfDefect (pairs : Nat) :
    let a := heClassicEvenP1OmegaGoodBONG (K := K) pairs
    a.truncatedPrefixDefect a ((-1 : Kˣ) ^ (pairs + 2))
      0 (2 * pairs + 4) = ⊤ := by
  dsimp only
  simpa only [heClassicEvenP1OmegaGoodBONG] using
    heClassicEvenP1_fullSelfDefect (K := K) pairs
      (heClassicOmega (K := K)) (heClassicOmega_order (K := K))

theorem heClassicEvenP2Omega_fullSelfDefect (pairs : Nat) :
    let a := heClassicEvenP2OmegaGoodBONG (K := K) pairs
    a.truncatedPrefixDefect a ((-1 : Kˣ) ^ (pairs + 2))
      0 (2 * pairs + 4) = ⊤ := by
  dsimp only
  simpa only [heClassicEvenP2OmegaGoodBONG] using
    heClassicEvenP2_fullSelfDefect (K := K) pairs
      (heClassicOmega (K := K)) (heClassicOmegaSharp (K := K))
      (heClassicOmega_order (K := K)) (by
        rw [heClassicOmegaSharp_order (K := K)])

private theorem he2022Classic_twoE_le_defect_one
    (heOne : ramificationIndex K = 1) :
    (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) <=
      BONG.GoodBONG.defectOrder (K := K) (1 : Kˣ) := by
  rw [BONG.GoodBONG.defectOrder_one, heOne]
  simp

private theorem he2022Classic_twoE_le_defect_discriminant :
    (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) <=
      BONG.GoodBONG.defectOrder (K := K)
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminantUnit := by
  rw [BONG.GoodBONG.defectOrder_discriminantUnit]
  norm_cast

/-- Lemma 7.9(i), first `P` row against `H_1^n(1)`. -/
theorem he2022ClassicLemma79i_P1Omega_HOne
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    let a := heClassicEvenP1OmegaGoodBONG (K := K) pairs
    let b := heClassicEvenHOneGoodBONG (K := K) pairs
    a.centralDefectTrigger b
      (BONG.GoodBONG.he2022ClassicLemma43Index pairs (by omega)) := by
  dsimp only
  exact BONG.GoodBONG.he2022ClassicLemma79i_of_zero_one_fullDefect
      pairs (heClassicEvenP1OmegaGoodBONG (K := K) pairs) heOne
      (heClassicEvenP1OmegaGoodBONG_order_zero pairs)
      (heClassicEvenP1OmegaGoodBONG_alpha_eq_one pairs)
      (heClassicEvenP1Omega_fullSelfDefect pairs) 1 (Or.inl rfl)
      (he2022Classic_one_order (K := K))
      (he2022Classic_twoE_le_defect_one heOne)

/-- Lemma 7.9(i), second `P` row against `H_1^n(1)`. -/
theorem he2022ClassicLemma79i_P2Omega_HOne
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    let a := heClassicEvenP2OmegaGoodBONG (K := K) pairs
    let b := heClassicEvenHOneGoodBONG (K := K) pairs
    a.centralDefectTrigger b
      (BONG.GoodBONG.he2022ClassicLemma43Index pairs (by omega)) := by
  dsimp only
  exact BONG.GoodBONG.he2022ClassicLemma79i_of_zero_one_fullDefect
      pairs (heClassicEvenP2OmegaGoodBONG (K := K) pairs) heOne
      (heClassicEvenP2OmegaGoodBONG_order_zero pairs)
      (heClassicEvenP2OmegaGoodBONG_alpha_eq_one pairs)
      (heClassicEvenP2Omega_fullSelfDefect pairs) 1 (Or.inl rfl)
      (he2022Classic_one_order (K := K))
      (he2022Classic_twoE_le_defect_one heOne)

/-- Lemma 7.9(i), first `P` row against `H_1^n(Delta)`. -/
theorem he2022ClassicLemma79i_P1Omega_HDiscriminant
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    let a := heClassicEvenP1OmegaGoodBONG (K := K) pairs
    let b := heClassicEvenHDiscriminantGoodBONG (K := K) pairs
    a.centralDefectTrigger b
      (BONG.GoodBONG.he2022ClassicLemma43Index pairs (by omega)) := by
  dsimp only
  exact BONG.GoodBONG.he2022ClassicLemma79i_of_zero_one_fullDefect
      pairs (heClassicEvenP1OmegaGoodBONG (K := K) pairs) heOne
      (heClassicEvenP1OmegaGoodBONG_order_zero pairs)
      (heClassicEvenP1OmegaGoodBONG_alpha_eq_one pairs)
      (heClassicEvenP1Omega_fullSelfDefect pairs)
      (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit (Or.inr rfl)
      (he2022Classic_discriminantUnit_order (K := K))
      (he2022Classic_twoE_le_defect_discriminant (K := K))

/-- Lemma 7.9(i), second `P` row against `H_1^n(Delta)`. -/
theorem he2022ClassicLemma79i_P2Omega_HDiscriminant
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    let a := heClassicEvenP2OmegaGoodBONG (K := K) pairs
    let b := heClassicEvenHDiscriminantGoodBONG (K := K) pairs
    a.centralDefectTrigger b
      (BONG.GoodBONG.he2022ClassicLemma43Index pairs (by omega)) := by
  dsimp only
  exact BONG.GoodBONG.he2022ClassicLemma79i_of_zero_one_fullDefect
      pairs (heClassicEvenP2OmegaGoodBONG (K := K) pairs) heOne
      (heClassicEvenP2OmegaGoodBONG_order_zero pairs)
      (heClassicEvenP2OmegaGoodBONG_alpha_eq_one pairs)
      (heClassicEvenP2Omega_fullSelfDefect pairs)
      (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit (Or.inr rfl)
      (he2022Classic_discriminantUnit_order (K := K))
      (he2022Classic_twoE_le_defect_discriminant (K := K))

/-! ## Exact endpoint-prefix identifications -/

theorem heClassicEvenP1Omega_prefixValueUnits (pairs : Nat) :
    let a := heClassicEvenP1OmegaGoodBONG (K := K) pairs
    a.prefixValueUnits (2 * pairs + 3) (by omega) =
      heClassicEvenP1Prefix (K := K) pairs
        (heClassicOmega (K := K)) := by
  dsimp only
  funext i
  unfold BONG.GoodBONG.prefixValueUnits
  simp only [heClassicEvenP1OmegaGoodBONG,
    heClassicEvenP1GoodBONG, heHuExactGoodBONG_valueUnit]
  exact congrFun (heClassicEvenP1Prefix_eq_initial
    (K := K) pairs (heClassicOmega (K := K))) i

theorem heClassicEvenP2Omega_prefixValueUnits (pairs : Nat) :
    let a := heClassicEvenP2OmegaGoodBONG (K := K) pairs
    a.prefixValueUnits (2 * pairs + 3) (by omega) =
      heClassicEvenP2Prefix (K := K) pairs
        (heClassicOmega (K := K))
        (heClassicOmegaSharp (K := K)) := by
  dsimp only
  funext i
  unfold BONG.GoodBONG.prefixValueUnits
  simp only [heClassicEvenP2OmegaGoodBONG,
    heClassicEvenP2GoodBONG, heHuExactGoodBONG_valueUnit]
  exact congrFun (heClassicEvenP2Prefix_eq_initial
    (K := K) pairs (heClassicOmega (K := K))
      (heClassicOmegaSharp (K := K))) i

theorem heClassicEvenP1Omega_prefixValues (pairs : Nat) :
    let a := heClassicEvenP1OmegaGoodBONG (K := K) pairs
    a.prefixValues (2 * pairs + 3) (by omega) =
      diagonalUnitCoefficients
        (heClassicEvenP1Prefix (K := K) pairs
          (heClassicOmega (K := K))) := by
  dsimp only
  rw [← BONG.GoodBONG.diagonalUnitCoefficients_prefixValueUnits]
  rw [heClassicEvenP1Omega_prefixValueUnits]

theorem heClassicEvenP2Omega_prefixValues (pairs : Nat) :
    let a := heClassicEvenP2OmegaGoodBONG (K := K) pairs
    a.prefixValues (2 * pairs + 3) (by omega) =
      diagonalUnitCoefficients
        (heClassicEvenP2Prefix (K := K) pairs
          (heClassicOmega (K := K))
          (heClassicOmegaSharp (K := K))) := by
  dsimp only
  rw [← BONG.GoodBONG.diagonalUnitCoefficients_prefixValueUnits]
  rw [heClassicEvenP2Omega_prefixValueUnits]

theorem heClassicEvenHOne_fullPrefixValues (pairs : Nat) :
    let b := heClassicEvenHOneGoodBONG (K := K) pairs
    b.prefixValues (2 * pairs + 2) le_rfl =
      diagonalUnitCoefficients (heClassicEvenH (K := K) pairs 1) := by
  dsimp only
  simpa only [heClassicEvenHOneGoodBONG] using
    heClassicEvenH_fullPrefixValues (K := K) pairs 1 (Or.inl rfl)
      (he2022Classic_one_order (K := K))

theorem heClassicEvenHDiscriminant_fullPrefixValues (pairs : Nat) :
    let b := heClassicEvenHDiscriminantGoodBONG (K := K) pairs
    b.prefixValues (2 * pairs + 2) le_rfl =
      diagonalUnitCoefficients
        (heClassicEvenH (K := K) pairs
          (Dyadic.dyadicDiscriminantClassLawsProved
            (K := K)).discriminantUnit) := by
  dsimp only
  simpa only [heClassicEvenHDiscriminantGoodBONG] using
    heClassicEvenH_fullPrefixValues (K := K) pairs
      (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit (Or.inr rfl)
      (he2022Classic_discriminantUnit_order (K := K))

/-! ## The matching endpoint central conditions -/

theorem he2022ClassicLemma79iii_P1Omega_HOne_endpointCentral
    (pairs : Nat) :
    BONG.GoodBONG.HeClassicPublishedCentralConditionAt
      (heClassicEvenP1OmegaGoodBONG (K := K) pairs)
      (heClassicEvenHOneGoodBONG (K := K) pairs)
      (BONG.GoodBONG.he2022ClassicLemma43Index pairs (by omega)) := by
  unfold BONG.GoodBONG.HeClassicPublishedCentralConditionAt
  intro _
  change DiagonalRepresents
    ((heClassicEvenHOneGoodBONG (K := K) pairs).prefixValues
      ((2 * pairs + 3) - 1) (by omega))
    ((heClassicEvenP1OmegaGoodBONG (K := K) pairs).prefixValues
      (2 * pairs + 3) (by omega))
  let hs : 2 * pairs + 2 = (2 * pairs + 3) - 1 := by omega
  have hcast := BONG.GoodBONG.heHuLemma43_diagonalRepresents_castLengths
    hs
    (rfl : 2 * pairs + 3 = 2 * pairs + 3)
    (he2022ClassicLemma79ii_evenHOne_represents_P1Prefix
      (K := K) pairs)
  convert hcast using 1
  · funext j
    have hj := congrFun (heClassicEvenHOne_fullPrefixValues
      (K := K) pairs) (Fin.cast hs.symm j)
    simpa [BONG.GoodBONG.prefixValues] using hj
  · funext j
    have hj := congrFun (heClassicEvenP1Omega_prefixValues
      (K := K) pairs) j
    simpa using hj

theorem he2022ClassicLemma79iii_P2Omega_HDiscriminant_endpointCentral
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    BONG.GoodBONG.HeClassicPublishedCentralConditionAt
      (heClassicEvenP2OmegaGoodBONG (K := K) pairs)
      (heClassicEvenHDiscriminantGoodBONG (K := K) pairs)
      (BONG.GoodBONG.he2022ClassicLemma43Index pairs (by omega)) := by
  unfold BONG.GoodBONG.HeClassicPublishedCentralConditionAt
  intro _
  change DiagonalRepresents
    ((heClassicEvenHDiscriminantGoodBONG (K := K) pairs).prefixValues
      ((2 * pairs + 3) - 1) (by omega))
    ((heClassicEvenP2OmegaGoodBONG (K := K) pairs).prefixValues
      (2 * pairs + 3) (by omega))
  let hs : 2 * pairs + 2 = (2 * pairs + 3) - 1 := by omega
  have hcast := BONG.GoodBONG.heHuLemma43_diagonalRepresents_castLengths
    hs
    (rfl : 2 * pairs + 3 = 2 * pairs + 3)
    (he2022ClassicLemma79ii_evenHDiscriminant_represents_P2Prefix
      (K := K) pairs heOne)
  convert hcast using 1
  · funext j
    have hj := congrFun (heClassicEvenHDiscriminant_fullPrefixValues
      (K := K) pairs) (Fin.cast hs.symm j)
    simpa [BONG.GoodBONG.prefixValues] using hj
  · funext j
    have hj := congrFun (heClassicEvenP2Omega_prefixValues
      (K := K) pairs) j
    simpa using hj

namespace BONG.GoodBONG

private theorem he2022Classic_centralIndex_ext
    {largeRank smallRank : Nat}
    (i j : CentralRepresentationIndex largeRank smallRank)
    (hval : i.val = j.val) : i = j := by
  cases i
  cases j
  simp_all

/-- Lemma 7.9(iii), common sufficiency step.  Lemma 7.8 supplies all
noncentral conditions and all central indices through `n`; only the single
endpoint representation from Lemma 7.9(ii) remains. -/
theorem he2022ClassicLemma79iii_represents_of_endpoint
    (pairs : Nat) (a : GoodBONG q L (2 * pairs + 4))
    (b : GoodBONG r M (2 * pairs + 2))
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (heOne : ramificationIndex K = 1)
    (hzero : forall k : Fin (2 * pairs + 4), a.order k = 0)
    (halpha : forall k : Fin (2 * pairs + 3), a.alphaValue k = 1)
    (ambient : q.Represents r)
    (hEndpoint : a.HeClassicPublishedCentralConditionAt b
      (he2022ClassicLemma43Index pairs (by omega))) :
    Lattice.Represents q r L M := by
  have hnoncentral := a.he2022ClassicLemma78i_of_zero_one_profile
    pairs b hAClassic hBClassic heOne hzero halpha
  apply a.he2022ClassicRepresents_of_pointwisePrime b (by omega) ambient
  · exact hnoncentral.1
  · exact hnoncentral.2.1
  · intro i
    by_cases hi : i.val <= 2 * pairs + 2
    · exact a.he2022ClassicLemma78iii_of_zero_profile pairs b
        hBClassic hzero i hi
    · have hval : i.val = 2 * pairs + 3 := by
        have := i.le_small_succ
        omega
      have hiEq : i = he2022ClassicLemma43Index pairs (by omega) :=
        he2022Classic_centralIndex_ext i _ hval
      simpa only [hiEq] using hEndpoint
  · exact hnoncentral.2.2

/-- Transport the terminal BONG-prefix representation back to coefficient
rows of the published lengths. -/
theorem he2022ClassicLemma79iii_literalPrefix_of_endpoint
    (pairs : Nat) (a : GoodBONG q L (2 * pairs + 4))
    (b : GoodBONG r M (2 * pairs + 2))
    {sourceCoefficients : Fin (2 * pairs + 2) → K}
    {targetCoefficients : Fin (2 * pairs + 3) → K}
    (hSource : b.prefixValues (2 * pairs + 2) le_rfl =
      sourceCoefficients)
    (hTarget : a.prefixValues (2 * pairs + 3) (by omega) =
      targetCoefficients)
    (hEndpoint : DiagonalRepresents
      (b.prefixValues ((2 * pairs + 3) - 1) (by omega))
      (a.prefixValues (2 * pairs + 3) (by omega))) :
    DiagonalRepresents sourceCoefficients targetCoefficients := by
  let hs : (2 * pairs + 3) - 1 = 2 * pairs + 2 := by omega
  have hcast := heHuLemma43_diagonalRepresents_castLengths hs rfl hEndpoint
  convert hcast using 1
  · funext j
    have hj := congrFun hSource j
    simpa [prefixValues] using hj.symm
  · funext j
    have hj := congrFun hTarget j
    simpa using hj.symm

end BONG.GoodBONG

/-! ## Integral representation and nonrepresentation -/

/-- Lemma 7.9(iii), matching first row. -/
theorem he2022ClassicLemma79iii_P1Omega_represents_HOne
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    (heClassicEvenP1OmegaModel (K := K) pairs).Represents
      (heClassicEvenHOneModel (K := K) pairs) := by
  let a := heClassicEvenP1OmegaGoodBONG (K := K) pairs
  let b := heClassicEvenHOneGoodBONG (K := K) pairs
  have hAClassic := heClassicEvenP1_isClassicIntegral (K := K) pairs
    (heClassicOmega (K := K)) (heClassicOmega_order (K := K))
  have hBClassic := heClassicEvenH_isClassicIntegral (K := K) pairs
    (1 : Kˣ) (Or.inl rfl) (he2022Classic_one_order (K := K))
  have hAmbient :
      (BONG.coefficientDiagonalSpace
        (heClassicEvenP1 (K := K) pairs
          (heClassicOmega (K := K)))).Represents
        (BONG.coefficientDiagonalSpace
          (heClassicEvenH (K := K) pairs 1)) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (heClassicEvenH (K := K) pairs 1)
      (heClassicEvenP1 (K := K) pairs
        (heClassicOmega (K := K)))).2
          (he2022ClassicLemma75iii_evenHOne_represents_P1Omega
            (K := K) pairs)
  have hrep :=
    BONG.GoodBONG.he2022ClassicLemma79iii_represents_of_endpoint
      pairs a b
      hAClassic hBClassic heOne
      (heClassicEvenP1OmegaGoodBONG_order_zero pairs)
      (heClassicEvenP1OmegaGoodBONG_alpha_eq_one pairs) hAmbient
      (he2022ClassicLemma79iii_P1Omega_HOne_endpointCentral pairs)
  exact hrep

/-- Lemma 7.9(iii), matching second row. -/
theorem he2022ClassicLemma79iii_P2Omega_represents_HDiscriminant
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    (heClassicEvenP2OmegaModel (K := K) pairs).Represents
      (heClassicEvenHDiscriminantModel (K := K) pairs) := by
  let delta := (Dyadic.dyadicDiscriminantClassLawsProved
    (K := K)).discriminantUnit
  let a := heClassicEvenP2OmegaGoodBONG (K := K) pairs
  let b := heClassicEvenHDiscriminantGoodBONG (K := K) pairs
  have hAClassic := heClassicEvenP2_isClassicIntegral (K := K) pairs
    (heClassicOmega (K := K)) (heClassicOmegaSharp (K := K))
    (heClassicOmega_order (K := K)) (by
      rw [heClassicOmegaSharp_order (K := K)])
  have hBClassic := heClassicEvenH_isClassicIntegral (K := K) pairs
    delta (Or.inr rfl) (he2022Classic_discriminantUnit_order (K := K))
  have hAmbient :
      (BONG.coefficientDiagonalSpace
        (heClassicEvenP2 (K := K) pairs
          (heClassicOmega (K := K))
          (heClassicOmegaSharp (K := K)))).Represents
        (BONG.coefficientDiagonalSpace
          (heClassicEvenH (K := K) pairs delta)) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (heClassicEvenH (K := K) pairs delta)
      (heClassicEvenP2 (K := K) pairs
        (heClassicOmega (K := K))
        (heClassicOmegaSharp (K := K)))).2
          (he2022ClassicLemma75iii_evenHDiscriminant_represents_P2Omega
            (K := K) pairs heOne)
  have hrep :=
    BONG.GoodBONG.he2022ClassicLemma79iii_represents_of_endpoint
      pairs a b hAClassic hBClassic heOne
      (heClassicEvenP2OmegaGoodBONG_order_zero pairs)
      (heClassicEvenP2OmegaGoodBONG_alpha_eq_one pairs) hAmbient
      (he2022ClassicLemma79iii_P2Omega_HDiscriminant_endpointCentral
        pairs heOne)
  exact hrep

/-- Lemma 7.9(iii), mismatching first row. -/
theorem he2022ClassicLemma79iii_P1Omega_not_represents_HDiscriminant
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    ¬ (heClassicEvenP1OmegaModel (K := K) pairs).Represents
      (heClassicEvenHDiscriminantModel (K := K) pairs) := by
  intro hrep
  let a := heClassicEvenP1OmegaGoodBONG (K := K) pairs
  let b := heClassicEvenHDiscriminantGoodBONG (K := K) pairs
  have hconditions := a.representationConditionsPrime_of_represents
    b (by omega) hrep
  have hEndpoint := hconditions.centralRepresentations
    (BONG.GoodBONG.he2022ClassicLemma43Index pairs (by omega))
    (he2022ClassicLemma79i_P1Omega_HDiscriminant pairs heOne)
  have hLiteral :=
    BONG.GoodBONG.he2022ClassicLemma79iii_literalPrefix_of_endpoint
      pairs a b
      (heClassicEvenHDiscriminant_fullPrefixValues pairs)
      (heClassicEvenP1Omega_prefixValues pairs) hEndpoint
  exact he2022ClassicLemma79ii_evenHDiscriminant_not_represents_P1Prefix
    (K := K) pairs heOne hLiteral

/-- Lemma 7.9(iii), mismatching second row. -/
theorem he2022ClassicLemma79iii_P2Omega_not_represents_HOne
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    ¬ (heClassicEvenP2OmegaModel (K := K) pairs).Represents
      (heClassicEvenHOneModel (K := K) pairs) := by
  intro hrep
  let a := heClassicEvenP2OmegaGoodBONG (K := K) pairs
  let b := heClassicEvenHOneGoodBONG (K := K) pairs
  have hconditions := a.representationConditionsPrime_of_represents
    b (by omega) hrep
  have hEndpoint := hconditions.centralRepresentations
    (BONG.GoodBONG.he2022ClassicLemma43Index pairs (by omega))
    (he2022ClassicLemma79i_P2Omega_HOne pairs heOne)
  have hLiteral :=
    BONG.GoodBONG.he2022ClassicLemma79iii_literalPrefix_of_endpoint
      pairs a b (heClassicEvenHOne_fullPrefixValues pairs)
      (heClassicEvenP2Omega_prefixValues pairs) hEndpoint
  exact he2022ClassicLemma79ii_evenHOne_not_represents_P2Prefix
    (K := K) pairs hLiteral

end Bong
