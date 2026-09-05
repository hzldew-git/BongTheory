/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.AlternatingEndpointTowerRepresentationProof
import Bong.QuadraticSpace.OrthogonalSumDiagonal

/-!
# Odd-dimensional normal forms for alternating endpoint towers

This file proves the local quadratic-space step used in He--Hu,
Proposition 2.7(v).  An alternating endpoint tower at unit scale, followed
by a coefficient of even valuation, is isometric to a hyperbolic tower
followed by a valuation-unit line.  The final line lies either in the
square class of the appended coefficient or in its discriminant twist.

The proof uses the already established determinant--Hasse classification.
It is independent of the He--Hu paper and is therefore kept in the shared
BONG layer.
-/

namespace Bong

open Dyadic BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [discriminant : DyadicDiscriminantClassLaws K]

namespace AlternatingEndpointTower

/-- The diagonal coefficient family `[1,-1]` repeated `pairs` times. -/
def standardHyperbolicEndpointTower (pairs : Nat) :
    Fin (2 * pairs) → Kˣ := fun i =>
  if Even i.val then 1 else -1

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] discriminant in
@[simp]
theorem standardHyperbolicEndpointTower_even {pairs : Nat}
    (t : Fin pairs) :
    standardHyperbolicEndpointTower (K := K) pairs
        ⟨2 * t.val, by omega⟩ = 1 := by
  simp [standardHyperbolicEndpointTower]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] discriminant in
@[simp]
theorem standardHyperbolicEndpointTower_odd {pairs : Nat}
    (t : Fin pairs) :
    standardHyperbolicEndpointTower (K := K) pairs
        ⟨2 * t.val + 1, by omega⟩ = -1 := by
  have hnot : ¬ Even (2 * t.val + 1) :=
    Nat.not_even_two_mul_add_one t.val
  simp [standardHyperbolicEndpointTower, hnot]

/-- Every binary block of the standard tower is hyperbolic. -/
theorem standardHyperbolicEndpointTower_pairClasses (pairs : Nat) :
    AlternatingEndpointPairClasses
      (standardHyperbolicEndpointTower (K := K) pairs) := by
  intro t
  left
  refine ⟨1, ?_⟩
  simp

omit discriminant in
/-- Every leading coefficient of the standard tower has unit scale. -/
theorem standardHyperbolicEndpointTower_leadingOrders (pairs : Nat) :
    AlternatingEndpointLeadingOrdersAt
      (standardHyperbolicEndpointTower (K := K) pairs) (1 : Kˣ) := by
  intro t
  simp

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] discriminant in
/-- Deleting the final pair from the standard tower gives the preceding
standard tower. -/
theorem init_standardHyperbolicEndpointTower (pairs : Nat) :
    init (standardHyperbolicEndpointTower (K := K) (pairs + 1)) =
      standardHyperbolicEndpointTower (K := K) pairs := by
  funext i
  simp only [init, standardHyperbolicEndpointTower]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] discriminant in
/-- The last pair of the standard tower is `[1,-1]`. -/
theorem lastPair_standardHyperbolicEndpointTower_zero (pairs : Nat) :
    lastPair (standardHyperbolicEndpointTower (K := K) (pairs + 1)) 0 = 1 := by
  simp [lastPair, standardHyperbolicEndpointTower]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] discriminant in
theorem lastPair_standardHyperbolicEndpointTower_one (pairs : Nat) :
    lastPair (standardHyperbolicEndpointTower (K := K) (pairs + 1)) 1 = -1 := by
  have hnot : ¬ Even (2 * pairs + 1) :=
    Nat.not_even_two_mul_add_one pairs
  simp [lastPair, standardHyperbolicEndpointTower, hnot]

/-- The signed determinant of `H^pairs` is one. -/
theorem signedDeterminant_standardHyperbolicEndpointTower (pairs : Nat) :
    signedDeterminant
      (standardHyperbolicEndpointTower (K := K) pairs) = 1 := by
  induction pairs with
  | zero =>
      simp [signedDeterminant, diagonalUnitDeterminant]
  | succ pairs ih =>
      rw [signedDeterminant_succ,
        init_standardHyperbolicEndpointTower,
        lastPair_standardHyperbolicEndpointTower_zero,
        lastPair_standardHyperbolicEndpointTower_one, ih]
      norm_num

omit discriminant in
/-- Remove a square of the uniformizer from an even-order coefficient. -/
theorem exists_valuationUnit_squareRepresentative_of_even_order
    (x : Kˣ) (hxEven : Even (ordUnit K x)) :
    ∃ u t : Kˣ, IsValuationUnit K (u : K) ∧ u = x * t ^ 2 := by
  rcases hxEven with ⟨k, hk⟩
  let t : Kˣ := uniformizerPowerUnit K (-k)
  let u : Kˣ := x * t ^ 2
  have huOrder : ordUnit K u = 0 := by
    simp only [u, t, ordUnit_mul, ordUnit_pow,
      ordUnit_uniformizerPowerUnit]
    omega
  exact ⟨u, t, (isValuationUnit_iff_ordUnit_eq_zero K u).2 huOrder, rfl⟩

/-- The finite diagonal space attached to `H^pairs ⊥ [epsilon]`. -/
noncomputable def hyperbolicEndpointTowerWithLineSpace
    (pairs : Nat) (epsilon : Kˣ) :
    QuadraticSpace K (Fin (2 * pairs + 1) → K) :=
  QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients
      (Fin.snoc (standardHyperbolicEndpointTower (K := K) pairs) epsilon))
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero
      (Fin.snoc (standardHyperbolicEndpointTower (K := K) pairs) epsilon))

/-- Exact odd-dimensional normal form for a fixed-unit-scale alternating
endpoint tower.  The equality witness records the paper's alternative
`epsilon in x F^x2` or `epsilon in Delta x F^x2`. -/
theorem oddNormalForm_of_even_order
    [HilbertSymbolLaws K] [DyadicUnramifiedNormLaws K]
    [DyadicDiagonalClassificationLaws K]
    {pairs : Nat} (a : Fin (2 * pairs) → Kˣ) (x : Kˣ)
    (ha : AlternatingEndpointPairClasses a)
    (haOrders : AlternatingEndpointLeadingOrdersAt a (1 : Kˣ))
    (hxEven : Even (ordUnit K x)) :
    ∃ epsilon t : Kˣ,
      IsValuationUnit K (epsilon : K) ∧
      (epsilon = x * t ^ 2 ∨
        epsilon = discriminant.discriminantUnit * x * t ^ 2) ∧
      (QuadraticSpace.finiteDiagonal
          (diagonalUnitCoefficients (Fin.snoc a x))
          (QuadraticSpace.diagonalUnitCoefficients_ne_zero
            (Fin.snoc a x))).IsIsometric
        (hyperbolicEndpointTowerWithLineSpace
          (K := K) pairs epsilon) := by
  let h := standardHyperbolicEndpointTower (K := K) pairs
  have hhClasses : AlternatingEndpointPairClasses h :=
    standardHyperbolicEndpointTower_pairClasses pairs
  have hhOrders : AlternatingEndpointLeadingOrdersAt h (1 : Kˣ) :=
    standardHyperbolicEndpointTower_leadingOrders pairs
  have haHasse :=
    diagonalHasseSymbol_eq_constant_mul_signedDeterminant
      a (1 : Kˣ) ha haOrders
  have hhHasse :=
    diagonalHasseSymbol_eq_constant_mul_signedDeterminant
      h (1 : Kˣ) hhClasses hhOrders
  have hhSigned : signedDeterminant h = 1 :=
    signedDeterminant_standardHyperbolicEndpointTower pairs
  have haCases := signedDeterminant_cases a ha
  rcases exists_valuationUnit_squareRepresentative_of_even_order x hxEven with
    ⟨eta, t, hetaUnit, heta⟩
  have hbaseHasse :
      diagonalHasseSymbol K a = diagonalHasseSymbol K h := by
    rw [haHasse, hhHasse, hhSigned]
    simp only [hilbertSymbol_one_right, mul_one]
  have hxeta : IsSquare (x * eta) := by
    refine ⟨x * t, ?_⟩
    rw [heta]
    simp only [pow_two]
    ac_rfl
  rcases haCases with haSquare | haDiscriminant
  · refine ⟨eta, t, hetaUnit, Or.inl heta, ?_⟩
    have hdetBase : IsSquare
        (diagonalUnitDeterminant a * diagonalUnitDeterminant h) := by
      rcases haSquare with ⟨s, hs⟩
      refine ⟨((-1 : Kˣ) ^ pairs) * s, ?_⟩
      rw [determinant_eq_sign_mul_signedDeterminant,
        determinant_eq_sign_mul_signedDeterminant, hhSigned, hs]
      simp only [mul_one]
      ac_rfl
    have hdet : IsSquare
        (diagonalUnitDeterminant (Fin.snoc a x) *
          diagonalUnitDeterminant (Fin.snoc h eta)) := by
      rw [diagonalUnitDeterminant_snoc, diagonalUnitDeterminant_snoc]
      have hproduct := hdetBase.mul hxeta
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hproduct
    have hcross :
        hilbertSymbol K (diagonalUnitDeterminant a) x =
          hilbertSymbol K (diagonalUnitDeterminant h) eta := by
      calc
        hilbertSymbol K (diagonalUnitDeterminant a) x =
            hilbertSymbol K (diagonalUnitDeterminant h) x :=
          hilbertSymbol_eq_of_isSquare_mul_left hdetBase
        _ = hilbertSymbol K (diagonalUnitDeterminant h) eta :=
          hilbertSymbol_eq_of_isSquare_mul_right hxeta
    have hself : hilbertSymbol K x x = hilbertSymbol K eta eta := by
      calc
        hilbertSymbol K x x = hilbertSymbol K eta x :=
          hilbertSymbol_eq_of_isSquare_mul_left hxeta
        _ = hilbertSymbol K eta eta :=
          hilbertSymbol_eq_of_isSquare_mul_right hxeta
    have hhasse :
        diagonalHasseSymbol K (Fin.snoc a x) =
          diagonalHasseSymbol K (Fin.snoc h eta) := by
      rw [diagonalHasseSymbol_snoc, diagonalHasseSymbol_snoc,
        hbaseHasse, hcross, hself]
    have hrep := DyadicDiagonalClassificationLaws.represents_of_invariants
      (Fin.snoc a x) (Fin.snoc h eta) hdet hhasse
    rcases DiagonalRepresents.toQuadraticSpaceRepresents
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero (Fin.snoc a x))
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero (Fin.snoc h eta))
        hrep with ⟨f⟩
    exact ⟨f.toIsometryOfFinrankEq rfl⟩
  · let epsilon := discriminant.discriminantUnit * eta
    have hepsilonUnit : IsValuationUnit K (epsilon : K) := by
      rw [isValuationUnit_iff_ordUnit_eq_zero]
      simp only [epsilon, ordUnit_mul,
        (isValuationUnit_iff_ordUnit_eq_zero K
          discriminant.discriminantUnit).1
            discriminant.discriminant_isValuationUnit,
        (isValuationUnit_iff_ordUnit_eq_zero K eta).1 hetaUnit]
      omega
    refine ⟨epsilon, t, hepsilonUnit, Or.inr ?_, ?_⟩
    · rw [show epsilon = discriminant.discriminantUnit * eta by rfl,
        heta]
      group
    · have hdetBaseDiscriminant : IsSquare
          ((diagonalUnitDeterminant a * diagonalUnitDeterminant h) *
            discriminant.discriminantUnit) := by
        rcases haDiscriminant with ⟨s, hs⟩
        refine ⟨((-1 : Kˣ) ^ pairs) * s, ?_⟩
        rw [determinant_eq_sign_mul_signedDeterminant,
          determinant_eq_sign_mul_signedDeterminant, hhSigned]
        simp only [mul_one]
        rw [show ((-1 : Kˣ) ^ pairs * signedDeterminant a) *
              ((-1 : Kˣ) ^ pairs) * discriminant.discriminantUnit =
              (((-1 : Kˣ) ^ pairs) * ((-1 : Kˣ) ^ pairs)) *
                (signedDeterminant a * discriminant.discriminantUnit) by
              ac_rfl,
          hs]
        ac_rfl
      have hdet : IsSquare
          (diagonalUnitDeterminant (Fin.snoc a x) *
            diagonalUnitDeterminant (Fin.snoc h epsilon)) := by
        rw [diagonalUnitDeterminant_snoc,
          diagonalUnitDeterminant_snoc,
          show epsilon = discriminant.discriminantUnit * eta by rfl]
        have hproduct := hdetBaseDiscriminant.mul hxeta
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hproduct
      have hsignEven : Even (ordUnit K ((-1 : Kˣ) ^ pairs)) := by
        rw [ordUnit_pow, ordUnit_neg_one_eq_zero]
        exact Even.zero
      have hsignDelta :
          hilbertSymbol K ((-1 : Kˣ) ^ pairs)
              discriminant.discriminantUnit = 1 := by
        rw [hilbertSymbol_comm]
        exact hilbertSymbol_discriminant_eq_one_of_even_order
          ((-1 : Kˣ) ^ pairs) hsignEven
      have haSignedX : hilbertSymbol K (signedDeterminant a) x = 1 :=
        hilbertSymbol_endpointClass_eq_one_of_even_order
          (Or.inr haDiscriminant) hxEven
      have hxetaRight :
          hilbertSymbol K ((-1 : Kˣ) ^ pairs) x =
            hilbertSymbol K ((-1 : Kˣ) ^ pairs) eta :=
        hilbertSymbol_eq_of_isSquare_mul_right hxeta
      have hcross :
          hilbertSymbol K (diagonalUnitDeterminant a) x =
            hilbertSymbol K (diagonalUnitDeterminant h) epsilon := by
        rw [determinant_eq_sign_mul_signedDeterminant,
          determinant_eq_sign_mul_signedDeterminant, hhSigned]
        simp only [mul_one]
        rw [hilbertSymbol_mul_left, haSignedX, mul_one,
          show epsilon = discriminant.discriminantUnit * eta by rfl,
          hilbertSymbol_mul_right, hsignDelta, one_mul]
        exact hxetaRight
      have hnegOneEven : Even (ordUnit K (-1 : Kˣ)) := by
        rw [ordUnit_neg_one_eq_zero]
        exact Even.zero
      have hdeltaNegOne :
          hilbertSymbol K discriminant.discriminantUnit (-1 : Kˣ) = 1 :=
        hilbertSymbol_discriminant_eq_one_of_even_order
          (-1 : Kˣ) hnegOneEven
      have hself :
          hilbertSymbol K x x = hilbertSymbol K epsilon epsilon := by
        calc
          hilbertSymbol K x x = hilbertSymbol K x (-1 : Kˣ) :=
            hilbertSymbol_self_eq_neg_one x
          _ = hilbertSymbol K eta (-1 : Kˣ) :=
            hilbertSymbol_eq_of_isSquare_mul_left hxeta
          _ = hilbertSymbol K
                (discriminant.discriminantUnit * eta) (-1 : Kˣ) := by
            rw [hilbertSymbol_mul_left, hdeltaNegOne, one_mul]
          _ = hilbertSymbol K epsilon (-1 : Kˣ) := by rfl
          _ = hilbertSymbol K epsilon epsilon :=
            (hilbertSymbol_self_eq_neg_one epsilon).symm
      have hhasse :
          diagonalHasseSymbol K (Fin.snoc a x) =
            diagonalHasseSymbol K (Fin.snoc h epsilon) := by
        rw [diagonalHasseSymbol_snoc, diagonalHasseSymbol_snoc,
          hbaseHasse, hcross, hself]
      have hrep := DyadicDiagonalClassificationLaws.represents_of_invariants
        (Fin.snoc a x) (Fin.snoc h epsilon) hdet hhasse
      rcases DiagonalRepresents.toQuadraticSpaceRepresents
          (QuadraticSpace.diagonalUnitCoefficients_ne_zero (Fin.snoc a x))
          (QuadraticSpace.diagonalUnitCoefficients_ne_zero
            (Fin.snoc h epsilon)) hrep with ⟨f⟩
      exact ⟨f.toIsometryOfFinrankEq rfl⟩

end AlternatingEndpointTower

end Bong
