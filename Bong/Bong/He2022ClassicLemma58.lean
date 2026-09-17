/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma57
import Bong.Bong.He2022ClassicCorollary313

/-!
# He (2024), Lemma 5.8

This file formalizes the odd-rank finite test for condition (iv) and its
equivalence with `J3_O(n)`.  Both parity branches of the literal
`C₂ⁿ(c)` row in Definition 2.6 remain visible.
-/

namespace Bong

open Dyadic BONG.GoodBONG AlternatingEndpointTower

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-! ## The two literal odd-rank determinant-class pairs -/

/-- The terminal ternary in the even-order branch of the publisher's
`C₂ⁿ(c)` row. -/
noncomputable def heClassicOddC2EvenTail
    (c omega omegaSharp : Kˣ) : Fin 3 → Kˣ :=
  ![c * omegaSharp, -(c * omegaSharp * omega), c * omega]

@[simp] theorem heClassicOddC2EvenTail_zero
    (c omega omegaSharp : Kˣ) :
    heClassicOddC2EvenTail c omega omegaSharp 0 = c * omegaSharp := rfl

@[simp] theorem heClassicOddC2EvenTail_one
    (c omega omegaSharp : Kˣ) :
    heClassicOddC2EvenTail c omega omegaSharp 1 =
      -(c * omegaSharp * omega) := rfl

@[simp] theorem heClassicOddC2EvenTail_two
    (c omega omegaSharp : Kˣ) :
    heClassicOddC2EvenTail c omega omegaSharp 2 = c * omega := rfl

/-- The even-order second-column ternary has the same determinant square
class as `[1,-1,c]`. -/
theorem heClassicOddC2EvenTail_determinantSquare_first
    (c omega omegaSharp : Kˣ) :
    IsSquare
      (diagonalUnitDeterminant
          (heClassicOddC2EvenTail (K := K) c omega omegaSharp) *
        diagonalUnitDeterminant (heHuOddFirstTail (K := K) c)) := by
  refine ⟨c * c * omegaSharp * omega, ?_⟩
  simp [heClassicOddC2EvenTail, heHuOddFirstTail,
    diagonalUnitDeterminant, Fin.prod_univ_three]
  ac_rfl

/-- The adjacent Hilbert symbol of the even-order second-column ternary is
negative for the fixed `omega, omega#` of Definition 2.6. -/
theorem heClassicOddC2EvenTail_adjacentHilbert
    [HilbertSymbolLaws K]
    (c omega omegaSharp : Kˣ)
    (hnegative : hilbertSymbol K omegaSharp omega = -1) :
    hilbertSymbol K
        (-(heClassicOddC2EvenTail c omega omegaSharp 0 *
          heClassicOddC2EvenTail c omega omegaSharp 1))
        (-(heClassicOddC2EvenTail c omega omegaSharp 1 *
          heClassicOddC2EvenTail c omega omegaSharp 2)) = -1 := by
  have hfirst :
      -(heClassicOddC2EvenTail c omega omegaSharp 0 *
          heClassicOddC2EvenTail c omega omegaSharp 1) =
        omega * (c * omegaSharp) ^ 2 := by
    simp only [heClassicOddC2EvenTail_zero,
      heClassicOddC2EvenTail_one, mul_neg, neg_neg, pow_two]
    ac_rfl
  have hsecond :
      -(heClassicOddC2EvenTail c omega omegaSharp 1 *
          heClassicOddC2EvenTail c omega omegaSharp 2) =
        omegaSharp * (c * omega) ^ 2 := by
    simp only [heClassicOddC2EvenTail_one,
      heClassicOddC2EvenTail_two, neg_mul, neg_neg, pow_two]
    ac_rfl
  rw [hfirst, hsecond, hilbertSymbol_mul_square_left,
    hilbertSymbol_mul_square_right, hilbertSymbol_comm]
  exact hnegative

/-- The even-order second-column ternary is anisotropic. -/
theorem heClassicOddC2EvenTail_anisotropic
    [HilbertSymbolLaws K]
    (c omega omegaSharp : Kˣ)
    (hnegative : hilbertSymbol K omegaSharp omega = -1) :
    DiagonalAnisotropic
      (diagonalUnitCoefficients
        (heClassicOddC2EvenTail (K := K) c omega omegaSharp)) := by
  rw [← not_diagonalIsotropic_iff_diagonalAnisotropic,
    diagonalUnitTernary_isotropic_iff_adjacentHilbertOne,
    heClassicOddC2EvenTail_adjacentHilbert c omega omegaSharp hnegative]
  norm_num

/-- The literal even-order rows `C₁ⁿ(c), C₂ⁿ(c)` form the two
quadratic-space classes in their common determinant square class. -/
theorem heClassicOddC_evenOrder_pairProperties
    [HilbertSymbolLaws K]
    (pairs : Nat) (c omega omegaSharp : Kˣ)
    (hnegative : hilbertSymbol K omegaSharp omega = -1) :
    HeHuSpacePairProperties
      (heClassicOddC1 (K := K) pairs c)
      (heClassicOddC2Even (K := K) pairs c omega omegaSharp) := by
  have Ptail : HeHuSpacePairProperties
      (heHuOddFirstTail (K := K) c)
      (heClassicOddC2EvenTail (K := K) c omega omegaSharp) := by
    apply HeHuSpacePairProperties.of_det_not
    · exact heClassicOddC2EvenTail_determinantSquare_first
        c omega omegaSharp
    · intro hrep
      have hfirstAnisotropic : DiagonalAnisotropic
          (diagonalUnitCoefficients (heHuOddFirstTail (K := K) c)) :=
        hrep.symm_of_sameRank.anisotropic_of
          (heClassicOddC2EvenTail_anisotropic c omega omegaSharp hnegative)
      exact ((not_diagonalIsotropic_iff_diagonalAnisotropic
        (diagonalUnitCoefficients (heHuOddFirstTail (K := K) c))).2
          hfirstAnisotropic) (heHuOddFirstTail_isotropic c)
  have P := Ptail.append
    (standardHyperbolicEndpointTower (K := K) pairs)
  simpa only [heClassicOddC1_eq_heHuOddFirst, heHuOddFirst,
    heClassicOddC2Even, heClassicOddC2EvenTail,
    heClassicScaledHyperbolicTower_zero] using P

/-- In the odd-order branch, the literal classic second row is exactly the
He--Hu odd determinant-class representative. -/
theorem heClassicOddC2Odd_eq_heHuOddSecond_of_odd
    (pairs : Nat) (c : Kˣ) (hodd : Odd (ordUnit K c)) :
    heClassicOddC2Odd (K := K) pairs c = heHuOddSecond pairs c := by
  have hNotEven : ¬ Even (ordUnit K c) := Int.not_even_iff_odd.mpr hodd
  rw [heHuOddSecond_of_not_even pairs c hNotEven]
  unfold heClassicOddC2Odd
  rw [heClassicScaledHyperbolicTower_zero]
  have htail :
      (let delta :=
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
       ![1, -delta, c * delta] : Fin 3 → Kˣ) =
        heHuOddSecondTailOdd c := by
    funext i
    fin_cases i <;> simp [heHuOddSecondTailOdd] <;> ac_rfl
  exact congrArg
    (Fin.append (standardHyperbolicEndpointTower (K := K) pairs)) htail

/-- The literal odd-order rows `C₁ⁿ(c), C₂ⁿ(c)` form the two
quadratic-space classes in their common determinant square class. -/
theorem heClassicOddC_oddOrder_pairProperties
    (pairs : Nat) (c : Kˣ) (hodd : Odd (ordUnit K c)) :
    HeHuSpacePairProperties
      (heClassicOddC1 (K := K) pairs c)
      (heClassicOddC2Odd (K := K) pairs c) := by
  rw [heClassicOddC1_eq_heHuOddFirst,
    heClassicOddC2Odd_eq_heHuOddSecond_of_odd pairs c hodd]
  exact heHu2022Definition34Proposition35Odd pairs c

namespace BONG.GoodBONG

/-! ## The literal tests and their terminal activation -/

/-- The signed determinant parameter
`c=(-1)^((n+1)/2)a_{1,n+2}` for `n=2*k+3`. -/
noncomputable def he2022ClassicLemma58C {m : Nat}
    (a : GoodBONG q L (m + 5)) (k : Nat) : Kˣ :=
  ((-1 : Kˣ) ^ (k + 2)) * a.prefixProduct (2 * k + 5)

/-- The two literal odd-rank rows in Lemma 5.8(ii), with the two parity
branches of Definition 2.6 kept separate. -/
noncomputable def HeClassicLemma58PublishedTests
    [DyadicDiscriminantClassLaws K]
    {m : Nat} (a : GoodBONG q L (m + 5)) (k : Nat)
    (_hSource : 2 * k + 6 <= m + 5) : Prop :=
  2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 5, by omega⟩ -
        a.order ⟨2 * k + 4, by omega⟩ →
    let c := he2022ClassicLemma58C a k
    (∀ hc : ordUnit K c = 0,
      let bC1 := heClassicOddC1GoodBONG (K := K) k c (by omega)
      let bC2 := heClassicOddC2EvenGoodBONG (K := K) k c
        (heClassicOmega (K := K)) (heClassicOmegaSharp (K := K)) hc
        (heClassicOmega_order (K := K))
        (heClassicOmegaSharp_order (K := K))
      a.LongRepresentationConditions bC1 ∧
        a.LongRepresentationConditions bC2) ∧
    (∀ hc : ordUnit K c = 1,
      let bC1 := heClassicOddC1GoodBONG (K := K) k c (by omega)
      let bC2 := heClassicOddC2OddGoodBONG (K := K) k c (by omega)
      a.LongRepresentationConditions bC1 ∧
        a.LongRepresentationConditions bC2)

/-- Lemma 5.8, implication `(i) -> (ii)`: specialize condition (iv) to
the two printed rows in the parity branch of `c`. -/
theorem he2022ClassicLemma58_all_to_tests
    [DyadicDiscriminantClassLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 5))
    (hSource : 2 * k + 6 <= m + 5)
    (hAll : HeClassicAllLongRepresentationConditions.{u, v, u}
      (n := 2 * k + 2) a) :
    a.HeClassicLemma58PublishedTests k hSource := by
  intro _hLarge
  dsimp only
  constructor
  · intro hc
    constructor
    · exact hAll _ (heClassicOddC1_isClassicIntegral (K := K) k _ (by omega))
    · exact hAll _ (heClassicOddC2Even_isClassicIntegral (K := K) k _ _ _
        hc (heClassicOmega_order (K := K))
        (heClassicOmegaSharp_order (K := K)))
  · intro hc
    constructor
    · exact hAll _ (heClassicOddC1_isClassicIntegral (K := K) k _ (by omega))
    · exact hAll _ (heClassicOddC2Odd_isClassicIntegral (K := K) k _ (by omega))

/-- At full rank the exact first row has exactly its displayed value units. -/
theorem heClassicOddC1_fullPrefixValueUnits
    (k : Nat) (c : Kˣ) (hc : 0 <= ordUnit K c) :
    let b := heClassicOddC1GoodBONG (K := K) k c hc
    b.prefixValueUnits (2 * k + 3) le_rfl =
      heClassicOddC1 (K := K) k c := by
  dsimp only
  funext i
  change (heClassicOddC1GoodBONG (K := K) k c hc).valueUnit i = _
  rw [heClassicOddC1GoodBONG, heHuExactGoodBONG_valueUnit]

/-- At full rank the exact odd-order second row has its displayed units. -/
theorem heClassicOddC2Odd_fullPrefixValueUnits
    (k : Nat) (c : Kˣ) (hc : 0 <= ordUnit K c) :
    let b := heClassicOddC2OddGoodBONG (K := K) k c hc
    b.prefixValueUnits (2 * k + 3) le_rfl =
      heClassicOddC2Odd (K := K) k c := by
  dsimp only
  funext i
  change (heClassicOddC2OddGoodBONG (K := K) k c hc).valueUnit i = _
  rw [heClassicOddC2OddGoodBONG, heHuExactGoodBONG_valueUnit]

/-- At full rank the exact even-order second row has its displayed units. -/
theorem heClassicOddC2Even_fullPrefixValueUnits
    (k : Nat) (c omega omegaSharp : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0)
    (homegaSharp : ordUnit K omegaSharp = 0) :
    let b := heClassicOddC2EvenGoodBONG (K := K) k c omega omegaSharp
      hc homega homegaSharp
    b.prefixValueUnits (2 * k + 3) le_rfl =
      heClassicOddC2Even (K := K) k c omega omegaSharp := by
  dsimp only
  funext i
  change (heClassicOddC2EvenGoodBONG (K := K) k c omega omegaSharp
    hc homega homegaSharp).valueUnit i = _
  rw [heClassicOddC2EvenGoodBONG, heHuExactGoodBONG_valueUnit]

/-- Under the preceding zero block and `R_(n+1)=0`, the order of `c` is
the terminal order `R_(n+2)`. -/
theorem he2022ClassicLemma58C_order {m k : Nat}
    (a : GoodBONG q L (m + 5))
    (hSource : 2 * k + 6 <= m + 5)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega))
    (hRn1 : a.order ⟨2 * k + 3, by omega⟩ = 0) :
    ordUnit K (he2022ClassicLemma58C a k) =
      a.order ⟨2 * k + 4, by omega⟩ := by
  have hPrefixZero : a.orderSequence.prefixSum (2 * k + 4) = 0 := by
    unfold BeliOrderSequence.prefixSum
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
    by_cases hlast : i = 2 * k + 3
    · subst i
      exact hRn1
    · let small : Fin (2 * k + 3) := ⟨i, by omega⟩
      have h := hJ1.1 small
      change a.order ⟨i, by omega⟩ = 0 at h
      exact h
  have hSign : ordUnit K ((-1 : Kˣ) ^ (k + 2)) = 0 := by
    rw [ordUnit_pow, ordUnit_neg]
    simp [ordUnit]
  unfold he2022ClassicLemma58C
  rw [ordUnit_mul, hSign, zero_add,
    a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (2 * k + 5) (by omega),
    show 2 * k + 5 = (2 * k + 4) + 1 by omega,
    a.orderSequence.prefixSum_succ, hPrefixZero,
    a.orderSequence_entryOrZero_eq_order
      (⟨2 * k + 4, by omega⟩ : Fin (m + 5)), zero_add]

/-- The terminal index `i=n+1` used in Lemma 5.8. -/
def he2022ClassicLemma58Index {m : Nat} (k : Nat)
    (hSource : 2 * k + 6 <= m + 5) :
    LongRepresentationIndex (m + 5) (2 * k + 3) where
  val := 2 * k + 4
  one_lt := by omega
  succ_lt_large := by omega
  le_small_succ := by omega

/-- A large final gap activates condition (iv) at the terminal index. -/
theorem he2022ClassicLemma58_terminalRepresentation
    {m k : Nat} (a : GoodBONG q L (m + 5))
    (b : GoodBONG r M (2 * k + 3))
    (hSource : 2 * k + 6 <= m + 5)
    (hLarge : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 5, by omega⟩ -
        a.order ⟨2 * k + 4, by omega⟩)
    (hLast : b.order ⟨2 * k + 2, by omega⟩ =
      a.order ⟨2 * k + 4, by omega⟩)
    (hLong : a.LongRepresentationConditions b) :
    DiagonalRepresents
      (b.prefixValues (2 * k + 3) le_rfl)
      (a.prefixValues (2 * k + 5) (by omega)) := by
  let i := he2022ClassicLemma58Index k hSource
  have hi := (a.heClassicLongConditions_iff_forall_at b).mp hLong i
  have hRep := hi (by
    refine ⟨?_, ?_, ?_⟩
    · simp [i, he2022ClassicLemma58Index]
    · change b.order ⟨2 * k + 2, by omega⟩ +
          2 * (ramificationIndex K : Int) <
        a.order ⟨2 * k + 5, by omega⟩
      rw [hLast]
      omega
    · change a.order ⟨2 * k + 4, by omega⟩ +
          2 * (ramificationIndex K : Int) <=
        b.order ⟨2 * k + 2, by omega⟩ +
          2 * (ramificationIndex K : Int)
      rw [hLast])
  simpa [i, he2022ClassicLemma58Index] using hRep

/-- The signed source prefix and the first printed row satisfy the
determinant hypothesis in Lemma 3.13. -/
theorem he2022ClassicLemma58_source_first_determinantSquare
    {m k : Nat} (a : GoodBONG q L (m + 5))
    (hSource : 2 * k + 6 <= m + 5) :
    let source := a.prefixValueUnits (2 * k + 5) (by omega)
    let c := he2022ClassicLemma58C a k
    IsSquare (-diagonalUnitDeterminant source *
      diagonalUnitDeterminant (heClassicOddC1 (K := K) k c)) := by
  dsimp only
  rw [a.diagonalUnitDeterminant_prefixValueUnits (2 * k + 5) (by omega),
    heClassicOddC1_eq_heHuOddFirst,
    diagonalUnitDeterminant_heHuOddFirst]
  refine ⟨a.prefixProduct (2 * k + 5), ?_⟩
  unfold he2022ClassicLemma58C
  have hEven : Even (1 + (k + 1) + (k + 2)) := ⟨k + 2, by omega⟩
  have hSign : (-1 : Kˣ) *
      (((-1 : Kˣ) ^ (k + 1)) * ((-1 : Kˣ) ^ (k + 2))) = 1 := by
    calc
      (-1 : Kˣ) *
          (((-1 : Kˣ) ^ (k + 1)) * ((-1 : Kˣ) ^ (k + 2))) =
          (-1 : Kˣ) ^ (1 + (k + 1) + (k + 2)) := by
            simp only [pow_add, pow_one, mul_assoc]
      _ = 1 := hEven.neg_one_pow
  have hNeg : -a.prefixProduct (2 * k + 5) =
      (-1 : Kˣ) * a.prefixProduct (2 * k + 5) := by
    apply Units.ext
    simp
  rw [hNeg]
  calc
    ((-1 : Kˣ) * a.prefixProduct (2 * k + 5)) *
        ((-1 : Kˣ) ^ (k + 1) *
          ((-1 : Kˣ) ^ (k + 2) * a.prefixProduct (2 * k + 5))) =
        ((-1 : Kˣ) *
          (((-1 : Kˣ) ^ (k + 1)) * ((-1 : Kˣ) ^ (k + 2)))) *
          (a.prefixProduct (2 * k + 5) *
            a.prefixProduct (2 * k + 5)) := by ac_rfl
    _ = a.prefixProduct (2 * k + 5) *
        a.prefixProduct (2 * k + 5) := by rw [hSign, one_mul]

/-- The common terminal contradiction used in both parity branches of
Lemma 5.8(ii). -/
theorem he2022ClassicLemma58_terminalContradiction
    [HilbertSymbolLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 5))
    (hSource : 2 * k + 6 <= m + 5)
    (hLarge : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 5, by omega⟩ -
        a.order ⟨2 * k + 4, by omega⟩)
    (c : Kˣ) (hc : 0 <= ordUnit K c)
    (hcOrder : ordUnit K c = a.order ⟨2 * k + 4, by omega⟩)
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (second : Fin (2 * k + 3) → Kˣ)
    (bSecond : GoodBONG r M (2 * k + 3))
    (hSecondValues : bSecond.prefixValueUnits (2 * k + 3) le_rfl = second)
    (hSecondLast : bSecond.order ⟨2 * k + 2, by omega⟩ =
      a.order ⟨2 * k + 4, by omega⟩)
    (hPair : HeHuSpacePairProperties
      (heClassicOddC1 (K := K) k c) second)
    (hLongFirst : a.LongRepresentationConditions
      (heClassicOddC1GoodBONG (K := K) k c hc))
    (hLongSecond : a.LongRepresentationConditions bSecond)
    (hcDef : c = he2022ClassicLemma58C a k) : False := by
  let bFirst := heClassicOddC1GoodBONG (K := K) k c hc
  have hFirstLast : bFirst.order ⟨2 * k + 2, by omega⟩ =
      a.order ⟨2 * k + 4, by omega⟩ := by
    calc
      bFirst.order ⟨2 * k + 2, by omega⟩ = ordUnit K c := by
        simp only [bFirst, heClassicOddC1GoodBONG,
          heHuExactGoodBONG_order, heClassicOddC1_order]
        simp
      _ = _ := hcOrder
  have hRepFirst := a.he2022ClassicLemma58_terminalRepresentation bFirst
    hSource hLarge hFirstLast hLongFirst
  have hRepSecond := a.he2022ClassicLemma58_terminalRepresentation bSecond
    hSource hLarge hSecondLast hLongSecond
  let source := a.prefixValueUnits (2 * k + 5) (by omega)
  have hRepFirstUnits : DiagonalRepresents
      (diagonalUnitCoefficients (heClassicOddC1 (K := K) k c))
      (diagonalUnitCoefficients source) := by
    change DiagonalRepresents
      (diagonalUnitCoefficients
        (bFirst.prefixValueUnits (2 * k + 3) le_rfl))
      (diagonalUnitCoefficients source) at hRepFirst
    rw [heClassicOddC1_fullPrefixValueUnits k c hc] at hRepFirst
    exact hRepFirst
  have hRepSecondUnits : DiagonalRepresents
      (diagonalUnitCoefficients second)
      (diagonalUnitCoefficients source) := by
    change DiagonalRepresents
      (diagonalUnitCoefficients
        (bSecond.prefixValueUnits (2 * k + 3) le_rfl))
      (diagonalUnitCoefficients source) at hRepSecond
    rw [hSecondValues] at hRepSecond
    exact hRepSecond
  subst c
  have hDet := a.he2022ClassicLemma58_source_first_determinantSquare hSource
  have hExactlyOne := heHu2022Lemma313CodimensionTwo
    (heClassicOddC1 (K := K) k (he2022ClassicLemma58C a k)) second
    hPair source hDet
  rcases hExactlyOne with hFirst | hSecond
  · exact hFirst.2 hRepSecondUnits
  · exact hSecond.1 hRepFirstUnits

/-- Lemma 5.8, implication `(ii) -> (iii)`.  If `J3_O(n)` failed,
Lemma 5.3 forces the two preceding boundary orders to be zero or one; the
two printed rows would then both represent in the signed source prefix,
contradicting Lemma 3.13. -/
theorem he2022ClassicLemma58_tests_to_j3O
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 5))
    (hSource : 2 * k + 6 <= m + 5)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * k + 2) (by omega))
    (hJ2O : a.HeClassicJ2O (2 * k + 3) (by omega) (by omega))
    (hTests : a.HeClassicLemma58PublishedTests k hSource) :
    a.HeClassicJ3O (2 * k + 3) (by omega) (by omega) := by
  unfold HeClassicJ3O
  by_contra hNotBound
  have hNotBound' : ¬ (a.order ⟨2 * k + 5, by omega⟩ -
      a.order ⟨2 * k + 4, by omega⟩ <=
        2 * (ramificationIndex K : Int)) := by
    simpa only [show 2 * k + 3 + 2 = 2 * k + 5 by omega,
      show 2 * k + 3 + 1 = 2 * k + 4 by omega] using hNotBound
  have hLarge : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 5, by omega⟩ -
        a.order ⟨2 * k + 4, by omega⟩ := by
    omega
  have hRAt : a.order ⟨2 * k + 2, by omega⟩ = 0 :=
    hJ1.1 ⟨2 * k + 2, by omega⟩
  have hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 := hJ2.1
  have hRn1Cases := a.heClassicBoundaryOrder_zeroOrOne_of_alphaOne
    (m := m + 3) (n := 2 * k + 3) (by omega) (by omega)
    hClassic hRAt hAlpha
  have hLemma53 := a.he2022ClassicLemma53
    (m := m + 3) (n := 2 * k + 3) (by omega)
    ⟨k + 1, by omega⟩ (by omega) hClassic hRAt hAlpha hJ2O
  have hRn1Zero : a.order ⟨2 * k + 3, by omega⟩ = 0 := by
    rcases hRn1Cases with hzero | hone
    · exact hzero
    · have hLastBound := hLemma53.2 (Or.inl hone)
      have hLastBound' : a.order ⟨2 * k + 5, by omega⟩ -
          a.order ⟨2 * k + 4, by omega⟩ <=
            2 * (ramificationIndex K : Int) - 1 := by
        simpa only [show 2 * k + 3 + 2 = 2 * k + 5 by omega,
          show 2 * k + 3 + 1 = 2 * k + 4 by omega] using hLastBound
      omega
  let nextTwo : Fin (m + 5) := ⟨2 * k + 4, by omega⟩
  have hNextTwoNonnegative : 0 <= a.order nextTwo :=
    ((a.he2022ClassicProposition24 hClassic).oddIndexed
      nextTwo nextTwo le_rfl (by
        exact ⟨k + 2, by simp only [nextTwo]; omega⟩) (by
        exact ⟨k + 2, by simp only [nextTwo]; omega⟩)).1
  have hRn2Cases : a.order ⟨2 * k + 4, by omega⟩ = 0 ∨
      a.order ⟨2 * k + 4, by omega⟩ = 1 := by
    by_cases hgt : 1 < a.order ⟨2 * k + 4, by omega⟩
    · have hLastBound := hLemma53.2 (Or.inr hgt)
      have hLastBound' : a.order ⟨2 * k + 5, by omega⟩ -
          a.order ⟨2 * k + 4, by omega⟩ <=
            2 * (ramificationIndex K : Int) - 1 := by
        simpa only [show 2 * k + 3 + 2 = 2 * k + 5 by omega,
          show 2 * k + 3 + 1 = 2 * k + 4 by omega] using hLastBound
      omega
    · have hnonnegative : 0 <= a.order ⟨2 * k + 4, by omega⟩ := by
        simpa only [nextTwo] using hNextTwoNonnegative
      omega
  let c := he2022ClassicLemma58C a k
  have hcOrderEq : ordUnit K c =
      a.order ⟨2 * k + 4, by omega⟩ := by
    simpa only [c] using
      a.he2022ClassicLemma58C_order hSource hJ1 hRn1Zero
  have hTestPair := hTests hLarge
  rcases hRn2Cases with hRn2Zero | hRn2One
  · have hcZero : ordUnit K c = 0 := hcOrderEq.trans hRn2Zero
    let hcNonnegative : 0 <= ordUnit K c := by rw [hcZero]
    let omega : Kˣ := heClassicOmega (K := K)
    let omegaSharp : Kˣ := heClassicOmegaSharp (K := K)
    let homega : ordUnit K omega = 0 := by
      exact heClassicOmega_order (K := K)
    let homegaSharp : ordUnit K omegaSharp = 0 := by
      exact heClassicOmegaSharp_order (K := K)
    let bC1 := heClassicOddC1GoodBONG (K := K) k c hcNonnegative
    let bC2 := heClassicOddC2EvenGoodBONG (K := K) k c omega omegaSharp
      hcZero homega homegaSharp
    have hLongPair := hTestPair.1 hcZero
    have hLongC1 : a.LongRepresentationConditions bC1 := by
      simpa only [bC1, hcNonnegative] using hLongPair.1
    have hLongC2 : a.LongRepresentationConditions bC2 := by
      simpa only [bC2, omega, omegaSharp, homega, homegaSharp] using
        hLongPair.2
    have hSecondValues :
        bC2.prefixValueUnits (2 * k + 3) le_rfl =
          heClassicOddC2Even (K := K) k c omega omegaSharp := by
      exact heClassicOddC2Even_fullPrefixValueUnits k c omega omegaSharp
        hcZero homega homegaSharp
    have hSecondLast : bC2.order ⟨2 * k + 2, by omega⟩ =
        a.order ⟨2 * k + 4, by omega⟩ := by
      calc
        bC2.order ⟨2 * k + 2, by omega⟩ = 0 := by
          simp only [bC2, heClassicOddC2EvenGoodBONG,
            heHuExactGoodBONG_order]
          exact heClassicOddC2Even_order_zero k c omega omegaSharp hcZero
            homega homegaSharp _
        _ = a.order ⟨2 * k + 4, by omega⟩ := hRn2Zero.symm
    have hPair : HeHuSpacePairProperties
        (heClassicOddC1 (K := K) k c)
        (heClassicOddC2Even (K := K) k c omega omegaSharp) := by
      exact heClassicOddC_evenOrder_pairProperties k c omega omegaSharp (by
        simpa only [omega, omegaSharp] using
          (heClassicOmegaSharp_hilbert_neg (K := K)))
    exact a.he2022ClassicLemma58_terminalContradiction hSource hLarge c
      hcNonnegative hcOrderEq
      (heClassicOddC2Even (K := K) k c omega omegaSharp) bC2
      hSecondValues hSecondLast hPair hLongC1 hLongC2 rfl
  · have hcOne : ordUnit K c = 1 := hcOrderEq.trans hRn2One
    let hcNonnegative : 0 <= ordUnit K c := by rw [hcOne]; omega
    let bC1 := heClassicOddC1GoodBONG (K := K) k c hcNonnegative
    let bC2 := heClassicOddC2OddGoodBONG (K := K) k c hcNonnegative
    have hLongPair := hTestPair.2 hcOne
    have hLongC1 : a.LongRepresentationConditions bC1 := by
      simpa only [bC1, hcNonnegative] using hLongPair.1
    have hLongC2 : a.LongRepresentationConditions bC2 := by
      simpa only [bC2, hcNonnegative] using hLongPair.2
    have hSecondValues :
        bC2.prefixValueUnits (2 * k + 3) le_rfl =
          heClassicOddC2Odd (K := K) k c := by
      exact heClassicOddC2Odd_fullPrefixValueUnits k c hcNonnegative
    have hSecondLast : bC2.order ⟨2 * k + 2, by omega⟩ =
        a.order ⟨2 * k + 4, by omega⟩ := by
      calc
        bC2.order ⟨2 * k + 2, by omega⟩ = ordUnit K c := by
          simp only [bC2, heClassicOddC2OddGoodBONG,
            heHuExactGoodBONG_order, heClassicOddC2Odd_order]
          simp
        _ = a.order ⟨2 * k + 4, by omega⟩ := hcOrderEq
    have hOdd : Odd (ordUnit K c) := by
      rw [hcOne]
      exact ⟨0, by omega⟩
    have hPair : HeHuSpacePairProperties
        (heClassicOddC1 (K := K) k c)
        (heClassicOddC2Odd (K := K) k c) :=
      heClassicOddC_oddOrder_pairProperties k c hOdd
    exact a.he2022ClassicLemma58_terminalContradiction hSource hLarge c
      hcNonnegative hcOrderEq (heClassicOddC2Odd (K := K) k c) bC2
      hSecondValues hSecondLast hPair hLongC1 hLongC2 rfl

/-- Lemma 5.8, implication `(iii) -> (i)`.  The corrected form of
Corollary 3.13(iii) supplies every instance of condition (iv); its explicit
preceding-gap premise is exactly Lemma 5.3(i). -/
theorem he2022ClassicLemma58_all_of_j3O
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 5))
    (hSource : 2 * k + 6 <= m + 5)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * k + 2) (by omega))
    (hJ2O : a.HeClassicJ2O (2 * k + 3) (by omega) (by omega))
    (hJ3O : a.HeClassicJ3O (2 * k + 3) (by omega) (by omega)) :
    HeClassicAllLongRepresentationConditions.{u, v, w}
      (n := 2 * k + 2) a := by
  intro W _ _ r M b _hBClassic
  apply (a.heClassicLongConditions_iff_forall_at b).2
  intro i
  have hzero := a.he2022ClassicLemma57_initialOrders_zero hSource hJ1
  have hRAt : a.order ⟨2 * k + 2, by omega⟩ = 0 :=
    hJ1.1 ⟨2 * k + 2, by omega⟩
  have hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 := hJ2.1
  have hnext := a.heClassicBoundaryOrder_zeroOrOne_of_alphaOne
    (m := m + 3) (n := 2 * k + 3) (by omega) (by omega)
    hClassic hRAt hAlpha
  have hLemma53 := a.he2022ClassicLemma53
    (m := m + 3) (n := 2 * k + 3) (by omega)
    ⟨k + 1, by omega⟩ (by omega) hClassic hRAt hAlpha hJ2O
  have hPriorGap : a.order ⟨2 * k + 4, by omega⟩ -
      a.order ⟨2 * k + 3, by omega⟩ <=
        2 * (ramificationIndex K : Int) := by
    have h := hLemma53.1
    have h' : a.order ⟨2 * k + 4, by omega⟩ -
        a.order ⟨2 * k + 3, by omega⟩ <=
          2 * (ramificationIndex K : Int) - 1 := by
      simpa only [show 2 * k + 3 + 1 = 2 * k + 4 by omega] using h
    omega
  have hLastGap : a.order ⟨2 * k + 5, by omega⟩ -
      a.order ⟨2 * k + 4, by omega⟩ <=
        2 * (ramificationIndex K : Int) := by
    unfold HeClassicJ3O at hJ3O
    simpa only [show 2 * k + 3 + 2 = 2 * k + 5 by omega,
      show 2 * k + 3 + 1 = 2 * k + 4 by omega] using hJ3O
  exact a.he2022ClassicCorollary313iii_with_prior_gap (2 * k + 1) b
    hSource hzero hnext hPriorGap hLastGap i

/-- He (2024), Lemma 5.8, with all three printed statements retained.
The ambient `n`-universality and `J3_E(n-1)` premises are recorded
verbatim even though this local equivalence uses the displayed classic
integrality, `J1'_E`, `J2_E`, and `J2_O` hypotheses. -/
theorem he2022ClassicLemma58
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 5))
    (hSource : 2 * k + 6 <= m + 5)
    (hClassic : Lattice.IsClassicIntegral q L)
    (_hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 3))
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * k + 2) (by omega))
    (_hJ3E : a.HeClassicJ3E (2 * k + 2) (by omega))
    (hJ2O : a.HeClassicJ2O (2 * k + 3) (by omega) (by omega)) :
    (HeClassicAllLongRepresentationConditions.{u, v, u}
        (n := 2 * k + 2) a ↔
      a.HeClassicLemma58PublishedTests k hSource) ∧
      (a.HeClassicLemma58PublishedTests k hSource ↔
        a.HeClassicJ3O (2 * k + 3) (by omega) (by omega)) := by
  constructor
  · constructor
    · exact a.he2022ClassicLemma58_all_to_tests hSource
    · intro hTests
      exact a.he2022ClassicLemma58_all_of_j3O hSource hClassic hJ1 hJ2
        hJ2O (a.he2022ClassicLemma58_tests_to_j3O hSource hClassic hJ1 hJ2
          hJ2O hTests)
  · constructor
    · exact a.he2022ClassicLemma58_tests_to_j3O hSource hClassic hJ1 hJ2
        hJ2O
    · intro hOdd
      exact a.he2022ClassicLemma58_all_to_tests hSource
        (a.he2022ClassicLemma58_all_of_j3O hSource hClassic hJ1 hJ2 hJ2O
          hOdd)

end BONG.GoodBONG

end Bong
