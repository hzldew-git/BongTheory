/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.He2022ClassicSectionEight

/-!
# Canonical number-field arithmetic data for He (2024), Section 8

This file fixes the finite-place and discriminant fields in
`HeClassic2024GlobalData` to their standard number-field meanings.  A caller
chooses only an equivalence between its place type and the height-one spectrum;
the dyadic predicate, ramification index, and odd-discriminant proposition are
then definitions rather than compatibility assumptions.
-/

namespace Bong

universe u v w u'

/-- The non-arithmetic fields of the global Section 8 model, together with an
identification of its places with the standard finite places of a number
field. -/
structure HeClassic2024NumberFieldGlobalData
    (K : Type u') [Field K] [NumberField K]
    (S : GlobalLocalLatticeSystem.{u, v, w}) where
  placeEquiv :
    S.Place ≃
      IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K)
  positiveDefinite : S.GlobalLattice → Prop
  isDiagonalIntegerLattice : S.GlobalLattice → Prop
  localAdjacentDefectsLarge : S.GlobalLattice → S.Place → Prop
  sumOfSquares : Nat → S.GlobalLattice
  notTotallyReal : Prop

namespace HeClassic2024NumberFieldGlobalData

variable {K : Type u'} [Field K] [NumberField K]
  {S : GlobalLocalLatticeSystem.{u, v, w}}

/-- The canonical global data.  Its three arithmetic fields are the actual
number-field definitions at the height-one prime selected by `placeEquiv`. -/
noncomputable def toGlobalData (D : HeClassic2024NumberFieldGlobalData K S) :
    HeClassic2024GlobalData S where
  positiveDefinite := D.positiveDefinite
  isDyadic p :=
    HeClassic2024NumberField.IsDyadicPrime K
      (D.placeEquiv p).asIdeal
  ramificationIndexAt p :=
    (D.placeEquiv p).asIdeal.ramificationIdx ℤ
  discriminantOdd := HeClassic2024NumberField.DiscriminantOdd K
  isDiagonalIntegerLattice := D.isDiagonalIntegerLattice
  localAdjacentDefectsLarge := D.localAdjacentDefectsLarge
  sumOfSquares := D.sumOfSquares
  notTotallyReal := D.notTotallyReal

/-- The standard height-one-spectrum identification has no residual
compatibility obligations: all three statements hold definitionally. -/
noncomputable def heightOneSpectrumIdentification
    (D : HeClassic2024NumberFieldGlobalData K S) :
    D.toGlobalData.HeightOneSpectrumIdentification K where
  placeEquiv := D.placeEquiv
  isDyadic_iff _ := Iff.rfl
  ramificationIndexAt_eq _ := rfl
  discriminantOdd_iff := Iff.rfl

/-- The prime-ideal bridge obtained from the canonical arithmetic data. -/
noncomputable def numberFieldDiscriminantBridge
    (D : HeClassic2024NumberFieldGlobalData K S) :
    D.toGlobalData.NumberFieldDiscriminantBridge K :=
  D.heightOneSpectrumIdentification.numberFieldDiscriminantBridge

/-- The remaining inputs for Section 8 after the standard finite-place
arithmetic has been fixed.  In particular, this structure contains no field
asserting discriminant parity, ramification positivity, or their equivalence.
-/
structure SectionEightInputs
    (D : HeClassic2024NumberFieldGlobalData K S) : Prop where
  positiveDefinite_admissible (M N : S.GlobalLattice) :
    D.toGlobalData.positiveDefinite N → S.globalAdmissible M N
  proposition82 : D.toGlobalData.Proposition82Laws
  theorem15_local (M : S.GlobalLattice) (p : S.Place) (n : Nat) :
    D.toGlobalData.isDyadic p → 1 ≤ n →
      n + 3 ≤ S.globalRank M → S.IsNUniversalAt M p n →
        D.toGlobalData.localAdjacentDefectsLarge M p →
          D.toGlobalData.ramificationIndexAt p = 1
  diagonal_localAdjacentDefectsLarge_of_universal_even
      (M : S.GlobalLattice) (p : S.Place) (n : Nat) :
    Even n → D.toGlobalData.isDiagonalIntegerLattice M →
      D.toGlobalData.isDyadic p →
        1 < D.toGlobalData.ramificationIndexAt p →
          S.globalRank M = n + 3 → S.IsNUniversalAt M p n →
            D.toGlobalData.localAdjacentDefectsLarge M p
  sumOfSquares_rank (m : Nat) :
    S.globalRank (D.toGlobalData.sumOfSquares m) = m
  sumOfSquares_localAdjacentDefectsLarge (m : Nat) (p : S.Place) :
    D.toGlobalData.isDyadic p →
      D.toGlobalData.localAdjacentDefectsLarge
        (D.toGlobalData.sumOfSquares m) p
  nonDyadic_localUniversal (m n : Nat) (p : S.Place) :
    1 ≤ n → n + 3 ≤ m → ¬ D.toGlobalData.isDyadic p →
      S.IsNUniversalAt (D.toGlobalData.sumOfSquares m) p n
  dyadic_unary_localUniversal (m : Nat) (p : S.Place) :
    4 ≤ m → D.toGlobalData.isDyadic p →
      D.toGlobalData.ramificationIndexAt p = 1 →
        S.IsNUniversalAt (D.toGlobalData.sumOfSquares m) p 1
  dyadic_higherRank_localUniversal (m n : Nat) (p : S.Place) :
    2 ≤ n → n + 3 ≤ m → D.toGlobalData.isDyadic p →
      D.toGlobalData.ramificationIndexAt p = 1 →
        S.IsNUniversalAt (D.toGlobalData.sumOfSquares m) p n
  sumOfSquaresGlobalization : D.toGlobalData.SumOfSquaresLocalGlobalLaws

/-- Construct all of `SectionEightLaws` from the genuine number-field
discriminant theorem and the remaining lattice-theoretic inputs. -/
theorem sectionEightLaws
    (D : HeClassic2024NumberFieldGlobalData K S)
    (H : D.SectionEightInputs) : D.toGlobalData.SectionEightLaws where
  positiveDefinite_admissible := H.positiveDefinite_admissible
  proposition82 := H.proposition82
  discriminantRamification :=
    D.numberFieldDiscriminantBridge.discriminantRamificationLaws
  ramificationIndexAt_pos p _ :=
    D.numberFieldDiscriminantBridge.ramificationIndexAt_pos p
  theorem15_local := H.theorem15_local
  diagonal_localAdjacentDefectsLarge_of_universal_even :=
    H.diagonal_localAdjacentDefectsLarge_of_universal_even
  sumOfSquares_rank := H.sumOfSquares_rank
  sumOfSquares_localAdjacentDefectsLarge :=
    H.sumOfSquares_localAdjacentDefectsLarge
  sumOfSquaresLocalUniversality :=
    HeClassic2024GlobalData.SumOfSquaresLocalUniversalityLaws.ofNumberFieldDiscriminantBridge
        D.numberFieldDiscriminantBridge
        H.nonDyadic_localUniversal
        H.dyadic_unary_localUniversal
        H.dyadic_higherRank_localUniversal
  sumOfSquaresGlobalization := H.sumOfSquaresGlobalization

end HeClassic2024NumberFieldGlobalData

end Bong
