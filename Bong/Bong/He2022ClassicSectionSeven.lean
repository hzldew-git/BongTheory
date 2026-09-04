/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicPublishedRepresentation
import Bong.Bong.HeHu2022Theorem12

/-!
# He (2024), Section 7: the explicit classic testing family

This file fixes the exact bundled meaning of Theorem 1.3 and proves its
necessity half for the literal finite table `C_e^n`.  In particular, the
family contains actual classic integral lattices, rather than condition-only
surrogates, and deletion minimality is stated for literal table entries.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Lattice.QuadraticLatticeModel

/-- Classic `n`-universality of a bundled local quadratic lattice. -/
def IsClassicNUniversal (X : QuadraticLatticeModel (K := K))
    (n : Nat) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact Lattice.IsClassicNUniversal.{u, u, u} X.form X.lattice n

/-- A finite family tests classic rank-`n` universality.  The source is
required to be classic integral, exactly as in Theorem 1.3. -/
def IsClassicUniversalityTestingFamily {I : Type u}
    (family : I -> QuadraticLatticeModel (K := K)) (n : Nat) : Prop :=
  forall X : QuadraticLatticeModel (K := K),
    X.IsClassicIntegral -> (forall i, X.Represents (family i)) ->
      X.IsClassicNUniversal n

/-- Literal deletion minimality for a classic testing family.  Distinct
indices are retained because Theorem 1.3 counts and deletes the displayed
lattices themselves. -/
def IsLiteralMinimalClassicUniversalityTestingFamily {I : Type u}
    (family : I -> QuadraticLatticeModel (K := K)) (n : Nat) : Prop :=
  IsClassicUniversalityTestingFamily family n ∧
    forall i, exists X : QuadraticLatticeModel (K := K),
      X.IsClassicIntegral ∧ ¬ X.Represents (family i) ∧
        forall j, j ≠ i -> X.Represents (family j)

/-- Necessity in Lemma 7.4 for every even entry of the printed table. -/
theorem classicUniversal_represents_publishedEven
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hX : X.IsClassicNUniversal (2 * pairs + 2))
    (i : HeClassicPublishedEvenTestingIndex (K := K) U
      (ramificationIndex K)) :
    X.Represents
      (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs i) := by
  let T := HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs i
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  exact hX.2 T.form T.lattice
    (HeClassicPublishedEvenTestingIndex.model_rank U hU pairs i)
    (HeClassicPublishedEvenTestingIndex.model_isClassicIntegral U hU pairs i)

/-- Necessity in Lemma 7.4 for every odd entry of the printed table. -/
theorem classicUniversal_represents_publishedOdd
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K))
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hX : X.IsClassicNUniversal (2 * pairs + 3))
    (i : HeClassicPublishedOddTestingIndex I) :
    X.Represents
      (HeClassicPublishedOddTestingIndex.model
        (K := K) U hU omegaData pairs i) := by
  let T := HeClassicPublishedOddTestingIndex.model
    (K := K) U hU omegaData pairs i
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  exact hX.2 T.form T.lattice
    (HeClassicPublishedOddTestingIndex.model_rank U hU omegaData pairs i)
    (HeClassicPublishedOddTestingIndex.model_isClassicIntegral
      U hU omegaData pairs i)

/-- The necessity direction of Lemma 7.4, even rank. -/
theorem classicUniversal_implies_all_publishedEven
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hX : X.IsClassicNUniversal (2 * pairs + 2)) :
    forall i : HeClassicPublishedEvenTestingIndex (K := K) U
      (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs i) :=
  fun i => classicUniversal_represents_publishedEven U hU pairs X hX i

/-- The necessity direction of Lemma 7.4, odd rank. -/
theorem classicUniversal_implies_all_publishedOdd
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K))
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hX : X.IsClassicNUniversal (2 * pairs + 3)) :
    forall i : HeClassicPublishedOddTestingIndex I,
      X.Represents
        (HeClassicPublishedOddTestingIndex.model
          (K := K) U hU omegaData pairs i) :=
  fun i => classicUniversal_represents_publishedOdd
    U hU omegaData pairs X hX i

end Lattice.QuadraticLatticeModel

end Bong
