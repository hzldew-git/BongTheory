/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma717Boundary
import Bong.Bong.Beli2019Lemma718TowerReplacement

/-!
# Beli (2019), Lemma 7.18(i): realization of the type-I normal form

The arithmetic normal-form predicate from `Beli2019Lemma718NormalForms`
records the desired coefficients.  This file proves its geometric existence:
the recursively replaced canonical tower is a literal sublattice of the
source lattice and carries exactly the type-I coefficient family.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The complete constructive output of Lemma 7.18(i). -/
structure Lemma718TypeIRealization
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat) where
  /-- The replacement lattice in the original ambient quadratic space. -/
  target : Lattice K V
  /-- The replacement is a literal sublattice of the source. -/
  lattice_le : target ≤ L
  /-- The good BONG on the replacement lattice. -/
  bong : GoodBONG q target (n + 3)
  /-- The source and target satisfy the exact type-I normal form. -/
  normalForm : Lemma718TypeINormalForm a bong R s

/-- The stopping data and endpoint-above alternative supply the two boundary
orders required by the recursive canonical-tower replacement. -/
def lemma718CanonicalPrefixData_of_typeI
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (stopping : Lemma717StoppingData a R s)
    (typeI : Lemma717IsTypeI a R s)
    (sourcePair : ∀ (j : Nat) (hj : 2 * j + 1 < s),
      a.valueUnit ⟨2 * j, by
        have hs := stopping.le_rank
        omega⟩ =
          lemma718CanonicalHigh (K := K) R ∧
        a.valueUnit ⟨2 * j + 1, by
          have hs := stopping.le_rank
          omega⟩ =
          lemma718CanonicalLow (K := K) R) :
    Lemma718CanonicalPrefixData a R s where
  even := stopping.even
  two_le := stopping.two_le
  le_rank := stopping.le_rank
  sourcePair := sourcePair
  suffixHead hs :=
    lemma717_suffixHead_ge a R s typeI.1 hs
  suffixSecond hs :=
    lemma717_suffixSecond_ge a R s stopping hs

/-- Construct the type-I replacement lattice and its exact normal form. -/
theorem exists_lemma718TypeIRealization
    [BeliCorollary44Laws.{u, v} K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (stopping : Lemma717StoppingData a R s)
    (typeI : Lemma717IsTypeI a R s)
    (sourcePair : ∀ (j : Nat) (hj : 2 * j + 1 < s),
      a.valueUnit ⟨2 * j, by
        have hs := stopping.le_rank
        omega⟩ =
          lemma718CanonicalHigh (K := K) R ∧
        a.valueUnit ⟨2 * j + 1, by
          have hs := stopping.le_rank
          omega⟩ =
          lemma718CanonicalLow (K := K) R) :
    Nonempty (Lemma718TypeIRealization a R s) := by
  let D := lemma718CanonicalPrefixData_of_typeI
    a R s stopping typeI sourcePair
  rcases a.exists_lemma718CanonicalPrefixReplacement R s D with ⟨E⟩
  exact ⟨{
    target := E.target
    lattice_le := E.lattice_le
    bong := E.bong
    normalForm := {
      stopping := stopping
      typeI := typeI
      sourcePair := sourcePair
      targetValues := by
        intro i
        simpa only [lemma718TypeITargetValues] using E.valueUnit i } }⟩

end BONG.GoodBONG

end Bong
