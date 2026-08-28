/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716Special
import Bong.Bong.Beli2019IntermediateReduction
import Bong.Bong.Beli2019Lemma216Complete

/-!
# The Section-7 special branch as a concrete recursive reduction

The revised condition package from Lemma 7.16 is converted back to the
original statement by Lemma 2.16, then combined with the strict special
sublattice geometry to form the exact `SublatticeReduction` consumed by the
well-founded induction.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L N : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]

/-- Each branch of the scale-free Lemma 7.16 conclusion gives a literal
strict-sublattice reduction of the same-space representation problem. -/
theorem Beli2019Lemma716SpecialConclusion.sublatticeReduction
    [DyadicDiscriminantClassLaws K]
    {a : GoodBONG q L (n + 3)} {c : GoodBONG q N (n + 3)}
    {R : Int} {s : Nat} {D : Lemma714StoppingData a R s}
    {S : TwoBlockSplitWitness a.toBONG 2 (by omega)}
    {ε η : Kˣ}
    (C : Beli2019Lemma716SpecialConclusion a c R s D S ε η)
    (hac : RepresentationConditions a c le_rfl) :
    Nonempty (Beli2019RepresentationProblem.SublatticeReduction
      (Beli2019RepresentationProblem.ofData a c le_rfl
        (QuadraticSpace.represents_refl q) hac)) := by
  cases C.realization with
  | typeI hI result hvalues hprime =>
      have htrigger : result.CentralTriggerEquivalence c :=
        result.beli2019Lemma216 c le_rfl hprime.orderCondition
          hprime.defectCondition
      have hconditions : RepresentationConditions result c le_rfl :=
        (representationConditions_iff_prime result c le_rfl htrigger).mpr
          hprime
      exact ⟨{
        index_eq := rfl
        lattice := S.lemma714SpecialLattice
        lattice_le := C.geometry.lattice_le
        volumeOrder_lt := C.geometry.volumeOrder_lt
        targetBONG := result
        conditions := hconditions }⟩
  | typeII hII result hvalues hprime =>
      have htrigger : result.CentralTriggerEquivalence c :=
        result.beli2019Lemma216 c le_rfl hprime.orderCondition
          hprime.defectCondition
      have hconditions : RepresentationConditions result c le_rfl :=
        (representationConditions_iff_prime result c le_rfl htrigger).mpr
          hprime
      exact ⟨{
        index_eq := rfl
        lattice := S.lemma714SpecialLattice
        lattice_le := C.geometry.lattice_le
        volumeOrder_lt := C.geometry.volumeOrder_lt
        targetBONG := result
        conditions := hconditions }⟩

/-- A counterexample in the special equal-gap branch descends to a strictly
smaller concrete representation problem. -/
theorem Beli2019Lemma716SpecialConclusion.counterexampleDescent
    [DyadicDiscriminantClassLaws K]
    {a : GoodBONG q L (n + 3)} {c : GoodBONG q N (n + 3)}
    {R : Int} {s : Nat} {D : Lemma714StoppingData a R s}
    {S : TwoBlockSplitWitness a.toBONG 2 (by omega)}
    {ε η : Kˣ}
    (C : Beli2019Lemma716SpecialConclusion a c R s D S ε η)
    (hac : RepresentationConditions a c le_rfl)
    (hp : (Beli2019RepresentationProblem.ofData a c le_rfl
      (QuadraticSpace.represents_refl q) hac).Counterexample) :
    ∃ next, next.Counterexample ∧
      Beli2019ProblemSmaller Beli2019RepresentationProblem.measure next
        (Beli2019RepresentationProblem.ofData a c le_rfl
          (QuadraticSpace.represents_refl q) hac) :=
  by
    rcases C.sublatticeReduction hac with ⟨E⟩
    exact E.counterexampleDescent _ hp

end BONG.GoodBONG

end Bong
