/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Necessity
import Bong.Bong.Beli2019SectionNineCases

/-!
# Beli (2019), Sections 7--9: well-founded final step

The sufficiency proof uses two nested descents.  Section 7 either reduces the
volume gap or reaches equal norm.  At equal norm, Section 9 uses the ordinary
head case (Lemma 9.3), the exceptional bad-BONG head case (Lemma 9.6), or the
smaller-volume construction of Lemma 9.12.  Rank drops in the two solved head
cases are covered by the same well-founded relation.

Every recursive node is a concrete `Beli2019RepresentationProblem`: it carries
its source and target quadratic lattices, good BONGs, ambient representation,
rank bound, and all four conditions of Theorem 2.1.  Its counterexample
predicate and rank-volume measure are fixed definitions.  In particular, the
final-step interface can no longer choose an arbitrary problem code, fake a
measure, or store the desired root representation as a field.
-/

namespace Bong

open Dyadic

universe u v w x

/-! ## Abstract outcomes matching Sections 7 and 9 -/

/-- Section 7 either reaches the equal-norm case or produces a strictly
smaller counterexample. -/
inductive Beli2019NormReductionOutcome
    {P : Type x} (smaller : P → P → Prop)
    (counterexample equalNorm : P → Prop) (p : P) : Prop
  | equalNormCase (equalNormAt : equalNorm p)
  | smallerVolume (next : P) (nextCounterexample : counterexample next)
      (decreases : smaller next p)

/-- Section 9 has the ordinary good-head solution, the exceptional bad-BONG
solution, or Lemma 9.12's strictly smaller-volume counterexample.  In the
first two cases the projected problem has smaller rank; if the parent were a
counterexample, that projected problem would also have to be one. -/
inductive Beli2019FinalStepOutcome
    {P : Type x} (smaller : P → P → Prop)
    (counterexample : P → Prop) (p : P) : Prop
  | goodBONGHead (next : P) (nextCounterexample : counterexample next)
      (decreases : smaller next p)
  | exceptionalHead (next : P) (nextCounterexample : counterexample next)
      (decreases : smaller next p)
  | smallerVolume (next : P) (nextCounterexample : counterexample next)
      (decreases : smaller next p)

/-! ## The combined reduction datum -/

/-- The exact proof-producing interface for Sections 7--9 at one instance of
Theorem 2.1.  The unresolved fields now classify and transform concrete
representation problems.  The solved branches return literal geometric
head certificates rather than the negation of an abstract counterexample. -/
structure Beli2019FinalStepData
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (hRank : n ≤ m) (ambient : q.Represents r)
    (conditions : RepresentationConditions a b hRank) where
  sectionSeven (p : Beli2019RepresentationProblem.{u, v, w} K) :
    p.Counterexample →
    Beli2019NormReductionOutcome
      (Beli2019ProblemSmaller Beli2019RepresentationProblem.measure)
      Beli2019RepresentationProblem.Counterexample
      Beli2019RepresentationProblem.EqualNorm p
  lemma912 (p : Beli2019RepresentationProblem.{u, v, w} K) :
    p.Counterexample → p.EqualNorm →
      Beli2019SectionNineResidual p →
    ∃ next, next.Counterexample ∧
      Beli2019ProblemSmaller Beli2019RepresentationProblem.measure next p

namespace Beli2019FinalStepData

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [targetLaws : Beli2006AlphaLaws.{u, w} K]
  [sourceLaws : Beli2006AlphaLaws.{u, v} K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}
  {a : BONG.GoodBONG q L (m + 1)}
  {b : BONG.GoodBONG r M (n + 1)}
  {hRank : n ≤ m} {ambient : q.Represents r}
  {conditions : RepresentationConditions a b hRank}

/-- Lemmas 9.3, 9.6, and 9.12 assemble into the three-way Section 9
outcome used by the descent. -/
theorem sectionNine
    (D : Beli2019FinalStepData a b hRank ambient conditions)
    (p : Beli2019RepresentationProblem.{u, v, w} K)
    (hp : p.Counterexample) (hequal : p.EqualNorm) :
    Beli2019FinalStepOutcome
      (Beli2019ProblemSmaller Beli2019RepresentationProblem.measure)
      Beli2019RepresentationProblem.Counterexample p := by
  cases beli2019SectionNine_cases p with
  | lemma93 ordinary =>
    rcases ordinary with ⟨input⟩
    let reduction := input.headReduction
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    exact .goodBONGHead reduction.next
      (Beli2019RepresentationProblem.HeadReduction.nextCounterexample
        p reduction hp)
      (Beli2019RepresentationProblem.HeadReduction.smaller p reduction)
  | lemma96 exceptional =>
    rcases exceptional with ⟨input⟩
    let reduction := input.headReduction
      (targetLaws := sourceLaws) (sourceLaws := targetLaws)
    exact .exceptionalHead reduction.next
      (Beli2019RepresentationProblem.HeadReduction.nextCounterexample
        p reduction hp)
      (Beli2019RepresentationProblem.HeadReduction.smaller p reduction)
  | lemma912 remaining =>
    obtain ⟨next, hnext, hsmaller⟩ := D.lemma912 p hp hequal remaining
    exact .smallerVolume next hnext hsmaller

/-- Sections 7 and 9 together strictly descend from every counterexample. -/
theorem descend
    (D : Beli2019FinalStepData a b hRank ambient conditions)
    (p : Beli2019RepresentationProblem.{u, v, w} K)
    (hp : p.Counterexample) :
    ∃ next, next.Counterexample ∧
      Beli2019ProblemSmaller Beli2019RepresentationProblem.measure next p := by
  cases D.sectionSeven p hp with
  | smallerVolume next hnext hsmaller =>
      exact ⟨next, hnext, hsmaller⟩
  | equalNormCase hequal =>
      cases D.sectionNine (targetLaws := targetLaws)
          (sourceLaws := sourceLaws) p hp hequal with
      | goodBONGHead next hnext hsmaller =>
          exact ⟨next, hnext, hsmaller⟩
      | exceptionalHead next hnext hsmaller =>
          exact ⟨next, hnext, hsmaller⟩
      | smallerVolume next hnext hsmaller =>
          exact ⟨next, hnext, hsmaller⟩

/-- Well-founded descent rules out every coded counterexample. -/
theorem not_counterexample
    (D : Beli2019FinalStepData a b hRank ambient conditions)
    (p : Beli2019RepresentationProblem.{u, v, w} K) :
    ¬p.Counterexample := by
  apply (beli2019ProblemSmaller_wellFounded
    Beli2019RepresentationProblem.measure).induction p
  intro current ih hcurrent
  obtain ⟨next, hnext, hsmaller⟩ :=
    D.descend (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      current hcurrent
  exact ih next hsmaller hnext

/-- Sections 7--9 prove sufficiency for the root pair. -/
theorem represents
    (D : Beli2019FinalStepData a b hRank ambient conditions) :
    Lattice.Represents q r L M := by
  by_contra hnot
  let root : Beli2019RepresentationProblem.{u, v, w} K :=
    Beli2019RepresentationProblem.ofData a b hRank ambient conditions
  have hroot : root.Counterexample := by
    change ¬Lattice.Represents q r L M
    exact hnot
  exact D.not_counterexample (targetLaws := targetLaws)
    (sourceLaws := sourceLaws) root hroot

end Beli2019FinalStepData

/-! The former theorem-level final-step typeclass has been removed.  This
abstract datum remains only as a proved generic descent combinator; the public
theorem is now `beli2019_sufficiency_complete`, whose inputs are the concrete
local results used in Sections 7--9. -/

end Bong
