/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIRepresentations

/-!
# Beli (2019), Lemma 9.12: type-I index-p reduction

This file converts the v2 form of the complete type-I claim back to the
original four-condition package and constructs the literal index-p reduction
consumed by the well-founded Section 9 descent.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG.Beli2019Lemma910Data

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {M : Lattice K V} {P : Lattice K W} {Q : Lattice K U}
  {N : Nat}

/-- Original condition (iii) and the v2 condition (iii') give the same
type-I claim, so the original four-condition package has the same scalar
characterization. -/
theorem representationConditions_iff_typeIScalarConditions
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (hsource : RepresentationConditions (a.castLength hlength) c le_rfl)
    (hfirst : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (N + 3)) =
      c.order (⟨0, by omega⟩ : Fin (N + 3)))
    (horderTarget :
      (E.bong.castLength hlength).RepresentationOrderCondition c le_rfl)
    (hN : 0 < N) :
    RepresentationConditions (E.bong.castLength hlength) c le_rfl ↔
      E.TypeIScalarConditions a c D hlength := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  let target := E.bong.castLength hlength
  have hprime := E.representationConditionsPrime_iff_typeIScalarConditions
    (sourceLaws := sourceLaws) (targetLaws := targetLaws)
    a c D horders hlength hdefectSourceTarget hsource hfirst
      horderTarget hN
  constructor
  · intro conditions
    have htriggers := target.beli2019Lemma216
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      c le_rfl conditions.orderCondition conditions.defectCondition
    apply hprime.mp
    exact (representationConditions_iff_prime
      target c le_rfl htriggers).mp conditions
  · intro hscalar
    have conditionsPrime := hprime.mpr hscalar
    have htriggers := target.beli2019Lemma216
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      c le_rfl conditionsPrime.orderCondition
        conditionsPrime.defectCondition
    exact (representationConditions_iff_prime
      target c le_rfl htriggers).mpr conditionsPrime

/-- The forward construction extracted from the scalar characterization.
Keeping this as a named theorem lets low-rank specializations reuse the
already checked conversion without transporting an entire dependent
representation problem. -/
theorem representationConditions_of_typeIScalarConditions
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (hsource : RepresentationConditions (a.castLength hlength) c le_rfl)
    (hfirst : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (N + 3)) =
      c.order (⟨0, by omega⟩ : Fin (N + 3)))
    (horderTarget :
      (E.bong.castLength hlength).RepresentationOrderCondition c le_rfl)
    (hN : 0 < N)
    (hscalar : E.TypeIScalarConditions a c D hlength) :
    RepresentationConditions (E.bong.castLength hlength) c le_rfl :=
  (E.representationConditions_iff_typeIScalarConditions
    (sourceLaws := sourceLaws) (targetLaws := targetLaws)
    a c D horders hlength hdefectSourceTarget hsource hfirst
      horderTarget hN).mpr hscalar

/-- The type-I claim produces the literal `IndexPReduction` consumed by the
well-founded Section 9 descent. -/
noncomputable def indexPReduction_of_typeIScalarConditions
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (hsource : RepresentationConditions (a.castLength hlength) c le_rfl)
    (hfirst : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (N + 3)) =
      c.order (⟨0, by omega⟩ : Fin (N + 3)))
    (horderTarget :
      (E.bong.castLength hlength).RepresentationOrderCondition c le_rfl)
    (hN : 0 < N)
    (ambient : q.Represents s)
    (hscalar : E.TypeIScalarConditions a c D hlength) :
    let problem := Beli2019RepresentationProblem.ofData
      (a.castLength hlength) c le_rfl ambient hsource
    Beli2019RepresentationProblem.IndexPReduction problem := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  have htarget : RepresentationConditions target c le_rfl :=
    E.representationConditions_of_typeIScalarConditions
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      a c D horders hlength hdefectSourceTarget hsource hfirst
        horderTarget hN hscalar
  let problem := Beli2019RepresentationProblem.ofData
    source c le_rfl ambient hsource
  change Beli2019RepresentationProblem.IndexPReduction problem
  exact {
    index_eq := rfl
    lattice := E.lattice
    inclusion := E.inclusion
    targetBONG := target
    conditions := htarget }

end BONG.GoodBONG.Beli2019Lemma910Data

end Bong
