/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912RankFourLemma910
import Bong.Bong.Beli2019Lemma912RankFourTargetConditions
import Bong.Bong.Beli2019Necessity

/-!
# Beli (2019), Lemma 9.12: quaternary type-I reduction

This file separates the representation-condition transport for an already
constructed Lemma 9.10 BONG from its numerical construction.
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
  {L : Lattice K V} {P : Lattice K W} {M : Lattice K U}

/-- The two non-scalar representation conditions for a quaternary Lemma 9.10
output. -/
structure RankFourConstructedConditions
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q L 4) (c : GoodBONG s M 4)
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data (N := 1) a D) : Prop where
  source : RepresentationConditions
    (a.castLength (show 3 + 1 = 1 + 3 from rfl)) c le_rfl
  first : (a.castLength (show 3 + 1 = 1 + 3 from rfl)).order
      (⟨0, by omega⟩ : Fin (1 + 3)) =
    c.order (⟨0, by omega⟩ : Fin (1 + 3))
  defect : (a.castLength (show 3 + 1 = 1 + 3 from rfl)).RepresentationDefectCondition
    (E.bong.castLength (show 3 + 1 = 1 + 3 from rfl))
  order : (E.bong.castLength
    (show 3 + 1 = 1 + 3 from rfl)).RepresentationOrderCondition c le_rfl

set_option maxHeartbeats 2000000 in
-- The inclusion adapter and the order transport are normalized at rank four.
/-- Inclusion and the original order condition provide the non-scalar
conditions for the constructed BONG. -/
theorem rankFourConstructedConditions
    [Beli2019InclusionConditionsLaws.{u, v} K]
    {R₁ R₂ A₁ β₁ : Int}
    (a : GoodBONG q L 4) (c : GoodBONG s M 4)
    (data : Beli2019Lemma912TypeIBetaDataRankFour a c A₁ β₁)
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data (N := 1) a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd 1 i) = ![R₁, R₂, R₁] i)
    (hfirst : a.order (0 : Fin 4) = c.order (0 : Fin 4))
    (hsource : RepresentationConditions a c (Nat.le_refl 3)) :
    E.RankFourConstructedConditions a c D := by
  let hlength : 3 + 1 = 1 + 3 := rfl
  let target := E.bong.castLength hlength
  have haCast : a.castLength hlength = a := by
    cases hlength
    rfl
  have hcCast : c.castLength hlength = c := by
    cases hlength
    rfl
  have hsourceTargetRaw : RepresentationConditions a target le_rfl :=
    a.representationConditions_of_lattice_le_via_adapter
      target E.inclusion.lattice_le
  have hsourceTarget : RepresentationConditions
      (a.castLength hlength) target le_rfl := by
    simpa only [haCast] using hsourceTargetRaw
  have hR₁ : a.order (0 : Fin 4) = R₁ := by
    simpa using horders (0 : Fin 3)
  have hR₂ : a.order (1 : Fin 4) = R₂ := by
    simpa using horders (1 : Fin 3)
  have hcZero : (c.castLength hlength).order (0 : Fin 4) = R₁ := by
    rw [hcCast]
    exact hfirst.symm.trans hR₁
  have hcOne : R₂ + 2 ≤ (c.castLength hlength).order (1 : Fin 4) := by
    rw [hcCast]
    simpa only [hR₂] using data.sourceSecondOrder
  have hsourceOrderCast : (a.castLength hlength).RepresentationOrderCondition
      (c.castLength hlength) le_rfl := by
    simpa only [haCast, hcCast] using hsource.orderCondition
  have hsourceCast : RepresentationConditions
      (a.castLength hlength) c le_rfl := by
    simpa only [haCast] using hsource
  have hfirstCast : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (1 + 3)) =
      c.order (⟨0, by omega⟩ : Fin (1 + 3)) := by
    rw [GoodBONG.order_castLength]
    convert hfirst using 1 <;> congr 1
  have horderRaw := beli2019Lemma912_typeI_orderCondition
    a c D E horders hlength hcZero hcOne hsourceOrderCast
  have horderTarget : target.RepresentationOrderCondition c le_rfl := by
    simpa only [target, hcCast] using horderRaw
  exact {
    source := hsourceCast
    first := hfirstCast
    defect := hsourceTarget.defectCondition
    order := horderTarget }

set_option maxHeartbeats 4000000 in
-- The generic positive-tail scalar characterization is instantiated with tail one.
/-- Once the two scalar inequalities are known, the constructed quaternary
BONG is the required index-`p` reduction. -/
noncomputable def indexPReduction_of_rankFourScalar
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q L 4) (c : GoodBONG s M 4)
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data (N := 1) a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd 1 i) = ![R₁, R₂, R₁] i)
    (_hfirst : a.order (0 : Fin 4) = c.order (0 : Fin 4))
    (ambient : q.Represents s)
    (hsource : RepresentationConditions a c (Nat.le_refl 3))
    (constructed : E.RankFourConstructedConditions a c D)
    (hscalar : E.TypeIScalarConditions a c D
      (show 3 + 1 = 1 + 3 from rfl)) :
    Beli2019RepresentationProblem.IndexPReduction
      (Beli2019RepresentationProblem.ofData
        a c (Nat.le_refl 3) ambient hsource) := by
  let hlength : 3 + 1 = 1 + 3 := rfl
  let target := E.bong.castLength hlength
  have htarget : RepresentationConditions target c le_rfl :=
    E.rankFourRepresentationConditions_of_typeIScalarConditions
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      a c D horders constructed.defect constructed.source constructed.first
        constructed.order hscalar
  exact {
    index_eq := rfl
    lattice := E.lattice
    inclusion := E.inclusion
    targetBONG := target
    conditions := htarget }

end BONG.GoodBONG.Beli2019Lemma910Data

end Bong
