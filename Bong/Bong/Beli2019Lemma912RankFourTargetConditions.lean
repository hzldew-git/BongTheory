/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIReduction

/-!
# Beli (2019), Lemma 9.12: quaternary target conditions

This file fixes the positive tail length to one before applying the general
type-I scalar characterization.  The specialization is kept opaque so later
quaternary assembly does not repeatedly normalize dependent length casts.
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

/-- Positive-tail specialization of the type-I scalar characterization at
quaternary rank. -/
theorem rankFourRepresentationConditions_of_typeIScalarConditions
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q L (3 + 1)) (c : GoodBONG s M (1 + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data (N := 1) a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd 1 i) = ![R₁, R₂, R₁] i)
    (hdefect :
      (a.castLength (show 3 + 1 = 1 + 3 from rfl)).RepresentationDefectCondition
        (E.bong.castLength (show 3 + 1 = 1 + 3 from rfl)))
    (hsource : RepresentationConditions
      (a.castLength (show 3 + 1 = 1 + 3 from rfl)) c le_rfl)
    (hfirst : (a.castLength (show 3 + 1 = 1 + 3 from rfl)).order
        (⟨0, by omega⟩ : Fin (1 + 3)) =
      c.order (⟨0, by omega⟩ : Fin (1 + 3)))
    (horder : (E.bong.castLength
      (show 3 + 1 = 1 + 3 from rfl)).RepresentationOrderCondition c le_rfl)
    (hscalar : E.TypeIScalarConditions a c D
      (show 3 + 1 = 1 + 3 from rfl)) :
    RepresentationConditions
      (E.bong.castLength (show 3 + 1 = 1 + 3 from rfl)) c le_rfl :=
  E.representationConditions_of_typeIScalarConditions
    (sourceLaws := sourceLaws) (targetLaws := targetLaws)
    a c D horders (show 3 + 1 = 1 + 3 from rfl)
      hdefect hsource hfirst horder (by omega) hscalar

end BONG.GoodBONG.Beli2019Lemma910Data

end Bong
