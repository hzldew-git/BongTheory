/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006SectionTwo
import Bong.Bong.DiagonalOrthogonalBasis

/-!
# Good BONGs with prescribed diagonal values

This file packages the reusable construction behind several coefficient
arguments in Beli's papers.  An equal-rank diagonal representation places a
prescribed nonzero coefficient family in the ambient quadratic space.  The
weak two-step inequalities and adjacent binary admissibility conditions are
then exactly Beli (2006), Definition 2.2, so Lemma 4.3 realizes the family as
a good BONG of an actual lattice.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M : Lattice K V} {n : Nat}

/-- A good BONG in `q` whose complete unit-valued coefficient sequence is
the prescribed family `c`. -/
structure PrescribedValuesGoodBONGData
    (q : QuadraticSpace K V) (n : Nat) (c : Fin n → Kˣ) where
  lattice : Lattice K V
  bong : GoodBONG q lattice n
  values : ∀ i, bong.valueUnit i = c i

/-- Numerical realization of a prescribed diagonal coefficient family as a
good BONG.  No paper-specific existence interface is used: the assumptions
are precisely the generic construction theorem of Beli (2003), Lemma 4.3,
and the adjacent-binary criterion of Beli (2006), Section 2. -/
theorem exists_prescribedValuesGoodBONGData
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    (reference : GoodBONG q M n) (c : Fin n → Kˣ)
    (hrep : DiagonalRepresents
      (GoodBONG.diagonalUnitCoefficients c) reference.toBONG.value)
    (hweak : ∀ (i : Fin n) (hi : i.1 + 2 < n),
      ordUnit K (c i) ≤ ordUnit K (c ⟨i.1 + 2, hi⟩))
    (hadjacent : ∀ (i : Fin n) (hi : i.1 + 1 < n),
      IsBinaryParameterAdmissible (c ⟨i.1 + 1, hi⟩ / c i)) :
    Nonempty (PrescribedValuesGoodBONGData q n c) := by
  rcases DiagonalRepresents.exists_orthogonalBasisData
      reference c hrep with ⟨X, hvalues⟩
  have hcriteria : X.SatisfiesGoodBONGCriteria := by
    refine ⟨?_, ?_⟩
    · intro i hi
      unfold OrthogonalBasisData.order
      rw [hvalues i, hvalues ⟨i.1 + 2, hi⟩]
      exact hweak i hi
    · intro i hi
      unfold OrthogonalBasisData.adjacentParameter
      rw [hvalues i, hvalues ⟨i.1 + 1, hi⟩]
      exact hadjacent i hi
  rcases (X.hasGoodRealization_iff_beli2006Criteria).2 hcriteria with
    ⟨L, b, hrealized, hgood⟩
  let good : GoodBONG q L n := ⟨b, hgood⟩
  refine ⟨{
    lattice := L
    bong := good
    values := ?_
  }⟩
  intro i
  apply Units.ext
  change b.value i = (c i : K)
  calc
    b.value i = X.value i := (X.value_eq_of_isRealizedBy hrealized i).symm
    _ = (X.valueUnit i : K) := (X.coe_valueUnit i).symm
    _ = (c i : K) := congrArg Units.val (hvalues i)

end BONG

end Bong
