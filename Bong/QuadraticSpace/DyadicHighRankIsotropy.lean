/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Reflexivity
import Bong.Bong.DiagonalQuaternaryUniversalityProof
import Bong.QuadraticSpace.Diagonalization

/-!
# High-rank isotropy over a dyadic local field

Every nondegenerate quadratic space of dimension at least five over the
dyadic local fields used in this project is isotropic.  We diagonalize the
space, use quaternary universality to make the first four coordinates
represent the negative of the fifth coefficient, and then transport the
resulting isotropic coordinate vector back to the original space.

This is the quadratic-space input used in O'Meara 93:18(v).  It is proved
without an additional local-law parameter.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The first five diagonal coordinates of a nondegenerate form of rank at
least five contain a nonzero isotropic vector. -/
theorem diagonalUnits_take_five_isotropic
    [FiniteDimensional K V] (q : QuadraticSpace K V)
    (hrank : 5 ≤ finrank K V) :
    DiagonalIsotropic
      (diagonalUnitCoefficients
        (diagonalUnitTake q.diagonalUnits 5 hrank)) := by
  let firstFour : Fin 4 → Kˣ :=
    diagonalUnitTake q.diagonalUnits 4 (by omega)
  let fifth : Kˣ := q.diagonalUnits ⟨4, by omega⟩
  obtain ⟨x, hx⟩ :=
    diagonalUnitQuaternary_exists_value firstFour (-fifth)
  let z : Fin 5 → K := Fin.lastCases 1 x
  refine ⟨z, ?_, ?_⟩
  · intro hz
    have hzlast : z (Fin.last 4) = 1 := by
      change (@Fin.lastCases 4 (fun _ => K) (1 : K)
        (fun i => x i) (Fin.last 4)) = 1
      exact Fin.lastCases_last
    exact (one_ne_zero : (1 : K) ≠ 0) (calc
      (1 : K) = z (Fin.last 4) := hzlast.symm
      _ = 0 := by simpa using congrFun hz (Fin.last 4))
  · unfold diagonalQuadratic
    rw [Fin.sum_univ_castSucc]
    have hprefix :
        (fun i : Fin 4 =>
          diagonalUnitCoefficients
              (diagonalUnitTake q.diagonalUnits 5 hrank) i.castSucc *
            z i.castSucc ^ 2) =
          (fun i : Fin 4 =>
            diagonalUnitCoefficients firstFour i * x i ^ 2) := by
      funext i
      simp [firstFour, z, diagonalUnitTake,
        diagonalUnitCoefficients]
    rw [show
      (∑ i : Fin 4,
          diagonalUnitCoefficients
              (diagonalUnitTake q.diagonalUnits 5 hrank) i.castSucc *
            z i.castSucc ^ 2) =
        ∑ i : Fin 4,
          diagonalUnitCoefficients firstFour i * x i ^ 2 by
      rw [hprefix]]
    change diagonalQuadratic (diagonalUnitCoefficients firstFour) x +
      (fifth : K) * 1 ^ 2 = 0
    rw [hx]
    simp

/-- Every finite-dimensional nondegenerate quadratic space of dimension at
least five over the dyadic local field contains a nonzero isotropic vector. -/
theorem exists_ne_zero_quadratic_eq_zero_of_five_le_finrank
    [FiniteDimensional K V] (q : QuadraticSpace K V)
    (hrank : 5 ≤ finrank K V) :
    ∃ z : V, z ≠ 0 ∧ q.quadratic z = 0 := by
  let coefficients : Fin (finrank K V) → K :=
    diagonalUnitCoefficients q.diagonalUnits
  have hprefix : DiagonalIsotropic
      (fun i : Fin 5 => coefficients (Fin.castLE hrank i)) := by
    change DiagonalIsotropic
      (diagonalUnitCoefficients
        (diagonalUnitTake q.diagonalUnits 5 hrank))
    exact q.diagonalUnits_take_five_isotropic hrank
  have hfull : DiagonalIsotropic coefficients :=
    (DiagonalRepresents.prefixOfLE coefficients hrank).isotropic_of hprefix
  rcases hfull with ⟨x, hx, hqx⟩
  let z : V := q.orthogonalFinBasis.equivFun.symm x
  refine ⟨z, ?_, ?_⟩
  · intro hz
    apply hx
    apply q.orthogonalFinBasis.equivFun.symm.injective
    simpa [z] using hz
  · have hcoordinate := q.diagonalModel_quadratic_equivFun z
    have hzcoordinate : q.orthogonalFinBasis.equivFun z = x := by
      change q.orthogonalFinBasis.equivFun
        (q.orthogonalFinBasis.equivFun.symm x) = x
      exact q.orthogonalFinBasis.equivFun.apply_symm_apply x
    rw [hzcoordinate] at hcoordinate
    rw [← hcoordinate, diagonalModel,
      finiteDiagonal_quadratic_apply]
    exact hqx

/-- Predicate form of high-rank isotropy. -/
theorem isotropic_of_five_le_finrank
    [FiniteDimensional K V] (q : QuadraticSpace K V)
    (hrank : 5 ≤ finrank K V) :
    ∃ z : V, z ≠ 0 ∧ q.quadratic z = 0 :=
  q.exists_ne_zero_quadratic_eq_zero_of_five_le_finrank hrank

end QuadraticSpace

end Bong
