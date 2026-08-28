/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalHasseSymbol
import Bong.Bong.Beli2019RepresentationTransitivity

/-!
# Extending a represented diagonal prefix by its determinant line

If a codimension-one diagonal prefix is represented by a nondegenerate form,
then the omitted line is determined up to a square by the determinant of the
completed form.  This file packages that paper-independent argument.
-/

namespace Bong

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K]

/-- Multiplying the final diagonal coefficient by a nonzero square does not
change the represented diagonal space. -/
theorem diagonalRepresents_snoc_mul_square {n : Nat}
    (head : Fin n → Kˣ) (d u : Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc head (d * u ^ 2)))
      (diagonalUnitCoefficients (Fin.snoc head d)) := by
  let F : (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K) :=
    { toFun := fun x ↦ Fin.snoc (Fin.init x) ((u : K) * x (Fin.last n))
      map_add' := by
        intro x y
        funext i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simp [mul_add]
        · simp only [Fin.snoc_castSucc, Pi.add_apply]
          change Fin.init (x + y) j = Fin.init x j + Fin.init y j
          rw [show Fin.init (x + y) = Fin.init x + Fin.init y by rfl]
          rfl
      map_smul' := by
        intro c x
        funext i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simp only [Fin.snoc_last, Pi.smul_apply, RingHom.id_apply,
            smul_eq_mul]
          ring
        · simp only [Fin.snoc_castSucc, Pi.smul_apply, RingHom.id_apply,
            smul_eq_mul]
          change Fin.init (c • x) j = c * Fin.init x j
          rw [show Fin.init (c • x) = c • Fin.init x by rfl]
          rfl }
  refine ⟨F, ?_, ?_⟩
  · intro x y hxy
    have hlast : x (Fin.last n) = y (Fin.last n) := by
      have h := congrFun hxy (Fin.last n)
      simp only [F, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last] at h
      exact mul_left_cancel₀ (Units.ne_zero u) h
    have hinit : Fin.init x = Fin.init y := by
      funext j
      have h := congrFun hxy j.castSucc
      simpa only [F, LinearMap.coe_mk, AddHom.coe_mk,
        Fin.snoc_castSucc] using h
    rw [← Fin.snoc_init_self x, ← Fin.snoc_init_self y, hinit, hlast]
  · intro x
    unfold diagonalQuadratic diagonalUnitCoefficients
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [F, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last,
      Fin.snoc_castSucc, Units.val_mul, Units.val_pow_eq_pow_val]
    simp only [Fin.init]
    ring

/-- Complete a represented codimension-one prefix when the proposed full
form has the same determinant square class as the target form. -/
theorem diagonalRepresents_of_prefix_of_determinant_square
    [DiagonalCodimensionOneCancellationLaws K]
    {n : Nat} (source base : Fin (n + 1) → Kˣ)
    (hprefix : DiagonalRepresents
      (diagonalUnitCoefficients (diagonalUnitPrefix source))
      (diagonalUnitCoefficients base))
    (hsquare : IsSquare
      (diagonalUnitDeterminant source * diagonalUnitDeterminant base)) :
    DiagonalRepresents (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients base) := by
  let head := diagonalUnitPrefix source
  let last := source (Fin.last n)
  let d := diagonalUnitDeterminant base * diagonalUnitDeterminant head
  have hsource : Fin.snoc head last = source := by
    exact Fin.snoc_init_self source
  have hdetSource : diagonalUnitDeterminant source =
      diagonalUnitDeterminant head * last := by
    rw [← hsource, diagonalUnitDeterminant_snoc]
  have hsquare' : IsSquare (d * last) := by
    simpa only [d, hdetSource, mul_assoc, mul_comm, mul_left_comm] using hsquare
  rcases hsquare' with ⟨s, hs⟩
  let u := s * d⁻¹
  have hlast : last = d * u ^ 2 := by
    have hs' : s * s = d * last := by
      simpa only [pow_two] using hs.symm
    calc
      last = d⁻¹ * (d * last) := by group
      _ = d⁻¹ * (s * s) := by rw [← hs']
      _ = d * u ^ 2 := by
        simp only [u, pow_two]
        calc
          d⁻¹ * (s * s) = s * s * d⁻¹ := by ac_rfl
          _ = (d * d⁻¹) * (s * s) * d⁻¹ := by simp
          _ = d * (s * d⁻¹) * (s * d⁻¹) := by ac_rfl
          _ = d * ((s * d⁻¹) * (s * d⁻¹)) := by rw [mul_assoc]
  have hscaled : DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients (Fin.snoc head d)) := by
    have h := diagonalRepresents_snoc_mul_square head d u
    rw [← hsource, hlast]
    exact h
  have hcompleted : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc head d))
      (diagonalUnitCoefficients base) := by
    simpa only [head, d] using
      determinantCompletion_represents_base_general base head hprefix
  exact hscaled.trans hcompleted

end BONG.GoodBONG

end Bong
