/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.DiagonalTailCancellation
import Bong.Bong.DiagonalRepresentationDeterminant
import Bong.Bong.DiagonalDeterminantExtension

/-!
# Codimension-one diagonal cancellation

This file proves the cancellation interface from finite-dimensional linear
algebra.  The orthogonal complement of an equal-codimension embedding is a
nondegenerate line.  The determinant identity identifies its coefficient,
up to a square, with the last coefficient of the target; common-tail Witt
cancellation then gives the required representation.
-/

namespace Bong

universe u

open BONG.GoodBONG

namespace DiagonalRepresents

variable {K : Type u} [Field K] [CharZero K]

private theorem codimensionOne_cancel
    {n : Nat} (base candidate : Fin n → Kˣ)
    (extended : Fin (n + 1) → Kˣ)
    (hprefix : diagonalUnitPrefix extended = base)
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients extended))
    (hsquare : IsSquare
      (diagonalUnitDeterminant candidate *
        diagonalUnitDeterminant base)) :
    DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients base) := by
  classical
  let source : Fin n → K := diagonalUnitCoefficients candidate
  let target : Fin (n + 1) → K := diagonalUnitCoefficients extended
  have hsource : ∀ i, source i ≠ 0 := fun i => Units.ne_zero (candidate i)
  have htarget : ∀ i, target i ≠ 0 := fun i => Units.ne_zero (extended i)
  let qs := QuadraticSpace.finiteDiagonal source hsource
  let qt := QuadraticSpace.finiteDiagonal target htarget
  have hspace : qt.Represents qs := by
    exact toQuadraticSpaceRepresents hsource htarget hrep
  rcases hspace with ⟨F⟩
  let rangeEquiv : (Fin n → K) ≃ₗ[K] LinearMap.range F.toLinearMap :=
    LinearEquiv.ofBijective F.toLinearMap.rangeRestrict
      ⟨by
        intro x y hxy
        apply F.injective
        exact congrArg Subtype.val hxy,
        LinearMap.surjective_rangeRestrict _⟩
  have hRangeNondegenerate :
      (qt.bilin.restrict (LinearMap.range F.toLinearMap)).Nondegenerate := by
    have hform :
        qt.bilin.restrict (LinearMap.range F.toLinearMap) =
          LinearMap.BilinForm.congr rangeEquiv qs.bilin := by
      ext x y
      change qt.bilin (x : Fin (n + 1) → K) (y : Fin (n + 1) → K) =
        qs.bilin (rangeEquiv.symm x) (rangeEquiv.symm y)
      rw [← F.map_bilin]
      congr 2
      · exact (congrArg Subtype.val (rangeEquiv.apply_symm_apply x)).symm
      · exact (congrArg Subtype.val (rangeEquiv.apply_symm_apply y)).symm
    rw [hform]
    exact qs.nondegenerate.congr rangeEquiv
  let range := LinearMap.range F.toLinearMap
  let complement := qt.bilin.orthogonal range
  have hRangeCompl : IsCompl range complement :=
    qt.bilin.isCompl_orthogonal_of_restrict_nondegenerate
      qt.isSymm.isRefl hRangeNondegenerate
  have hComplementNondegenerate :
      (qt.bilin.restrict complement).Nondegenerate := by
    rw [qt.bilin.restrict_nondegenerate_iff_isCompl_orthogonal
      qt.isSymm.isRefl]
    have horth : qt.bilin.orthogonal complement = range := by
      exact qt.bilin.orthogonal_orthogonal qt.nondegenerate
        qt.isSymm.isRefl range
    rw [horth]
    exact hRangeCompl.symm
  have hComplementFinrank : Module.finrank K complement = 1 := by
    change Module.finrank K
        (qt.bilin.orthogonal (LinearMap.range F.toLinearMap)) = 1
    rw [qt.bilin.finrank_orthogonal qt.nondegenerate,
      LinearMap.finrank_range_of_inj F.injective]
    simp
  have hComplementPos : 0 < Module.finrank K complement := by
    rw [hComplementFinrank]
    omega
  obtain ⟨z, hz⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp hComplementPos
  have hzAnisotropic : qt.IsAnisotropic (z : Fin (n + 1) → K) := by
    change qt.quadratic (z : Fin (n + 1) → K) ≠ 0
    intro hzQuadratic
    apply hz
    apply hComplementNondegenerate.1 z
    intro y
    obtain ⟨c, rfl⟩ :=
      (finrank_eq_one_iff_of_nonzero' z hz).mp
        hComplementFinrank y
    change qt.bilin (z : Fin (n + 1) → K)
      (c • (z : Fin (n + 1) → K)) = 0
    rw [map_smul]
    change c * qt.quadratic (z : Fin (n + 1) → K) = 0
    rw [hzQuadratic, mul_zero]
  let c : Kˣ := Units.mk0 (qt.quadratic (z : Fin (n + 1) → K))
    hzAnisotropic
  let fullMap : (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K) :=
    { toFun := fun x =>
        F.toLinearMap (Fin.init x) + x (Fin.last n) • (z : Fin (n + 1) → K)
      map_add' := by
        intro x y
        change F.toLinearMap (Fin.init x + Fin.init y) +
            (x (Fin.last n) + y (Fin.last n)) •
              (z : Fin (n + 1) → K) = _
        rw [map_add, add_smul]
        abel
      map_smul' := by
        intro a x
        change F.toLinearMap (a • Fin.init x) +
            (a * x (Fin.last n)) • (z : Fin (n + 1) → K) = _
        rw [map_smul, smul_add, mul_smul]
        simp only [RingHom.id_apply] }
  have fullMap_injective : Function.Injective fullMap := by
    intro x y hxy
    have hxOrthogonal :
        qt.bilin (z : Fin (n + 1) → K) (F.toLinearMap (Fin.init x)) = 0 :=
      by
        rw [qt.isSymm.eq]
        exact z.property _ ⟨Fin.init x, rfl⟩
    have hyOrthogonal :
        qt.bilin (z : Fin (n + 1) → K) (F.toLinearMap (Fin.init y)) = 0 :=
      by
        rw [qt.isSymm.eq]
        exact z.property _ ⟨Fin.init y, rfl⟩
    change F.toLinearMap (Fin.init x) +
        x (Fin.last n) • (z : Fin (n + 1) → K) =
      F.toLinearMap (Fin.init y) +
        y (Fin.last n) • (z : Fin (n + 1) → K) at hxy
    have hpair := congrArg
      (fun w => qt.bilin (z : Fin (n + 1) → K) w) hxy
    change qt.bilin (z : Fin (n + 1) → K)
        (F.toLinearMap (Fin.init x) +
          x (Fin.last n) • (z : Fin (n + 1) → K)) =
      qt.bilin (z : Fin (n + 1) → K)
        (F.toLinearMap (Fin.init y) +
          y (Fin.last n) • (z : Fin (n + 1) → K)) at hpair
    simp only [map_add, map_smul, hxOrthogonal, hyOrthogonal, zero_add,
      smul_eq_mul] at hpair
    have hlast : x (Fin.last n) = y (Fin.last n) :=
      mul_right_cancel₀ hzAnisotropic hpair
    have himage : F.toLinearMap (Fin.init x) =
        F.toLinearMap (Fin.init y) := by
      apply add_right_cancel
      simpa only [hlast] using hxy
    have hinit : Fin.init x = Fin.init y := F.injective himage
    rw [← Fin.snoc_init_self x, ← Fin.snoc_init_self y, hinit, hlast]
  have hcompletion : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc candidate c))
      (diagonalUnitCoefficients extended) := by
    refine ⟨fullMap, fullMap_injective, ?_⟩
    intro x
    have horthogonal : qt.bilin (F.toLinearMap (Fin.init x))
        (z : Fin (n + 1) → K) = 0 := by
      exact z.property _ ⟨Fin.init x, rfl⟩
    calc
      diagonalQuadratic (diagonalUnitCoefficients extended) (fullMap x) =
          qt.quadratic (fullMap x) := by
            rw [QuadraticSpace.finiteDiagonal_quadratic_apply]
      _ = qt.quadratic (F.toLinearMap (Fin.init x)) +
          qt.quadratic (x (Fin.last n) • (z : Fin (n + 1) → K)) := by
            change qt.quadratic (F.toLinearMap (Fin.init x) +
                x (Fin.last n) • (z : Fin (n + 1) → K)) = _
            rw [qt.quadratic_add]
            simp [horthogonal]
      _ = qs.quadratic (Fin.init x) +
          x (Fin.last n) ^ 2 * qt.quadratic (z : Fin (n + 1) → K) := by
            rw [F.map_quadratic, qt.quadratic_smul]
      _ = diagonalQuadratic
          (diagonalUnitCoefficients (Fin.snoc candidate c)) x := by
            rw [QuadraticSpace.finiteDiagonal_quadratic_apply]
            unfold diagonalQuadratic diagonalUnitCoefficients
            rw [Fin.sum_univ_castSucc]
            simp only [source, Fin.snoc_castSucc, Fin.init, Fin.snoc_last, c,
              Units.val_mk0]
            simp [diagonalUnitCoefficients, mul_comm]
  obtain ⟨p, hp⟩ :=
    exists_prod_eq_mul_square_of_sameRank hcompletion
  let A := diagonalUnitDeterminant candidate
  let B := diagonalUnitDeterminant base
  let d := extended (Fin.last n)
  have hextended : Fin.snoc base d = extended := by
    rw [← hprefix]
    exact Fin.snoc_init_self extended
  have hpDeterminant :
      (diagonalUnitDeterminant (Fin.snoc candidate c) : K) =
        (diagonalUnitDeterminant extended : K) * (p : K) ^ 2 := by
    change (∏ i, (((Fin.snoc candidate c : Fin (n + 1) → Kˣ) i) : K)) =
        (∏ i, (extended i : K)) * (p : K) ^ 2 at hp
    rw [Fin.prod_univ_castSucc] at hp
    simpa [diagonalUnitDeterminant, Fin.snoc_castSucc, Fin.snoc_last]
      using hp
  rw [diagonalUnitDeterminant_snoc, ← hextended,
    diagonalUnitDeterminant_snoc] at hpDeterminant
  have hpUnits : A * c = B * d * p ^ 2 := by
    apply Units.ext
    simpa only [A, B, d, Units.val_mul, Units.val_pow_eq_pow_val]
      using hpDeterminant
  rcases hsquare with ⟨s, hs⟩
  change A * B = s * s at hs
  have hc : c = B * d * p ^ 2 / A := by
    rw [← hpUnits]
    simp
  have hcdSquare : IsSquare (c * d) := by
    refine ⟨s * d * p / A, ?_⟩
    rw [hc, pow_two]
    have hB : B = s * s / A := by
      rw [← hs]
      simp
    rw [hB]
    simp only [div_eq_mul_inv]
    ac_rfl
  rcases hcdSquare with ⟨t, ht⟩
  let u := t * d⁻¹
  have hcScale : c = d * u ^ 2 := by
    have ht' : t * t = c * d := by
      simpa only [pow_two] using ht.symm
    calc
      c = d⁻¹ * (c * d) := by
        simp [mul_comm, mul_left_comm]
      _ = d⁻¹ * (t * t) := by rw [← ht']
      _ = d * u ^ 2 := by
        simp [u, pow_two, mul_assoc, mul_comm, mul_left_comm]
  have hscaled : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc candidate d))
      (diagonalUnitCoefficients (Fin.snoc candidate c)) := by
    have h := diagonalRepresents_snoc_mul_square candidate d u
    rw [← hcScale] at h
    exact h.symm_of_sameRank
  have hsameTail : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc candidate d))
      (diagonalUnitCoefficients (Fin.snoc base d)) := by
    rw [hextended]
    exact hscaled.trans hcompletion
  apply cancel_common_last (d : K)
    (diagonalUnitCoefficients candidate)
    (diagonalUnitCoefficients base)
  · exact Units.ne_zero d
  · exact fun i => Units.ne_zero (candidate i)
  · exact fun i => Units.ne_zero (base i)
  · simpa [diagonalUnitCoefficients] using hsameTail

end DiagonalRepresents

/-- The algebraic codimension-one cancellation theorem supplies the global
default instance used by the Beli development. -/
noncomputable instance diagonalCodimensionOneCancellationLawsProved
    (K : Type u) [Field K] [CharZero K] :
    DiagonalCodimensionOneCancellationLaws K where
  cancel := DiagonalRepresents.codimensionOne_cancel

end Bong
