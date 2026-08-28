/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.DeterminantIsometry
import Bong.Lattice.ModularIsometry
import Bong.Lattice.ModularVolume
import Bong.Lattice.OrthogonalDecompositionVolume
import Bong.Lattice.ProjectionScaling

/-!
# Refined determinant rigidity for unimodular lattices

Two full unimodular lattices in the same quadratic space have Gram
determinants differing by the square of a valuation unit.  Consequently
their refined determinant classes agree.  Transporting one lattice along a
field isometry gives the corresponding statement for isometric spaces.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L N : Lattice K V} {M : Lattice K W}

/-- Two full lattices of the same volume order in one quadratic space have
the same refined determinant class.  The change-of-basis determinant has
valuation zero because the two Gram determinants have equal valuation. -/
theorem determinantClass_eq_of_volumeOrder_eq_sameSpace
    (hvolume : volumeOrder q L = volumeOrder q N) :
    determinantClass q L = determinantClass q N := by
  classical
  let b := L.standardAmbientBasis
  let c := N.standardAmbientBasis
  let P := Matrix.det (b.toMatrix c)
  have hb : basisLattice b = L := basisLattice_standardAmbientBasis L
  have hc : basisLattice c = N := basisLattice_standardAmbientBasis N
  have hdet : basisGramDeterminant q c =
      basisGramDeterminant q b * P ^ 2 := by
    exact basisGramDeterminant_changeBasis q b c
  have hPne : P ≠ 0 := by
    intro hzero
    have hcne :=
      (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero c).mp q.nondegenerate
    change basisGramDeterminant q c ≠ 0 at hcne
    apply hcne
    rw [hdet, hzero]
    simp
  let p : Kˣ := Units.mk0 P hPne
  have hbOrder : ord K (basisGramDeterminant q b) =
      (volumeOrder q L : WithTop Int) := by
    rw [← coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant, hb]
  have hcOrder : ord K (basisGramDeterminant q c) =
      (volumeOrder q N : WithTop Int) := by
    rw [← coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant, hc]
  have hpOrder : ordUnit K p = 0 := by
    have hord := congrArg (ord K) hdet
    rw [ord_mul, ord_pow, hbOrder, hcOrder, hvolume] at hord
    have hPord : ord K P = ((ordUnit K p : Int) : WithTop Int) := by
      simpa only [p, Units.val_mk0] using (coe_ordUnit K p).symm
    rw [hPord] at hord
    have hordCoe :
        ((volumeOrder q N : Int) : WithTop Int) =
          ((volumeOrder q N + (ordUnit K p + ordUnit K p) : Int) :
            WithTop Int) := by
      simpa only [two_nsmul, WithTop.coe_add] using hord
    have hordInt : volumeOrder q N =
        volumeOrder q N + (ordUnit K p + ordUnit K p) :=
      WithTop.coe_injective hordCoe
    omega
  have hpUnit : IsValuationUnit K (p : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K p).2 hpOrder
  have hunit : basisGramUnit q c = basisGramUnit q b * p ^ 2 := by
    apply Units.ext
    exact hdet
  calc
    determinantClass q L = unitSquareClass K (basisGramUnit q b) := by
      rw [unitSquareClass_basisGramUnit_eq_determinantClass, hb]
    _ = unitSquareClass K (basisGramUnit q c) := by
      rw [hunit, unitSquareClass_mul_unit_square K
        (basisGramUnit q b) p hpUnit]
    _ = determinantClass q N := by
      rw [unitSquareClass_basisGramUnit_eq_determinantClass, hc]

/-- Equal-volume lattices in field-isometric quadratic spaces have equal
refined determinant class. -/
theorem determinantClass_eq_of_volumeOrder_eq_spaceIsometry
    (hvolume : volumeOrder q L = volumeOrder r M)
    (f : QuadraticSpace.Isometry q r) :
    determinantClass q L = determinantClass r M := by
  let mapped : Lattice K W := map f.toLinearEquiv L
  let lift : Isometry q r L mapped := Isometry.toMap q f L
  have hmappedVolume : volumeOrder r mapped = volumeOrder r M := by
    exact (volumeOrder_eq_of_isometry lift).symm.trans hvolume
  exact (determinantClass_eq_of_isometry lift).trans
    (determinantClass_eq_of_volumeOrder_eq_sameSpace hmappedVolume)

/-- Integral duality inverts the refined determinant class.  This is the
determinant part of O'Meara 93:24, with the valuation-unit refinement kept
explicit. -/
theorem determinantClass_dualLattice (q : QuadraticSpace K V)
    (L : Lattice K V) :
    determinantClass q (dualLattice q L) =
      (determinantClass q L)⁻¹ := by
  classical
  let b := L.standardAmbientBasis
  let db := q.bilin.dualBasis q.nondegenerate b
  have hL : basisLattice b = L :=
    basisLattice_standardAmbientBasis L
  have hdual : basisLattice db = dualLattice q L := by
    rw [← hL, dualLattice_basisLattice]
  have hunit : basisGramUnit q db * basisGramUnit q b = 1 := by
    apply Units.ext
    exact basisGramDeterminant_dualBasis_mul q b
  have hclass :
      unitSquareClass K (basisGramUnit q db) *
          unitSquareClass K (basisGramUnit q b) = 1 := by
    rw [← unitSquareClass_mul, hunit, unitSquareClass_one]
  calc
    determinantClass q (dualLattice q L) =
        unitSquareClass K (basisGramUnit q db) := by
      rw [← hdual,
        unitSquareClass_basisGramUnit_eq_determinantClass]
    _ = (unitSquareClass K (basisGramUnit q b))⁻¹ :=
      eq_inv_of_mul_eq_one_left hclass
    _ = (determinantClass q L)⁻¹ := by
      rw [unitSquareClass_basisGramUnit_eq_determinantClass, hL]

/-- The refined determinant class of a unimodular lattice depends only on
its ambient quadratic space. -/
theorem determinantClass_eq_of_unimodular_sameSpace
    (hL : IsUnimodular q L) (hN : IsUnimodular q N) :
    determinantClass q L = determinantClass q N := by
  classical
  let b := L.standardAmbientBasis
  let c := N.standardAmbientBasis
  let P := Matrix.det (b.toMatrix c)
  have hb : basisLattice b = L := basisLattice_standardAmbientBasis L
  have hc : basisLattice c = N := basisLattice_standardAmbientBasis N
  have hdet : basisGramDeterminant q c =
      basisGramDeterminant q b * P ^ 2 := by
    exact basisGramDeterminant_changeBasis q b c
  have hPne : P ≠ 0 := by
    intro hzero
    have hcne :=
      (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero c).mp q.nondegenerate
    change basisGramDeterminant q c ≠ 0 at hcne
    apply hcne
    rw [hdet, hzero]
    simp
  let p : Kˣ := Units.mk0 P hPne
  have hbOrder : ord K (basisGramDeterminant q b) = 0 := by
    rw [← coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant,
      hb, hL.volumeOrder_eq]
    simp
  have hcOrder : ord K (basisGramDeterminant q c) = 0 := by
    rw [← coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant,
      hc, hN.volumeOrder_eq]
    simp
  have hpOrder : ordUnit K p = 0 := by
    have hord := congrArg (ord K) hdet
    rw [ord_mul, ord_pow, hbOrder, hcOrder] at hord
    have hPord : ord K P = ((ordUnit K p : Int) : WithTop Int) := by
      simpa only [p, Units.val_mk0] using (coe_ordUnit K p).symm
    rw [hPord] at hord
    have hordCoe : ((0 : Int) : WithTop Int) =
        ((ordUnit K p + ordUnit K p : Int) : WithTop Int) := by
      simpa only [zero_add, two_nsmul, WithTop.coe_add,
        WithTop.coe_zero] using hord
    have hordInt : (0 : Int) = ordUnit K p + ordUnit K p :=
      WithTop.coe_injective hordCoe
    omega
  have hpUnit : IsValuationUnit K (p : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K p).2 hpOrder
  have hunit : basisGramUnit q c = basisGramUnit q b * p ^ 2 := by
    apply Units.ext
    exact hdet
  calc
    determinantClass q L = unitSquareClass K (basisGramUnit q b) := by
      rw [unitSquareClass_basisGramUnit_eq_determinantClass, hb]
    _ = unitSquareClass K (basisGramUnit q c) := by
      rw [hunit, unitSquareClass_mul_unit_square K
        (basisGramUnit q b) p hpUnit]
    _ = determinantClass q N := by
      rw [unitSquareClass_basisGramUnit_eq_determinantClass, hc]

/-- Unimodular lattices in field-isometric quadratic spaces have equal
refined determinant class. -/
theorem determinantClass_eq_of_unimodular_spaceIsometry
    (hL : IsUnimodular q L) (hM : IsUnimodular r M)
    (f : QuadraticSpace.Isometry q r) :
    determinantClass q L = determinantClass r M := by
  let mapped : Lattice K W := map f.toLinearEquiv L
  let lift : Isometry q r L mapped := Isometry.toMap q f L
  have hmapped : IsUnimodular r mapped :=
    hL.mapLatticeIsometry lift
  exact (determinantClass_eq_of_isometry lift).trans
    (determinantClass_eq_of_unimodular_sameSpace hmapped hM)

end Lattice

end Bong
