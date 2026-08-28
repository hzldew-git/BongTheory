/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.BasisUnits
import Bong.Lattice.Determinant
import Mathlib.LinearAlgebra.Determinant

/-!
# Lattice volume in an arbitrary integral ambient basis

The chosen standard integral basis in the definition of lattice determinant
may be replaced by any field basis whose valuation-ring span is the lattice.
The transition determinant is a valuation unit, so the Gram determinant has
the same valuation and refined determinant class.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- A lattice is the basis lattice of its chosen standard ambient basis. -/
theorem basisLattice_standardAmbientBasis (L : Lattice K V) :
    basisLattice L.standardAmbientBasis = L := by
  apply Lattice.ext
  exact L.toSubmodule_eq_span_standardAmbientBasis.symm

/-- The tautological equivalence between the integral span of a basis and the
underlying submodule of its basis lattice. -/
noncomputable def basisSpanEquivBasisLattice
    (b : Basis (Fin (finrank K V)) K V) :
    Submodule.span (IntegerRing K) (Set.range b) ≃ₗ[IntegerRing K]
      (basisLattice b).toSubmodule :=
  LinearEquiv.ofEq _ _ (by rfl)

@[simp]
theorem coe_basisSpanEquivBasisLattice
    (b : Basis (Fin (finrank K V)) K V)
    (x : Submodule.span (IntegerRing K) (Set.range b)) :
    ((basisSpanEquivBasisLattice b x :
      (basisLattice b).toSubmodule) : V) = (x : V) :=
  rfl

/-- The integral transition matrix from an integral ambient basis to the
chosen standard integral basis of its basis lattice. -/
noncomputable def basisLatticeIntegralChangeMatrix
    (b : Basis (Fin (finrank K V)) K V) :
    Matrix (Fin (finrank K V)) (Fin (finrank K V)) (IntegerRing K) :=
  LinearMap.toMatrix (b.restrictScalars (IntegerRing K))
    (basisLattice b).standardIntegralBasis
      (basisSpanEquivBasisLattice b).toLinearMap

/-- Extending the integral transition matrix to the field gives the ambient
change-of-basis matrix. -/
theorem basisLatticeIntegralChangeMatrix_map
    (b : Basis (Fin (finrank K V)) K V) :
    (algebraMap (IntegerRing K) K).mapMatrix
        (basisLatticeIntegralChangeMatrix b) =
      (basisLattice b).standardAmbientBasis.toMatrix b := by
  ext i j
  simp [basisLatticeIntegralChangeMatrix, LinearMap.toMatrix_apply,
    Module.Basis.toMatrix_apply,
    algebraMap_standardIntegralBasis_repr,
    coe_basisSpanEquivBasisLattice]

/-- The integral change-of-basis determinant is a unit of the valuation
ring. -/
theorem isUnit_det_basisLatticeIntegralChangeMatrix
    (b : Basis (Fin (finrank K V)) K V) :
    IsUnit (basisLatticeIntegralChangeMatrix b).det := by
  exact (basisSpanEquivBasisLattice b).isUnit_det
      (b.restrictScalars (IntegerRing K))
        (basisLattice b).standardIntegralBasis

/-- The field image of the integral change-of-basis determinant has valuation
zero. -/
theorem isValuationUnit_det_basisLatticeIntegralChangeMatrix
    (b : Basis (Fin (finrank K V)) K V) :
    IsValuationUnit K
      (((basisLatticeIntegralChangeMatrix b).det : IntegerRing K) : K) := by
  rcases isUnit_det_basisLatticeIntegralChangeMatrix b with ⟨u, hu⟩
  have hunit := isValuationUnit_coe_integerRingUnit u
  have hu' : ((u : IntegerRing K) : K) =
      (((basisLatticeIntegralChangeMatrix b).det : IntegerRing K) : K) := by
    exact congrArg (fun z : IntegerRing K => (z : K)) hu
  rw [← hu']
  exact hunit

/-- The Gram matrix of a quadratic form in an arbitrary ambient basis. -/
noncomputable def basisGramMatrix (q : QuadraticSpace K V)
    (b : Basis (Fin (finrank K V)) K V) :
    Matrix (Fin (finrank K V)) (Fin (finrank K V)) K :=
  LinearMap.BilinForm.toMatrix b q.bilin

/-- The Gram determinant in an arbitrary ambient basis. -/
noncomputable def basisGramDeterminant (q : QuadraticSpace K V)
    (b : Basis (Fin (finrank K V)) K V) : K :=
  (basisGramMatrix q b).det

/-- Nondegeneracy makes every basis Gram determinant nonzero. -/
theorem basisGramDeterminant_ne_zero (q : QuadraticSpace K V)
    (b : Basis (Fin (finrank K V)) K V) :
    basisGramDeterminant q b ≠ 0 :=
  (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
    q.nondegenerate

/-- The nonzero Gram determinant in an arbitrary integral ambient basis. -/
noncomputable def basisGramUnit (q : QuadraticSpace K V)
    (b : Basis (Fin (finrank K V)) K V) : Kˣ :=
  Units.mk0 (basisGramDeterminant q b)
    (basisGramDeterminant_ne_zero q b)

@[simp]
theorem coe_basisGramUnit (q : QuadraticSpace K V)
    (b : Basis (Fin (finrank K V)) K V) :
    (basisGramUnit q b : K) = basisGramDeterminant q b :=
  rfl

/-- The Gram determinant in an integral ambient basis differs from the chosen
lattice determinant by the square of a valuation-unit determinant. -/
theorem basisGramDeterminant_eq_determinant_mul_sq
    (q : QuadraticSpace K V)
    (b : Basis (Fin (finrank K V)) K V) :
    basisGramDeterminant q b =
      determinant q (basisLattice b) *
        Matrix.det
          ((basisLattice b).standardAmbientBasis.toMatrix b) ^ 2 := by
  let P := (basisLattice b).standardAmbientBasis.toMatrix b
  have hmatrix :
      P.transpose * integralGramMatrix q (basisLattice b) * P =
        basisGramMatrix q b := by
    exact LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
      (basisLattice b).standardAmbientBasis b q.bilin
  change (basisGramMatrix q b).det =
    (integralGramMatrix q (basisLattice b)).det * P.det ^ 2
  rw [← hmatrix]
  simp only [Matrix.det_mul, Matrix.det_transpose]
  ring

/-- The ambient transition determinant from the standard basis to an
integral ambient basis has valuation zero. -/
theorem isValuationUnit_det_standardAmbientBasis_toMatrix
    (b : Basis (Fin (finrank K V)) K V) :
    IsValuationUnit K
      (Matrix.det ((basisLattice b).standardAmbientBasis.toMatrix b)) := by
  let A := basisLatticeIntegralChangeMatrix b
  let P := (basisLattice b).standardAmbientBasis.toMatrix b
  have hmap : (algebraMap (IntegerRing K) K).mapMatrix A = P :=
    basisLatticeIntegralChangeMatrix_map b
  have hdet : ((A.det : IntegerRing K) : K) = P.det := by
    change algebraMap (IntegerRing K) K A.det = P.det
    rw [RingHom.map_det, hmap]
  rw [← hdet]
  exact isValuationUnit_det_basisLatticeIntegralChangeMatrix b

/-- The refined square class of an integral-basis Gram determinant is the
lattice determinant class. -/
theorem unitSquareClass_basisGramUnit_eq_determinantClass
    (q : QuadraticSpace K V)
    (b : Basis (Fin (finrank K V)) K V) :
    unitSquareClass K (basisGramUnit q b) =
      determinantClass q (basisLattice b) := by
  let p := Matrix.det
    ((basisLattice b).standardAmbientBasis.toMatrix b)
  have hpUnit : IsValuationUnit K p := by
    simpa [p] using
      isValuationUnit_det_standardAmbientBasis_toMatrix b
  have hpne : p ≠ 0 := by
    intro hp
    rw [hp, IsValuationUnit, ord_zero] at hpUnit
    exact WithTop.top_ne_zero hpUnit
  let pu : Kˣ := Units.mk0 p hpne
  have hunit : basisGramUnit q b =
      determinantUnit q (basisLattice b) * pu ^ 2 := by
    apply Units.ext
    change basisGramDeterminant q b =
      determinant q (basisLattice b) * p ^ 2
    exact basisGramDeterminant_eq_determinant_mul_sq q b
  rw [hunit, determinantClass]
  exact unitSquareClass_mul_unit_square K
    (determinantUnit q (basisLattice b)) pu hpUnit

/-- The lattice volume order is the valuation of the Gram determinant in any
integral ambient basis. -/
theorem coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant
    (q : QuadraticSpace K V)
    (b : Basis (Fin (finrank K V)) K V) :
    (volumeOrder q (basisLattice b) : WithTop Int) =
      ord K (basisGramDeterminant q b) := by
  rw [coe_volumeOrder,
    basisGramDeterminant_eq_determinant_mul_sq,
    ord_mul, ord_pow,
    isValuationUnit_det_standardAmbientBasis_toMatrix b]
  simp

/-- Scaling every vector of a basis scales its Gram matrix by the square of
the scalar. -/
theorem basisGramMatrix_smul (q : QuadraticSpace K V) (a : Kˣ)
    (b : Basis (Fin (finrank K V)) K V) :
    basisGramMatrix q (a • b) = (a : K) ^ 2 • basisGramMatrix q b := by
  ext i j
  simp only [basisGramMatrix,
    LinearMap.BilinForm.toMatrix_apply, Basis.smul_apply,
    Units.smul_def, Matrix.smul_apply, smul_eq_mul,
    LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  ring

/-- Scaling a basis by `a` multiplies its Gram determinant by
`a ^ (2 * finrank)`. -/
theorem basisGramDeterminant_smul (q : QuadraticSpace K V) (a : Kˣ)
    (b : Basis (Fin (finrank K V)) K V) :
    basisGramDeterminant q (a • b) =
      (a : K) ^ (2 * finrank K V) * basisGramDeterminant q b := by
  rw [basisGramDeterminant, basisGramMatrix_smul,
    Matrix.det_smul, Fintype.card_fin]
  rw [← pow_mul]
  rfl

/-- Gram determinants transform by the square of the basis-transition
determinant. -/
theorem basisGramDeterminant_changeBasis (q : QuadraticSpace K V)
    (b c : Basis (Fin (finrank K V)) K V) :
    basisGramDeterminant q c = basisGramDeterminant q b *
      Matrix.det (b.toMatrix c) ^ 2 := by
  have hmatrix :=
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b c q.bilin
  rw [basisGramDeterminant, basisGramDeterminant,
    basisGramMatrix, basisGramMatrix]
  rw [← hmatrix]
  simp only [Matrix.det_mul, Matrix.det_transpose]
  ring

/-- Independently multiplying the vectors of a finite basis changes the
lattice volume order by twice the sum of the multiplier orders. -/
theorem volumeOrder_basisLattice_unitsSMul
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (q : QuadraticSpace K V) (b : Basis ι K V) (a : ι → Kˣ) :
    volumeOrder q (basisLattice (b.unitsSMul a)) =
      volumeOrder q (basisLattice b) +
        2 * ∑ i, ordUnit K (a i) := by
  let e : ι ≃ Fin (finrank K V) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  let bFin : Basis (Fin (finrank K V)) K V := b.reindex e
  let cFin : Basis (Fin (finrank K V)) K V :=
    (b.unitsSMul a).reindex e
  have hb : basisLattice bFin = basisLattice b :=
    basisLattice_reindex b e
  have hc : basisLattice cFin = basisLattice (b.unitsSMul a) :=
    basisLattice_reindex (b.unitsSMul a) e
  have hdet := basisGramDeterminant_changeBasis q bFin cFin
  let A : Kˣ := ∏ i, a i
  have hmatrix : Matrix.det (bFin.toMatrix cFin) = (A : K) := by
    rw [← Basis.det_apply]
    have hreindex : (b.unitsSMul a).reindex e =
        bFin.unitsSMul (a ∘ e.symm) := by
      ext j
      simp [bFin, Basis.unitsSMul_apply]
    change bFin.det ((b.unitsSMul a).reindex e) = (A : K)
    rw [hreindex, bFin.det_unitsSMul_self]
    change (∏ j : Fin (finrank K V), ((a (e.symm j) : Kˣ) : K)) =
      ((∏ i, a i : Kˣ) : K)
    calc
      (∏ j : Fin (finrank K V), ((a (e.symm j) : Kˣ) : K)) =
          ∏ i : ι, ((a i : Kˣ) : K) :=
        Equiv.prod_comp e.symm (fun i : ι ↦ ((a i : Kˣ) : K))
      _ = ((∏ i, a i : Kˣ) : K) := by simp
  have hordA : ordUnit K A = ∑ i, ordUnit K (a i) := by
    dsimp only [A]
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp [ordUnit]
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi,
          ordUnit_mul, ih]
  apply WithTop.coe_injective
  rw [← hc, ← hb]
  have hleft :=
    coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant q cFin
  have hright :=
    coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant q bFin
  rw [hleft, hdet, hmatrix, ord_mul, ord_pow, ← hright,
    ← coe_ordUnit, hordA]
  norm_cast

/-- The Gram determinants in a basis and its bilinear dual multiply to one. -/
theorem basisGramDeterminant_dualBasis_mul
    (q : QuadraticSpace K V)
    (b : Basis (Fin (finrank K V)) K V) :
    basisGramDeterminant q
        (q.bilin.dualBasis q.nondegenerate b) *
      basisGramDeterminant q b = 1 := by
  let db := q.bilin.dualBasis q.nondegenerate b
  let P := b.toMatrix db
  have hmixed : LinearMap.toMatrix₂ db b q.bilin = 1 := by
    ext i j
    rw [LinearMap.toMatrix₂_apply, Matrix.one_apply,
      LinearMap.BilinForm.apply_dualBasis_left]
    simp [eq_comm]
  have hchange :=
    LinearMap.toMatrix₂_mul_basis_toMatrix b b db b q.bilin
  have hPG : P.transpose * basisGramMatrix q b = 1 := by
    rw [hmixed] at hchange
    change P.transpose * LinearMap.toMatrix₂ b b q.bilin = 1
    simpa [P] using hchange
  have hdetPG : P.det * (basisGramMatrix q b).det = 1 := by
    have h := congrArg Matrix.det hPG
    simpa only [Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_one] using h
  rw [basisGramDeterminant_changeBasis q b db]
  change ((basisGramMatrix q b).det * P.det ^ 2) *
    (basisGramMatrix q b).det = 1
  calc
    ((basisGramMatrix q b).det * P.det ^ 2) *
        (basisGramMatrix q b).det =
      (P.det * (basisGramMatrix q b).det) ^ 2 := by ring
    _ = 1 := by rw [hdetPG]; simp

/-- Rescaling a rank-`n` lattice by `a` changes its volume order by
`2 n ord(a)`. -/
theorem volumeOrder_rescale (q : QuadraticSpace K V)
    (a : Kˣ) (L : Lattice K V) :
    volumeOrder q (rescale a L) =
      volumeOrder q L + 2 * (finrank K V : Int) * ordUnit K a := by
  let b := L.standardAmbientBasis
  have hL : (volumeOrder q L : WithTop Int) =
      ord K (basisGramDeterminant q b) := by
    rw [← basisLattice_standardAmbientBasis L]
    exact coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant q b
  have hscaled : basisLattice (a • b) = rescale a L := by
    rw [← rescale_basisLattice,
      basisLattice_standardAmbientBasis]
  have hM : (volumeOrder q (rescale a L) : WithTop Int) =
      ord K (basisGramDeterminant q (a • b)) := by
    rw [← hscaled]
    exact coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant
      q (a • b)
  apply WithTop.coe_injective
  rw [hM, basisGramDeterminant_smul, ord_mul, ord_pow,
    ← coe_ordUnit, ← hL]
  norm_cast
  rw [Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- Integral duality negates the lattice volume order. -/
theorem volumeOrder_dualLattice (q : QuadraticSpace K V)
    (L : Lattice K V) :
    volumeOrder q (dualLattice q L) = -volumeOrder q L := by
  let b := L.standardAmbientBasis
  let db := q.bilin.dualBasis q.nondegenerate b
  have hL : (volumeOrder q L : WithTop Int) =
      ord K (basisGramDeterminant q b) := by
    rw [← basisLattice_standardAmbientBasis L]
    exact coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant q b
  have hdualLattice : dualLattice q L = basisLattice db := by
    rw [← basisLattice_standardAmbientBasis L,
      dualLattice_basisLattice]
  have hD : (volumeOrder q (dualLattice q L) : WithTop Int) =
      ord K (basisGramDeterminant q db) := by
    rw [hdualLattice]
    exact coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant q db
  have hproduct := basisGramDeterminant_dualBasis_mul q b
  have hord : ord K (basisGramDeterminant q db) +
      ord K (basisGramDeterminant q b) = 0 := by
    rw [← ord_mul, hproduct]
    simp
  rw [← hD, ← hL] at hord
  have hint : volumeOrder q (dualLattice q L) +
      volumeOrder q L = 0 := by
    exact_mod_cast hord
  omega

end Lattice

end Bong
