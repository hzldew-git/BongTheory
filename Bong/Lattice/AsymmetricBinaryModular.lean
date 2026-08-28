/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.MinimalScaleComponent

/-!
# Binary modular components with one strict norm inequality

Beli (2019), Lemma 5.1 uses a scale-generating pair `x, y` for which
`ord B(x,y) < ord Q(x)` but only `ord B(x,y) ≤ ord Q(y)`.  One strict
inequality is enough: it makes the product of the diagonal Gram entries
strictly smaller than the square of the mixed entry in the valuative order.
This file records the corresponding asymmetric version of the binary
construction from O'Meara 91C.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

variable {q : QuadraticSpace K V} {L : Lattice K V} {x y : V}

/-- The Gram determinant is dominated by the mixed term when the left norm
has strictly larger order and the right norm has no smaller order. -/
theorem ord_binaryGramDeterminant_eq_of_left_strict
    (hxy : q.bilin x y ≠ 0)
    (hx : ord K (q.bilin x y) < ord K (q.quadratic x))
    (hy : ord K (q.bilin x y) ≤ ord K (q.quadratic y)) :
    ord K (q.quadratic x * q.quadratic y - q.bilin x y ^ 2) =
      ord K (q.bilin x y ^ 2) := by
  by_cases hqx : q.quadratic x = 0
  · rw [hqx, zero_mul, zero_sub, ord_neg]
  · by_cases hqy : q.quadratic y = 0
    · rw [hqy, mul_zero, zero_sub, ord_neg]
    · let d := Units.mk0 (q.bilin x y) hxy
      let ax := Units.mk0 (q.quadratic x) hqx
      let ay := Units.mk0 (q.quadratic y) hqy
      have hxInt : ordUnit K d < ordUnit K ax := by
        apply WithTop.coe_lt_coe.mp
        simpa [d, ax] using hx
      have hyInt : ordUnit K d ≤ ordUnit K ay := by
        apply WithTop.coe_le_coe.mp
        simpa [d, ay] using hy
      apply (ord K).map_sub_eq_of_lt_right
      rw [ord_mul, ord_pow]
      change 2 • ord K (d : K) < ord K (ax : K) + ord K (ay : K)
      rw [← coe_ordUnit K ax, ← coe_ordUnit K ay, ← coe_ordUnit K d]
      have hsum :
          ((ordUnit K d + ordUnit K d : Int) : WithTop Int) <
            ((ordUnit K ax + ordUnit K ay : Int) : WithTop Int) :=
        WithTop.coe_lt_coe.mpr (add_lt_add_of_lt_of_le hxInt hyInt)
      simpa only [two_nsmul, WithTop.coe_add] using hsum

/-- The asymmetric Gram determinant is nonzero. -/
theorem binaryGramDeterminant_ne_zero_of_left_strict
    (hxy : q.bilin x y ≠ 0)
    (hx : ord K (q.bilin x y) < ord K (q.quadratic x))
    (hy : ord K (q.bilin x y) ≤ ord K (q.quadratic y)) :
    q.quadratic x * q.quadratic y - q.bilin x y ^ 2 ≠ 0 := by
  intro hzero
  have hord := ord_binaryGramDeterminant_eq_of_left_strict hxy hx hy
  rw [hzero, ord_zero] at hord
  have hpow : q.bilin x y ^ 2 ≠ 0 := pow_ne_zero 2 hxy
  exact (ord_eq_top_iff K).not.mpr hpow hord.symm

/-- The asymmetric scale pair is linearly independent. -/
theorem binaryPair_linearIndependent_of_left_strict
    (hxy : q.bilin x y ≠ 0)
    (hx : ord K (q.bilin x y) < ord K (q.quadratic x))
    (hy : ord K (q.bilin x y) ≤ ord K (q.quadratic y)) :
    LinearIndependent K (BONG.binaryPairFamily x y) := by
  have hdet := binaryGramDeterminant_ne_zero_of_left_strict hxy hx hy
  rw [linearIndependent_fin2]
  constructor
  · intro hyzero
    change y = 0 at hyzero
    apply hxy
    rw [hyzero]
    simp
  · intro a haxy
    change a • y = x at haxy
    apply hdet
    rw [← haxy, q.quadratic_smul, LinearMap.BilinForm.smul_left]
    simp [QuadraticSpace.quadratic]
    ring

/-- The form restricted to an asymmetric scale pair is nondegenerate. -/
theorem binaryPair_restrict_nondegenerate_of_left_strict
    (hxy : q.bilin x y ≠ 0)
    (hx : ord K (q.bilin x y) < ord K (q.quadratic x))
    (hy : ord K (q.bilin x y) ≤ ord K (q.quadratic y)) :
    (q.bilin.restrict (BONG.binaryPairSpan (K := K) x y)).Nondegenerate := by
  let hli := binaryPair_linearIndependent_of_left_strict hxy hx hy
  let b := BONG.binaryPairBasis (K := K) x y hli
  apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).2
  rw [Matrix.det_fin_two]
  simp only [LinearMap.BilinForm.toMatrix_apply,
    LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
  simp only [b, BONG.coe_binaryPairBasis,
    BONG.binaryPairFamily_zero, BONG.binaryPairFamily_one]
  change q.quadratic x * q.quadratic y - q.bilin x y * q.bilin y x ≠ 0
  rw [q.isSymm.eq y x]
  simpa [pow_two] using binaryGramDeterminant_ne_zero_of_left_strict hxy hx hy

/-- The asymmetric binary basis has volume order twice the mixed order. -/
theorem volumeOrder_binaryPairBasis_eq_two_mul_ordUnit_of_left_strict
    (hxy : q.bilin x y ≠ 0)
    (hx : ord K (q.bilin x y) < ord K (q.quadratic x))
    (hy : ord K (q.bilin x y) ≤ ord K (q.quadratic y)) :
    volumeOrder
        (q.restrict (BONG.binaryPairSpan (K := K) x y)
          (binaryPair_restrict_nondegenerate_of_left_strict hxy hx hy))
        (basisLattice
          (BONG.binaryPairBasis (K := K) x y
            (binaryPair_linearIndependent_of_left_strict hxy hx hy))) =
      2 * ordUnit K (Units.mk0 (q.bilin x y) hxy) := by
  let P := BONG.binaryPairSpan (K := K) x y
  let hli := binaryPair_linearIndependent_of_left_strict hxy hx hy
  let hnondeg := binaryPair_restrict_nondegenerate_of_left_strict hxy hx hy
  let b : Basis (Fin 2) K P := BONG.binaryPairBasis (K := K) x y hli
  have hfin : finrank K P = 2 := by
    simpa using Module.finrank_eq_card_basis b
  let e : Fin 2 ≃ Fin (finrank K P) := finCongr hfin.symm
  let bfin : Basis (Fin (finrank K P)) K P := b.reindex e
  have hbfin : basisLattice bfin = basisLattice b := basisLattice_reindex b e
  have hmatrix :
      LinearMap.BilinForm.toMatrix bfin (q.bilin.restrict P) =
        Matrix.reindex e e
          (LinearMap.BilinForm.toMatrix b (q.bilin.restrict P)) := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, bfin, Basis.coe_reindex, Function.comp_apply]
  have hdet :
      basisGramDeterminant (q.restrict P hnondeg) bfin =
        q.quadratic x * q.quadratic y - q.bilin x y ^ 2 := by
    change (LinearMap.BilinForm.toMatrix bfin (q.bilin.restrict P)).det = _
    rw [hmatrix, Matrix.det_reindex_self, Matrix.det_fin_two]
    simp only [LinearMap.BilinForm.toMatrix_apply,
      LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
    change q.bilin (b 0 : V) (b 0 : V) * q.bilin (b 1 : V) (b 1 : V) -
      q.bilin (b 0 : V) (b 1 : V) * q.bilin (b 1 : V) (b 0 : V) = _
    rw [show (b 0 : V) = x by
        rw [show (b 0 : V) = BONG.binaryPairFamily x y 0 by
          exact BONG.coe_binaryPairBasis x y hli 0]
        exact BONG.binaryPairFamily_zero x y,
      show (b 1 : V) = y by
        rw [show (b 1 : V) = BONG.binaryPairFamily x y 1 by
          exact BONG.coe_binaryPairBasis x y hli 1]
        exact BONG.binaryPairFamily_one x y]
    change q.quadratic x * q.quadratic y - q.bilin x y * q.bilin y x = _
    rw [q.isSymm.eq y x, pow_two]
  apply WithTop.coe_injective
  rw [show basisLattice
      (BONG.binaryPairBasis (K := K) x y
        (binaryPair_linearIndependent_of_left_strict hxy hx hy)) =
      basisLattice bfin by exact hbfin.symm]
  rw [coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant, hdet,
    ord_binaryGramDeterminant_eq_of_left_strict hxy hx hy, ord_pow]
  have hcoe := coe_ordUnit K (Units.mk0 (q.bilin x y) hxy)
  change (((ordUnit K (Units.mk0 (q.bilin x y) hxy) : Int) :
      WithTop Int)) = ord K (q.bilin x y) at hcoe
  rw [← hcoe, two_nsmul]
  rw [show (2 * ordUnit K (Units.mk0 (q.bilin x y) hxy) : Int) =
      ordUnit K (Units.mk0 (q.bilin x y) hxy) +
        ordUnit K (Units.mk0 (q.bilin x y) hxy) by omega,
    WithTop.coe_add]

/-- The binary lattice generated by an asymmetric scale pair. -/
noncomputable def asymmetricBinaryScaleComponent
    (hxy : q.bilin x y ≠ 0)
    (hx : ord K (q.bilin x y) < ord K (q.quadratic x))
    (hy : ord K (q.bilin x y) ≤ ord K (q.quadratic y)) :
    QuadraticSublattice q :=
  basisQuadraticSublattice (BONG.binaryPairSpan (K := K) x y)
    (binaryPair_restrict_nondegenerate_of_left_strict hxy hx hy)
    (BONG.binaryPairBasis (K := K) x y
      (binaryPair_linearIndependent_of_left_strict hxy hx hy))

/-- An asymmetric binary component generated inside `L` is contained in `L`. -/
theorem asymmetricBinaryScaleComponent_ambientSubmodule_le
    (hxy : q.bilin x y ≠ 0)
    (hx : ord K (q.bilin x y) < ord K (q.quadratic x))
    (hy : ord K (q.bilin x y) ≤ ord K (q.quadratic y))
    (hxL : x ∈ L) (hyL : y ∈ L) :
    (asymmetricBinaryScaleComponent (q := q) hxy hx hy).ambientSubmodule ≤
      L.toSubmodule := by
  apply basisQuadraticSublattice_ambientSubmodule_le
  intro i
  rw [BONG.coe_binaryPairBasis]
  fin_cases i
  · exact hxL
  · exact hyL

/-- The asymmetric component has scale contained in the mixed principal ideal. -/
theorem asymmetricBinaryScaleComponent_scaleIdeal_le
    (hxy : q.bilin x y ≠ 0)
    (hx : ord K (q.bilin x y) < ord K (q.quadratic x))
    (hy : ord K (q.bilin x y) ≤ ord K (q.quadratic y)) :
    scaleIdeal (asymmetricBinaryScaleComponent (q := q) hxy hx hy).space
        (asymmetricBinaryScaleComponent (q := q) hxy hx hy).lattice ≤
      principalIdeal (K := K) (q.bilin x y) := by
  let hli := binaryPair_linearIndependent_of_left_strict hxy hx hy
  let b := BONG.binaryPairBasis (K := K) x y hli
  change scaleIdeal
      (q.restrict (BONG.binaryPairSpan (K := K) x y)
        (binaryPair_restrict_nondegenerate_of_left_strict hxy hx hy))
      (basisLattice b) ≤ _
  apply scaleIdeal_basisLattice_le_of_basis _ b
    (principalIdeal (K := K) (q.bilin x y))
  intro i j
  change q.bilin (b i : V) (b j : V) ∈
    principalIdeal (K := K) (q.bilin x y)
  rw [show (b i : V) = BONG.binaryPairFamily x y i by
      exact BONG.coe_binaryPairBasis x y hli i,
    show (b j : V) = BONG.binaryPairFamily x y j by
      exact BONG.coe_binaryPairBasis x y hli j]
  have hi : i = 0 ∨ i = 1 := by
    have hval : i.val = 0 ∨ i.val = 1 := by omega
    rcases hval with hval | hval
    · exact Or.inl (Fin.ext hval)
    · exact Or.inr (Fin.ext hval)
  have hj : j = 0 ∨ j = 1 := by
    have hval : j.val = 0 ∨ j.val = 1 := by omega
    rcases hval with hval | hval
    · exact Or.inl (Fin.ext hval)
    · exact Or.inr (Fin.ext hval)
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  all_goals simp only [BONG.binaryPairFamily_zero, BONG.binaryPairFamily_one]
  · change q.quadratic x ∈ principalIdeal (K := K) (q.bilin x y)
    exact mem_principalIdeal_of_ord_le hxy hx.le
  · exact generator_mem_principalIdeal (q.bilin x y)
  · rw [q.isSymm.eq y x]
    exact generator_mem_principalIdeal (q.bilin x y)
  · change q.quadratic y ∈ principalIdeal (K := K) (q.bilin x y)
    exact mem_principalIdeal_of_ord_le hxy hy

/-- An asymmetric scale component is modular at its mixed pairing. -/
theorem asymmetricBinaryScaleComponent_isModular
    (hxy : q.bilin x y ≠ 0)
    (hx : ord K (q.bilin x y) < ord K (q.quadratic x))
    (hy : ord K (q.bilin x y) ≤ ord K (q.quadratic y)) :
    IsModular (asymmetricBinaryScaleComponent (q := q) hxy hx hy).space
      (asymmetricBinaryScaleComponent (q := q) hxy hx hy).lattice
      (Units.mk0 (q.bilin x y) hxy) := by
  apply isModular_of_scaleIdeal_le_of_volumeOrder_eq
  · exact asymmetricBinaryScaleComponent_scaleIdeal_le hxy hx hy
  · change volumeOrder
        (q.restrict (BONG.binaryPairSpan (K := K) x y)
          (binaryPair_restrict_nondegenerate_of_left_strict hxy hx hy))
        (basisLattice
          (BONG.binaryPairBasis (K := K) x y
            (binaryPair_linearIndependent_of_left_strict hxy hx hy))) = _
    rw [volumeOrder_binaryPairBasis_eq_two_mul_ordUnit_of_left_strict hxy hx hy]
    have hfin : finrank K (BONG.binaryPairSpan (K := K) x y) = 2 := by
      simpa using Module.finrank_eq_card_basis
        (BONG.binaryPairBasis (K := K) x y
          (binaryPair_linearIndependent_of_left_strict hxy hx hy))
    change 2 * ordUnit K (Units.mk0 (q.bilin x y) hxy) =
      (finrank K (BONG.binaryPairSpan (K := K) x y) : Int) *
        ordUnit K (Units.mk0 (q.bilin x y) hxy)
    rw [hfin]
    norm_num

end Lattice

end Bong
