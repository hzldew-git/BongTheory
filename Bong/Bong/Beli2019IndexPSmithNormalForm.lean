/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrimeIndexChain

/-!
# Smith normal form for an index-uniformizer inclusion

The volume condition in `Beli2019IndexPInclusion` forces the sum of the
Smith exponents to be one.  Consequently exactly one exponent is one and
all the others vanish: after choosing a suitable ambient basis, the smaller
lattice is obtained by multiplying one basis vector by the uniformizer.

This is the module-theoretic normal form underlying the first paragraph of
Beli (2019), Section 5.  It uses only Smith normal form over the valuation
ring and the Gram determinant transformation law.
-/

namespace Bong.Lattice

open Module
open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Scaling all basis coordinates by uniformizer powers changes the Gram
determinant by the square of the total power. -/
theorem basisGramDeterminant_powerBasis
    (q : QuadraticSpace K V)
    (b : Basis (Fin (finrank K V)) K V)
    (e : Fin (finrank K V) → Nat) :
    basisGramDeterminant q (powerBasis b e) =
      basisGramDeterminant q b *
        uniformizer K ^ (2 * ∑ i, e i) := by
  rw [basisGramDeterminant_changeBasis q b]
  congr 1
  have hdet := b.det_unitsSMul_self
    (fun i => uniformizerUnit K ^ e i)
  have hdet' : Matrix.det (b.toMatrix (powerBasis b e)) =
      uniformizer K ^ ∑ i, e i := by
    rw [← Basis.det_apply]
    rw [show powerBasis b e =
      b.unitsSMul (fun i => uniformizerUnit K ^ e i) by rfl]
    rw [hdet]
    simp only [Units.val_pow_eq_pow_val, coe_uniformizerUnit]
    exact Finset.prod_pow_eq_pow_sum Finset.univ e (uniformizer K)
  rw [hdet', ← pow_mul]
  congr 1
  omega

/-- Scaling by a vector of Smith powers raises the lattice volume order by
twice the sum of those powers. -/
theorem volumeOrder_basisLattice_powerBasis
    (q : QuadraticSpace K V)
    (b : Basis (Fin (finrank K V)) K V)
    (e : Fin (finrank K V) → Nat) :
    volumeOrder q (basisLattice (powerBasis b e)) =
      volumeOrder q (basisLattice b) + 2 * ∑ i, (e i : Int) := by
  apply WithTop.coe_injective
  change (volumeOrder q (basisLattice (powerBasis b e)) : WithTop Int) =
    (volumeOrder q (basisLattice b) : WithTop Int) +
      (2 * ∑ i, (e i : Int) : Int)
  rw [coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant,
    coe_volumeOrder_basisLattice_eq_ord_basisGramDeterminant,
    basisGramDeterminant_powerBasis, ord_mul, ord_pow,
    ord_uniformizer]
  congr 1
  rw [nsmul_one]
  norm_cast

namespace SmithPowerBasisData

/-- In Smith data for an index-`\mathfrak p` inclusion, the exponents sum
to one. -/
theorem sum_exponent_eq_one {M N : Lattice K V}
    (q : QuadraticSpace K V) (D : SmithPowerBasisData N M)
    (inclusion : Beli2019IndexPInclusion q M N) :
    ∑ i, D.exponent i = 1 := by
  have hvolume := volumeOrder_basisLattice_powerBasis q
    D.topAmbientBasis D.exponent
  rw [D.powerBasis_top_eq_bot, D.basisLattice_botAmbientBasis,
    D.basisLattice_topAmbientBasis, inclusion.volumeOrder_eq] at hvolume
  have hsumInt : ∑ i, (D.exponent i : Int) = 1 := by omega
  exact_mod_cast hsumInt

/-- Precisely one Smith exponent is one, and every other exponent is zero. -/
theorem exists_unique_unit_exponent {M N : Lattice K V}
    (q : QuadraticSpace K V) (D : SmithPowerBasisData N M)
    (inclusion : Beli2019IndexPInclusion q M N) :
    ∃ i, D.exponent i = 1 ∧ ∀ j, j ≠ i → D.exponent j = 0 := by
  classical
  have hsum := D.sum_exponent_eq_one q inclusion
  have hsumpos : 0 < ∑ i, D.exponent i := by omega
  rcases Finset.sum_pos_iff.mp hsumpos with ⟨i, _, hi⟩
  have hiLe : D.exponent i ≤ ∑ j, D.exponent j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hiEq : D.exponent i = 1 := by omega
  refine ⟨i, hiEq, ?_⟩
  intro j hji
  have hjMem : j ∈
      (Finset.univ : Finset (Fin (finrank K V))).erase i := by
    simp [hji]
  have hjLe : D.exponent j ≤
      ∑ k ∈ (Finset.univ : Finset (Fin (finrank K V))).erase i,
        D.exponent k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hjMem
  have hdecomp := Finset.sum_erase_add Finset.univ D.exponent
    (Finset.mem_univ i)
  by_contra hjNe
  have hjPos : 0 < D.exponent j := Nat.pos_of_ne_zero hjNe
  omega

/-- The Smith power basis of an index-`\mathfrak p` inclusion is a single
coordinate scaling. -/
theorem powerBasis_eq_coordinateScaleBasis {M N : Lattice K V}
    (q : QuadraticSpace K V) (D : SmithPowerBasisData N M)
    (inclusion : Beli2019IndexPInclusion q M N) :
    ∃ i, powerBasis D.topAmbientBasis D.exponent =
      coordinateScaleBasis D.topAmbientBasis i := by
  classical
  rcases D.exists_unique_unit_exponent q inclusion with
    ⟨i, hi, hother⟩
  refine ⟨i, ?_⟩
  ext j
  by_cases hji : j = i
  · subst j
    rw [coordinateScaleBasis_apply_same]
    simp [powerBasis, Basis.unitsSMul_apply, hi, Units.smul_def,
      coe_uniformizerUnit]
  · rw [coordinateScaleBasis_apply_of_ne _ hji]
    simp [powerBasis, Basis.unitsSMul_apply, hother j hji]

end SmithPowerBasisData

/-- Every literal index-`\mathfrak p` inclusion has a basis in which the
smaller lattice is obtained by scaling one coordinate by the uniformizer. -/
theorem indexPInclusion_exists_coordinateScaleBasis
    (q : QuadraticSpace K V) (M N : Lattice K V)
    (inclusion : Beli2019IndexPInclusion q M N) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)),
      basisLattice b = M ∧
        basisLattice (coordinateScaleBasis b i) = N := by
  let D := Classical.choice
    (exists_smithPowerBasisData N M inclusion.lattice_le)
  rcases D.powerBasis_eq_coordinateScaleBasis q inclusion with ⟨i, hi⟩
  refine ⟨D.topAmbientBasis, i, D.basisLattice_topAmbientBasis, ?_⟩
  rw [← hi, D.powerBasis_top_eq_bot, D.basisLattice_botAmbientBasis]

end Bong.Lattice
