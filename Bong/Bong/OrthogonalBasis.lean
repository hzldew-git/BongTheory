/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BasisLattice
import Bong.Bong.Binary
import Bong.Bong.BinaryInvariant
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# BONGs from ordered orthogonal bases

An anisotropic orthogonal binary basis whose first quadratic value has no
larger valuation than the second is recursively a BONG of its integral basis
lattice.  This is the constructive content of Beli (2003), Lemma 3.3(ii).
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace BONG

private noncomputable def orthogonalFinTwoTailVector
    (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis) (i : Fin 1) :
    q.vectorOrthogonal (basis 0) := by
  refine ⟨basis i.succ, ?_⟩
  rw [q.mem_vectorOrthogonal_iff]
  exact (LinearMap.BilinForm.iIsOrtho_def.mp horth)
    0 i.succ (Fin.succ_ne_zero i).symm

@[simp]
private theorem coe_orthogonalFinTwoTailVector
    (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis) (i : Fin 1) :
    (orthogonalFinTwoTailVector q basis horth i : V) = basis i.succ :=
  rfl

private noncomputable def orthogonalFinTwoTailBasis
    (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0) :
    Basis (Fin 1) K (q.vectorOrthogonal (basis 0)) := by
  letI := basis.finiteDimensional_of_finite
  have hvectorNe : orthogonalFinTwoTailVector q basis horth 0 ≠ 0 := by
    intro hzero
    have hcoe : basis 1 = 0 := by
      simpa using congrArg Subtype.val hzero
    apply hne1
    rw [hcoe]
    simp
  have hli : LinearIndependent K
      (orthogonalFinTwoTailVector q basis horth) :=
    linearIndependent_unique_iff.mpr hvectorNe
  have hdim := q.finrank_vectorOrthogonal hne0
  have hbfin : Module.finrank K V = 2 := by
    simpa using finrank_eq_card_basis basis
  have htailfin : Module.finrank K (q.vectorOrthogonal (basis 0)) = 1 := by
    omega
  exact basisOfLinearIndependentOfCardEqFinrank'
    (orthogonalFinTwoTailVector q basis horth) hli
    (by simp [htailfin])

@[simp]
private theorem coe_orthogonalFinTwoTailBasis
    (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0) (i : Fin 1) :
    (orthogonalFinTwoTailBasis q basis horth hne0 hne1 i : V) =
      basis i.succ := by
  rw [orthogonalFinTwoTailBasis]
  simp

/-- An ordered anisotropic orthogonal binary basis gives a BONG of its basis
lattice. -/
noncomputable def ofOrthogonalBasisFinTwoOfOrdLe
    (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0)
    (horder : ord K (q.quadratic (basis 0)) ≤
      ord K (q.quadratic (basis 1))) :
    BONG V q (Lattice.basisLattice basis) 2 := by
  let tailBasis :=
    orthogonalFinTwoTailBasis q basis horth hne0 hne1
  let tailQ := q.orthogonalSpace (basis 0) hne0
  have tailOrthogonal : tailQ.bilin.iIsOrtho tailBasis := by
    rw [LinearMap.BilinForm.iIsOrtho_def]
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have tailNe : tailQ.quadratic (tailBasis 0) ≠ 0 := by
    change q.quadratic (tailBasis 0 : V) ≠ 0
    rw [coe_orthogonalFinTwoTailBasis]
    exact hne1
  let tailBONG : BONG (q.vectorOrthogonal (basis 0)) tailQ
      (Lattice.basisLattice tailBasis) 1 :=
    ofOrthogonalBasisFinOne tailQ tailBasis tailOrthogonal tailNe
  have generator :=
    Lattice.isNormGenerator_basisLattice_fin_two_of_ord_le
      q basis horth hne0 horder
  have hprojection :
      (Lattice.basisLattice basis).projectedLattice q (basis 0) hne0 =
        Lattice.basisLattice tailBasis := by
    apply Lattice.projectedLattice_basisLattice_fin_succ
      q basis hne0 tailBasis
    intro i
    exact coe_orthogonalFinTwoTailBasis
      q basis horth hne0 hne1 i
  exact BONG.cons (basis 0) generator hne0
    (tailBONG.castLattice hprojection.symm)

/-- The constructed BONG has exactly the supplied orthogonal basis vectors. -/
@[simp]
theorem ambientVector_ofOrthogonalBasisFinTwoOfOrdLe
    (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0)
    (horder : ord K (q.quadratic (basis 0)) ≤
      ord K (q.quadratic (basis 1))) (i : Fin 2) :
    (ofOrthogonalBasisFinTwoOfOrdLe q basis horth hne0 hne1 horder).ambientVector i =
      basis i := by
  cases i using Fin.cases with
  | zero =>
      rw [ofOrthogonalBasisFinTwoOfOrdLe, ambientVector_cons_zero]
  | succ i =>
      rw [ofOrthogonalBasisFinTwoOfOrdLe, ambientVector_cons_succ,
        ambientVector_castLattice,
        ambientVector_ofOrthogonalBasisFinOne]
      exact coe_orthogonalFinTwoTailBasis
        q basis horth hne0 hne1 i

/-- The constructed BONG values are the diagonal quadratic values. -/
@[simp]
theorem value_ofOrthogonalBasisFinTwoOfOrdLe
    (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0)
    (horder : ord K (q.quadratic (basis 0)) ≤
      ord K (q.quadratic (basis 1))) (i : Fin 2) :
    (ofOrthogonalBasisFinTwoOfOrdLe q basis horth hne0 hne1 horder).value i =
      q.quadratic (basis i) := by
  rw [← quadratic_ambientVector,
    ambientVector_ofOrthogonalBasisFinTwoOfOrdLe]

/-- The value units of the constructed BONG are the units attached to the
diagonal values. -/
@[simp]
theorem valueUnit_ofOrthogonalBasisFinTwoOfOrdLe
    (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0)
    (horder : ord K (q.quadratic (basis 0)) ≤
      ord K (q.quadratic (basis 1))) (i : Fin 2) :
    (ofOrthogonalBasisFinTwoOfOrdLe
      q basis horth hne0 hne1 horder).valueUnit i =
        Units.mk0 (q.quadratic (basis i)) (by
          cases i using Fin.cases with
          | zero => exact hne0
          | succ i => simpa [Subsingleton.elim i 0] using hne1) := by
  apply Units.ext
  rw [coe_valueUnit, Units.val_mk0,
    value_ofOrthogonalBasisFinTwoOfOrdLe]

/-- The binary parameter of the constructed BONG is the quotient of its two
diagonal values. -/
theorem binaryParameter_ofOrthogonalBasisFinTwoOfOrdLe
    (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0)
    (horder : ord K (q.quadratic (basis 0)) ≤
      ord K (q.quadratic (basis 1))) :
    (ofOrthogonalBasisFinTwoOfOrdLe
      q basis horth hne0 hne1 horder).binaryParameter =
        Units.mk0 (q.quadratic (basis 1)) hne1 /
          Units.mk0 (q.quadratic (basis 0)) hne0 := by
  unfold binaryParameter
  rw [valueUnit_ofOrthogonalBasisFinTwoOfOrdLe,
    valueUnit_ofOrthogonalBasisFinTwoOfOrdLe]

/-- Beli's relative order for an ordered orthogonal binary basis is the
difference of the two diagonal orders. -/
theorem binaryOrderGap_ofOrthogonalBasisFinTwoOfOrdLe
    (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0)
    (horder : ord K (q.quadratic (basis 0)) ≤
      ord K (q.quadratic (basis 1))) :
    (ofOrthogonalBasisFinTwoOfOrdLe
      q basis horth hne0 hne1 horder).binaryOrderGap =
        ordUnit K (Units.mk0 (q.quadratic (basis 1)) hne1) -
          ordUnit K (Units.mk0 (q.quadratic (basis 0)) hne0) := by
  rw [binaryOrderGap, order_eq_ordUnit, order_eq_ordUnit,
    valueUnit_ofOrthogonalBasisFinTwoOfOrdLe,
    valueUnit_ofOrthogonalBasisFinTwoOfOrdLe]

/-- Beli's refined invariant for an ordered orthogonal binary basis is the
class of the quotient of its diagonal values. -/
theorem binaryDeterminantInvariant_ofOrthogonalBasisFinTwoOfOrdLe
    (q : QuadraticSpace K V) (basis : Basis (Fin 2) K V)
    (horth : q.bilin.iIsOrtho basis)
    (hne0 : q.quadratic (basis 0) ≠ 0)
    (hne1 : q.quadratic (basis 1) ≠ 0)
    (horder : ord K (q.quadratic (basis 0)) ≤
      ord K (q.quadratic (basis 1))) :
    (ofOrthogonalBasisFinTwoOfOrdLe
      q basis horth hne0 hne1 horder).binaryDeterminantInvariant =
        unitSquareClass K
          (Units.mk0 (q.quadratic (basis 1)) hne1 /
            Units.mk0 (q.quadratic (basis 0)) hne0) := by
  rw [binaryDeterminantInvariant_eq_parameter,
    binaryUnitSquareClass, binaryParameter_ofOrthogonalBasisFinTwoOfOrdLe]

end BONG

end Bong
