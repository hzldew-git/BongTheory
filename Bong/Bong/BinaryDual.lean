/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryDiagonal
import Bong.Bong.UnaryDual
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Reverse duality for diagonal binary BONGs

This file proves the `R₁ ≤ R₂` branch of the binary case of Beli (2003),
Lemma 4.8.  In this branch the BONG is an orthogonal integral basis, and the
reversed dual basis is constructed recursively as a BONG of the dual lattice.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- The second reverse-dual vector, regarded as lying in the orthogonal
complement of the first. -/
private noncomputable def reverseDualBinaryTailVector
    (b : BONG V q L 2) (i : Fin 1) :
    q.vectorOrthogonal (b.reverseDualBasis 0) := by
  refine ⟨b.reverseDualBasis i.succ, ?_⟩
  rw [q.mem_vectorOrthogonal_iff]
  exact (LinearMap.BilinForm.iIsOrtho_def.mp
    b.reverseDualBasis_iIsOrtho) 0 i.succ (Fin.succ_ne_zero i).symm

@[simp]
private theorem coe_reverseDualBinaryTailVector (b : BONG V q L 2)
    (i : Fin 1) :
    (b.reverseDualBinaryTailVector i : V) =
      b.reverseDualVector i.succ :=
  b.reverseDualBasis_apply i.succ

/-- The singleton tail basis in the first reverse-dual orthogonal complement. -/
private noncomputable def reverseDualBinaryTailBasis (b : BONG V q L 2) :
    Basis (Fin 1) K (q.vectorOrthogonal (b.reverseDualBasis 0)) := by
  letI := b.basis.finiteDimensional_of_finite
  have hne : b.reverseDualBinaryTailVector 0 ≠ 0 := by
    intro hzero
    have hcoe : b.reverseDualBasis 1 = 0 := by
      simpa using congrArg Subtype.val hzero
    have hquadratic : q.quadratic (b.reverseDualBasis 1) ≠ 0 := by
      simpa using b.quadratic_reverseDualVector_ne_zero 1
    apply hquadratic
    rw [hcoe]
    simp
  have hli : LinearIndependent K b.reverseDualBinaryTailVector :=
    linearIndependent_unique_iff.mpr hne
  have hx : q.IsAnisotropic (b.reverseDualBasis 0) :=
    b.reverseDualBasis_isAnisotropic 0
  have hdim := q.finrank_vectorOrthogonal hx
  have hbfin : Module.finrank K V = 2 := b.length_eq_finrank.symm
  have htailfin : Module.finrank K
      (q.vectorOrthogonal (b.reverseDualBasis 0)) = 1 := by
    omega
  exact basisOfLinearIndependentOfCardEqFinrank'
    b.reverseDualBinaryTailVector hli (by simp [htailfin])

@[simp]
private theorem coe_reverseDualBinaryTailBasis (b : BONG V q L 2)
    (i : Fin 1) :
    (b.reverseDualBinaryTailBasis i : V) =
      b.reverseDualVector i.succ := by
  rw [reverseDualBinaryTailBasis]
  simp

private theorem reverseDualBinaryTailBasis_iIsOrtho
    (b : BONG V q L 2) :
    (q.orthogonalSpace (b.reverseDualBasis 0)
      (b.reverseDualBasis_isAnisotropic 0)).bilin.iIsOrtho
        b.reverseDualBinaryTailBasis := by
  rw [LinearMap.BilinForm.iIsOrtho_def]
  intro i j hij
  exact (hij (Subsingleton.elim i j)).elim

private theorem reverseDualBinaryTailBasis_ne_zero
    (b : BONG V q L 2) :
    (q.orthogonalSpace (b.reverseDualBasis 0)
      (b.reverseDualBasis_isAnisotropic 0)).quadratic
        (b.reverseDualBinaryTailBasis 0) ≠ 0 := by
  change q.quadratic
    (b.reverseDualBinaryTailBasis 0 : V) ≠ 0
  rw [coe_reverseDualBinaryTailBasis]
  exact b.quadratic_reverseDualVector_ne_zero 1

private theorem reverseDualBasis_order_le (b : BONG V q L 2)
    (horder : b.order 0 ≤ b.order 1) :
    ord K (q.quadratic (b.reverseDualBasis 0)) ≤
      ord K (q.quadratic (b.reverseDualBasis 1)) := by
  rw [b.reverseDualBasis_apply, b.reverseDualBasis_apply,
    b.ord_quadratic_reverseDualVector,
    b.ord_quadratic_reverseDualVector]
  simp only [Fin.rev]
  exact WithTop.coe_le_coe.mpr (Int.neg_le_neg horder)

/-- The reversed dual basis, recursively realized as a BONG of its basis
lattice in the diagonal binary branch. -/
private noncomputable def reverseDualBinaryBasisBONG
    (b : BONG V q L 2) (horder : b.order 0 ≤ b.order 1) :
    BONG V q (Lattice.basisLattice b.reverseDualBasis) 2 := by
  let x := b.reverseDualBasis 0
  have hx : q.IsAnisotropic x :=
    b.reverseDualBasis_isAnisotropic 0
  have generator : Lattice.IsNormGenerator q
      (Lattice.basisLattice b.reverseDualBasis) x := by
    exact Lattice.isNormGenerator_basisLattice_fin_two_of_ord_le
      q b.reverseDualBasis b.reverseDualBasis_iIsOrtho
      hx (b.reverseDualBasis_order_le horder)
  let tailBasis := b.reverseDualBinaryTailBasis
  let tailQ := q.orthogonalSpace x hx
  let tailBONG : BONG (q.vectorOrthogonal x) tailQ
      (Lattice.basisLattice tailBasis) 1 :=
    BONG.ofOrthogonalBasisFinOne tailQ tailBasis
      b.reverseDualBinaryTailBasis_iIsOrtho
      b.reverseDualBinaryTailBasis_ne_zero
  have hprojection :
      (Lattice.basisLattice b.reverseDualBasis).projectedLattice q x hx =
        Lattice.basisLattice tailBasis := by
    have htail : ∀ i,
        (b.reverseDualBinaryTailBasis i : V) =
          b.reverseDualBasis i.succ := by
      intro i
      calc
        (b.reverseDualBinaryTailBasis i : V) =
            b.reverseDualVector i.succ :=
          b.coe_reverseDualBinaryTailBasis i
        _ = b.reverseDualBasis i.succ :=
          (b.reverseDualBasis_apply i.succ).symm
    simpa [x, tailBasis] using
      Lattice.projectedLattice_basisLattice_fin_succ
        q b.reverseDualBasis hx b.reverseDualBinaryTailBasis htail
  exact BONG.cons x generator hx
    (tailBONG.castLattice hprojection.symm)

@[simp]
private theorem ambientVector_reverseDualBinaryBasisBONG
    (b : BONG V q L 2) (horder : b.order 0 ≤ b.order 1)
    (i : Fin 2) :
    (b.reverseDualBinaryBasisBONG horder).ambientVector i =
      b.reverseDualVector i := by
  cases i using Fin.cases with
  | zero =>
      rw [reverseDualBinaryBasisBONG, ambientVector_cons_zero]
      exact b.reverseDualBasis_apply 0
  | succ i =>
      rw [reverseDualBinaryBasisBONG, ambientVector_cons_succ,
        ambientVector_castLattice,
        ambientVector_ofOrthogonalBasisFinOne]
      exact b.coe_reverseDualBinaryTailBasis i

/-- In the diagonal binary branch, the reverse-dual basis lattice is the
actual integral dual lattice. -/
theorem basisLattice_reverseDualBasis_eq_dualLattice_binary_of_order_le
    (b : BONG V q L 2) (horder : b.order 0 ≤ b.order 1) :
    Lattice.basisLattice b.reverseDualBasis =
      Lattice.dualLattice q L := by
  calc
    Lattice.basisLattice b.reverseDualBasis =
        Lattice.dualLattice q (Lattice.basisLattice b.basis) :=
      b.basisLattice_reverseDualBasis
    _ = Lattice.dualLattice q L :=
      (congrArg (Lattice.dualLattice q)
        (b.lattice_eq_basisLattice_of_order_le horder)).symm

/-- The binary reverse-dual BONG in the `R₁ ≤ R₂` branch. -/
noncomputable def reverseDualBinaryOfOrderLe
    (b : BONG V q L 2) (horder : b.order 0 ≤ b.order 1) :
    BONG V q (Lattice.dualLattice q L) 2 :=
  (b.reverseDualBinaryBasisBONG horder).castLattice
    (b.basisLattice_reverseDualBasis_eq_dualLattice_binary_of_order_le
      horder)

@[simp]
theorem ambientVector_reverseDualBinaryOfOrderLe
    (b : BONG V q L 2) (horder : b.order 0 ≤ b.order 1)
    (i : Fin 2) :
    (b.reverseDualBinaryOfOrderLe horder).ambientVector i =
      b.reverseDualVector i := by
  rw [reverseDualBinaryOfOrderLe, ambientVector_castLattice,
    ambientVector_reverseDualBinaryBasisBONG]

/-- The binary dual BONG values are the reversed reciprocals. -/
@[simp]
theorem value_reverseDualBinaryOfOrderLe
    (b : BONG V q L 2) (horder : b.order 0 ≤ b.order 1)
    (i : Fin 2) :
    (b.reverseDualBinaryOfOrderLe horder).value i =
      ((b.valueUnit (Fin.rev i))⁻¹ : K) := by
  rw [← (b.reverseDualBinaryOfOrderLe horder).quadratic_ambientVector,
    b.ambientVector_reverseDualBinaryOfOrderLe horder,
    b.quadratic_reverseDualVector]

/-- The binary reverse-dual construction is automatically good. -/
noncomputable def reverseDualBinaryGoodOfOrderLe
    (b : BONG V q L 2) (horder : b.order 0 ≤ b.order 1) :
    GoodBONG q (Lattice.dualLattice q L) 2 where
  toBONG := b.reverseDualBinaryOfOrderLe horder
  good := b.reverseDualBinaryOfOrderLe horder |>.isGood_binary

@[simp]
theorem ambientVector_reverseDualBinaryGoodOfOrderLe
    (b : BONG V q L 2) (horder : b.order 0 ≤ b.order 1)
    (i : Fin 2) :
    (b.reverseDualBinaryGoodOfOrderLe horder).toBONG.ambientVector i =
      b.reverseDualVector i :=
  b.ambientVector_reverseDualBinaryOfOrderLe horder i

end BONG

end Bong
