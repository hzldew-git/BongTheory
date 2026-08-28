/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BasisLattice
import Bong.Bong.Binary
import Bong.Lattice.NormGenerator

/-!
# Diagonalization of binary BONG lattices

Beli (2003), Corollary 3.4(ii) states that a binary BONG whose first order is
at most its second order is an actual orthogonal integral basis.  The proof
uses the unary basis-lattice theorem and the reconstruction lemma.
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

private theorem value_mem_principalIdeal_zero (b : BONG V q L 2)
    (horder : b.order 0 ≤ b.order 1) (i : Fin 2) :
    b.value i ∈ Lattice.principalIdeal (K := K) (b.value 0) := by
  refine Fin.cases (Lattice.generator_mem_principalIdeal (b.value 0))
    (fun j => ?_) i
  have hj : j = 0 := Subsingleton.elim j 0
  subst j
  apply Lattice.mem_principalIdeal_of_ord_le (b.value_ne_zero 0)
  calc
    ord K (b.value 0) = (b.order 0 : WithTop Int) :=
      (b.coe_order 0).symm
    _ ≤ (b.order 1 : WithTop Int) := WithTop.coe_le_coe.mpr horder
    _ = ord K (b.value 1) := b.coe_order 1

/-- Under increasing binary orders, the head generates the basis-lattice norm. -/
theorem head_isNormGenerator_basisLattice_of_order_le
    (b : BONG V q L 2) (horder : b.order 0 ≤ b.order 1) :
    Lattice.IsNormGenerator q (Lattice.basisLattice b.basis) b.head := by
  constructor
  · rw [← b.ambientVector_zero_eq_head]
    exact Submodule.subset_span ⟨0, rfl⟩
  · rw [b.normIdeal_basisLattice]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [← b.value_zero_eq_quadratic_head]
      exact value_mem_principalIdeal_zero b horder i
    · rw [Lattice.principalIdeal, Submodule.span_le]
      rintro _ ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact Submodule.subset_span ⟨0, b.value_zero_eq_quadratic_head⟩

/-- Beli (2003), Corollary 3.4(ii): increasing orders give a diagonal lattice. -/
theorem lattice_eq_basisLattice_of_order_le
    (b : BONG V q L 2) (horder : b.order 0 ≤ b.order 1) :
    L = Lattice.basisLattice b.basis := by
  have hprojection :
      L.projectedLattice q b.head b.head_isAnisotropic =
        (Lattice.basisLattice b.basis).projectedLattice q b.head
          b.head_isAnisotropic :=
    b.tail.lattice_eq_basisLattice.trans
      b.projectedLattice_basisLattice.symm
  apply Lattice.eq_of_normIdeal_eq_of_projectedLattice_eq
    q L (Lattice.basisLattice b.basis) b.head
    b.head_isNormGenerator
    (b.head_isNormGenerator_basisLattice_of_order_le horder)
    b.head_isAnisotropic
  · rw [b.head_isNormGenerator.normIdeal_eq,
      (b.head_isNormGenerator_basisLattice_of_order_le horder).normIdeal_eq]
  · exact hprojection

/-- Nonnegative binary relative order is the same diagonalization criterion. -/
theorem lattice_eq_basisLattice_of_binaryOrderGap_nonneg
    (b : BONG V q L 2) (hgap : 0 ≤ b.binaryOrderGap) :
    L = Lattice.basisLattice b.basis := by
  apply b.lattice_eq_basisLattice_of_order_le
  rw [binaryOrderGap] at hgap
  omega

end BONG

end Bong
