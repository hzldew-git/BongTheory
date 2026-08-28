/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalDecompositionSuffix
import Bong.Lattice.OrthogonalDecompositionTail
import Bong.Lattice.OrthogonalDecompositionProduct

/-!
# Splitting an orthogonal decomposition at an arbitrary cut

Every numerical cut packages the corresponding prefix and suffix as a
two-component orthogonal decomposition.  Its product presentation identifies
the orthogonal sum of the two restricted quadratic spaces with the original
ambient quadratic lattice.
-/

namespace Bong

open Dyadic Module

namespace Lattice.OrthogonalDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The prefix and suffix quadratic sublattices at a fixed cut. -/
noncomputable def prefixSuffixComponents
    (D : OrthogonalDecomposition q L t) (k : Nat) :
    Fin 2 → QuadraticSublattice q :=
  Fin.cases (D.prefixQuadraticSublattice k)
    (fun _ ↦ D.suffixQuadraticSublattice k)

@[simp]
theorem prefixSuffixComponents_zero
    (D : OrthogonalDecomposition q L t) (k : Nat) :
    D.prefixSuffixComponents k 0 = D.prefixQuadraticSublattice k :=
  rfl

@[simp]
theorem prefixSuffixComponents_one
    (D : OrthogonalDecomposition q L t) (k : Nat) :
    D.prefixSuffixComponents k 1 = D.suffixQuadraticSublattice k :=
  rfl

/-- The two-component orthogonal decomposition obtained by cutting at `k`.
The definition is valid also for the empty and full cuts. -/
noncomputable def prefixSuffixDecomposition
    (D : OrthogonalDecomposition q L t) (k : Nat) :
    OrthogonalDecomposition q L 2 where
  component := D.prefixSuffixComponents k
  orthogonal := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · intro x y
      exact D.bilin_prefixCarrier_suffixCarrier_eq_zero k x.property y.property
    · intro x y
      exact q.isSymm.eq (x : V) (y : V) |>.trans
        (D.bilin_prefixCarrier_suffixCarrier_eq_zero k y.property x.property)
    · exact (hij rfl).elim
  sum_eq := by
    rw [iSup_fin_two_eq_sup_tail, prefixSuffixComponents_zero,
      prefixSuffixComponents_one,
      D.prefixQuadraticSublattice_ambientSubmodule,
      D.suffixQuadraticSublattice_ambientSubmodule]
    exact D.prefixAmbientSubmodule_sup_suffixAmbientSubmodule k

@[simp]
theorem prefixSuffixDecomposition_zero
    (D : OrthogonalDecomposition q L t) (k : Nat) :
    (D.prefixSuffixDecomposition k).component 0 =
      D.prefixQuadraticSublattice k :=
  rfl

@[simp]
theorem prefixSuffixDecomposition_one
    (D : OrthogonalDecomposition q L t) (k : Nat) :
    (D.prefixSuffixDecomposition k).component 1 =
      D.suffixQuadraticSublattice k :=
  rfl

/-- Integral product presentation of a prefix and its complementary suffix.
-/
noncomputable def prefixSuffixLatticeIsometry
    (D : OrthogonalDecomposition q L t) (k : Nat) :
    Lattice.Isometry
      ((D.prefixQuadraticSublattice k).space.orthogonalSum
        (D.suffixQuadraticSublattice k).space)
      q
      (Lattice.product (D.prefixQuadraticSublattice k).lattice
        (D.suffixQuadraticSublattice k).lattice)
      L :=
  (D.prefixSuffixDecomposition k).pairProductLatticeIsometry

end Lattice.OrthogonalDecomposition

end Bong
