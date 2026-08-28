/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.MaximalNormSplittingDual
import Bong.Bong.BinaryModularInvariant

/-!
# Order bounds for Beli (2003), Lemma 4.1

The finite concatenation in Lemma 4.1 is driven by a simple local fact.  In
a unary or modular-binary component, every BONG order is at most the first
order.  The first order is the order of the selected norm generator, and the
norm-gap inequalities of a maximal norm splitting make those first orders
nondecreasing from one component to the next.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

namespace Lattice.MaximalNormSplitting

open Lattice.OrthogonalDecomposition

variable (M : Lattice.MaximalNormSplitting q L t)
  (c : M.toOrthogonalDecomposition.ComponentBONGFamily)

/-- Every order in a unary or modular-binary component is bounded by the
first component order. -/
theorem component_order_le_first (i : Fin t)
    (j : Fin (M.toOrthogonalDecomposition.componentRank i)) :
    (c i).order j ≤ (c i).order (M.componentFirstIndex i) := by
  rcases M.componentRank_eq_one_or_two i with hOne | hTwo
  · have hj : j = M.componentFirstIndex i := by
      apply Fin.ext
      change j.val = 0
      change M.toOrthogonalDecomposition.componentRank i = 1 at hOne
      omega
    rw [hj]
  · let bTwo := (c i).castLength hTwo
    have hmodular : Lattice.IsModular
        (M.toOrthogonalDecomposition.component i).space
        (M.toOrthogonalDecomposition.component i).lattice
        (M.scaleGenerator i) :=
      M.component_isModular c i
    have hj : j.val = 0 ∨ j.val = 1 := by
      change M.toOrthogonalDecomposition.componentRank i = 2 at hTwo
      omega
    rcases hj with hj | hj
    · have hEq : j = M.componentFirstIndex i := by
        apply Fin.ext
        exact hj
      rw [hEq]
    · have hzero : (M.componentFirstIndex i).val = 0 := rfl
      let oneOriginal :
          Fin (M.toOrthogonalDecomposition.componentRank i) :=
        ⟨1, by
          change M.componentRank i = 2 at hTwo
          omega⟩
      let zeroOriginal :
          Fin (M.toOrthogonalDecomposition.componentRank i) :=
        ⟨0, M.componentRank_pos i⟩
      have hcastOne :
          (bTwo.order (1 : Fin 2)) = (c i).order j := by
        calc
          (bTwo.order (1 : Fin 2)) = (c i).order oneOriginal := by
            simpa [bTwo, oneOriginal] using
              BONG.order_castLength (c i) hTwo (1 : Fin 2)
          _ = (c i).order j := by
            congr 1
            apply Fin.ext
            exact hj.symm
      have hcastZero :
          (bTwo.order (0 : Fin 2)) =
            (c i).order (M.componentFirstIndex i) := by
        calc
          (bTwo.order (0 : Fin 2)) = (c i).order zeroOriginal := by
            simpa [bTwo, zeroOriginal] using
              BONG.order_castLength (c i) hTwo (0 : Fin 2)
          _ = (c i).order (M.componentFirstIndex i) := by
            congr 1
      rw [← hcastOne, ← hcastZero]
      exact bTwo.order_one_le_order_zero_of_isModular
        (M.scaleGenerator i) hmodular

/-- Every local component order is bounded by the order of the component's
chosen norm generator. -/
theorem component_order_le_normGeneratorOrder (i : Fin t)
    (j : Fin (M.toOrthogonalDecomposition.componentRank i)) :
    (c i).order j ≤ ordUnit K (M.normGenerator i) := by
  calc
    (c i).order j ≤ (c i).order (M.componentFirstIndex i) :=
      M.component_order_le_first c i j
    _ = ordUnit K (M.normGenerator i) :=
      M.componentFirst_order_eq_normGeneratorOrder c i

/-- The norm-generator orders of a maximal norm splitting are
nondecreasing. -/
theorem normGeneratorOrder_mono {i j : Fin t} (hij : i < j) :
    ordUnit K (M.normGenerator i) ≤ ordUnit K (M.normGenerator j) := by
  have h := (M.normGap_bounds hij).1
  omega

/-- Every order in an earlier component is bounded by the head order of
every later component.  This is exactly the norm-generator hypothesis used
by the binary orthogonal-product constructor. -/
theorem component_order_le_later_first {i j : Fin t} (hij : i < j)
    (k : Fin (M.toOrthogonalDecomposition.componentRank i)) :
    (c i).order k ≤ (c j).order (M.componentFirstIndex j) := by
  calc
    (c i).order k ≤ ordUnit K (M.normGenerator i) :=
      M.component_order_le_normGeneratorOrder c i k
    _ ≤ ordUnit K (M.normGenerator j) := M.normGeneratorOrder_mono hij
    _ = (c j).order (M.componentFirstIndex j) :=
      (M.componentFirst_order_eq_normGeneratorOrder c j).symm

end Lattice.MaximalNormSplitting

end Bong
