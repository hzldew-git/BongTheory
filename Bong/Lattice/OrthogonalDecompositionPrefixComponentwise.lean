/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009ComponentwiseAssembly
import Bong.Dyadic.UnitsCongruentModuloAlgebra
import Bong.Lattice.OrthogonalDecompositionDeterminant
import Bong.Lattice.OrthogonalDecompositionPrefixProduct

/-!
# Componentwise isometries of orthogonal-decomposition prefixes

If the first `n + 1` components of two finite orthogonal decompositions are
pairwise isometric, their integral prefix lattices are isometric.  This is
the prefix analogue of the ambient componentwise assembly theorem.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

namespace Lattice.OrthogonalDecomposition

/-- Refined determinant square class after adjoining the component at a
prefix cut. -/
theorem unitSquareClass_prefix_succ_eq_mul_component
    {t : Nat} (D : OrthogonalDecomposition q L t) (p : Fin t) :
    unitSquareClass K
        ((D.prefixQuadraticSublattice (p.val + 1)).refinedDeterminantUnit) =
      unitSquareClass K
        ((D.prefixQuadraticSublattice p.val).refinedDeterminantUnit *
          (D.component p).refinedDeterminantUnit) := by
  have hdet := Lattice.determinantClass_eq_of_isometry
    (D.prefixComponentLatticeIsometry p)
  rw [Lattice.determinantClass_orthogonalProduct] at hdet
  change
    unitSquareClass K
          ((D.prefixQuadraticSublattice p.val).refinedDeterminantUnit) *
        unitSquareClass K ((D.component p).refinedDeterminantUnit) =
      unitSquareClass K
        ((D.prefixQuadraticSublattice (p.val + 1)).refinedDeterminantUnit)
      at hdet
  rw [← unitSquareClass_mul] at hdet
  exact hdet.symm

/-- Pairwise isometries of equal-length prefixes assemble even when the two
ambient orthogonal decompositions have different total component counts. -/
noncomputable def prefixComponentwiseIsometryOfDifferentCounts
    {s t n : Nat}
    (P : OrthogonalDecomposition q L s)
    (Q : OrthogonalDecomposition q M t)
    (hP : n + 1 ≤ s) (hQ : n + 1 ≤ t)
    (f : ∀ i : Fin (n + 1), Lattice.Isometry
      (P.component (P.prefixIndexEquiv (n + 1) hP i).1).space
      (Q.component (Q.prefixIndexEquiv (n + 1) hQ i).1).space
      (P.component (P.prefixIndexEquiv (n + 1) hP i).1).lattice
      (Q.component (Q.prefixIndexEquiv (n + 1) hQ i).1).lattice) :
    Lattice.Isometry
      (P.prefixQuadraticSublattice (n + 1)).space
      (Q.prefixQuadraticSublattice (n + 1)).space
      (P.prefixQuadraticSublattice (n + 1)).lattice
      (Q.prefixQuadraticSublattice (n + 1)).lattice :=
  (P.prefixBlockProductIsometry hP).symm |>.trans
    ((BONG.blockProductLatticeIsometry
      (P.prefixBlockSpace hP) (Q.prefixBlockSpace hQ)
      (P.prefixBlockLattice hP) (Q.prefixBlockLattice hQ) f).trans
        (Q.prefixBlockProductIsometry hQ))

/-- The refined determinant units of componentwise-isometric equal-length
prefixes differ by a square, without requiring equal ambient component
counts. -/
theorem exists_prefixDeterminantUnit_eq_mul_square_of_componentwiseIsometry_of_differentCounts
    {s t n : Nat}
    (P : OrthogonalDecomposition q L s)
    (Q : OrthogonalDecomposition q M t)
    (hP : n + 1 ≤ s) (hQ : n + 1 ≤ t)
    (f : ∀ i : Fin (n + 1), Lattice.Isometry
      (P.component (P.prefixIndexEquiv (n + 1) hP i).1).space
      (Q.component (Q.prefixIndexEquiv (n + 1) hQ i).1).space
      (P.component (P.prefixIndexEquiv (n + 1) hP i).1).lattice
      (Q.component (Q.prefixIndexEquiv (n + 1) hQ i).1).lattice) :
    ∃ u : Kˣ,
      (Q.prefixQuadraticSublattice (n + 1)).refinedDeterminantUnit =
        (P.prefixQuadraticSublattice (n + 1)).refinedDeterminantUnit * u ^ 2 := by
  let F := P.prefixComponentwiseIsometryOfDifferentCounts Q hP hQ f
  have hclass := Lattice.determinantClass_eq_of_isometry F
  change Dyadic.unitSquareClass K
      (P.prefixQuadraticSublattice (n + 1)).refinedDeterminantUnit =
    Dyadic.unitSquareClass K
      (Q.prefixQuadraticSublattice (n + 1)).refinedDeterminantUnit at hclass
  obtain ⟨u, hu⟩ := BONG.GoodBONG.exists_square_mul_eq_of_unitSquareClass_eq
    (P.prefixQuadraticSublattice (n + 1)).refinedDeterminantUnit
    (Q.prefixQuadraticSublattice (n + 1)).refinedDeterminantUnit hclass
  exact ⟨u, hu.symm⟩

/-- Pairwise isometries of the components before a positive cut assemble to
an isometry of the corresponding prefix quadratic lattices. -/
noncomputable def prefixComponentwiseIsometry
    {t n : Nat}
    (P : OrthogonalDecomposition q L t)
    (Q : OrthogonalDecomposition q M t)
    (hk : n + 1 ≤ t)
    (f : ∀ i : Fin (n + 1), Lattice.Isometry
      (P.component (P.prefixIndexEquiv (n + 1) hk i).1).space
      (Q.component (Q.prefixIndexEquiv (n + 1) hk i).1).space
      (P.component (P.prefixIndexEquiv (n + 1) hk i).1).lattice
      (Q.component (Q.prefixIndexEquiv (n + 1) hk i).1).lattice) :
    Lattice.Isometry
      (P.prefixQuadraticSublattice (n + 1)).space
      (Q.prefixQuadraticSublattice (n + 1)).space
      (P.prefixQuadraticSublattice (n + 1)).lattice
      (Q.prefixQuadraticSublattice (n + 1)).lattice :=
  (P.prefixBlockProductIsometry hk).symm |>.trans
    ((BONG.blockProductLatticeIsometry
      (P.prefixBlockSpace hk) (Q.prefixBlockSpace hk)
      (P.prefixBlockLattice hk) (Q.prefixBlockLattice hk) f).trans
        (Q.prefixBlockProductIsometry hk))

/-- Equality of corresponding components is the most common specialization
of `prefixComponentwiseIsometry`. -/
noncomputable def prefixComponentwiseIsometryOfEq
    {t n : Nat}
    (P : OrthogonalDecomposition q L t)
    (Q : OrthogonalDecomposition q M t)
    (hk : n + 1 ≤ t)
    (hcomponent : ∀ i : Fin (n + 1),
      P.component (P.prefixIndexEquiv (n + 1) hk i).1 =
        Q.component (Q.prefixIndexEquiv (n + 1) hk i).1) :
    Lattice.Isometry
      (P.prefixQuadraticSublattice (n + 1)).space
      (Q.prefixQuadraticSublattice (n + 1)).space
      (P.prefixQuadraticSublattice (n + 1)).lattice
      (Q.prefixQuadraticSublattice (n + 1)).lattice := by
  apply P.prefixComponentwiseIsometry Q hk
  intro i
  rw [hcomponent i]
  exact Lattice.Isometry.refl _ _

/-- The refined determinant units of componentwise-isometric prefixes
differ by an actual square. -/
theorem exists_prefixDeterminantUnit_eq_mul_square_of_componentwiseIsometry
    {t n : Nat}
    (P : OrthogonalDecomposition q L t)
    (Q : OrthogonalDecomposition q M t)
    (hk : n + 1 ≤ t)
    (f : ∀ i : Fin (n + 1), Lattice.Isometry
      (P.component (P.prefixIndexEquiv (n + 1) hk i).1).space
      (Q.component (Q.prefixIndexEquiv (n + 1) hk i).1).space
      (P.component (P.prefixIndexEquiv (n + 1) hk i).1).lattice
      (Q.component (Q.prefixIndexEquiv (n + 1) hk i).1).lattice) :
    ∃ s : Kˣ,
      (Q.prefixQuadraticSublattice (n + 1)).refinedDeterminantUnit =
        (P.prefixQuadraticSublattice (n + 1)).refinedDeterminantUnit * s ^ 2 := by
  let F := P.prefixComponentwiseIsometry Q hk f
  have hclass := Lattice.determinantClass_eq_of_isometry F
  change Dyadic.unitSquareClass K
      (P.prefixQuadraticSublattice (n + 1)).refinedDeterminantUnit =
    Dyadic.unitSquareClass K
      (Q.prefixQuadraticSublattice (n + 1)).refinedDeterminantUnit at hclass
  obtain ⟨s, hs⟩ := BONG.GoodBONG.exists_square_mul_eq_of_unitSquareClass_eq
    (P.prefixQuadraticSublattice (n + 1)).refinedDeterminantUnit
    (Q.prefixQuadraticSublattice (n + 1)).refinedDeterminantUnit hclass
  exact ⟨s, hs.symm⟩

end Lattice.OrthogonalDecomposition

end Bong
