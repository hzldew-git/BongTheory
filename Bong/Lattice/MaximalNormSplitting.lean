/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Jordan

/-!
# Maximal norm splittings

This file formalizes Beli (2003), Definitions 7 and 8.  We use the equivalent
order inequalities in the remark following Definition 8; this avoids the
paper's auxiliary notation `n L^s` while retaining its exact mathematical
content.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/--
A maximal norm splitting in the sense of Beli (2003), Definition 8.

Each component is unary or modular binary.  The scales occur in
nondecreasing order, and the norm gaps satisfy the equivalent inequalities
from the remark following the definition.
-/
structure MaximalNormSplitting (q : QuadraticSpace K V)
    (L : Lattice K V) (t : Nat) extends OrthogonalDecomposition q L t where
  /-- A chosen generator of the scale ideal of each component. -/
  scaleGenerator : Fin t → Kˣ
  /-- A chosen generator of the norm ideal of each component. -/
  normGenerator : Fin t → Kˣ
  /-- The selected elements generate the component scale ideals. -/
  scaleIdeal_eq : ∀ i,
    scaleIdeal (component i).space (component i).lattice =
      principalIdeal (K := K) (scaleGenerator i : K)
  /-- The selected elements generate the component norm ideals. -/
  normIdeal_eq : ∀ i,
    normIdeal (component i).space (component i).lattice =
      principalIdeal (K := K) (normGenerator i : K)
  /-- Every component is unary or modular binary. -/
  unary_or_modular_binary : ∀ i,
    finrank K (component i).carrier = 1 ∨
      (finrank K (component i).carrier = 2 ∧
        IsModular (component i).space (component i).lattice
          (scaleGenerator i))
  /-- Component scales are ordered as in Definition 8. -/
  scaleOrder_mono : ∀ {i j : Fin t}, i < j →
    ordUnit K (scaleGenerator i) ≤ ordUnit K (scaleGenerator j)
  /-- The equivalent norm-gap inequalities from the remark after Definition 8. -/
  normGap_bounds : ∀ {i j : Fin t}, i < j →
    0 ≤ ordUnit K (normGenerator j) - ordUnit K (normGenerator i) ∧
      ordUnit K (normGenerator j) - ordUnit K (normGenerator i) ≤
        2 * (ordUnit K (scaleGenerator j) -
          ordUnit K (scaleGenerator i))

namespace MaximalNormSplitting

variable {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The rank of one component of a maximal norm splitting. -/
noncomputable def componentRank (M : MaximalNormSplitting q L t)
    (i : Fin t) : Nat :=
  finrank K (M.component i).carrier

/-- Every component has rank one or two. -/
theorem componentRank_eq_one_or_two (M : MaximalNormSplitting q L t)
    (i : Fin t) : M.componentRank i = 1 ∨ M.componentRank i = 2 := by
  rcases M.unary_or_modular_binary i with h | h
  · exact Or.inl h
  · exact Or.inr h.1

/-- Every component has positive rank. -/
theorem componentRank_pos (M : MaximalNormSplitting q L t)
    (i : Fin t) : 0 < M.componentRank i := by
  rcases M.componentRank_eq_one_or_two i with h | h
  · omega
  · omega

/-- Every component has rank at most two. -/
theorem componentRank_le_two (M : MaximalNormSplitting q L t)
    (i : Fin t) : M.componentRank i ≤ 2 := by
  rcases M.componentRank_eq_one_or_two i with h | h
  · omega
  · omega

/-- A property-A Jordan splitting is a maximal norm splitting. -/
noncomputable def ofJordanPropertyA (J : JordanDecomposition q L t)
    (hJ : J.HasPropertyA) : MaximalNormSplitting q L t where
  toOrthogonalDecomposition := J.toOrthogonalDecomposition
  scaleGenerator := J.scaleGenerator
  normGenerator := J.normGenerator
  scaleIdeal_eq := J.scaleIdeal_eq
  normIdeal_eq := J.normIdeal_eq
  unary_or_modular_binary := by
    intro i
    rcases hJ.1 i with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, J.modular i⟩
  scaleOrder_mono := by
    intro i j hij
    exact (J.scaleOrder_strict hij).le
  normGap_bounds := by
    intro i j hij
    have h := hJ.2 hij
    exact ⟨h.1.le, h.2.le⟩

@[simp]
theorem ofJordanPropertyA_component
    (J : JordanDecomposition q L t) (hJ : J.HasPropertyA) (i : Fin t) :
    (ofJordanPropertyA J hJ).component i = J.component i :=
  rfl

@[simp]
theorem ofJordanPropertyA_scaleGenerator
    (J : JordanDecomposition q L t) (hJ : J.HasPropertyA) (i : Fin t) :
    (ofJordanPropertyA J hJ).scaleGenerator i = J.scaleGenerator i :=
  rfl

@[simp]
theorem ofJordanPropertyA_normGenerator
    (J : JordanDecomposition q L t) (hJ : J.HasPropertyA) (i : Fin t) :
    (ofJordanPropertyA J hJ).normGenerator i = J.normGenerator i :=
  rfl

end MaximalNormSplitting

end Lattice

end Bong
