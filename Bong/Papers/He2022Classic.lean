/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.He2022ClassicConditions
import Bong.Bong.He2022ClassicModels
import Bong.Bong.He2022ClassicProfiles

/-!
# He: classic n-universal quadratic forms over dyadic local fields

Canonical review and distribution entry point for Zilong He, *On classic
n-universal quadratic forms over dyadic local fields*, manuscripta math. 174
(2024), 559--595.  The publisher version of record is the sole semantic
authority.

This layer formalizes the complete Theorem 1.1 proposition, classic integrality,
classic `n`-universality, classic maximality, existence of classic-maximal
over-lattices, the abstract maximal testing reduction, and the proved Section 2
BONG core through Proposition 2.10, including exact good-BONG realizations and
order profiles for every row in Definition 2.6.  It does not yet claim the
paper's explicit proof of the main BONG criterion or the minimal testing-set
classification.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The abstract classic-maximal testing reduction used before the paper's
explicit testing-family classification. -/
theorem heClassicMaximalTestingReduction
    (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat) :
    IsClassicNUniversal.{u, v, w} q L n ↔
      IsClassicIntegral q L ∧
        RepresentsAllClassicMaximalOfRank.{u, v, w} q L n :=
  isClassicNUniversal_iff_representsAllClassicMaximal q L n

end Lattice

end Bong
