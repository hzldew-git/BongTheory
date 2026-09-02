/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.He2022ClassicConditions

/-!
# He: classic n-universal quadratic forms over dyadic local fields

Canonical review and distribution entry point for Zilong He, *On classic
n-universal quadratic forms over dyadic local fields*, manuscripta math. 174
(2024), 559--595.  The publisher version of record is the sole semantic
authority.

This layer formalizes the complete Theorem 1.1 proposition, classic integrality,
classic `n`-universality,
classic maximality, existence of classic-maximal over-lattices, and the
abstract maximal testing reduction.  It does not claim the paper's explicit
proof of that BONG criterion or the minimal testing-set classification.
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
