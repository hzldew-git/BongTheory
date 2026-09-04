/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.He2022ClassicConditions
import Bong.Bong.He2022ClassicModels
import Bong.Bong.He2022ClassicProfiles
import Bong.Bong.He2022ClassicLemma29
import Bong.Bong.He2022ClassicPublishedTestingSet
import Bong.Bong.He2022ClassicLemma211
import Bong.Bong.He2022ClassicLemma31

/-!
# He: classic n-universal quadratic forms over dyadic local fields

Canonical review and distribution entry point for Zilong He, *On classic
n-universal quadratic forms over dyadic local fields*, manuscripta math. 174
(2024), 559--595.  The publisher version of record is the sole semantic
authority.

This layer formalizes the complete Theorem 1.1 proposition, classic integrality,
classic `n`-universality, classic maximality, existence of classic-maximal
over-lattices, the abstract maximal testing reduction, and the proved Section 2
BONG core through Proposition 2.10, including exact good-BONG realizations,
order profiles, and alpha profiles for every row in Definition 2.6.  Lemma
2.11 is proved with its original arbitrary-ambient quantifier as well as its
two common-hyperbolic-head branches.  The
literal finite `C_e^n` indices, all three cardinality formulas of Proposition
2.8(ii), and classic integrality of every indexed row are also proved.  It
does not yet claim the paper's explicit proof of the main BONG criterion or
the minimality theorem.
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
