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
import Bong.Bong.He2022ClassicLemma32
import Bong.Bong.He2022ClassicLemma33
import Bong.Bong.He2022ClassicLemma34
import Bong.Bong.He2022ClassicLemma35
import Bong.Bong.He2022ClassicLemma36
import Bong.Bong.He2022ClassicLemma37
import Bong.Bong.He2022ClassicLemma38
import Bong.Bong.He2022ClassicLemma39

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
two common-hyperbolic-head branches.  The pointwise branches of Lemma 3.1,
the unequal-rank nonessential-index proof of Lemma 3.2, and the first-index
defect calculation of Lemma 3.3 and the full even-index defect calculation
of Lemma 3.4 are also formalized.  The latter includes both ramification
branches and the alternating-prefix domination split.  Lemma 3.5's
mixed-prefix alternative and its quantified target-tail bounds are also
formalized.  Lemma 3.6's terminal odd-rank inequality and its explicit
Theorem 2.5(ii) endpoint are formalized as well.  Lemma 3.7's chained
terminal-defect bounds and strict source-gap consequence are formalized.
Lemma 3.8's contradiction proof for the publisher's two-defect trigger in
Theorem 2.5(iii) is formalized, with the publisher trigger kept distinct from
the older alpha-trigger formulation until Beli's equivalence hypotheses are
available.  Lemma 3.9 is formalized in both of its published parts: part (i)
constructs the truncated target BONG and transports the capped defects into
Lemma 3.8, while part (ii) proves the terminal parity contradiction through
Lemma 3.7.  Both parts retain arbitrary source tails as well as exact-rank
specializations.  The
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
