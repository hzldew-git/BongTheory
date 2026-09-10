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
import Bong.Bong.He2022ClassicLemma57
import Bong.Bong.He2022ClassicLemma58
import Bong.Bong.He2022ClassicTheorem51
import Bong.Bong.He2022ClassicCorollary63
import Bong.Bong.He2022ClassicCorollary63OddCounterexample
import Bong.Bong.He2022ClassicSectionSeven
import Bong.Bong.He2022ClassicLemma711
import Bong.Lattice.He2022ClassicSectionEight

/-!
# He: classic n-universal quadratic forms over dyadic local fields

Canonical review and distribution entry point for Zilong He, *On classic
n-universal quadratic forms over dyadic local fields*, manuscripta math. 174
(2024), 559--595.  The semantic authority for this formalization is the
author-corrected v5 TeX manuscript `classic_dyadic-n-uni-v5.tex`, frozen at
SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
The publisher version of record and later arXiv revision are retained as
comparison sources.

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
odd-rank Section 5 development now includes the exact conditions `J1_O`,
`J2_O`, and `J3_O`, Lemmas 5.3--5.8, the literal `C₁ⁿ(c)` and
`C₁ⁿ(c c-tilde-sharp)` tests, and the complete three-way equivalence in
Lemma 5.7 between all classic targets, those two tests, and `J2_O(n)`.  The
complete Lemma 5.8 equivalence between condition (iv), the parity-dependent
literal pair `C₁ⁿ(c), C₂ⁿ(c)`, and `J3_O(n)` is proved as well, including the
terminal determinant-class contradiction and the corrected explicit
preceding-gap premise in Corollary 3.13(iii).  Proposition 5.2 and Theorem 5.1
are assembled at their full odd-rank endpoints; necessity includes an explicit
one-rank descent for classic universality, while sufficiency reconstructs all
four revised Beli representation conditions.  The
literal finite `C_e^n` indices, all three cardinality formulas of Proposition
2.8(ii), and classic integrality of every indexed row are also proved.  The
complete Theorem 1.1 criterion, the full local rank range of Theorem 1.5,
the published even branch of Corollary 6.3, Section 7 ambient exhaustion,
Lemma 7.4 for both literal finite testing tables, the complete Lemma 7.7
boundary argument, all three clauses of Lemma 7.10, and the four odd-rank
deletion constructions of Lemma 7.11 are included as checked endpoints.  The
v5 Lemma 7.1 bridge is proved in its ambient, low-defect, ramification-one,
and exceptional `C₁(1)` branches.  In particular, every displayed row in both
parity tables has a literal deletion witness, and both tables are proved to
test classic universality.  Thus the even and odd literal-minimality halves of
Theorem 1.3 are both kernel checked.

Section 8's global--local deductions, including Proposition 8.2, the global
sentence of Theorem 1.5, Lemma 8.1, the even part of Lemma 8.3, Theorems 1.7
and 1.9, and the even part of Theorem 1.8, are proved over explicit arithmetic
proof-data packages.  Concrete number-field localization,
coefficient-transport, and strong-approximation instances remain to be
constructed, so these conditional endpoints are not
reported as full global formalizations.  Proposition 8.2 itself is derived
from lower positive-definite globalization, localization, and representation-
transport laws rather than stored as a final-conclusion field.  Theorem 1.9's
local-to-global step is likewise derived from rank and integrality
localization plus an explicit strong-approximation representation law.  The
number-field discriminant--ramification equivalence is proved for prime ideals,
including both directions, the even-discriminant witness, and positivity.  A
typed bridge transports those results to the abstract finite-place layer.  The
finite-place
sufficiency part of Theorem 1.9 is also derived from separate non-dyadic,
dyadic unary, and dyadic higher-rank laws instead of being stored as an
all-places conclusion.  The
publisher's broader Lemma 7.1(ii)
remains false when the ramification index is greater than one;
its kernel-checked counterexample is retained as a regression result.  The
author-corrected v5 replaces it by the exact `e=1` or low-defect alternatives
and adds the `C₁(1)` exceptional row when `e>1`.  Those corrected statements,
the resulting Corollary 7.2 bridge, unconditional odd Lemma 7.4, and odd
literal minimality are all proved here.  Kernel acceptance and semantic
agreement with v5 remain separate from independent human sign-off.  Moreover,
v5 Corollary 6.3 and Lemma 8.3 invoke an unsupported reduction to even `n`.
The omitted odd clause of Corollary 6.3 is in fact false: a kernel-checked
ramification-two, `n=3` counterexample is included, with nonisometry to the
diagonal lattice proved by good-BONG order invariance.  Only the even
Corollary 6.3 is retained, and the downstream affected claims remain within
the conditional Section 8 boundary documented in audit Reports 24 and 26.
Only the explicit `n ≥ 2`, even-rank parts of Lemma 8.3 and Theorem 1.8 are
exported; no unrestricted odd compatibility endpoint remains.  Reports
27--32 document these lowered interfaces and the parity scope.
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
