/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.HeHu2022Conditions
import Bong.Bong.HeHu2022SectionTwo
import Bong.Bong.HeHu2022Lemma211
import Bong.Bong.HeHu2022SectionThreeSharp
import Bong.Bong.HeHu2022SectionThreeBinary
import Bong.Bong.HeHu2022SectionThreeSpaces
import Bong.Bong.HeHu2022Proposition35iii
import Bong.Bong.HeHu2022Definition36
import Bong.Bong.HeHu2022Lemma39
import Bong.Bong.HeHu2022Lemma310
import Bong.Bong.HeHu2022Lemma311
import Bong.Bong.HeHu2022Lemma313
import Bong.Bong.HeHu2022AmbientRank
import Bong.Bong.HeHu2022Lemma314
import Bong.Bong.HeHu2022Proposition37
import Bong.Bong.HeHu2022SectionFour
import Bong.Bong.HeHu2022Lemma42
import Bong.Bong.HeHu2022Lemma43
import Bong.Bong.HeHu2022Lemma44
import Bong.Bong.HeHu2022Lemma45
import Bong.Bong.HeHu2022Theorem41
import Bong.Bong.HeHu2022Corollary46
import Bong.Bong.HeHu2022Theorem47
import Bong.Bong.HeHu2022SectionFive
import Bong.Bong.HeHu2022Lemma57
import Bong.Bong.HeHu2022Lemma58
import Bong.Bong.HeHu2022Lemma59
import Bong.Bong.HeHu2022Lemma510
import Bong.Bong.HeHu2022Lemma511
import Bong.Bong.HeHu2022Proposition55
import Bong.Bong.HeHu2022Theorem51
import Bong.Bong.HeHu2022Theorem53
import Bong.Bong.HeHu2022SectionSix
import Bong.Bong.HeHu2022Theorem11
import Bong.Bong.BeliUniversalMaximal

/-!
# He--Hu: n-universal quadratic forms over dyadic local fields

This is the canonical review and distribution entry point for Zilong He and
Yong Hu, *On n-universal quadratic forms over dyadic local fields*, Sci. China
Math. 67 (2024), 1481--1506.

The implementation name records the work's 2022 provenance, while the
publisher version of record (2024) is the sole semantic authority.  The
  Theorem 1.1 criterion is proved at its exact arbitrary-source-rank
  statement in `HeHu2022Theorem11`.  Direct endpoints for Definition 2.4, Lemma 2.2,
  Corollary 2.3, Propositions 2.5--2.7, Theorem 2.8, and Lemmas 2.9--2.11 are
  supplied by the Section 2 modules.  Definition 3.1 and Propositions 3.2--3.3
  are supplied by the first two Section 3 modules.  Definition 3.4 and all
  three clauses of Proposition 3.5, including the unique excluding-space
  assertion and its exceptional binary case, are proved by the space and
  codimension-two modules. Definition 3.6 is realized by canonical maximal
  representatives in each displayed space. Lemma 3.10 is proved by an exact
  recursive good-BONG construction on the literal half-hyperbolic tower.
  Lemma 3.11 is proved for every Table 2 row: its even- and odd-rank
  alternatives retain the published endpoint blocks and compute every
  displayed `R_i` order, including the exceptional `2-2e` penultimate term.
  Proposition 3.7 is proved for every Table 2 row.  The three critical
  volume endpoints are discharged by the published Table 1 space
  classification: the binary case uses the two nonisometric determinant
  classes, while the ternary and quaternary cases contradict anisotropy of
  the displayed candidate spaces.
  The Section 4 module fixes the exact `I1^E`, `I2^E`, and `I3^E`
  conditions, proves the generic Theorem 2.8 universality factorization, and
  proves the complete invariant conversion used in Theorem 4.7.  Lemma 4.2
  is proved in both directions: its necessity uses the literal
  `N_1^n(1)` and `N_1^n(Delta)` models and their separated determinant
  square classes, while its sufficiency uses a deep same-rank completion.
  Lemma 4.3 is proved with the literal `N_2^n(Delta)` target: both strict
  defect conclusions and the terminal nonrepresentation assertion are
  checked through the Proposition 2.7(v) and Lemma 3.14(i) normal forms.
  Lemma 4.4 is proved in both directions: necessity specializes to that
  literal target, while sufficiency treats every integral even-rank target,
  including both terminal-order branches. Lemma 4.5 is likewise proved in
  both directions, including the exceptional binary defect branch.  The three
  component equivalences are assembled into the proved even-rank Theorem 4.1
  endpoint in `HeHu2022Theorem41`.
  Section 5 currently includes the exact odd-rank conditions, Remark 5.2,
  and Lemmas 5.4 and 5.6--5.9.  Lemma 5.7 uses the literal
  `N_2^3(delta*pi)` test BONG, proves its revised central trigger, and proves
  the required source prefix does not represent it. Lemma 5.8 constructs the
  published sharp unit with its exact complementary defect. Lemma 5.9 uses
  the two literal first-column tests, proves both numerical triggers, and
  proves that their representations cannot coexist, hence condition (iii')
  fails for at least one test. Lemma 5.10 is proved in all three directions:
  it retains both literal first-column tests and the existential exceptional
  ternary test, reduces nonterminal indices to Lemma 4.4, and checks both
  terminal alpha branches through Lemmas 2.11, 5.4, and 3.14.
  Lemma 5.11 is also proved in all three directions.  Its second-column
  test is constructed separately in the even- and odd-valuation rows of
  Table 1, its terminal large-gap implication uses the exact threshold
  `G_n`, and the reverse contradiction is the codimension-two exclusive
  representation statement of Lemma 3.13.  Proposition 5.5 now assembles
  the five even-prefix and odd-boundary conditions, with the paper's implicit
  descent from `n`-universality to `(n-1)`-universality proved by adjoining
  an integral unit line.  Theorems 5.1 and 5.3 are direct proved endpoints;
  the latter also proves both parenthetical equivalences in its first case.
  Section 6 is complete: Lemma 6.1 eliminates the even boundary alpha by an
  explicit finite-minimum calculation (including equation (6.1)); Corollary
  6.2 identifies Theorem 1.1(i),(iii)(1) with `I1^O`; and Lemma 6.3 expands
  `alpha_(n+2) <= G_n` into both printed parity rows of
  Theorem 1.1(iii)(2).
  The ambient-space rank classification used in Corollary 4.6, Theorem 4.7,
  and Theorem 1.1 is also proved: the stable range is exactly `m >= n+3`,
  apart from the published binary/quaternary `H perp H` exception.
  All three clauses of Lemma 3.9 are proved by exact good-BONG models; in
  particular clause (iii) retains the published coefficient list
  `<delta*kappa#, -delta*kappa#*kappa*pi^(2-2e), delta*kappa>`.
  Lemmas 3.13--3.14 are proved by the explicit determinant--Hasse and Table 1
  comparison modules. Corollary 4.6, Theorem 4.7, and the complete
  Theorem 1.1 equivalence (including impossible small source ranks) are
  checked endpoints.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The maximal-lattice testing reduction underlying the testing-set result
of He--Hu.  This is not the paper's explicit list or its minimality proof. -/
theorem heHuMaximalTestingReduction
    (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat) :
    IsNUniversal.{u, v, w} q L n ↔
      IsIntegral q L ∧ RepresentsAllOMaximalOfRank.{u, v, w} q L n :=
  beliUniversalLemma41 q L n

end Lattice

end Bong
