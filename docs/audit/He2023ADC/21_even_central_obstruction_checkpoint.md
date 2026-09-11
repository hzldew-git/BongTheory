# Lemma 6.6: exact central representation obstructions

Date: 2026-09-05. Authority: Zilong He, *On n-ADC integral quadratic
lattices over algebraic number fields*, Doc. Math. 30 (2025), Lemma 6.6,
pp. 1000--1001. Publisher PDF SHA-256:
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

## Frozen scope and verdict

| Frozen commit | Scope | Independent AI assessment |
|---|---|---|
| `1e9ba63818ea4f0df72426b710f1f020af51be50` | Three capped-trigger support lemmas | Correct trigger argument only |
| `e8e1188ed7ad69c163914e6a1ac62eff96ca3486` | Five prefix-space support lemmas | Correct parity, raw-defect and non-representation arguments |
| `cd8ecbddef7b18979cfabcc1b1ba0afd640268cb` | Actual-target profile and both numbered endpoints | `FULLY_FORMALIZED` / `PROVISIONAL_MATCH` |

The aggregate assessment covers 2/2 clauses of one numbered lemma. It does
not cover Lemma 6.7 or Theorem 6.2. Section 6 now has complete local proofs
for 4/12 numbered items: Theorem 6.1 and Lemmas 6.4--6.6. Human semantic
approval, exact-revision clean-kit CI and release promotion remain pending.

## Paper and formal statements

Let n=2k+2 and m=n+2. The source is an integral dyadic lattice with a good
BONG, whose first n orders alternate 0,-2e. Assume R_(n+2) >= 2-2e and
the capped adjacent defect d[-a_(n+1,n+2)] > 1-R_(n+2).

| Clause | Additional alternative | Actual target | Public endpoint |
|---|---|---|---|
| (i), n >= 2 | R_(n+1) even, or raw signed-prefix defect 2e | N_2^n(Delta) | `Bong.BONG.GoodBONG.heADC2025Lemma66i` |
| (ii), n >= 4 | R_(n+1) even, or raw signed-prefix defect infinity | N_2^n(1) | `Bong.BONG.GoodBONG.heADC2025Lemma66ii` |

Each formal endpoint accepts any good BONG on any integral-isometric copy
of the specified target. It concludes the literal published trigger at
i=n+1 and the negation of its required prefix-space representation:

    [b_1,...,b_n] does not embed into [a_1,...,a_(n+1)].

The conjunction is exactly failure of Theorem 3.6(iii) at that point. It is
not replaced by mere lattice non-representation or failure of an equivalent
whole-package criterion. Report 20 records why the published defect trigger,
rather than the older auxiliary-alpha trigger, is used here.

Primary statement relationship: `LOGICALLY_EQUIVALENT`. No ambient or
lattice representation, target profile, determinant separation, next-order
zero condition or custom mathematical law is assumed. Source and target
integrality match the paper's standing convention; the target condition
also follows from its isometry with the named maximal lattice. The public
endpoints use the common universe for K, V and W.

## Proof fidelity

The target profile is derived from the actual published Lemma 4.11(ii)
criteria. All its adjacent pairs have gap -2e, including the raised final
pair (1,1-2e). The full signed source and target prefixes therefore have
capped defects at least 2e; self-prefix domination cancels the two equal
signs and proves d[a_(1,n)b_(1,n)] >= 2e.

Combining that bound with the capped adjacent hypothesis gives the strict
current mixed-defect bound. The previous mixed defect is nonnegative.
Together with S_n=1-2e<R_(n+2), these are precisely the two strict
inequalities in the published trigger. The source cap alpha_n is retained
when needed; full-end caps are omitted only where the definition requires.

For even R_(n+1), proved Proposition 2.7(v) supplies an actual hyperbolic
tower plus valuation-unit line. It requires evenness, not order zero.
The specified first-column even space embeds in this odd normal form.
For the raw-defect alternative, infinity selects the square class, while
finite defect 2e excludes it and selects the Delta class. The proved
equal-determinant endpoint-tower theorem is used only after pair classes
and common leading scale are established. The first n coordinates embed
into the first n+1 coordinates.

The proved same-parameter exactly-one theorem then excludes W_2^n(mu)
from that odd prefix. An actual lattice isometry and exact BONG
diagonalization transport the exclusion to the arbitrary target BONG.
The transport direction is W_2^n(mu) to the target's full diagonalization,
then hypothetically to the source prefix. Matching determinants alone is
never substituted for this space identification.

## Boundary, trust and independent review

At n=2, both full even prefixes have one pair. No nonexistent S_0 is used.
The Delta target is defined and the prefix exclusion is binary-to-ternary.
The square second-column target is genuinely undefined at n=2; `0 < k`
in clause (ii) is exactly the paper's n >= 4 restriction. At e=1 the
cross-order inequality remains strict. Raw and capped defects are kept
separate, including infinity in the square alternative.

The separate read-only reviewer independently re-elaborated each frozen
module, the canonical entry and the complete ADC audit. All 12 new
support/endpoint transitive axiom sets are exactly `propext`,
`Classical.choice`, and `Quot.sound`. No incomplete proof, custom axiom,
native solver, circular dependency or assumed classification result was
found. Established Beli and He--Hu results are intentionally reused.

## Author review card

Paper and formal statement: the two exact obstruction clauses above.
Definitions requiring confirmation: the capped adjacent defect, the raw
signed-prefix defect, the one-based central index and space representation.
No difference in assumptions, quantifier order, logical conclusion or
defined low-rank objects was found by the independent AI review.

Author question: confirm that failure at i=n+1 means the trigger together
with failure of the displayed prefix representation. Domain-expert
question: review the common-parameter first/second exclusion and the
binary Delta case. Formalization-expert question: review the alpha caps,
exact-diagonalization transport and internally derived target profile.

Author decision, name, date and signature: not supplied. Human domain-
expert and formalization-expert approvals: not supplied. The provisional
AI verdict is not human sign-off and does not justify `VERIFIED_MATCH`.

## Reproducibility and deployment

Lean 4.32.1 and the committed Lake lock remain fixed. All local checks
used existing dependencies; modified mathlib, aesop and batteries worktrees
were preserved. These checks are not a clean environment certificate.
The local Theorem 6.1 kit at `a734545` predates all three modules above;
the remote published-profile artifact is older still. Neither certifies
this lemma. A fresh source-only package and exact-revision clean-kit run
remain required. Whole-paper grade: C; verdict: `NOT_COMPLETE`.
