# Audit scope: Universal integral quadratic forms over dyadic local fields

## Frozen paper

- Title: *Universal integral quadratic forms over dyadic local fields*
- Author: Constantin-Nicolae Beli
- Version: [arXiv:2008.10113v2](https://arxiv.org/abs/2008.10113v2)
- Version date: 26 June 2022
- Frozen PDF length: 19 pages
- SHA-256: `35ECB7CB20A42768A6F55D80E69D4699837419854FAB021515020CCC7488986C`

## Formalization baseline

- Repository: `D:\AI-Workspace\Projects\BongTheory`
- Base commit: `3b9b0aef8e5882ea750d6e73b872af4ef9ba9044`
- Proof assistant: Lean 4.32.1
- Mathematical library: mathlib v4.32.1
- Completion audit date: 1 September 2026

The implementation remains a working-tree overlay until it is committed.  The
base commit therefore identifies the upstream baseline, not the complete
formal artifact.

## Scope

The formal scope is the paper's complete mathematical content:

1. universality, integrality, and unary-representation reductions;
2. Lemmas 2.2--2.14, Corollary 2.9, and Theorem 2.1;
3. the Jordan-coordinate criterion of Theorem 3.1;
4. Lemmas 4.1--4.9, Corollary 4.5, and Corollary 4.10;
5. every imported classification, representation, maximal-lattice, and
   cancellation result used transitively by those endpoints.

The introductory restatements of earlier Beli theorems are linked to the
separately audited 2009/2010 and 2019-v2 formalizations.  Historical,
bibliographic, and priority claims are outside formal scope.

## Achieved scope

All numbered mathematical results in the stated scope have checked Lean proof
paths and are collected by `Bong.Bong.BeliUniversalComplete`.  The public
endpoints contain no paper-specific law or data parameters.

Theorem 3.1 requires one source-fidelity qualification.  Direct substitution
of the Jordan profile into Theorem 2.1, II(b), gives coefficient `2 r_1` in
the ideal exponents of (3.2.1) and (3.2.2), whereas the frozen paper prints
`r_1`.  The formalization therefore keeps two predicates:

- `UniversalTheorem31DirectConditions`, proved equivalent to universality
  for every prescribed Jordan decomposition;
- `UniversalTheorem31Conditions`, the literal printed predicate, proved
  equivalent under the additional normalization `r_1 = 0`.

No unproved equality between these predicates is assumed.  Current paper-wide
status is **`FORMALIZATION_COMPLETE_WITH_SOURCE_DISCREPANCY`**.  Semantic
status remains **`PROVISIONAL_MATCH`** pending independent domain and Lean
review.

## Audit policy

Compilation is not semantic confirmation.  The audit separately tracks exact
definitions, quantifiers, endpoint conventions, source normalizations, theorem
coverage, kernel axioms, and reproducibility.  A result is not labelled
`VERIFIED_MATCH` until the blank review cards receive independent signatures.
