# Formalization certificate draft

## Artifact identity

- Paper: Constantin-Nicolae Beli, *Universal integral quadratic forms over
  dyadic local fields*.
- Frozen source: arXiv:2008.10113v2, revised 26 June 2022.
- PDF SHA-256:
  `35ECB7CB20A42768A6F55D80E69D4699837419854FAB021515020CCC7488986C`.
- Formalization release candidate: `v0.2.0-rc.1`.
- Umbrella import: `Bong.Bong.BeliUniversalComplete`.
- Kernel audit: `BongTest.BeliUniversalAudit`.

## Machine-checked scope

The checked public endpoints cover Theorem 2.1, the arbitrary-Jordan direct
derivation of Theorem 3.1, Lemmas 4.1--4.9, Corollary 4.5(i)--(iv), and
Corollary 4.10.  Their signatures expose no project-specific law or data
parameter.  The audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Source qualification

Theorem 3.1(3.2.1--2) prints coefficient `r_1`, whereas substitution of
`R_2 = 2r_1 - u_1` and `u_1 = 0` into Theorem 2.1 gives coefficient `2r_1`.
The unconditional public endpoint uses the directly derived exponent.  A
separate endpoint proves the literal printed predicate under first fundamental
scale order zero.  This draft does not treat the difference as an
author-confirmed correction.

## Current classification

- Kernel status: **checked**.
- Coverage status:
  **`FORMALIZATION_COMPLETE_WITH_SOURCE_DISCREPANCY`**.
- Semantic-fidelity status: **`PROVISIONAL_MATCH`**.
- Project grade: **B**.

Compilation and reproducibility do not replace independent comparison with the
paper.  This draft must not be presented as `VERIFIED_MATCH` or Grade A until
the signatures below are completed by independent reviewers.

## Independent mathematical review

- Reviewer:
- Affiliation or public profile:
- Exact paper version and hash checked:
- Theorem-card decisions:
- Decision on the Theorem 3.1 coefficient:
- Reservations or exclusions:
- Date:
- Signature or immutable approval link:

## Independent Lean review

- Reviewer:
- Affiliation or public profile:
- Exact repository commit and tag checked:
- Platform and Lean/Lake versions:
- Build and audit commands:
- Trust-boundary decision:
- Reservations or exclusions:
- Date:
- Signature or immutable approval link:
