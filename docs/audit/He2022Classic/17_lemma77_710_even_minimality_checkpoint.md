# Lemmas 7.7 and 7.10: even minimality checkpoint

Date: 2026-09-07. Fixed code commit:
`0e48f148d67d0fa838044b249963cd9f508b4abd`. Lean: 4.32.1. The sole
semantic authority is the 37-page publisher version of record with SHA-256
`51F3626A15692E2FF0BAAE62F0EBCC4B8BEE02052C4D3CB1EA579B02E17480C1`.

## Published scope

Lemma 7.7 on journal pp. 589--590 proves all four Theorem 2.5 representation
conditions for `P2^(n+2)(Delta)` against either `C` column when `n >= 2` is
even and the determinant parameter has defect zero or one. Its proof treats
the last three defect indices and last three central indices explicitly, then
uses Corollaries 3.10--3.13 for the stable ranges.

Lemma 7.10 on journal pp. 591--592 supplies every even-rank deletion witness:

- for `e > 1`, `P2^(n+2)(Delta)` misses only `H_e^n(1)`;
- for `e = 1`, the two `P(omega)` rows miss the two exceptional `H` rows in
  opposite order;
- a large `C1` or `C2` row misses exactly its paired opposite column.

Together with Lemma 7.4, these are the even-rank testing and minimality claims
of Theorem 1.3(i),(iii).

## Formal endpoints

`Bong/Bong/He2022ClassicLemma77.lean` proves the literal source and target
profiles, formulas (7.1)--(7.5), all boundary indices, the stable-range
assembly, and the two bundled integral representation theorems
`he2022ClassicLemma77_C1_represents` and
`he2022ClassicLemma77_C2_represents`.

`Bong/Bong/He2022ClassicLemma710Exceptional.lean` proves the finite-table
specializations for `P2(Delta)` and both `P(omega)` sources, including all
exceptional representations and nonrepresentations. It packages three
literal exceptional-row deletion witnesses, covering both ramification
branches.

`Bong/Bong/He2022ClassicSectionSeven.lean` combines those witnesses with
`he2022ClassicLemma710iii_publishedC_deletionWitness`. The endpoint
`he2022ClassicLemma710_publishedEven_deletionWitness` quantifies over every
index in the literal published even table. The endpoint
`he2022ClassicTheorem13_even_literalMinimal` combines that theorem with the
proved Lemma 7.4 equivalence.

## Semantic assessment

Lemma 7.7 and Lemma 7.10 are `FULLY_FORMALIZED` with correspondence status
`PROVISIONAL_MATCH`. The even branch of Theorem 1.3, including literal
minimality, is `FULLY_FORMALIZED`; the paper-wide Theorem 1.3 remains
`PARTIAL_FORMALIZATION` because its odd branch is not complete.

The false literal Lemma 7.1(ii) is not used as an axiom or silently repaired.
Its checked counterexample and the resulting odd-branch limitation remain in
`SOURCE_DELTA.md`.

## Mechanical evidence

At the fixed code commit:

- both new modules, the Section 7 aggregator, the canonical paper entry, and
  `BongTest/He2022ClassicAudit.lean` compile locally;
- the changed-scope scanner finds no `sorry`, `admit`, project `axiom`,
  `opaque`, `unsafe`, or `native_decide` proof escape;
- every new principal endpoint reports only `propext`, `Classical.choice`,
  and `Quot.sound`.

This is not yet an exact-commit clean Review Kit or GitHub Actions result.
Those deployment gates, independent human semantic sign-off, the odd branch,
and the global applications remain open.
