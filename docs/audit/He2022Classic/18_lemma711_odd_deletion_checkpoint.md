# Lemma 7.11: odd-table deletion checkpoint

Date: 2026-09-07. Fixed code commit:
`404b410bc8381dd999b97374a33bdca5a3c0c07d`. Lean: 4.32.1. The sole
semantic authority is the 37-page publisher version of record with SHA-256
`51F3626A15692E2FF0BAAE62F0EBCC4B8BEE02052C4D3CB1EA579B02E17480C1`.

## Published scope

Lemma 7.11 on journal p. 592 supplies an odd-rank deletion witness for every
row in the two-column testing table. For a deleted first-column row, its
auxiliary larger lattice is formed by adjoining the displayed ternary tail;
for a deleted second-column row, the opposite large row is used. The proof
then combines the unique codimension-two excluded space from Lemma 3.15(ii)
with Proposition 3.5(iii) to show that the auxiliary lattice represents every
other row and misses the selected one.

## Formal endpoints

`Bong/Bong/He2022ClassicLemma711.lean` constructs the literal auxiliary
coefficient rows, proves their good-BONG and classic-integrality profiles,
and establishes all four parity-sensitive excluding-space comparisons. It
then derives the integral representation of every nondeleted row through the
published representation criterion.

The table map is proved injective at the diagonal-representation level, so a
distinct finite index really denotes a different target isometry class. The
unified endpoint
`he2022ClassicLemma711_publishedOdd_deletionWitness` quantifies over every
index of `HeClassicPublishedOddTestingIndex` and returns a classic-integral
lattice which misses exactly that row among the literal published family.

## Semantic boundary

The deletion/irredundancy half of Lemma 7.11 is `FULLY_FORMALIZED` with
correspondence status `PROVISIONAL_MATCH`. This result does not use the false
literal Lemma 7.1(ii), and therefore remains valid independently of the
publisher's obstructed odd-rank sufficiency chain.

This checkpoint does **not** promote the odd table to a universality testing
family. Lemma 7.4's odd testing implication, and hence the odd full-minimality
claim in Theorem 1.3, still require a valid replacement for that chain. The
distinction between row-by-row deletion and testing sufficiency is retained in
the canonical module and manifest.

## Mechanical evidence

At the fixed code commit:

- `Bong.Bong.He2022ClassicLemma711` and `Bong.Papers.He2022Classic` build from
  source;
- `BongTest/He2022ClassicAudit.lean` checks the new public declarations;
- the scoped scanner finds no `sorry`, `admit`, project `axiom`, `opaque`,
  `unsafe`, or `native_decide` proof escape;
- the principal new endpoints report only `propext`, `Classical.choice`, and
  `Quot.sound`.

An exact-commit clean Review Kit, GitHub Actions result, and release asset are
separate deployment gates and are not claimed by this local checkpoint.
