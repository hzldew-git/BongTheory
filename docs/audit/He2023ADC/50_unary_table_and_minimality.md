# Unary table and minimality checkpoint

## Source authority and scope

The sole semantic authority is the publisher version of record, pp. 990--994.
Definition 4.1 leaves only the first column in rank one. Proposition 4.2 then
states table exhaustion and the unique rank-three space representing every
unary space except a selected one. Remark 4.3 counts the unary maximal
lattices, and Lemma 4.9(ii) asserts minimality of the resulting universality
testing set for every `n >= 1`.

This checkpoint formalizes exactly the dyadic rank-one boundary. It does not
extend the result to non-dyadic fields and does not reconstruct the cited
O'Meara 63:9 unit-square-class count.

## Source-to-formal correspondence

| Publisher content | Formal endpoint | Status |
|---|---|---|
| Definition 4.1, unary `W_1^1(c)` and `N_1^1(c)` | `HeADC2025PublishedUnaryTestingIndex`, `.parameter`, `.model` | `LOGICALLY_EQUIVALENT` in the dyadic scope |
| Proposition 4.2(ii), unary exhaustion | `QuadraticLatticeModel.exists_heADC2025PublishedUnaryIndex_for_model` | `LOGICALLY_EQUIVALENT` in the dyadic scope |
| Proposition 4.2(iii), unique excluding ternary space | `QuadraticLatticeModel.heADC2025Proposition42iiiUnary` | `LOGICALLY_EQUIVALENT` in the dyadic scope |
| Remark 4.3, unary count before cited substitution | `heADC2025Remark43UnaryCard` | unconditional exact count `2 * |U|` |
| Remark 4.3, printed count | `heADC2025Remark43UnaryCardPublished` | `FORMALIZED_RELATIVE_TO_CITED_COUNTING_LAW` |
| Lemma 4.9(ii), rank-one boundary | `QuadraticLatticeModel.heADC2025Lemma49iiUnary` | literal deletion-minimality proved |

## Proof mechanics and boundary checks

The index is the disjoint pair of unit square-class representatives and their
uniformizer multiples. Completeness first diagonalizes an arbitrary rank-one
model and then normalizes its coefficient into this finite family. If two
indices give ambiently isometric unary spaces, the determinant square-class
invariant and representative-system irredundancy force equality of indices.

For a selected parameter `c`, the witness is the actual maximal lattice on
`W_2^3(c)`. Proposition 4.2(iii) proves that it misses `W_1^1(c)` and
represents every other unary square class. This supplies a witness after
deleting each individual table row, so the theorem proves literal
deletion-minimality rather than minimality only after quotienting duplicate
presentations.

The finite index has cardinality `2 * |U|`. Substitution of
`|U| = 2 * (N p)^e` gives the publisher's `4 * (N p)^e`; that substitution
is exposed as `HeADC2025Corollary721CountingLaw`, an ordinary theorem premise.
It is not a Lean axiom and no generic repository proof of O'Meara 63:9 is
claimed.

## Mechanical evidence

At exact code revision `da6fbd41a4dc0323380b1013283bd20f9fa6b729`,
`He2023ADCUnaryTesting.lean`, the canonical paper entry, and the expanded
paper audit compile with Lean 4.32.1. The canonical entry completed 5,032
build jobs. Six selected dependency reports contain exactly `propext`,
`Classical.choice`, and `Quot.sound`. The focused transitive gate reports
`AXIOM_GATE_PASS: 60154 declarations checked`; the scoped forbidden-token,
100-column, and `git diff --check` checks pass across the changed sources.
There are 2,755 tracked Lean sources at this checkpoint.

These are local checks at the exact code commit. A fresh Review Kit for this
later revision, GitHub-hosted CI, artifact upload, and independent human
semantic approval remain separate gates.

## Audit verdict

The dyadic unary table, its exhaustion and unique excluding space, its exact
`2 * |U|` count, and the rank-one case of Lemma 4.9(ii) are
`FULLY_FORMALIZED` with semantic status `PROVISIONAL_MATCH`. The printed
residue-norm count remains conditional on the explicitly named cited input.
Whole-paper verdict: `NOT_COMPLETE`. Whole-paper grade: D, unchanged because
the previously identified publisher mismatches remain.
