# Corollary 7.21 isometry catalogue and counts

Status: `FORMALIZED_RELATIVE_TO_CITED_COUNTING_LAW` /
`PROVISIONAL_MATCH`.

Historical-status note: report 57 at `4ad37e1` proves O'Meara 63:9 and
removes the counting-law premise from the current endpoint. The statements
below describe the exact earlier checkpoint and are retained as an audit
record.

Code checkpoint:
`bd0c9a3f66d3465cd518bae2d75386887f79d5a5` on
`feat/he-formalization`.

## Source authority and locator

The semantic authority is the published *Documenta Mathematica* version,
DOI 10.4171/DM/1003, SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.
Corollary 7.21 and its proof are printed on p. 1016. The later arXiv
revision is comparison-only.

For odd `n>=3`, the publisher states that the rank-`n+2` `n`-ADC lattices
have exactly

`(8e+6)(N p)^e`

integral-isometry classes, of which

`(8e-2)(N p)^e`

are not `O_F`-maximal. The proof counts the three top rows of Lemma 7.20(i),
the four lower rows for every `r` from `0` through `e-1`, and then removes
the single maximal overlap of Lemma 7.20(ii).

## Exact finite catalogue

`HeADC2025Corollary721Index K I` is partitioned by construction into a
maximal left summand and a nonmaximal right summand. Its pieces are:

- three top-row copies of `U`, giving `3|U|`;
- the Lemma 7.20(ii) overlap row, giving one further maximal copy of `U`;
- all four ambient rows for `r<e-1`;
- the remaining three rows at `r=e-1`.

Thus the maximal index has cardinality `4|U|`, the nonmaximal index has
cardinality `(4e-1)|U|`, and the whole index has cardinality
`(4e+3)|U|`. These three formulas are proved without the numerical
square-class count.

Every index is first proved nonexceptional and therefore denotes an inhabited
Definition 7.16 class. `model` chooses one bundled lattice from that class.
The theorem `isExactNADCIsometryCatalogue` proves all four properties needed
to interpret the publisher's phrase "up to isometry":

- every model has rank `2k+5`;
- every model is `(2k+3)`-ADC;
- every bundled `(2k+3)`-ADC lattice of rank `2k+5` is integrally isometric
  to a model;
- integrally isometric models have equal indices.

Completeness starts from an arbitrary lattice, constructs a good BONG using
the proved structural implementation, applies Remark 7.17 exhaustion, and
normalizes its ambient space to a published odd row. Irredundancy uses Lemma
7.15 to recover the penultimate order and the proved published ambient-row
classification to recover the remaining index. No caller-supplied BONG or
classification law occurs in these public conclusions.

## Maximal versus nonmaximal classes

`model_isOMaximal_iff` proves that a model is `O_F`-maximal exactly when its
index lies in the left summand. The three top rows are maximal by the proved
endpoint criterion. The lower maximal row is identified with the named
second-column maximal lattice from Lemma 7.20(ii).

For the converse, `lower_maximal_index_characterization` shows that a maximal
class below the top row must have `r=e-1`, second column, and a unit parameter.
The proof derives the ambient second-column model from Theorem 7.2's overlap,
then uses maximal-lattice uniqueness and Lemma 7.15 to recover `r=e-1`.
This excludes every index in the right summand and proves the claimed
nonmaximal count is a count of actual lattice classes, not merely table rows.

## Numerical square-class boundary

The substitution

`|U| = 2(N p)^e`

is cited by the publisher from O'Meara 63:9. It is represented by the explicit
proposition-valued class `HeADC2025Corollary721CountingLaw`. No proved generic
instance for this arithmetic cardinality theorem is currently present.

Under that visible premise, `card_index_published` and
`card_nonmaximalIndex_published` prove exactly the two printed formulas, and
`heADC2025Corollary721` packages them with the exact catalogue and maximality
partition. Consequently, the classification, irredundancy, and counts in
terms of `|U|` are unconditional inside the current dyadic interface, while
the final residue-norm formulas remain conditional on the cited external
counting theorem. Kernel acceptance does not discharge this explicit premise.

## Statement-strength verdict

The catalogue and maximality partition are `LOGICALLY_EQUIVALENT` to the
classification content used in the published count. The parameterization
`n=2k+3` is exactly the source domain of odd `n>=3`, and the rank is literally
`n+2=2k+5`. Isometry always means integral lattice isometry.

The numerical wrapper is a `PROVISIONAL_MATCH` relative to the exact
O'Meara 63:9 cardinality statement. It is not an unconditional proof of that
cited result. Human confirmation of the row accounting and the cited
cardinality normalization remains pending.

## Trust and mechanical evidence

At the stated checkpoint:

- `He2023ADCCorollary721.lean`, the canonical paper entry, and the complete
  paper audit compile directly with Lean 4.32.1;
- seven selected dependency reports contain exactly `propext`,
  `Classical.choice`, and `Quot.sound`;
- the focused transitive gate reports
  `AXIOM_GATE_PASS: 59853 declarations checked`;
- the comment-aware scanner checks 2,742 tracked Lean sources and finds no
  forbidden proof token outside comments;
- the scoped 100-column check and `git diff --check` pass.

The warnings about locally modified `mathlib`, `aesop`, and `batteries`
dependency worktrees were pre-existing and were not edited. Exact-revision
clean Review Kit CI, release packaging, proof of the cited counting law, and
human semantic approval remain separate gates. Section 7 now has nineteen
fully formalized items, one source-quantifier mismatch in Lemma 7.13, and this
one result formalized relative to its cited numerical input.
