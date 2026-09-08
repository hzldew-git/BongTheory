# Binary main-theorem correction and exact count

Status: `PUBLISHED_STATEMENTS_REFUTED_AND_CORRECTED`.

Historical-status note: report 57 at `4ad37e1` proves O'Meara 63:9 and makes
the current corrected count and source refutation unconditional. References
below to a visible counting premise describe this earlier checkpoint.

Code checkpoint:
`f7e8fb7e1b8d43b66a62e500f61f7eeba004f136` on
`feat/he-formalization`.

## Source authority and locators

The semantic authority is the published *Documenta Mathematica* version,
DOI 10.4171/DM/1003, SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.
Theorem 1.9 is printed on p. 985 and Theorem 1.10 on p. 986. Their proof on
p. 1017 invokes the even-rank Theorem 1.9(ii), which in turn is obtained
from Theorem 6.2. The later arXiv revision is comparison-only.

For `n=2`, Theorem 1.9(ii) lists only maximal rank-four lattices and the
exceptional nonmaximal class in `W_1^4(Delta)`. Theorem 1.10 consequently
prints the binary count

`8 * (N p)^e + 1`.

The already verified second-discriminant lattice in `W_2^4(Delta)` is an
additional nonmaximal 2-ADC integral-isometry class. Thus these are
downstream manifestations of the same omitted binary class already recorded
for Lemma 6.8(iv) and Theorem 6.2.

## Corrected finite catalogue

`HeADC2025QuaternaryCatalogue.Index U` is the disjoint sum of:

- the four published maximal rank-four rows, each indexed by `U`; and
- two Boolean-indexed nonmaximal models: the exceptional class and the
  second-discriminant boundary class.

The theorem `isExactIsometryCatalogue` proves that every entry has rank four
and is 2-ADC, every rank-four 2-ADC lattice is integrally isometric to an
entry, and integrally isometric entries have equal indices. Irredundancy uses
maximality to separate the four published rows from the two boundary models,
and the proved nonisometry of their ambient spaces to separate the two
nonmaximal classes.

`model_isOMaximal_iff` proves that maximality is exactly membership in the
published-table summand. Consequently `card_index` proves the unconditional
intermediate count

`4 * |U| + 2`.

Under the same explicit O'Meara 63:9 counting law used by the paper,
`card_index_corrected` gives

`8 * (N p)^e + 2`.

## Literal source refutations and correction

The formalization freezes the printed binary statements before refuting
them:

- `not_heADC2025Theorem19iiBinaryStatement` proves that the binary
  specialization of Theorem 1.9(ii) is false;
- `not_heADC2025Theorem110BinaryCountStatement` proves that the printed
  `+1` count is false under the paper's own counting input; and
- the earlier `not_heADC2025Theorem62BinaryStatement` records the identical
  classification failure in Theorem 6.2.

The separate theorem `heADC2025Theorem19ii_binary_corrected` proves the exact
three-way biconditional: maximal, the first-discriminant exception, or the
second-discriminant boundary class. The bundled endpoint
`heADC2025Theorems19iiAnd110BinaryCorrected` packages that classification,
the exact catalogue, and the corrected numerical count. The publisher text
is never silently replaced by the repaired statement.

## Trust and mechanical evidence

At the stated checkpoint, the new catalogue module, canonical paper entry,
and expanded paper audit compile directly with Lean 4.32.1. Selected
dependency reports for the catalogue, completeness, irredundancy,
maximality partition, source refutations, and corrected endpoints contain
exactly `propext`, `Classical.choice`, and `Quot.sound`. The numerical result
retains `HeADC2025Corollary721CountingLaw` as a visible theorem premise; it is
not a Lean axiom or a proved repository instance.

Exact-revision clean Review Kit CI, author/publisher confirmation of the
source correction, and independent human semantic approval remain separate
gates.
