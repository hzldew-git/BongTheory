# Non-dyadic Remark 4.3 catalogue derivation

## Status

Checkpoint: `5194689170d3287eff67d442d62b3b5ff526cd89`.

Classification: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.

The maximal-row exhaustion and row-irredundancy clauses formerly stored in
`CatalogueLaws` are now derived theorems.  The derivation reuses the invariant
formalization of Proposition 4.2(ii) and Lemma 4.4(i) from Report 71, together
with explicit lattice-to-space transport and maximal-lattice uniqueness.

## Source bridge

The sole statement authority is Zilong He, *On n-ADC integral quadratic
lattices over algebraic number fields*, *Documenta Mathematica* 30 (2025),
no. 4, 981--1022, pp. 990--994, DOI 10.4171/DM/1003.  Publisher-PDF SHA-256:

`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Proposition 4.2(ii) classifies every positive-rank quadratic space by a
defined Table 4.7 row.  Remark 4.3 then passes this space classification to
the maximal lattices on those spaces.  Lemma 4.4(i) distinguishes the rows.
The Lean implementation preserves the positive-rank hypothesis explicitly.

## Formal derivation

`CatalogueLaws` now contains a `Proposition42Laws` package instead of a bare
`SectionFiveLaws` package.  It retains only the additional lattice-level facts
needed for the passage from quadratic spaces to integral isometry:

- maximality of each defined target row;
- transport of integral isometry to ambient-space isometry;
- uniqueness, up to integral isometry, of maximal lattices on isometric
  ambient spaces;
- existence of a maximal lattice on a prescribed ambient space and the
  same-rank maximality-transfer theorem used in Proposition 4.15; and
- the generic O'Meara 1958 representation theorem used in Lemma 4.8.

From these inputs Lean proves:

1. `CatalogueLaws.maximal_complete`: Proposition 4.2(ii) selects a defined
   row on the ambient space, target maximality and maximal-lattice uniqueness
   then give the required integral isometry;
2. `CatalogueLaws.target_irredundant`: an integral isometry is sent to an
   ambient-space isometry and Lemma 4.4(i) forces equality of both row
   parameters; and
3. the binary and general exact catalogues, Lemma 4.7(ii), Proposition 4.16,
   and the non-dyadic Theorem 1.10 now consume those derived theorems.

Neither maximal-row exhaustion nor row irredundancy is a structure field.
The earlier conclusion-field form of Proposition 4.15 was already removed in
Report 65.

## Mechanical evidence

With Lean 4.32.1 at the checkpoint above:

- the focused catalogue audit and canonical paper audit complete a 5,563-job
  build;
- `maximal_complete` and `target_irredundant` each report only `propext`;
- the binary exact catalogue reports only `propext` and `Quot.sound`;
- the general exact catalogue and assembled non-dyadic Theorem 1.10 report
  only `propext`, `Classical.choice`, and `Quot.sound`;
- the focused imported-closure axiom gate reports
  `AXIOM_GATE_PASS: 61046 declarations checked`;
- the comment-aware scanner checks 2,787 tracked Lean sources;
- all 27 CI policy tests pass;
- the paper manifest parses, every changed Lean line is at most 100 columns,
  and `git diff --check` passes.

This is local cached kernel evidence.  It is not a fresh-extraction Review Kit
receipt, GitHub exact-tag evidence, or independent human semantic approval.

## Remaining trust boundary

The result remains conditional because the repository does not yet construct
the concrete non-dyadic local field, the actual Table 4.7 lattices, their
maximality, or the maximal-lattice uniqueness and representation interfaces.
The determinant--Hasse--Hilbert invariant package from Reports 70--71 also
still needs a concrete instance.  These are proposition-valued mathematical
inputs, not Lean axioms.
