# Section 8 class-number-one regularity derivation

Status: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.

Code checkpoint:
`4ccd9fabf788cc3a8b6a04bb03049409f0bee696` on
`feat/he2023adc-continuation`.

## Source authority and locator

The semantic authority is Zilong He, *On n-ADC integral quadratic lattices
over algebraic number fields*, *Documenta Mathematica* 30 (2025), no. 4,
981--1022, DOI 10.4171/DM/1003. The audited publisher PDF has SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Lemma 8.1 and its proof are on publisher page 1017. The proof opens with the
sentence that class number one makes `M` `n`-regular, and then applies
Theorem 1.3. The later arXiv revision is comparison-only.

## Formal change

The earlier `SectionEightLaws` interface stored the complete implication

```text
HasClassNumberOne M -> IsNRegular M n
```

as one proposition-valued field. The new
`ClassNumberRegularityLaws` interface instead records only the two lower-level
facts used by the standard genus argument:

1. if `N` is locally represented by `M` at every finite place, with the
   required rank and integrality hypotheses, then some lattice `M'` in the
   genus of `M` globally represents `N`;
2. global representation transports from an isometric source lattice.

The theorem
`ClassNumberRegularityLaws.classNumberOne_implies_nRegular` now proves the
published implication. It chooses the genus representative `M'`, uses class
number one to identify `M'` with `M`, and transports the representation.
`SectionEightLaws.classNumberOne_implies_nRegular` is a compatibility endpoint
derived from that proof, and Lemma 8.1(i) consumes the derived theorem.

Thus no `SectionEightLaws` field now states class-number-one regularity as a
final conclusion.

## Mechanical evidence

The following focused command succeeds with Lean 4.32.1:

```text
lake build BongTest.He2023ADCClassNumberRegularityAudit
```

The build completes four jobs. Its three explicit axiom reports state that
the lower-level regularity theorem, the Section 8 compatibility endpoint, and
Lemma 8.1(i) depend on no axioms. The canonical audit also exposes both new
declarations. No `sorry`, `admit`, custom `axiom`, native evaluation, or
external solver occurs in the changed source or audit file.

## Fidelity boundary

This checkpoint formalizes the logical genus argument, not its concrete
number-field arithmetic. A future unconditional implementation must construct
`ClassNumberRegularityLaws` for actual integral quadratic lattices over every
algebraic number field. In particular, the genus-lifting theorem and
isometry-transport theorem remain explicit proposition-valued inputs.

This is a strictly lower conditional boundary than the former final-conclusion
field, but it does not change the whole-paper Grade-D status, discharge the
other `SectionEightLaws` fields, provide human semantic approval, or constitute
an exact clean Review Kit receipt.
