# Theorem 8.2 definite/indefinite derivation

Status: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.

Code checkpoint:
`4565c1218a12d3603bb35d8dc985fcfa2335ef27` on
`feat/he2023adc-local-maximality`.

## Source authority and locator

The semantic authority is Zilong He, *On n-ADC integral quadratic lattices
over algebraic number fields*, *Documenta Mathematica* 30 (2025), no. 4,
981--1022, DOI 10.4171/DM/1003. The audited publisher PDF has SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Theorem 8.2 and its proof are on publisher page 1017. The definite case is
attributed to Meyer, Theorem 5.2. In the indefinite case, the proof invokes
Xu, Theorem 1.5 prime, to choose a rank-`n` sublattice represented by only one
spinor genus in `gen(M)`, and then O'Meara 104:5 to conclude that this spinor
genus contains only one integral isometry class. Corollary 8.3 applies the
result across pages 1017--1018.

## Formal change

The earlier `SectionEightLaws` interface stored the complete conclusion
`HasDistinguishingRankSublattice M n` as the field
`distinguishing_rank_sublattice`. That final-conclusion field has been
removed.

`HeADC2025GlobalData` now records definite lattices and spinor-genus
membership explicitly. The new `DistinguishingSublatticeLaws` package
separates exactly three external inputs:

1. Meyer's definite-case distinguishing-sublattice theorem;
2. Xu's indefinite construction of a rank-`n` represented sublattice whose
   representing lattices in the genus lie in the same spinor genus;
3. O'Meara 104:5 in the form that same-spinor-genus indefinite lattices of
   the relevant rank are integrally isometric.

`DistinguishingSublatticeLaws.distinguishing_rank_sublattice` performs the
definite/indefinite split. In the indefinite branch it obtains Xu's lattice,
uses the uniqueness property to put any competing genus representative in
the same spinor genus, and applies the O'Meara input. The
`SectionEightLaws` compatibility endpoint and `heADC2025Theorem82` consume
this derived theorem; Corollary 8.3 and Theorem 1.7 remain downstream proofs.

## Mechanical evidence

With Lean 4.32.1,

```text
lake build Bong.Lattice.He2023ADCSectionEight \
  BongTest.He2023ADCDistinguishingSublatticeAudit
```

completes four jobs. The focused audit runs directly. The derived lower
theorem, its compatibility endpoint, Theorem 8.2, Corollary 8.3, and Theorem
1.7 use only the allowed standard axioms `propext`, `Classical.choice`, and
`Quot.sound`.

An incremental compatibility build of the paper entry, canonical audit, and
focused audit completes all 5,563 planned jobs. The focused transitive gate
reports `AXIOM_GATE_PASS: 61083 declarations checked`. The comment-aware
scanner checks 2,734 tracked Lean sources; deployment-policy and formatting
checks pass.

As in Report 74, the whole-paper build reused locally copied project
artifacts. It is not a fresh-extraction or independent Review Kit receipt.

## Fidelity boundary

This checkpoint formalizes the composition of the three source steps; it
does not formalize Meyer, Xu, or O'Meara 104:5 themselves. Their exact
hypotheses, the construction of definite and spinor-genus predicates for
actual integral quadratic lattices over number fields, and the concrete
instances of all three law fields remain open to implementation and human
semantic review.

The whole-paper Grade-D verdict is unchanged because these external inputs,
other arithmetic law packages, and the already documented published
statement mismatches remain unresolved. This checkpoint is not a completion
or release certificate.
