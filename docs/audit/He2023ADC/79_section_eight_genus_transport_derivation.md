# Section 8 genus transport derivation

Status: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.

Code checkpoint:
`97068f7f4617b37f69980a056afa7f6e01eab4d3` on
`feat/he2023adc-local-maximality`.

## Source authority and locator

The semantic authority is Zilong He, *On n-ADC integral quadratic lattices
over algebraic number fields*, *Documenta Mathematica* 30 (2025), no. 4,
981--1022, DOI 10.4171/DM/1003. The audited publisher PDF has SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Corollary 8.3 is stated on publisher page 1017 and its proof continues on
page 1018. The proof chooses `M'` in `gen(M)`, uses
`M'_p \cong M_p` at every finite prime, transports representation of the
distinguishing rank-`n` lattice, and finally reverses the resulting isometry.
Thus the proof uses the definition of genus through local equivalence, not an
unexplained primitive relation. Rank preservation in the genus is implicit in
the displayed rank hypotheses of Theorem 8.2.

## Formal change

The former `SectionEightLaws` stored genus symmetry, rank preservation in a
genus, and extraction of local equivalence as three finished fields. They are
now derived from `GenusTransportLaws`, whose source-level inputs are:

1. `inGenus M N` if and only if the localizations are equivalent at every
   finite place;
2. symmetry of local equivalence;
3. preservation of local rank by local equivalence;
4. existence of a finite place; and
5. the still-explicit isometry-symmetry and representation-transport facts.

`GenusTransportLaws.inGenus_symm` unfolds the placewise definition and
reverses each local equivalence. `localEquivalent_of_inGenus` specializes the
same definition. `rank_eq_of_inGenus` chooses one finite place and combines
local-rank preservation with `Theorem13Laws.rank_localize` on both lattices.
Corollary 8.3 and Theorem 1.7 consume these derived endpoints.

This is not merely a renaming of the old fields: two relation properties and
the global rank equality are now proof terms. Isometry symmetry and local
representation transport remain visible arithmetic inputs because the
abstract system does not yet define either relation concretely.

## Mechanical evidence

With Lean 4.32.1, `Bong.Lattice.He2023ADCSectionEight` and
`BongTest.He2023ADCGenusTransportAudit` complete a four-job focused build.
The focused audit runs directly. Local-equivalence extraction and global-rank
preservation have empty axiom sets; genus symmetry uses only `propext`.
Corollary 8.3 and Theorem 1.7 report only `propext`, `Classical.choice`, and
`Quot.sound`.

An incremental paper-entry and canonical-audit build completes all 5,562
planned jobs. The combined paper-entry and focused imported-closure gate
reports `AXIOM_GATE_PASS: 61134 declarations checked`. The comment-aware
scanner checks 2,738 tracked Lean sources, all 30 policy tests pass, and
changed Lean lines satisfy the 100-column policy.

These checks reuse local project artifacts. A fresh-extraction full build of
an exact Review Kit remains a separate reproducibility gate.

## Fidelity boundary

The new package captures the mathematical definition and derives its routine
consequences, but it does not construct global quadratic lattices,
localizations, local equivalences, or integral isometries over a number field.
Concrete instances of all five lower inputs remain open.

The whole-paper Grade-D verdict is unchanged because concrete number-field
and non-dyadic instances, documented publisher mismatches, exact-tag
deployment, and human semantic review remain unresolved. This report is not
a completion or release certificate.
