# O'Meara 82K global maximality directions

Status: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.

Code checkpoint:
`0c5211bb0f5a2f1954a0e6b63ceac53a6bb67121` on
`feat/he2023adc-local-maximality`.

## Source authority and locator

The semantic authority is Zilong He, *On n-ADC integral quadratic lattices
over algebraic number fields*, *Documenta Mathematica* 30 (2025), no. 4,
981--1022, DOI 10.4171/DM/1003. The audited publisher PDF has SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Theorem 1.5(ii) is stated on publisher page 984. Its proof on page 1016 says
that the global assertion follows from part (i) and O'Meara section 82K.
Lemma 8.1(ii) on pages 1016--1017 uses the forward direction explicitly:
an `O_F`-maximal lattice has an `O_{F_p}`-maximal localization at every
finite prime.

## Formal change

The earlier `SectionEightLaws` interface stored the complete biconditional

```text
isGlobalMaximal M <-> forall p, localMaximal (localize p M).
```

That finished field has been removed. The new `GlobalMaximalityLaws` package
records the two directional arithmetic inputs separately:

1. global maximality localizes to every finite prime;
2. maximality at every finite localization globalizes.

`GlobalMaximalityLaws.globalMaximal_iff_localMaximal` assembles the
biconditional. A theorem-level compatibility endpoint preserves every
downstream proof. Lemma 8.1(ii), Theorem 1.5(ii), and Theorem 1.7 therefore
consume the derived equivalence rather than a final-conclusion structure
field.

## Mechanical evidence

With Lean 4.32.1, the Section 8 module and
`BongTest.He2023ADCGlobalMaximalityAudit` complete a four-job focused build.
The audit runs directly. The lower biconditional, its compatibility endpoint,
and Lemma 8.1(ii) have empty axiom sets. Theorem 1.5(ii) reports only
`propext`; Theorem 1.7 reports only `propext`, `Classical.choice`, and
`Quot.sound`.

An incremental compatibility build of the paper entry, canonical audit, and
focused audit completes all 5,563 planned jobs. The combined paper-entry and
focused imported-closure gate reports
`AXIOM_GATE_PASS: 61118 declarations checked`. The comment-aware scanner
checks 2,737 tracked Lean sources, all 30 policy tests pass, and changed Lean
lines satisfy the 100-column policy.

These checks reuse local project artifacts. A fresh-extraction full build of
an exact Review Kit remains a separate reproducibility gate.

## Fidelity boundary

This checkpoint formalizes the two directions and their uses; it does not
construct global integral lattices and their finite localizations or prove
either O'Meara 82K direction for that concrete model. Those two directional
instances remain explicit mathematical obligations.

The whole-paper Grade-D verdict is unchanged because concrete number-field
instances, other arithmetic packages, documented published mismatches,
exact-tag deployment, and human semantic review remain unresolved. This is
not a completion or release certificate.
