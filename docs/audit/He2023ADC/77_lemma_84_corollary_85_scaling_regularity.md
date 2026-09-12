# Lemma 8.4 and Corollary 8.5 scaling regularity

Status: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.

Code checkpoint:
`0a94683dd9e1092d4e1e0ed78958b55fc1d65ee5` on
`feat/he2023adc-local-maximality`.

## Source authority and locator

The semantic authority is Zilong He, *On n-ADC integral quadratic lattices
over algebraic number fields*, *Documenta Mathematica* 30 (2025), no. 4,
981--1022, DOI 10.4171/DM/1003. The audited publisher PDF has SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Lemma 8.4 and Corollary 8.5 are on publisher page 1018. The proof of Lemma
8.4 states that 2-regularity is invariant under scaling. Corollary 8.5 says
that `M` is 2-ADC exactly when it is locally 2-ADC and isometric to the
half-scale `L(1/2)` of a stable 2-regular lattice `L`.

## Formal change

The earlier `SectionEightLaws` interface stored three one-way finished facts:

```text
IsNRegular M 2 -> IsNRegular (scaleTwo M) 2;
isHalfScaleOf M (scaleTwo M);
IsNRegular L 2 -> isHalfScaleOf M L -> IsNRegular M 2.
```

All three fields have been removed. The new `ScalingRegularityLaws` package
records the stronger and source-faithful scaling biconditional at every rank,
and fixes the orientation of half-scaling by

```text
isHalfScaleOf M L <-> L = scaleTwo M.
```

From these two laws Lean derives the forward regularity step in Lemma 8.4,
the canonical half-scale witness in Corollary 8.5, and the reverse regularity
transport used by that corollary. The existing public `SectionEightLaws`
names are preserved as theorem-level compatibility endpoints.

## Mechanical evidence

With Lean 4.32.1, the Section 8 module and
`BongTest.He2023ADCScalingRegularityAudit` complete a four-job focused build.
The audit runs directly. All three lower theorems and all three compatibility
endpoints have empty axiom sets; Lemma 8.4 and Corollary 8.5 report only the
allowed standard axiom `propext`.

An incremental compatibility build of the paper entry, canonical audit, and
focused audit completes all 5,563 planned jobs. The combined paper-entry and
focused imported-closure gate reports
`AXIOM_GATE_PASS: 61108 declarations checked`. The comment-aware scanner
checks 2,736 tracked Lean sources, all 30 policy tests pass, and changed Lean
lines satisfy the 100-column policy.

These checks reuse local project artifacts. A fresh-extraction full build of
an exact Review Kit remains a separate reproducibility gate.

## Fidelity boundary

This checkpoint proves the logical consequences of scaling invariance and
the exact half-scale orientation. It does not yet implement the scaling
operation on concrete global integral quadratic lattices or prove the
scaling biconditional from that construction. Those tasks remain the visible
mathematical boundary.

The whole-paper Grade-D verdict is unchanged because concrete number-field
instances, other arithmetic packages, documented published mismatches,
exact-tag deployment, and human semantic review remain unresolved. This is
not a completion or release certificate.
