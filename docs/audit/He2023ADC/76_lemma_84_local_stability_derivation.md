# Lemma 8.4 local stability derivation

Status: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.

Code checkpoint:
`677c1ae57a26365c0c0615a7894646851d0ef167` on
`feat/he2023adc-local-maximality`.

## Source authority and locator

The semantic authority is Zilong He, *On n-ADC integral quadratic lattices
over algebraic number fields*, *Documenta Mathematica* 30 (2025), no. 4,
981--1022, DOI 10.4171/DM/1003. The audited publisher PDF has SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Lemma 8.4 and its proof are on publisher page 1018. The proof first applies
Theorem 1.3 to obtain global 2-regularity and local 2-ADC. It states that
2-regularity is invariant under scaling. At each finite prime it then invokes
Theorem 6.2 and Proposition 4.16 to obtain the hyperbolic-or-exceptional local
form, scales that alternative by two, and concludes stability at every prime.

## Formal change

The earlier `SectionEightLaws` interface stored the finished implication

```text
IsLocallyNADC M 2 -> isStable (scaleTwo M).
```

That final-conclusion field has been removed. `HeADC2025GlobalData` now
records placewise stability and a named predicate for the exact local-form
alternative used in the printed proof. The new `ScalingStabilityLaws` package
separates three inputs:

1. local 2-ADC implies the Theorem 6.2/Proposition 4.16 local-form alternative;
2. scaling either local form gives stability at that place; and
3. global stability is equivalent to stability at every finite place.

`ScalingStabilityLaws.locallyTwoADC_scaleTwo_stable` composes those inputs
pointwise. The compatibility endpoint in `SectionEightLaws` and
`heADC2025Lemma84` consume this derived theorem. The 2-regular scaling
invariance used for the other conjunct of Lemma 8.4 remains an explicit law.

## Mechanical evidence

With Lean 4.32.1,

```text
lake build Bong.Lattice.He2023ADCSectionEight \
  BongTest.He2023ADCScalingStabilityAudit
```

completes four jobs. The focused audit runs directly. The derived local-to-
global stability theorem, its compatibility endpoint, Lemma 8.4, and
Corollary 8.5 report only the allowed standard axiom `propext`.

The focused imported-closure gate checks 168 declarations. The combined
paper-entry and focused imported-closure gate reports
`AXIOM_GATE_PASS: 61096 declarations checked`. The comment-aware scanner
checks 2,735 tracked Lean sources, and all 30 policy tests pass.

An incremental compatibility build of the paper entry, canonical audit, and
focused audit completes all 5,563 planned jobs.

These are local incremental checks that reuse copied project artifacts. A
fresh-extraction full build of an exact Review Kit remains a separate
reproducibility gate.

## Fidelity boundary

This checkpoint formalizes the composition in the second half of the printed
proof. It does not yet construct the hyperbolic and exceptional alternatives
inside the abstract global/local system, connect them to the already proved
dyadic and conditional non-dyadic classifications, or instantiate placewise
stability for number-field lattices. It also does not discharge scaling
invariance of 2-regularity.

The whole-paper Grade-D verdict is unchanged because these arithmetic inputs,
other concrete law packages, the documented published statement mismatches,
exact-tag deployment, and human semantic review remain unresolved. This is
not a completion or release certificate.
