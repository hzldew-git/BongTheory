# Lemma 6.8(v)--(vi): nonexceptional corank-two classes

Date: 2026-09-05. Sole authority: the Doc. Math. version of record,
DOI 10.4171/DM/1003, p. 983 and pp. 1002--1003. Publisher PDF SHA-256:
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

## Frozen scope and verdict

Code: `b728bce20942191785d0b50f2c068e0b5ee7c2f7`. The four new modules are
`He2023ADCEvenCorankTwoGenericOrders`, `He2023ADCEvenCorankTwoGenericTests`,
`He2023ADCEvenCorankTwoGeneric`, and `He2023ADCPublishedParameterDomain`.
The canonical entry and ADC audit import and query the new endpoints.

Clauses (v) and (vi) have proof status `FULLY_FORMALIZED` and semantic
status `PROVISIONAL_MATCH`, with the representative convention below
explicitly disclosed. Independent read-only AI review found no blocker.
Together with report 23, Lemma 6.8 is still `PARTIALLY_FORMALIZED`, 4/6
clauses: (iii) and (iv) remain open. Section 6 remains at 5/12 fully
completed numbered items. Whole-paper Grade C and `NOT_COMPLETE` remain.

## Statements and the printed representative convention

Put n=2k+2, m=n+2. The public endpoints
`Bong.Lattice.heADC2025Lemma68v` and `heADC2025Lemma68vi` quantify over
arbitrary actual lattices, with n-ADC and an actual ambient isometry to
the corresponding W_1 or W_2 space. Their conclusions are actual integral
lattice isometries to N_1 or N_2 with the original parameter c.

The representative-independent domain `HeHuSharpDomain c` excludes the
square and Delta square classes, not just two literal scalar values.
Page 983 defines normalized unit representatives U and V=U union pi U.
Normalization forces the square representative to be literally 1. It does
not by itself force the separately chosen Delta into U. Reading the printed
V minus {1,Delta} literally therefore needs the compatible choice Delta in U.

`heADCNormalizedRepresentative_eq_one_of_isSquare` proves the first fact.
`heADCSharpDomain_publishedParameter_iff` proves the exact equivalence
between class exclusions and literal exclusions on V, with the explicit
premise `hDelta : exists i, U i = Delta`. The two `Published` wrappers
then give the printed-parameter statements. This premise is a representative
choice, not a classification law; it is not silently inferred from the
normalization. No theorem certifies bare c!=1,Delta without membership and
compatibility. See `SOURCE_DELTA.md` and the author question below.

With this convention the printed wrappers are `LOGICALLY_EQUIVALENT` to
the stated clauses. The class-domain cores also allow arbitrary scalar
representatives and normalize them internally.

## Proof audit

The actual signed determinant class supplies codimension-two embeddings of
N_1^n(1), N_1^n(Delta), and N_2^n(Delta). Their integral representations
follow from n-ADC, not from a supplied table or representation hypothesis.
The source determinant exponent is k+1 and the target exponent is k+2.

Lemma 6.4(ii) forces the alternating head and R_(n+1)=0. The finite full
signed defect is d(c)<2e; finiteness is proved before using `toNat`.
A terminal order -2e would force full defect at least 2e. The remaining
value 1-2e is excluded using the odd-gap result. Lemma 6.7(i), with actual
N_2^n(Delta), then forces alpha_(n+1)=1 and raw terminal defect 1-R_(n+2).
The zero-alpha alternative contradicts the established order bounds.

The raw signed-head defect is at least 2e, so strict domination gives full
signed defect equal to terminal raw defect. Consequently R_(n+2)=1-d(c).
The raw, capped, head and full defects are never identified by definition.
The complete profile is derived, not assumed.

Each parameter is normalized modulo a coordinate square to valuation zero
or one. The proved unit and unit-uniformizer branches of Lemma 4.11(iii)
give integral maximality. Ambient square transport and maximal-lattice
uniqueness return the conclusion to the original parameter. Both ambient
columns, n=2, arbitrary ramification and e=1 are included. The binary
second test is N_2^2(Delta), never the undefined N_2^2(1).

## Trust and reproducibility

Main-agent checks passed the four modules, canonical entry and full ADC
audit. Independent replay re-elaborated the frozen sources from Git and
passed the same four modules, entry and audit. All 16 new queried theorem
dependency sets are exactly `propext`, `Classical.choice`, `Quot.sound`.
No custom axiom, native shortcut, supplied classification law or circular
maximality premise was found. All new lines satisfy the 100-column limit.
The 23 supplemental scanner tests and 2682 tracked-source scan also pass.

These are cached-local checks with pre-existing dependency modifications
preserved. They are not clean CI. The earlier f6f7485/c82668b clean kit
contains full Lemma 6.7 but neither report 23 nor this addition. An exact
new kit, clean CI, release promotion and human review remain separate gates.
The independent review was interrupted by a connection failure, then
resumed and completed; no failed or incomplete run is counted as approval.

## Author and expert review card

Author: confirm that the intended representative convention selects the
fixed Delta in U before using V minus {1,Delta}. Domain expert: check the
three actual embeddings, signed-defect domination and original-parameter
transport. Formalization expert: check proof irrelevance in the second
model, internal rank casts and normalization, and full dependency closure.
Names, dates, signatures and independent human decisions: not supplied.

## Subsequent package receipt

The source-only kit at clean commit
`d05a89885573dd17ec097f059f4a635a96736b7b` includes this report and the
four completed clauses of Lemma 6.8. Its 1898 project Lean sources are
included among 1944 files; the archive has 5806365 bytes. Extraction and
all 1943 payload hashes passed. Archive SHA-256:
`FB75D0711589F584E2C8B7AE054CFCBA97B6FD172271D51CB747484BFE41C646`.
This is structure-only verification. No clean build, uploaded release,
or later second-endpoint proof is certified by this package receipt.
