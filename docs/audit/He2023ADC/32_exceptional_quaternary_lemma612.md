# Lemma 6.12 exceptional quaternary checkpoint

Status: `FULLY_FORMALIZED` / semantic `PROVISIONAL_MATCH`.

Code checkpoint: `cf9f83be635d6e459cfb429ad73b4c7a31f1ddf4`.

## Source authority

The sole semantic authority is the publisher version of record:

- Zilong He, *On n-ADC integral quadratic lattices over algebraic number
  fields*, *Documenta Mathematica* 30 (2025), no. 4, 981--1022;
- DOI: <https://doi.org/10.4171/DM/1003>;
- publisher PDF SHA-256:
  `E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

The proof was audited source first and code second against Lemma 6.12 and its
use of Proposition 4.2(iii), Theorem 3.6, and Lemma 4.11(i). The later arXiv
revision is comparison material only.

## Formal statement and construction

The formal construction is the actual exceptional lattice

`H perp <1, -Delta * pi^(2 - 2e)>`.

Its supplied good BONG has the exact order profile
`[0, -2e, 0, 2 - 2e]`. The development proves that it is integral, lies in
the ambient space `W_1^4(Delta)`, has split hyperbolic head and full signed
defect `2e`, and is not norm-maximal. These facts are derived in
`He2023ADCExceptionalQuaternaryCandidate.lean`; they are not assumptions of
the final theorem.

The three final endpoints are:

- `GoodBONG.heADCExceptionalQuaternaryCandidate_is2ADC`;
- `GoodBONG.heADCExceptionalQuaternaryCandidate_not_is3ADC`;
- `GoodBONG.heADCExceptionalQuaternaryCandidate_not_isOMaximal`.

Together they formalize all assertions of Lemma 6.12.

## Complete maximal-binary testing

The 2-ADC proof checks the full dyadic maximal binary catalogue rather than a
single model family. It supplies:

- the two discriminant endpoints `N_1^2(Delta)` and `N_1^2(1)`, using the
  actual ternary prefix and the half-hyperbolic identification;
- the generic unit and unit-uniformizer families, including the square-class
  normalization back to the original integral targets;
- the finite-defect representation criterion with the beta-one parity case;
- an explicit proof that `N_2^2(Delta)` is the unique catalogue item not
  represented by the ambient quadratic space and therefore is not a required
  target.

The resulting theorem quantifies over every integral norm-maximal binary
lattice represented by the ambient quaternary space and proves that the
exceptional lattice represents it. The general maximal-testing reduction then
gives the literal local 2-ADC predicate.

## Failure of 3-ADC

The negative clause uses an actual represented maximal ternary target with
orders `[0, -2e, 1]`. The terminal mixed defect forced by the exceptional
quaternary profile is `0`, while the comparison alpha is at least `1/2`.
Theorem 3.6 therefore rules out integral representation. This gives the
negation of the local 3-ADC predicate, rather than merely a failed candidate
embedding.

## Nonvacuity and trust checks

`BongTest.He2023ADCExceptionalQuaternaryQ2` instantiates the 2-ADC,
not-3-ADC and nonmaximal conclusions over `Q_2`. Thus the hypotheses are
jointly inhabited in the intended dyadic setting.

The eight new proof modules, the canonical paper entry, the full paper audit
entry, and the concrete `Q_2` entry all compile directly with Lean 4.32.1.
Sixteen newly printed axiom sets are exactly
`[propext, Classical.choice, Quot.sound]`. The focused enforcing gate checked
57,886 declarations, and the source scanner checked 2,705 tracked Lean files
with 23 scanner tests and found no forbidden proof tokens outside comments.

This checkpoint has undergone the principal source-to-code semantic audit,
but it has not received independent human sign-off. Exact-revision clean-kit
CI and release promotion are also pending. Consequently the semantic label is
`PROVISIONAL_MATCH`, not `VERIFIED_MATCH`.

## Scope boundary

This checkpoint completes Lemma 6.12 only. It does not prove Lemmas
6.9--6.11, repair the mismatch in Lemma 6.8(iv) at `n = 2`, or certify the
printed proof of Theorem 6.2. Those obligations remain separate.

## Author review card

Reviewers should confirm:

1. the lattice and order profile are exactly those printed in Lemma 6.12;
2. Proposition 4.2(iii) removes only `N_2^2(Delta)` from the required maximal
   binary catalogue in the ambient `W_1^4(Delta)`;
3. the two endpoint and generic-family proofs cover every remaining maximal
   binary class without adding a representative convention;
4. the terminal defect and alpha comparison reproduce the published failure
   of 3-ADC.

Author decision: unsigned. Domain-expert decision: unsigned.
Formalization-expert decision: unsigned.
