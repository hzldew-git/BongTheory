# O'Meara 63:9 unit square-class count

Status: `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`.

Code checkpoint:
`4ad37e1` on `feat/he-formalization`.

## Source authority and exact scope

The semantic authority for the paper-facing use is the published
*Documenta Mathematica* version of He (2025), p. 1016, DOI
10.4171/DM/1003. Its proof of Corollary 7.21 cites O'Meara 63:9 for

`|O_F^times / O_F^{times 2}| = 2 * (N p)^e`.

The formal theorem uses the repository's normalized valuation, residue field,
ramification index, and unit square-class quotient. It proves

`Nat.card (ValuationUnitClass K) = 2 * q^e`

for every `K` satisfying `DyadicContext K`, where
`q = Nat.card (normalizedResidueField K)` and
`e = ramificationIndex K`. The theorem is not supplied as a class field or
proposition-valued parameter.

## Formal proof chain

The proof is split into four auditable layers.

1. `PowerIdealResidueQuotient.lean` constructs the leading-coefficient map
   from `p^n` to the residue field, proves its kernel is `p^(n+1)`, proves
   surjectivity, and obtains an additive equivalence
   `p^n / p^(n+1) ≃ k`.
2. `PrincipalUnitResidueQuotient.lean` applies the same construction to
   `1 + p^n`. For positive `n`, multiplication modulo `1 + p^(n+1)` becomes
   addition in the residue field, yielding
   `(1+p^n)/(1+p^(n+1)) ≃ k`.
3. `UnitSquareClassOddLayer.lean` quotients the principal-unit filtration by
   squares. At every positive odd depth below `2e`, the successive layer is
   equivalent to the residue field. The kernel proof uses the odd-depth
   square-correction lemma and is stated as an equality of actual subgroups.
4. `UnitSquareClassCount.lean` proves the even layers collapse, the endpoint
   at depth `2e` consists exactly of the trivial and discriminant classes,
   and induction contributes one residue-field factor for each of the `e`
   odd layers. This gives `Bong.Dyadic.card_valuationUnitClass`.

The endpoint proof at depth `2e` is not a cardinality assumption: it derives
the two alternatives from the already proved discriminant-class theorem and
proves the discriminant class is nonsquare.

## Representative systems and paper formulas

`He2023ADCUnitRepresentativeCount.lean` proves that every finite complete and
irredundant normalized representative system `U` is equivalent to
`ValuationUnitClass K`. Consequently
`card_heHuCompleteUnitRepresentativeSystem` transports the intrinsic count to
the exact parameter system used by He.

The namespace `HeADC2025Corollary721CountingLaw` is retained only for API
continuity. It is now a namespace of unconditional theorems; there is no
typeclass or caller-supplied counting law. The following conclusions therefore
have no counting premise:

- Remark 4.3: `4 * (N p)^e` unary testing classes;
- Corollary 7.21: `(8e+6)(N p)^e` total and `(8e-2)(N p)^e` nonmaximal
  odd-corank-two classes;
- the corrected binary count `8(N p)^e+2`;
- every numerical dyadic branch bundled by
  `heADC2025Theorem110DyadicCorrected`.

The published binary value `8(N p)^e+1` remains formally refuted. Proving the
unit square-class count strengthens the refutation because the contradiction
no longer depends on assuming the publisher's cited numerical input.

## Trust and mechanical evidence

At the stated code checkpoint:

- the canonical He ADC entry and all three audit entries complete 5,554 build
  jobs under Lean 4.32.1;
- the comment-aware scanner checks 2,769 tracked Lean sources and finds no
  forbidden proof token outside comments;
- the focused transitive gate reports
  `AXIOM_GATE_PASS: 60573 declarations checked`;
- selected quotient, odd-layer, endpoint, total-count, representative-count,
  catalogue-count, and Theorem 1.10 endpoints report exactly `propext`,
  `Classical.choice`, and `Quot.sound`;
- all changed Lean sources satisfy the scoped 100-column check, and
  `git diff --check` passes.

Warnings about locally modified dependency worktrees predate this checkpoint
and those dependency worktrees were not changed. A fresh exact-revision Review
Kit, GitHub-hosted CI, and independent human semantic approval remain separate
gates.

## Audit verdict

The cited O'Meara 63:9 cardinality input is now `FULLY_FORMALIZED` inside the
repository's dyadic interface. The paper-facing normalization is a
`PROVISIONAL_MATCH` pending independent human review. This closes one former
arithmetic trust boundary but does not complete He (2025): concrete
non-dyadic, global number-field, and external enumeration instances remain
open, and the publisher mismatches recorded for the binary statements and
Lemma 7.13 remain unchanged.
