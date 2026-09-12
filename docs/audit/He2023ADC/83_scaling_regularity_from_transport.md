# Scaling regularity from primitive transport

Status: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.

Code checkpoint:
`9ebf43c8d1c5ead35a1865435ff1e166fc89b7e3` on
`feat/he2023adc-scaling-transport`.

## Source authority and locator

The semantic authority is Zilong He, *On n-ADC integral quadratic lattices
over algebraic number fields*, *Documenta Mathematica* 30 (2025), no. 4,
981--1022, DOI 10.4171/DM/1003. The audited publisher PDF has SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Lemma 8.4 and Corollary 8.5 occur on publisher page 1018. The proof of Lemma
8.4 invokes invariance of 2-regularity under scaling. Report 77 exposed that
invariance as the explicit `ScalingRegularityLaws.nRegular_scaleTwo_iff`
boundary.

## Formal change

The new `ScalingTransportLaws` interface no longer takes the finished
regularity biconditional as a field. It records only:

- surjectivity of `scaleTwo` on the ambient global-lattice type;
- preservation of global rank;
- preservation and reflection of global integrality;
- preservation and reflection of local representation when source and target
  are both scaled;
- preservation and reflection of global representation under the same
  simultaneous scaling; and
- the exact orientation of the half-scale relation.

Lean proves

```text
IsNRegular (scaleTwo M) n <-> IsNRegular M n
```

for every rank `n`. In the forward direction, each test lattice is scaled and
all four clauses in `IsNRegular` are transported. In the reverse direction,
surjectivity supplies a half-scaled preimage of an arbitrary test lattice;
rank, integrality, local representation, and the final global representation
are transported back. The theorem `toScalingRegularityLaws` then constructs
the earlier Section 8 interface, so all existing Lemma 8.4 and Corollary 8.5
endpoints remain reusable.

## Mechanical evidence

With Lean 4.32.1, the new module and focused audit build successfully. The
focused audit checks both `nRegular_scaleTwo_iff` and
`toScalingRegularityLaws`; Lean reports that neither declaration depends on
any axiom. The canonical He ADC audit imports and checks both declarations.

An exact single-paper Review Kit, fresh extraction, full declaration gate,
and GitHub-hosted exact-head checks remain separate reproducibility gates for
this new checkpoint.

## Fidelity boundary

This checkpoint proves that regularity invariance is a formal consequence of
primitive simultaneous-scaling transport. It does not yet construct the
global-lattice scaling operation over a number field or prove the six
transport fields for that concrete construction. The half-scale orientation
also remains an explicit arithmetic identification.

Accordingly, the whole-paper Grade-D `NOT_COMPLETE` verdict is unchanged.
The published boundary mismatches, concrete number-field and non-dyadic law
instances, external catalogue inputs, exact release promotion, and human
semantic sign-off remain open.
