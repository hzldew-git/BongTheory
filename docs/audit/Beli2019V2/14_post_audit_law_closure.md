# Post-audit Local-law Closure

> Historical stage notice (28 August 2026): this addendum records only the
> first closure step.  All remaining interfaces were subsequently discharged;
> see `15_unconditional_completion_audit.md`.

## Scope

The numbered reports `00`--`13` describe the M660 source snapshot identified
in the original audit. This addendum records the subsequent M661 closure and
does not retroactively change that snapshot identifier.

## Closed interface

`Bong.Dyadic.QuadraticDefectHensel` proves, from `DyadicContext` alone, the
two fields previously supplied by `QuadraticDefectLaws`:

1. `quadraticDefect K a = top` if and only if `a` is a square;
2. a nonsquare has quadratic defect at most `2 * ramificationIndex K`.

The key argument divides a principal-unit error of order greater than `2e`
by four and applies Hensel's lemma to `X^2 + X - c` over the normalized
valuation ring. Compactness supplies adic completeness, hence the required
Henselian structure.

## Main-theorem impact

The explicit `QuadraticDefectLaws` parameter has been removed from
`Bong.beli2019Theorem21` and `Bong.beli2019Theorem21_prime`. The current public
signature therefore contains 48 project-specific law/data-instance slots,
down from 49 in the audited M660 snapshot.

This is one genuine local-law closure, not merely a repackaging of an
assumption. The overall semantic verdict remains `FORMALIZATION_WEAKER` and
grade C because the other local arithmetic, Jordan, classification,
Section 4/5, scaling, and representation interfaces remain explicit.

## Trust check

The focused audit in `BongTest.QuadraticDefectHenselAudit` reports only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

The same three standard Lean axioms are reported for both Beli 2019 main
endpoints after the parameter removal.

The complete default build succeeds after this change with 4,547 jobs. The
first run after changing the root import graph exposed stale cached object
dependencies; rebuilding those generated objects and rerunning the same
command completed successfully.
