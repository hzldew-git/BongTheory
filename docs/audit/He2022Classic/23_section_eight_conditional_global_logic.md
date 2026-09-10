# Section 8 conditional global-logic checkpoint

Historical note: Report 27 later derives Proposition 8.2 from lower laws, and
Report 28 replaces the unrestricted Lemma 8.3/Theorem 1.8 endpoint names below
by explicit `n >= 2`, even-rank versions.
Report 29 later derives the Theorem 1.9 local-to-global step from localization
and a separate strong-approximation representation law.
Report 30 later factors out the necessity-side discriminant/ramification
direction and derives its contrapositive witness.  Report 31 records that the
converse direction is separately required by the unary sufficiency branch.
Report 31 later derives the finite-place sufficiency conclusion of Theorem 1.9
from the separate non-dyadic, dyadic unary, and dyadic higher-rank branches.

## Scope

`Bong/Lattice/He2022ClassicSectionEight.lean` formalizes the deductions in
author-corrected v5 Section 8 and the associated main Theorems 1.5 and
1.7--1.9. The file deliberately separates two layers:

1. concrete local BONG mathematics already proved in the repository, including
   `he2022ClassicTheorem15_allRanks`; and
2. number-field localization, finite-extension, ramification/discriminant,
   and strong-approximation inputs that still require concrete instances.

The second layer is represented by fields of proof-data structures, not by
Lean axioms. Consequently the endpoints in this report have status
`CONDITIONAL_FORMALIZATION`, not `FULLY_FORMALIZED`.

## Lemma 8.1

`HeClassic2024LocalExtensionData.Lemma81Laws` records the finite-extension
inputs on the source coefficients:

- multiplication of the valuation by the relative ramification index;
- the corresponding lower bound for quadratic defect;
- the tower identity for the absolute ramification index; and
- transfer of a good BONG to the extended local field.

The public endpoints are `he2022ClassicLemma81i`,
`he2022ClassicLemma81ii`, and `he2022ClassicLemma81iii`. The coefficient type
represents nonzero base-field coefficients, which is necessary because the
formal order has type `Int` rather than an extended value at zero.

## Proposition 8.2 and Theorem 1.5

`he2022ClassicProposition82_positive` exposes the proposition's first,
stronger premise: representation of every positive-definite classic integral
global target of rank `n`. `he2022ClassicProposition82` derives the paper's
stated universality consequence by showing that every positive-definite target
is admissible for the global universality predicate.

`he2022ClassicTheorem15_atPlace` packages the already proved local obstruction
at one dyadic place. `he2022ClassicTheorem15_discriminantOdd` checks the final
global deduction: equality of every dyadic ramification index to one implies
odd discriminant through the explicit
`unramified_iff_discriminantOdd` field.

This does not yet construct the localization of a global lattice or identify
the abstract local premise with the concrete `GoodBONG` endpoint.

## Theorems 1.7--1.9 and Lemma 8.3

- `he2022ClassicTheorem17` derives the diagonal rank-`n+3` obstruction from a
  ramified dyadic place, Proposition 8.2, the local coefficient-profile input,
  and Theorem 1.5.
- `he2022ClassicLemma83_even` exposes the local obstruction under a ramified finite
  extension.  This remains a single premise not only because scalar-extension
  infrastructure is absent, but also because v5 does not justify its opening
  reduction to even `n` and the invoked odd Corollary 6.3 extension is false;
  see Reports 24 and 26.
- `he2022ClassicTheorem18_even` localizes universality on both sides and contradicts
  Lemma 8.3 at the selected pair of places.
- `he2022ClassicTheorem19` proves the sums-of-squares biconditional. Necessity
  uses Proposition 8.2 and Theorem 1.5 at every dyadic place; sufficiency uses
  explicit local-universality and strong-approximation fields.

The standing positive-rank convention is made explicit as `1 <= n`; the
rank hypotheses are exactly `rank L = n+3` or `n+3 <= m` as appropriate.

## Remaining implementation boundary

Whole-paper completion still requires concrete constructions or proved
instances for:

- number-field lattices and their finite localizations;
- O'Meara 81:14 globalization used in Proposition 8.2;
- valuation, defect, and good-BONG transport under local field extension;
- the equivalence between dyadic unramifiedness and odd number-field
  discriminant;
- the diagonal integer coefficient argument in Theorem 1.7; and
- all local cases and strong approximation in the sufficiency of Theorem 1.9.

In addition, unconditional Lemma 8.3 and Theorem 1.8 require either a new
odd-rank local argument not using the false Corollary 6.3 extension or an
explicit even-rank restriction in the source.

No conditional endpoint is promoted to an unconditional source match until
these fields have concrete instances and have passed independent semantic
review.
