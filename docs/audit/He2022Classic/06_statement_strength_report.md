# Statement strength report

The proved testing theorem quantifies over every classic-maximal rank-`n`
lattice. The publisher's Theorem 1.3 replaces that abstract family with explicit
minimal lists, so the current endpoint is not a substitute for Theorem 1.3.

`HeClassicTheorem11Statement` records all branches of the explicit BONG
classification. `he2022ClassicTheorem11` now proves that proposition, including
both directions, all source ranks, and both parity branches for n >= 2. The
intended relationship is `LOGICALLY_EQUIVALENT`; final semantic acceptance
remains `PROVISIONAL_MATCH` pending independent human confirmation.

For Theorem 1.5 the primary relationship is `SPECIAL_CASE_ONLY`: the endpoint
proves the local implication for n >= 2. The paper also allows n = 1 and draws
a conclusion about all dyadic primes and the number-field discriminant.

For Theorem 1.3 and Lemma 7.4 the current testing endpoint covers even rank;
neither full odd-rank sufficiency nor proper-subset minimality follows merely
from constructing the finite indices. The extra lower-even J2 premise in the
available odd endpoint is not hidden.

The false literal assertion in Lemma 7.1(ii) is not replaced by an equivalent
theorem. Its refutation and the explicitly qualified alternative are separate
results; see `SOURCE_DELTA.md`.
