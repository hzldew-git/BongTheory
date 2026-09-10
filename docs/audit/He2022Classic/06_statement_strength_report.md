# Statement strength report

The abstract maximal-testing theorem quantifies over every classic-maximal
rank-`n` lattice. The Section 7 endpoints separately prove that both literal
v5 lists are sufficient and deletion-minimal.

`HeClassicTheorem11Statement` records all branches of the explicit BONG
classification. `he2022ClassicTheorem11` now proves that proposition, including
both directions, all source ranks, and both parity branches for n >= 2. The
intended relationship is `LOGICALLY_EQUIVALENT`; final semantic acceptance
remains `PROVISIONAL_MATCH` pending independent human confirmation.

For Theorem 1.5 the endpoint `he2022ClassicTheorem15_allRanks` proves the
local-field implication throughout the published range n >= 1. The separate
unary endpoint follows the source's alpha-invariant contradiction, while the
n >= 2 branch uses Theorem 1.1. The paper additionally starts with a global
number-field lattice and concludes that two is unramified, equivalently that
the number-field discriminant is odd. That final deduction is now encoded by
`he2022ClassicTheorem15_discriminantOdd` over explicit localization and
discriminant laws. The complete printed theorem therefore has a fully proved
local component and a `CONDITIONAL_FORMALIZATION` global component; it is not
an unconditional whole-theorem formalization.

Theorems 1.7 and 1.9 and the valid even-rank part of Theorem 1.8 are stated at
their logical endpoints in `He2022ClassicSectionEight.lean`. Their extra parameters are
bundled proof-data structures identifying the cited number-field results.
These hypotheses make the endpoints weaker as formalization evidence than
unconditional implementations, even though the conclusions and rank/parity
quantifiers match v5. Report 23 lists the boundary field by field.

Report 27 narrows that boundary for Proposition 8.2.  The complete local
universality conclusion is no longer assumed by `SectionEightLaws`; it is
proved for an arbitrary local rank-`n` lattice from positive-definite
globalization, localization of integrality and representation, and transport
across local equivalence.  Because those four arithmetic laws still lack
concrete number-field instances, the semantic status remains conditional.

Report 28 also weakens the formal statement of Lemma 8.3 and Theorem 1.8
relative to unrestricted v5 by requiring `n >= 2` and `Even n`.  This is an
intentional fidelity safeguard: it matches the only case handled by the
written proof and leaves the unsupported odd branch absent rather than
encoding it as a supplied conclusion.

Report 29 narrows Theorem 1.9's sufficiency boundary.  The implication from
finite-place local universality to global universality is now proved by
localizing an arbitrary admissible global target and invoking a separate
strong-approximation representation law.  Since that law and the concrete
localizations remain uninstantiated, this is still conditional evidence.

Report 30 further weakens the assumed arithmetic interface without weakening
any formal conclusion: the former full equivalence between odd discriminant
and dyadic ramification index one is replaced by the single direction used by
Theorems 1.5, 1.7, and 1.9.  The existence of a ramified dyadic place under an
even discriminant is proved by contraposition.

For Theorem 1.3 the current endpoints prove Lemma 7.4 in both parity branches,
all of Lemmas 7.7, 7.10, and 7.11, and a literal deletion witness for every
table row. The odd proof uses the corrected v5 Lemma 7.1 bridge to derive the
complete even table one rank lower; its public theorem has no extra lower-even
J2 premise. The older conditional reductions remain available only as
intermediate results.

The false broader assertion in the publisher comparison copy is not conflated
with v5. Its refutation and the author-corrected v5 theorem are separate
results; see `SOURCE_DELTA.md` and Report 22.
