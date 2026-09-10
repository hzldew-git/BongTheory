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

Report 30 factors the former full equivalence by retaining the direction used
by Theorems 1.5, 1.7, and the necessity half of Theorem 1.9.  The existence of
a ramified dyadic place under an even discriminant is proved by contraposition.
Report 31 then exposes the converse direction specifically where v5 uses it,
in the dyadic unary sufficiency branch of Theorem 1.9. Report 32 proves both
directions for actual number-field prime ideals, together with the
even-discriminant witness and positivity, and transports them through a typed
place bridge. Thus they are no longer unproved arithmetic inputs, although the
global place identification is still conditional.

Report 31 removes another final-conclusion field from Theorem 1.9.  Instead of
assuming local universality at every finite place, the formalization assumes
the three arithmetic cases named in v5 and proves their exhaustive split.  It
also makes `1 <= n` operational: `n = 1` and `n >= 2` reach distinct local
criteria, while the non-totally-real hypothesis is reserved for the later
strong-approximation step.

For Theorem 1.3 the current endpoints prove Lemma 7.4 in both parity branches,
all of Lemmas 7.7, 7.10, and 7.11, and a literal deletion witness for every
table row. The odd proof uses the corrected v5 Lemma 7.1 bridge to derive the
complete even table one rank lower; its public theorem has no extra lower-even
J2 premise. The older conditional reductions remain available only as
intermediate results.

The false broader assertion in the publisher comparison copy is not conflated
with v5. Its refutation and the author-corrected v5 theorem are separate
results; see `SOURCE_DELTA.md` and Report 22.
