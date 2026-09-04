# Author review cards

1. Confirm `IsClassicIntegral` against the paper's bilinear normalization.
2. Confirm that the volume-order argument produces maximal classic integral
   over-lattices without an unrecorded nondegeneracy hypothesis.
3. Do not identify `heClassicMaximalTestingReduction` with the explicit or
   minimal testing families in Theorem 1.3.
4. Check every field of `HeClassicEvenConditions` and
   `HeClassicOddConditions`, especially the one-based to zero-based conversion.
5. Re-audit all statements solely against the publisher version, because arXiv
   v3 postdates publication.

## Theorem 1.1: full local criterion

Paper location: pp. 560-561. Formal endpoint:
`Bong.BONG.GoodBONG.he2022ClassicTheorem11`.

Paper statement: over a dyadic local field, a classic integral lattice with a
good BONG is classic n-universal, for n >= 2, exactly when its rank is at least
n + 3 and all the displayed initial-order, parity, defect, and terminal-gap
conditions hold.

Formal translation: the same universality predicate is equivalent to the
bundled published conditions for every source rank and n >= 2. Both directions
are proved; small source ranks are excluded by proof, not by a new premise.
The preceding definition of the proposition is not itself its proof.

Definitions requiring confirmation: scale integrality; integral isometric
representation; the signed prefix defect; valuation of two; and indexing of
adjacent entries. The field interfaces include the quadratic-defect,
Hilbert-symbol, and dyadic discriminant laws with their proved instances.

No quantifier or conclusion restriction is identified for this endpoint.
The paper uses one-based indices and the implementation uses zero-based
indices. Isometry, not equality of chosen bases, is the equivalence convention.
Source corrections in intermediate lemmas are disclosed in `SOURCE_DELTA.md`.

Current status: `PROVISIONAL_MATCH`; no human approval has been recorded.

Questions for the author/domain expert: Do all parity and defect branches,
including the low-rank exclusions, express the published statement? Are the
disclosed intermediate source corrections acceptable as proved helpers?
Question for the formalization expert: Do the concrete field-law instances,
universes, and transitive dependencies preserve this scope?

Author decision, reviewer name, date, and signature: not provided.

## Theorem 1.5: local special case only

Paper location: p. 562; separate unary proof on p. 586. Formal endpoint:
`Bong.BONG.GoodBONG.he2022ClassicTheorem15`.

Paper statement: if the localized lattice is classic n-universal, its rank is
at least n + 3 >= 4, and every unsigned adjacent defect is greater than one,
then the dyadic ramification index is one. If this holds at every dyadic prime,
two is unramified in the number field, equivalently its discriminant is odd.

Formal translation: at a single dyadic field, under those local assumptions
and the additional restriction n >= 2, the ramification index is one.
The source rank is written m + 1 so adjacent indices have type `Fin m`.

Common definitions and assumptions: classic integrality, classic
n-universality, rank bound, unsigned adjacent defects, and dyadic valuation.
Differences: the unary n = 1 case is absent; there is no number-field variable,
all-places quantifier, localization construction, or discriminant conclusion.

Current status: `PARTIAL_FORMALIZATION`; relationship: `SPECIAL_CASE_ONLY`.
Question for the author/domain expert: Confirm that this is a useful local
specialization, without treating it as the entire theorem.
Question for the formalization expert: Verify that no implicit global claim
is introduced by the endpoint name.

Author decision, reviewer name, date, and signature: not provided.

## Theorem 1.3: separate the testing obligations

Paper location: p. 561. The source asserts even and odd testing equivalences,
the displayed residue-cardinality counts, and inclusion-minimality of the
testing families. The current code constructs the literal indexed rows and
proves even testing equivalence, but does not prove all these obligations.

Current status: `PARTIAL_FORMALIZATION`. The qualified odd testing endpoint
has an extra lower-even J2 premise; it is not the printed unconditional theorem.
Question for the author/domain expert: How should the refuted literal
Lemma 7.1(ii) and the affected odd testing chain be resolved?
Question for the formalization expert: Check testing sufficiency, irredundancy,
counts of isometry classes, and deletion-minimality separately.

No source erratum or human approval is asserted by this card.
