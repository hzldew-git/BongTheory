# Author review cards

1. Confirm `IsClassicIntegral` against the paper's bilinear normalization.
2. Confirm that the volume-order argument produces maximal classic integral
   over-lattices without an unrecorded nondegeneracy hypothesis.
3. Do not identify `heClassicMaximalTestingReduction` with the explicit or
   minimal testing families in Theorem 1.3.
4. Check every field of `HeClassicEvenConditions` and
   `HeClassicOddConditions`, especially the one-based to zero-based conversion.
5. Re-audit all statements against the author-corrected v5 file and its frozen
   hash; use the publisher and arXiv copies only to inspect recorded deltas.

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

## Proposition 8.2: positive-definite globalization route

Paper location: v5 lines 1660--1674.  Formal derivation:
`HeClassic2024GlobalData.Proposition82Laws.he2022ClassicProposition82_positive`.

For each finite place and each integral local rank-`n` lattice, the formal
proof requests a positive-definite integral global lattice of the same rank
whose localization is equivalent to that local lattice.  It applies the
paper's global representation hypothesis, localizes the representation, and
transports it across the local equivalence.  The public statement retains the
paper's positive-integer hypothesis.

Current status: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.  The final
Proposition 8.2 conclusion is proved rather than supplied, but the concrete
O'Meara 81:14 globalization and localization instances are not constructed.
Question for the author/domain expert: confirm that the interface matches the
globalization used for dyadic, unary, and non-dyadic test lattices.  Question
for the formalization expert: instantiate the four laws for actual
number-field lattices and verify the orientation of local equivalence.

Author decision, reviewer name, date, and signature: not provided.

## Theorem 1.5: complete local range, conditional global deduction

Paper location: p. 562; separate unary proof on p. 586. Formal endpoint:
`Bong.BONG.GoodBONG.he2022ClassicTheorem15_allRanks`, with branch endpoints
`he2022ClassicTheorem15_unary` and `he2022ClassicTheorem15`.

Paper statement: if the localized lattice is classic n-universal, its rank is
at least n + 3 >= 4, and every unsigned adjacent defect is greater than one,
then the dyadic ramification index is one. If this holds at every dyadic prime,
two is unramified in the number field, equivalently its discriminant is odd.

Formal translation: at a single dyadic field, under the corresponding local
assumptions and throughout n >= 1, the ramification index is one. The source
rank is written `tail + 2` so adjacent indices have type `Fin (tail + 1)`.
The unary proof converts classic 1-universality to scalar universality, applies
Beli's universal criterion, and proves alpha_1 > 1 by checking every candidate
in its defining finite minimum. The n >= 2 branch is the previously checked
Theorem 1.1 argument. The all-dyadic-primes conclusion is separately proved
by `he2022ClassicTheorem15_discriminantOdd`; Report 32 proves the required
number-field discriminant theorem and supplies its typed place bridge.

Common definitions and assumptions: classic integrality, classic
n-universality, rank bound, unsigned adjacent defects, and dyadic valuation.
Difference: the concrete localizations and place bridge are not yet
constructed; the discriminant theorem itself is now proved.

Current status: `FULLY_FORMALIZED_LOCAL_COMPONENT` plus
`CONDITIONAL_FORMALIZATION` of the global deduction; relationship to the full
printed theorem remains partial until the arithmetic package is instantiated.
Question for the author/domain expert: Confirm the local translation and the
unary bridge to Beli's criterion, without treating it as the global clause.
Question for the formalization expert: Verify that no implicit global claim
is introduced by the endpoint name.

Author decision, reviewer name, date, and signature: not provided.

## Theorem 1.3: separate the testing obligations

Paper location: p. 561, with the v5 proof bridge in Lemma 7.1. The source
asserts even and odd testing equivalences, the displayed residue-cardinality
counts, and inclusion-minimality of the testing families. The code constructs
the literal indexed rows and proves both equivalences plus a deletion witness
for every row. O'Meara 63:5 and 63:9 and all three counts are internally
proved.

Current status: `FULLY_FORMALIZED_PROVISIONAL_MATCH` to v5. The final odd
endpoint has no lower-even J2 premise; that condition occurs only inside the
factored proof. Question for the author/domain expert: Confirm that the three
v5 Lemma 7.1 branches and the extra `C_1(1)` row are represented exactly.
Question for the formalization expert: Check the odd-to-even table case split,
the construction of the source good BONG, both testing equivalences, and both
rowwise deletion arguments independently.

The author's provision of v5 selects the source version but does not itself
constitute independent semantic or Lean-expert sign-off.

## Corollary 6.3 and Lemma 8.3: v6 repair required

Paper locations: v5 lines 1361--1365 and 1681--1692. Both statements are
unrestricted in parity, but both proofs begin by assuming that `n` is even
without a cited reduction. The even proof uses terminal-order conclusions
which are not the literal odd clause of Theorem 1.1.

Current status: `SOURCE_STATEMENT_FALSE_IN_ODD_RANK`. The formal code proves
`he2022ClassicCorollary63_even` and constructs an `e=2`, `n=3` source lattice
that is classic `3`-universal but not isometric to the diagonal lattice with
the same displayed coefficients. Therefore Corollary 6.3 must be restricted
to even `n >= 2` or replaced by a genuinely different odd conclusion. Lemma
8.3 and Theorem 1.8 stay conditional and need the same restriction or a new
odd proof.  Report 28 applies the even-rank restriction to the Lean endpoints;
Reports 24 and 26 give the counterexample and source analysis.

Author decision on the v6 repair, reviewer name, date, and signature: not
provided.

## Section 8 and Theorems 1.7--1.9: conditional arithmetic layer

Paper location: v5 Section 8. Formal endpoints are collected in
`Bong/Lattice/He2022ClassicSectionEight.lean` and audited from the canonical
paper module.

The rank bounds, positive-rank convention, selected ramified pair of places,
and both directions of the sums-of-squares biconditional are explicit. The
proof-data structures separately name localization/globalization,
ramification and defect scaling, good-BONG transfer, discriminant parity, the
diagonal coefficient step, the ramified-extension obstruction, separate
finite-place universality branches, and strong approximation.

Current status: `CONDITIONAL_FORMALIZATION`. Question for the author/domain
expert: confirm that Report 23 partitions the cited arithmetic inputs exactly
as the v5 proofs use them. Question for the formalization expert: construct
and audit concrete number-field instances before promoting any endpoint to an
unconditional match.

The formal Lemma 8.3 and Theorem 1.8 endpoints additionally require
`n >= 2` and `Even n`; their unrestricted odd branches are not present.
The author should confirm this restriction or provide a replacement odd proof
before a future source version is treated as complete.

For Theorem 1.9, the global-universality conclusion is no longer an input.
The proof localizes each admissible integral rank-`n` target and then invokes
an explicit strong-approximation representation law.  The formalization
expert should instantiate this law for actual number-field lattices and check
that finite-place representation plus the encoded real-place admissibility is
exactly the hypothesis used by the cited theorem; see Report 29.

For the discriminant step, Report 32 proves for actual number fields that odd
discriminant is equivalent to ramification index one at every dyadic prime
ideal. It also proves the even-discriminant witness and positivity. The
number-field expert should now review only the structural identification of
the abstract finite places and indices with these prime ideals; see Reports 30
and 32.

For Theorem 1.9's finite-place step, the all-places conclusion is now derived
from separate non-dyadic, dyadic unary, and dyadic higher-rank laws.  The
number-field expert should confirm those are exactly the three local cases in
v5 line 1700 and supply concrete bridges to the cited local theorems; see
Report 31.

Author decision, reviewer name, date, and signature: not provided.
