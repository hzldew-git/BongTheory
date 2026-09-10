# Hidden assumptions

Classic integrality is stronger than norm integrality under the repository
normalization `Q(x)=B(x,x)`: every bilinear pairing must be integral. The local
field interface, finite-dimensionality, lattice fullness, and source classic
integrality are explicit. The new global layer types localization, positivity,
ramification, and extension of scalars abstractly; its concrete number-field
instances remain outside the proved scope.

Theorem 1.1 and the all-ranks local Theorem 1.5 endpoint visibly take
`QuadraticDefectLaws`, `HilbertSymbolLaws`, and
`DyadicDiscriminantClassLaws`. These arithmetic interfaces must be read along
with their proved instances; their presence is not erased by a standard-only
axiom report. Neither endpoint assumes the classic-universality criterion as
a new law. The unary branch derives scalar universality from classic
1-universality and invokes the proved Beli universal criterion; it does not
postulate the unary conclusion. The local endpoint itself contains no
number-field localization, all-dyadic-primes quantifier, or discriminant
equivalence.

`HeClassic2024LocalExtensionData.Lemma81Laws`,
`HeClassic2024GlobalData.SectionEightLaws`, and
`HeClassic2024ExtensionData.Lemma83Laws` expose every arithmetic input used by
the conditional Section 8 deductions. In particular, they expose O'Meara
81:14 globalization, localization of universality, the ramification-index and
defect scaling laws, transfer of a good BONG, the discriminant/unramifiedness
directions, the diagonal coefficient step, the ramified-extension
obstruction, and strong approximation for sums of squares. These structures
are theorem premises and have no concrete instances in this checkpoint; a
standard-only axiom report does not discharge them. See Report 23.

Report 27 removes the complete Proposition 8.2 conclusion from
`SectionEightLaws`.  Its replacement `Proposition82Laws` still assumes four
concrete facts: integrality localizes, an arbitrary integral local lattice
has a positive-definite integral globalization of the same rank up to local
equivalence, representation localizes, and representation is invariant under
equivalence of the represented local lattice.  These are ordinary theorem
premises, not Lean axioms, and concrete number-field instances remain open.

The local ramified-extension obstruction is not available in unrestricted
rank.  `Lemma83Laws.local_ramified_obstruction` explicitly requires
`2 <= n` and `Even n`; these are not implementation conveniences but the
scope of the argument actually written in v5.  No field or theorem supplies
the unsupported odd branch; see Report 28.

Report 29 removes the global-universality conclusion from the
`sumOfSquares_local_to_global` field.  The replacement package still assumes
global integrality of the sum-of-squares lattice, rank and integrality
localization, and strong approximation for an admissible global target once
all finite-place representations are known.  The concrete number-field and
archimedean interpretation of those premises remains open.

Report 30 removes the reverse direction from the general
`DiscriminantRamificationLaws` package.  Its remaining arithmetic premise says
that ramification index one at every dyadic place implies odd discriminant,
and its contrapositive existence witness is derived in Lean.  Report 31 makes
clear that the converse direction is nevertheless required by the unary
sufficiency branch of Theorem 1.9; it is now a separate field of the specialized
local-universality package.  Concrete number-field instances of both directions
are still required.

Report 31 removes the all-finite-places local-universality conclusion from
`SectionEightLaws`.  Its replacement exposes four concrete inputs: odd
discriminant gives ramification index one at a dyadic place; the sum-of-squares
lattice is locally universal at non-dyadic places; its dyadic unary case holds
at ramification index one; and its dyadic `n >= 2` case follows from the local
criterion.  Lean derives the exhaustive case split, but concrete completion
instances and bridges to the local BONG theorems remain open.

`card_heClassicUnitRepresentatives` derives O'Meara 63:9 from the proved
principal-unit filtration, after constructing the explicit equivalence between
the published representative index and the intrinsic unit square-class
quotient. The same equivalence restricts non-defect-one representatives to the
depth-two principal-unit subgroup; its proved cardinality gives O'Meara 63:5.
Consequently all three `he2022ClassicProposition28ii_*` numerical endpoints are
unconditional and no paper-specific counting-law interface remains.

The older auxiliary endpoint named
`all_publishedOdd_implies_classicUniversal_of_lowerJ2` retains the lower-even
J2 premise explicitly. It remains useful as a factored proof step but is not
the v5 source endpoint.

Report 20 historically sharpened this dependency. The endpoint
`all_publishedOdd_implies_classicUniversal_of_lowerTerminalUpper` needs only
the single lower-even terminal inequality; for `e > 1`,
`all_publishedOdd_implies_classicUniversal_of_lowerJ2Prime` needs lower
`J2'_E`. Author-corrected v5 now removes any external premise at the public
endpoint: `all_publishedOdd_implies_all_publishedEven_v5` derives the complete
even table directly, and
`all_publishedOdd_implies_classicUniversal_v5_auto` obtains lower `J2_E` from
the already proved even necessity theorem. All field-law interfaces remain
visible theorem assumptions; no paper-specific v5 bridge is introduced as an
axiom.
