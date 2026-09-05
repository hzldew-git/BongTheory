# Formal declaration inventory

- `Bong.Lattice.IsNADC`: local dyadic `n`-ADC predicate.
- `Bong.Lattice.IsNUniversal.isNADC`: proved implication.
- `RepresentsAllRelevantOMaximalOfRank`: the restricted maximal test family.
- `heADCLemma21LocalDyadic`: proved local dyadic specialization of Lemma 2.1.

Additional concrete declaration groups are:

- `isNADC_iff_isNUniversal_of_rank_add_three_le`: dyadic stable-rank equivalence.
- `He2023ADCSectionThree`: direct endpoints for Lemma 3.1 through Theorem 3.6.
- `He2023ADCPublishedRepresentation`: `heADC2025Theorem36Published` and
  `heADC2025Theorem36PublishedFull`, retaining the publisher's exact
  condition-(iii) sum of capped defects; report 20 distinguishes packages.
- `He2023ADCSectionFour`: space tables, representation lemmas, maximal table,
  and rank-at-least-two literal minimal testing sets.
- `OMaximalVolume`: maximality and isometry characterized by volume order.
- `He2023ADCMaximalProfiles`: Remark 4.10 and ten canonical-model branches of
  the arbitrary-lattice criteria in Lemmas 4.11--4.12.
- `He2023ADCPublishedProfiles`: whole-space and maximal-lattice transport,
  the exceptional even rows, all odd rows, and the unary boundary on the
  published `W/N` families; the auxiliary `kappa` is constructed internally.
- `He2023ADCGenericProfiles`: both nonexceptional unit and unit-uniformizer
  columns, with defect parity and the sharp partner derived from the domain.
- `heADCLemma414LocalDyadic`, `heADCProposition415LocalDyadic`: maximality and ADC.
- `He2023ADCOddMaximalStructure`: normalized ambient exhaustion, the complete
  order profile of an arbitrary odd-rank maximal lattice, and
  `heADC2025Proposition413`, proving all order, alpha, and capped-defect clauses.
- `He2023ADCQuaternaryMaximal`: maximal isotropic lattices represent the
  half-hyperbolic plane; the quaternary exception is precisely `N_2^4(1)`;
  `heADC2025Proposition416Dyadic` includes its integral `A perp A^(pi)` model.
  `heADCAForm_bilin_apply` verifies the exact published Gram normalization.
- `He2023ADCEvenRepresentationBounds`: represented endpoint pairs, the strict
  cross-gap square conclusion including codimension one, and a two-class
  next-order bound. These are support lemmas, not separate paper results.
- `He2023ADCEvenFirstTests`: constructed good BONGs on the actual first-column
  tests, their determinant separation, and `heADC2025Lemma64ii`.
- `He2023ADCEvenFirstDefects`: `heADC2025Lemma64i`, including exact raw
  signed-prefix defects and the equal-rank unconditional order conclusion.
- `He2023ADCEvenSecondTests`: `heADC2025Lemma64iii`, including the empty-head
  binary discriminant case and the exact three final-pair alternatives.
- `He2023ADCEvenMixedTests`: the two actual kappa profiles and
  `heADC2025Lemma64iv` for all five named tests, deriving the strict rank
  inequality and next order in `{0,1,2}`.

- `He2023ADCEvenTerminalObstruction`: arbitrary actual target profiles and
  `heADC2025Lemma65i`, with the precise failing index n.
- `He2023ADCEvenPenultimateObstruction`: capped alternating and mixed-prefix
  bounds and `heADC2025Lemma65ii`, with the precise failing index n-1.
- `He2023ADCEvenCorankOneTests`: actual exactly-one maximal tests in
  Lemma 4.6(i)'s even corank-one specialization and the necessary ADC profile.
- `He2023ADCCorankOneVolume`: maximal-superlattice volume gap and the
  standard-tail maximality proof, not a converse of Proposition 4.13.
- `He2023ADCCorankOneAmbient`: two concrete ambient embeddings and the
  raised-tail exclusion of all but the second-column unit row.
- `He2023ADCEvenCorankOne`: `Bong.Lattice.heADC2025Theorem61`, the complete
  equivalence on arbitrary full lattices, constructing its BONG internally.
- `He2023ADCEvenCentralTrigger`: three capped-defect inequalities proving
  the actual published central trigger, including the binary boundary.
- `He2023ADCEvenCentralPrefix`: five prefix geometry lemmas using arbitrary
  even next order or raw defect class, then same-parameter non-representation.
- `He2023ADCEvenCentralObstruction`: target profiles from actual isometries,
  `heADC2025Lemma66_endpoint`, and both full numbered `heADC2025Lemma66i/ii`.
- `He2023ADCEvenCentralAlpha`: actual representation bounds the terminal
  capped defect; alpha alternatives and raw-defect equality are derived;
  `heADC2025Lemma67_endpoint` and both full `heADC2025Lemma67i/ii` are exported.
- `He2023ADCEvenCorankTwoTests`: actual hyperbolic/nonexceptional ambient
  embeddings and n-ADC lifting to the named maximal tests.
- `He2023ADCSignedDeterminant`: full-product square-class/defect transport
  from actual ambient isometry, and the raw alternating-head lower bound.
- `He2023ADCEvenCorankTwoFirst`: arbitrary-lattice endpoints
  `Bong.Lattice.heADC2025Lemma68i` and `heADC2025Lemma68ii`; these complete
  only 2/6 clauses of Lemma 6.8, with exact rank restrictions retained.
- `He2023ADCEvenCorankTwoGenericOrders`, `GenericTests`, and `Generic`
  prove clauses (v),(vi) on the actual class-exclusion domain, deriving
  all tests, orders, normalization and original-parameter lattice isometry.
- `He2023ADCPublishedParameterDomain` proves the normalized square
  representative equals 1 and bridges the printed exclusion on V with
  explicit Delta in U. Its `Published` wrappers expose that convention.
  Together with report 23 this earlier checkpoint supplied 4/6 clauses.
- `AlternatingEndpointEvenOrders` and `He2023ADCEvenEndpointExclusion`
  normalize even leading orders only in the ambient quadratic space and
  exclude both an even-leading endpoint tower and final order -2e.
- `He2023ADCEvenSecondEndpointOrders` and `He2023ADCEvenSecondEndpointTests`
  derive the full terminal profile from internally constructed actual tests.
- `He2023ADCEvenCorankTwoSecond` exports full `heADC2025Lemma68iii` and
  only the n>=4 endpoint `heADC2025Lemma68iv_of_pos`, on arbitrary actual
  lattices. Report 25 raises the count to 5/6 whole clauses; n=2 of (iv)
  is explicitly not asserted.

`GlobalLocalLatticeSystem` defines global ADC, global universality, local ADC,
and regularity. Its `heADCTheorem13` and `heADCTheorem14*` are conditional
logical reductions, not constructions of number-field completions or proofs
of the global arithmetic inputs. `BongTest.He2023ADCAudit` prints the actual
public types and selected transitive axiom sets.
