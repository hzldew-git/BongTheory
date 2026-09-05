# Formal declaration inventory

- `Bong.Lattice.IsNADC`: local dyadic `n`-ADC predicate.
- `Bong.Lattice.IsNUniversal.isNADC`: proved implication.
- `RepresentsAllRelevantOMaximalOfRank`: the restricted maximal test family.
- `heADCLemma21LocalDyadic`: proved local dyadic specialization of Lemma 2.1.

Additional concrete declaration groups are:

- `isNADC_iff_isNUniversal_of_rank_add_three_le`: dyadic stable-rank equivalence.
- `He2023ADCSectionThree`: direct endpoints for Lemma 3.1 through Theorem 3.6.
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

`GlobalLocalLatticeSystem` defines global ADC, global universality, local ADC,
and regularity. Its `heADCTheorem13` and `heADCTheorem14*` are conditional
logical reductions, not constructions of number-field completions or proofs
of the global arithmetic inputs. `BongTest.He2023ADCAudit` prints the actual
public types and selected transitive axiom sets.
