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
- `heADCLemma414LocalDyadic`, `heADCProposition415LocalDyadic`: maximality and ADC.

`GlobalLocalLatticeSystem` defines global ADC, global universality, local ADC,
and regularity. Its `heADCTheorem13` and `heADCTheorem14*` are conditional
logical reductions, not constructions of number-field completions or proofs
of the global arithmetic inputs. `BongTest.He2023ADCAudit` prints the actual
public types and selected transitive axiom sets.
