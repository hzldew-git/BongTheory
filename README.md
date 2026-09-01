# BongTheory

`BongTheory` is a Lean 4 formalization of the theory of bases of norm generators
(BONGs) for quadratic lattices over dyadic local fields.  Its principal source
results are five papers by Constantin N. Beli published or circulated in 2003,
2006, 2009/2010, 2019/2022, and 2022.

## Current status

- Proof-assistant status: the public theorem endpoints compile without
  project-specific law parameters and use only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Semantic-fidelity status: `PROVISIONAL_MATCH`.
- Beli Universal coverage status:
  `FORMALIZATION_COMPLETE_WITH_SOURCE_DISCREPANCY`; its printed Theorem 3.1
  exponent is kept separate from the exponent derived from Theorem 2.1.
- Project grade: B.
- Local reproducibility status:
  `REPRODUCIBLE_WITH_DOCUMENTED_EXTERNAL_DEPENDENCIES` at commit
  `5befe079dbf3569d1760b8e66bc52aef0de21745`.
- Public hosted reproducibility status: exact-tag Ubuntu and Windows checks
  passed under the scopes and cache boundaries recorded in the public
  `v0.2.0-rc.1` receipt.  The initial Ubuntu build succeeded but its following
  audit step exposed a cross-platform workflow-path defect; the failure and
  corrected exact-tag run are both retained in that receipt.

Compilation is evidence that Lean accepts the encoded statements.  It is not,
by itself, evidence that every paper statement has been translated faithfully.
The independent mathematical-review package is under [`docs/audit`](docs/audit).

## Formalized public results

| Source | Paper result | Lean endpoint |
|---|---|---|
| Beli 2003 | Theorem 1 | `Bong.BONG.beliTheoremOne_proved` |
| Beli 2003 | Theorem 2 | `Bong.Lattice.beliTheoremTwo_proved` |
| Beli 2003 | Theorem 3 | `Bong.BONG.beliTheoremThree_proved` |
| Beli 2006 | Theorem 3.2 | `Bong.beli2006Theorem32_proved` |
| Beli 2006 | Theorem 4.5 | `Bong.beli2006Theorem45_proved` |
| Beli 2009/2010 | Theorem 3.1 | `Bong.BONG.GoodBONG.beli2009Theorem31_concrete` |
| Beli 2019 v2 | Theorem 2.1 | `Bong.beli2019Theorem21` |
| Beli 2019 v2 | Theorem 2.1 with (iii') | `Bong.beli2019Theorem21_prime` |
| Beli Universal | Theorem 2.1 | `Bong.BONG.GoodBONG.isUniversal_iff_universalTheorem21Conditions` |
| Beli Universal | Theorem 3.1, direct derivation | `Bong.Lattice.JordanDecomposition.isUniversal_iff_universalTheorem31DirectConditions` |
| Beli Universal | Corollary 4.10 | `Bong.BONG.GoodBONG.beliUniversalCorollary410` |

See [`THEOREM_INDEX.md`](THEOREM_INDEX.md) for a fuller source-to-code map and
[`SOURCES.md`](SOURCES.md) for the exact paper versions used.

## Reproduce locally

The repository pins Lean in [`lean-toolchain`](lean-toolchain) and all Lake
dependencies in [`lake-manifest.json`](lake-manifest.json).

```text
lake exe cache get
lake build
lake env lean BongTest/FinalPublicTheoremAudit.lean
lake env lean BongTest/Beli2006Audit.lean
lake env lean BongTest/Beli2009Audit.lean
lake env lean BongTest/Beli2019Audit.lean
lake env lean BongTest/BeliUniversalAudit.lean
```

For the complete clean-clone protocol and expected output, see
[`REPRODUCING.md`](REPRODUCING.md).  The audited Windows source-rebuild receipt
is [`docs/reproducibility/clean-clone-5befe079.md`](docs/reproducibility/clean-clone-5befe079.md).
The current public hosted receipt is
[`docs/reproducibility/github-actions-v0.2.0-rc.1.md`](docs/reproducibility/github-actions-v0.2.0-rc.1.md).

## Repository layout

```text
Bong/                  formal definitions and proofs
BongTest/              compilation, signature, and axiom audits
docs/audit/            semantic-fidelity review packages
docs/DevelopmentHistory.md
                       chronological M0--M... development record
```

Development scratch files and generated `.olean` files are intentionally not
tracked.  Publisher PDFs are not redistributed; the repository records source
links and cryptographic hashes instead.

## Trust and review

The formal trust boundary and the distinction between kernel checking,
reproducibility, and mathematical semantic review are documented in
[`TRUST.md`](TRUST.md).  Instructions for independent reviewers are in
[`REVIEWING.md`](REVIEWING.md).

## License and citation

The Lean source is released under Apache-2.0; see [`LICENSE`](LICENSE).  Citation
metadata is provided in [`CITATION.cff`](CITATION.cff).  The papers remain under
their respective publishers' or arXiv licences.
