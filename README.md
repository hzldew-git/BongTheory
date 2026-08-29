# BongTheory

`BongTheory` is a Lean 4 formalization of the theory of bases of norm generators
(BONGs) for quadratic lattices over dyadic local fields.  Its principal source
results are four papers by Constantin N. Beli published or circulated in 2003,
2006, 2009/2010, and 2019/2022.

## Current status

- Proof-assistant status: the public theorem endpoints compile without
  project-specific law parameters and use only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Semantic-fidelity status: `PROVISIONAL_MATCH`.
- Project grade: B.
- Local reproducibility status:
  `REPRODUCIBLE_WITH_DOCUMENTED_EXTERNAL_DEPENDENCIES` at commit
  `ee826e7a8e67dda053563c01e027b2379bd68e6f`.
- Public hosted reproducibility status: exact-tag Ubuntu and Windows checks
  passed under the scopes and cache boundaries recorded in the public
  GitHub Actions receipt.

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
```

For the complete clean-clone protocol and expected output, see
[`REPRODUCING.md`](REPRODUCING.md).  The audited Windows source-rebuild receipt
is [`docs/reproducibility/clean-clone-ee826e7.md`](docs/reproducibility/clean-clone-ee826e7.md),
and the public release-candidate CI receipt is
[`docs/reproducibility/github-actions-v0.1.0-rc.1.md`](docs/reproducibility/github-actions-v0.1.0-rc.1.md).

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
