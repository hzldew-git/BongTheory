# BongTheory

`BongTheory` is a Lean 4 formalization of the theory of bases of norm generators
(BONGs) for quadratic lattices over dyadic local fields.  Its principal source
results are five papers by Constantin N. Beli published or circulated in 2003,
2006, 2009/2010, 2019, and 2020. The two arXiv papers use their frozen 2022
v2 revisions. Active extensions cover the published versions of the He--Hu
`n`-universality paper, He's classic `n`-universality paper, and He's `n`-ADC
paper; those three extensions are explicitly marked partial.

## Current status

- Proof-assistant status: the public theorem endpoints compile without
  project-specific law parameters and use only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Semantic-fidelity status: `PROVISIONAL_MATCH`.
- Beli 2020 coverage status:
  `FORMALIZATION_COMPLETE_WITH_SOURCE_DISCREPANCY`; its printed Theorem 3.1
  exponent is kept separate from the exponent derived from Theorem 2.1.
- He-paper coverage status: `PARTIAL`. The He--Hu and He classic headline
  criteria currently have complete proposition/condition layers but not proofs
  of the equivalences. The ADC entry proves only the local dyadic specialization
  of Lemma 2.1.
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
| Beli 2020 | Theorem 2.1 | `Bong.BONG.GoodBONG.isUniversal_iff_universalTheorem21Conditions` |
| Beli 2020 | Theorem 3.1, direct derivation | `Bong.Lattice.JordanDecomposition.isUniversal_iff_universalTheorem31DirectConditions` |
| Beli 2020 | Corollary 4.10 | `Bong.BONG.GoodBONG.beliUniversalCorollary410` |

See [`THEOREM_INDEX.md`](THEOREM_INDEX.md) for a fuller source-to-code map and
[`SOURCES.md`](SOURCES.md) for the exact paper versions used.

## He papers under active formalization

| Published source | Current public endpoint | Honest status |
|---|---|---|
| He--Hu, *Sci. China Math.* 67 (2024), Theorems 1.1-1.2 | `heHu2022Theorem11`, `heHu2022Theorem12PublishedEvenLiteral`, `heHu2022Theorem12PublishedOddLiteral` | proved; semantic review remains provisional |
| He, *manuscripta math.* 174 (2024), Theorem 1.1 | `Bong.BONG.GoodBONG.he2022ClassicTheorem11` | full local equivalence proved; testing and global parts of the paper remain incomplete |
| He, *Doc. Math.* 30 (2025), Lemmas 4.11-4.12 | published-family endpoints in `He2023ADCPublishedProfiles` and `He2023ADCGenericProfiles` | maximal profiles proved; the paper remains partially formalized |

The Classic paper's literal Lemma 7.1(ii) is refuted for ramification index
greater than one; it is not assumed or silently repaired. The local
Theorem 1.5 endpoint covers n >= 2 only. See each paper's fidelity report for
exact coverage, assumptions, source discrepancies, and missing human approval.

For these three papers the publisher version of record is the sole semantic
authority. Preprints are retained only as separately hashed comparison sources.
The implementation order and promotion gates are recorded in
[`docs/HePapersRoadmap.md`](docs/HePapersRoadmap.md).

## Download one paper

Reviewers do not need the complete development tree. The
[`paper-specific Review Kit index`](papers/INDEX.md) links released source-only
ZIPs and records pending kits. Each kit contains its canonical Lean entry,
axiom audit, fidelity package, exact source commit, and checksums. Every kit is
generated from the local transitive import closure and is built again after
extraction; unreleased manifests are also built as per-paper CI artifacts.

The metadata-driven procedure in [`papers/SCHEMA.md`](papers/SCHEMA.md) is the
default distribution requirement for every later BONG-related paper added to
this repository.

## Reproduce locally

The repository pins Lean in [`lean-toolchain`](lean-toolchain) and all Lake
dependencies in [`lake-manifest.json`](lake-manifest.json).

```text
lake exe cache get
lake build
lake env lean BongTest/FinalPublicTheoremAudit.lean
lake env lean BongTest/Beli2003Audit.lean
lake env lean BongTest/Beli2006Audit.lean
lake env lean BongTest/Beli2009Audit.lean
lake env lean BongTest/Beli2019Audit.lean
lake env lean BongTest/Beli2020Audit.lean
lake env lean BongTest/HeHu2022Audit.lean
lake env lean BongTest/He2022ClassicAudit.lean
lake env lean BongTest/He2023ADCAudit.lean
```

For the complete clean-clone protocol and expected output, see
[`REPRODUCING.md`](REPRODUCING.md).  The audited Windows source-rebuild receipt
is [`docs/reproducibility/clean-clone-5befe079.md`](docs/reproducibility/clean-clone-5befe079.md).
The current public hosted receipt is
[`docs/reproducibility/github-actions-v0.2.0-rc.1.md`](docs/reproducibility/github-actions-v0.2.0-rc.1.md).

## Repository layout

```text
Bong/                  formal definitions and proofs
Bong/Papers/           canonical paper-specific import entry points
BongTest/              compilation, signature, and axiom audits
papers/                paper manifests, download index, and packaging standard
scripts/paper-kits/     Review Kit generation and clean-extract verification
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
