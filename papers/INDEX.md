# Paper-specific Lean 4 review kits

Each row provides a canonical paper entry point, a kernel/axiom audit, and a
standalone source-only Review Kit. The kits contain the paper's complete local
import closure and pinned Lake metadata, but no `.lake`, `.olean`, publisher
PDF, unrelated milestone test, or Git history.

| Paper | Formalization entry | Audit | Fidelity materials | Review Kit download/status |
|---|---|---|---|---|
| Beli 2003 | [`Bong.Papers.Beli2003`](../Bong/Papers/Beli2003.lean) | [`BongTest.Beli2003Audit`](../BongTest/Beli2003Audit.lean) | [`Beli2003`](../docs/audit/Beli2003) | [`Beli2003 review kit`](https://github.com/hzldew-git/BongTheory/releases/download/v0.3.0-rc.1/BongTheory-Beli2003-v0.3.0-rc.1-review-kit.zip) |
| Beli 2006 | [`Bong.Papers.Beli2006`](../Bong/Papers/Beli2006.lean) | [`BongTest.Beli2006Audit`](../BongTest/Beli2006Audit.lean) | [`Beli2006`](../docs/audit/Beli2006) | [`Beli2006 review kit`](https://github.com/hzldew-git/BongTheory/releases/download/v0.3.0-rc.1/BongTheory-Beli2006-v0.3.0-rc.1-review-kit.zip) |
| Beli 2009/2010 | [`Bong.Papers.Beli2009`](../Bong/Papers/Beli2009.lean) | [`BongTest.Beli2009Audit`](../BongTest/Beli2009Audit.lean) | [`Beli2009`](../docs/audit/Beli2009) | [`Beli2009 review kit`](https://github.com/hzldew-git/BongTheory/releases/download/v0.3.0-rc.1/BongTheory-Beli2009-v0.3.0-rc.1-review-kit.zip) |
| Beli 2019 v2 | [`Bong.Papers.Beli2019`](../Bong/Papers/Beli2019.lean) | [`BongTest.Beli2019Audit`](../BongTest/Beli2019Audit.lean) | [`Beli2019V2`](../docs/audit/Beli2019V2) | [`Beli2019 review kit`](https://github.com/hzldew-git/BongTheory/releases/download/v0.3.0-rc.1/BongTheory-Beli2019-v0.3.0-rc.1-review-kit.zip) |
| Beli 2020 | [`Bong.Papers.Beli2020`](../Bong/Papers/Beli2020.lean) | [`BongTest.Beli2020Audit`](../BongTest/Beli2020Audit.lean) | [`Beli2020`](../docs/audit/Beli2020) | [`Beli2020 review kit`](https://github.com/hzldew-git/BongTheory/releases/download/v0.3.0-rc.1/BongTheory-Beli2020-v0.3.0-rc.1-review-kit.zip) |
| He--Hu 2022 (published 2024) | [`Bong.Papers.HeHu2022`](../Bong/Papers/HeHu2022.lean) | [`BongTest.HeHu2022Audit`](../BongTest/HeHu2022Audit.lean) | [`HeHu2022`](../docs/audit/HeHu2022) | Pending next release; manifest [`hehu2022`](hehu2022/paper.json) |
| He 2022 Classic (published 2024) | [`Bong.Papers.He2022Classic`](../Bong/Papers/He2022Classic.lean) | [`BongTest.He2022ClassicAudit`](../BongTest/He2022ClassicAudit.lean) | [`He2022Classic`](../docs/audit/He2022Classic) | Pending next release; manifest [`he2022classic`](he2022classic/paper.json) |
| He 2023 ADC (published 2025) | [`Bong.Papers.He2023ADC`](../Bong/Papers/He2023ADC.lean) | [`BongTest.He2023ADCAudit`](../BongTest/He2023ADCAudit.lean) | [`He2023ADC`](../docs/audit/He2023ADC) | Pending next release; manifest [`he2023adc`](he2023adc/paper.json) |

The Beli 2020 row denotes the paper first submitted in 2020. Its frozen source
is arXiv:2008.10113v2, revised in 2022. The paper year and revision year are
recorded separately throughout the repository.

For the three He papers, the historical work year remains in the implementation
name, while `publicationYear`, the full journal citation, DOI, and publisher PDF
hash are recorded separately. Only the publisher version of record is
authoritative; arXiv files are comparison sources.
The current proof order and promotion gates are in
[`docs/HePapersRoadmap.md`](../docs/HePapersRoadmap.md).

## Verification inside any kit

### Verified development checkpoint: 2026-09-05

Before the next tagged release, the following independent CI artifacts are
available for the fixed merge-test source commit
`6bf3bdf8bd272109e898335683f05bb76664330c`. Its source tree is identical to
branch commit `db0398506b2e242288bc979217972c6a1d175674`.

| Paper | Independently verified CI artifact | Scope of this checkpoint |
|---|---|---|
| He--Hu 2022 | [Download He--Hu checkpoint](https://github.com/hzldew-git/BongTheory/actions/runs/33929872783/artifacts/9958197730) | Published-paper development and audit; human semantic sign-off remains pending |
| He 2023 ADC | [Download ADC checkpoint](https://github.com/hzldew-git/BongTheory/actions/runs/33929872783/artifacts/9958233657) | Partial paper, including all published Lemma 4.11-4.12 profiles; does not include later Proposition 4.13, dyadic Proposition 4.16, Lemmas 6.4-6.7 or Theorem 6.1 |

These are temporary workflow artifacts with 30-day retention, not permanent
Release assets. Consult the [workflow run](https://github.com/hzldew-git/BongTheory/actions/runs/33929872783)
for the separate paper jobs. A green job for one paper does not certify the
others or a later commit. The Classic job had not completed when this
checkpoint index was recorded. Tagged releases remain the permanent download
channel above.

These older artifacts predate the enforcing transitive-axiom gate added on
5 September. Their successful builds and individually inspected axiom
reports must not be described as passing that newer gate. Newly generated
kits include `BongTest.PaperAxiomGate` automatically; see
[`SCHEMA.md`](SCHEMA.md) and the
[deployment correction](../docs/audit/HePaperDeploymentCheckpoint-20260905.md).

### Build and audit

```text
lake exe cache get
lake build
lake env lean <audit-path-from-paper-manifest.json>
```

The Mathlib cache is an optimization. A fresh extraction may instead run
`lake --no-cache build` to compile the pinned dependency closure locally.
