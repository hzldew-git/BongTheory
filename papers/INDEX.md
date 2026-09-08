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
| He--Hu 2022 (published 2024) | [`Bong.Papers.HeHu2022`](../Bong/Papers/HeHu2022.lean) | [`BongTest.HeHu2022Audit`](../BongTest/HeHu2022Audit.lean) | [`HeHu2022`](../docs/audit/HeHu2022) | [`HeHu2022 review kit`](https://github.com/hzldew-git/BongTheory/releases/download/v0.4.0-rc.1/BongTheory-HeHu2022-v0.4.0-rc.1-review-kit.zip); complete formal coverage, human sign-off pending |
| He 2023 ADC (published 2025) | [`Bong.Papers.He2023ADC`](../Bong/Papers/He2023ADC.lean) | [`BongTest.He2023ADCAudit`](../BongTest/He2023ADCAudit.lean), [`Q2 boundary`](../BongTest/He2023ADCQuaternaryBoundaryQ2.lean), [`Q2 Lemma 6.12`](../BongTest/He2023ADCExceptionalQuaternaryQ2.lean), [`dyadic Lemma 4.6`](../BongTest/He2023ADCLemma46Audit.lean), [`non-dyadic Lemma 4.6`](../BongTest/He2023ADCNonDyadicLemma46Audit.lean), [`non-dyadic table`](../BongTest/He2023ADCNonDyadicTableAudit.lean), [`non-dyadic Lemma 4.8`](../BongTest/He2023ADCNonDyadicLemma48Audit.lean), [`non-dyadic Proposition 4.15`](../BongTest/He2023ADCNonDyadicProposition415Audit.lean), [`non-dyadic Proposition 4.16`](../BongTest/He2023ADCNonDyadicProposition416Audit.lean), [`non-dyadic minimal testing`](../BongTest/He2023ADCNonDyadicMinimalTestingAudit.lean) | [`He2023ADC`](../docs/audit/He2023ADC) | [`He2023ADC review kit`](https://github.com/hzldew-git/BongTheory/releases/download/v0.4.0-rc.1/BongTheory-He2023ADC-v0.4.0-rc.1-review-kit.zip); in-progress Grade-D artifact: all dyadic Lemma 4.6 branches are actual-lattice theorems and the complete non-dyadic deduction is conditional on explicit lower-level laws; publisher Table 1 and non-dyadic Table 4.7 finite data are concrete; non-dyadic Lemmas 4.7(ii), 4.8, 4.14 and Propositions 4.15--4.16 have internal deductions with remaining actual-lattice laws explicit; published mismatches and global/external-classification inputs remain explicit |

The Beli 2020 row denotes the paper first submitted in 2020. Its frozen source
is arXiv:2008.10113v2, revised in 2022. The paper year and revision year are
recorded separately throughout the repository.

For the two deployed He papers, the historical work year remains in the implementation
name, while `publicationYear`, the full journal citation, DOI, and publisher PDF
hash are recorded separately. Only the publisher version of record is
authoritative; arXiv files are comparison sources.
The current proof order and promotion gates are in
[`docs/HePapersRoadmap.md`](../docs/HePapersRoadmap.md).

## Verification inside any kit

### New checkpoint with an enforcing axiom gate: 2026-09-05

This independently verified ADC kit uses actual merge-test source
`c82668b97ed80f0cead4493206cb6483c4e8d77d`, whose tree is identical to
branch head `f6f7485b6a3acabedbec5a7facce46f8ee7365ab`.

| Paper | Download | Verified scope |
|---|---|---|
| He 2023 ADC | [ADC kit through full Lemma 6.7](https://github.com/hzldew-git/BongTheory/actions/runs/33942437722/artifacts/9962394872) | Partial paper, including Proposition 4.13, dyadic 4.16, Theorem 6.1 and Lemmas 6.4--6.7; enforced dependency check on 57,480 declarations; later Lemma 6.8 additions are not included |

The logs and exact revision/hash receipts are in the
[deployment checkpoint](../docs/audit/HePaperDeploymentCheckpoint-20260905.md).
These are 30-day workflow artifacts, not permanent release assets or
whole-paper semantic certificates. Other jobs in the same run and subsequent
commits need their own evidence; no shared green status is assumed.

### Earlier development checkpoint without the new gate

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
others or a later commit. Tagged releases remain the permanent download
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
