# Exact Review Kit receipt through Report 68

This receipt fixes the independently extracted local proof-closure evidence for
commit `9350ca37181f3275129d16e091e9dd09a7ee5846`. That clean checkpoint
contains the non-dyadic Table 4.7 developments and every He ADC result recorded
through Report 68.

## Archive identity

- generated archive:
  `BongTheory-He2023ADC-ci-9350ca3-review-kit.zip`;
- archive size: 6,280,568 bytes;
- SHA-256:
  `D0E8EB1D552F1E72C9F9FA93B4E37905E5846057B383C5E0AAF5FC26795C420C`;
- recorded source commit:
  `9350ca37181f3275129d16e091e9dd09a7ee5846`;
- recorded source-tree state: `clean`;
- recorded local Lean sources under `Bong` and `BongTest`: 1,996;
- recorded packaged files: 2,087.

The archive contains 2,086 payload hashes in `FILES.sha256`. A separate
structure-only extraction verified every payload hash. The source archive has
no `.lake` or `.git` directory, compiled Lean artifact, or publisher PDF. It
also has no He classic Lean source, paper manifest, or audit directory.

This legacy archive predates the stricter paper-isolation format introduced
for the public `v0.4.0-rc.1` release. Its shared root-level `CITATION.cff`,
`SOURCES.md`, `TRUST.md`, `THEOREM_INDEX.md`, `REVIEWING.md`, audit landing
page, and sign-off template include references to other papers. In particular,
the theorem index names He classic declarations even though their source files
are absent. The current verifier therefore rejects this legacy archive because
its manifest lacks a paper-specific theorem-index prefix. This is a disclosed
documentation-isolation defect, not a proof-source or dependency-closure leak.
The final tagged He ADC package is regenerated with paper-specific versions of
all seven documents and is checked to contain exactly one paper manifest,
paper directory, audit directory, and theorem-index prefix.

## Dependency closure

All nine dependency worktrees in the full-build extraction were checked clean,
with `HEAD` exactly equal to the revision in `lake-manifest.json`:

```text
mathlib           520045ab14e26149ee970e2e617ca04b09bde5d6
plausible         e12c1910fe855cbfc38803cd4e55543906d5fa62
LeanSearchClient  c5d5b8fe6e5158def25cd28eb94e4141ad97c843
importGraph       7e9612bf0b9ee66db3cb5b9988a35afc706f5a12
proofwidgets      6e311e2a844da9b2cc3971187df2fe0066947b93
aesop             a7dbf0c63b694e47f425f3dcddbc0e178bb432d3
Qq                38d591e778f100aec9762bb582f9c7f55f50e9dc
batteries         023ce7d62a0531e22a5331e20b587817a80d49ff
Cli               88679d088c9720c27ebdf2ba4dafe17341747f94
```

No project `.olean` or other compiled output was copied into the extraction
before verification.

## Independent extraction and build

The initial unconstrained build in the fresh extraction exhausted host memory
and terminated with `std::bad_alloc`; Lean reported no source or proof error.
The same extraction was then resumed in stages with one worker and two workers,
both deliberately interrupted after stable progress, and finally with four
workers. Only artifacts produced inside this extraction were reused. The final
run completed all `5,581` jobs with Lean 4.32.1.

The following eleven paper gates were then rerun directly in the extracted
tree; each exited successfully:

```text
lake env lean BongTest/He2023ADCAudit.lean
lake env lean BongTest/He2023ADCQuaternaryBoundaryQ2.lean
lake env lean BongTest/He2023ADCExceptionalQuaternaryQ2.lean
lake env lean BongTest/He2023ADCLemma46Audit.lean
lake env lean BongTest/He2023ADCNonDyadicTableAudit.lean
lake env lean BongTest/He2023ADCNonDyadicLemma46Audit.lean
lake env lean BongTest/He2023ADCNonDyadicLemma48Audit.lean
lake env lean BongTest/He2023ADCNonDyadicProposition415Audit.lean
lake env lean BongTest/He2023ADCNonDyadicProposition416Audit.lean
lake env lean BongTest/He2023ADCNonDyadicMinimalTestingAudit.lean
lake env lean BongTest/PaperAxiomGate.lean
```

The standalone enforcing gate reported:

```text
AXIOM_GATE_PASS: 60948 declarations checked
```

Both checked-in exact-arithmetic verifiers were also rerun from this
extraction:

```text
wolframscript -file scripts/verification/verify_he2023adc_table1.wl
wolframscript -file scripts/verification/verify_he2023adc_nondyadic_table.wl
```

The first confirmed all 48 Table 1 determinants, symmetry, positive
definiteness, and the literal 21-row selection. The second confirmed all 12
published Table 4.7 symbolic profile checks. Every reported Boolean check was
`True`.

## Scope of this receipt

This closes local mechanical proof-closure reproducibility for exact clean
checkpoint `9350ca3` through Reports 61--68 and supersedes Report 60 for that
source closure. It does not include the later invariant derivations in Reports
70--72. It is deliberately retained as historical exact-source evidence, not
as the final release asset, because of the disclosed root-document isolation
defect.

It also does not certify GitHub-hosted exact-tag CI, concrete instances of the
remaining non-dyadic and global arithmetic laws, the external catalogue and
local-computation inputs, publisher corrections, or independent human
semantic sign-off. The paper therefore remains Grade D and `NOT_COMPLETE`.
