# Exact Review Kit receipt through Report 59

This receipt fixes the independently extracted local Review Kit evidence for
commit `8ead7f470ad0e9b27327dffa11bac2e4854d0609`. That clean checkpoint
contains the publisher Table 1 matrix certificate together with every earlier
He ADC result recorded through Report 59.

## Archive identity

- generated archive:
  `BongTheory-He2023ADC-ci-8ead7f4-review-kit.zip`;
- archive size: 6,229,631 bytes;
- SHA-256:
  `36F68A93590F669FFE8B0A50F1FE5F613000877442AE2919F0CC86401C446254`;
- recorded source commit:
  `8ead7f470ad0e9b27327dffa11bac2e4854d0609`;
- recorded source-tree state: `clean`;
- recorded tracked local Lean sources: 1,983;
- recorded packaged files: 2,065.

The archive contains 2,064 payload hashes in `FILES.sha256`. A separate
structure-only extraction verified every payload hash and found no packaged
`.lake` or `.git` directory, compiled Lean artifact, or publisher PDF. The He
classic formalization is absent from this paper-specific package.

## Dependency closure

All nine dependency worktrees in the full-build extraction were checked
clean, with `HEAD` exactly equal to the revision in `lake-manifest.json`:

```text
mathlib           520045ab14e26149ee970e2e617ca04b09bde5d6
plausible         e12c1910fe855cbfc38803cd4e55543906d5fa62
LeanSearchClient  c5d5b8fe6e5158def25cd28eb94e4141ad97c843
importGraph       7e9612bf0b9ee66db3cb5b9988a35afc706f5a12
proofwidgets      6e311e2a844da9b2cc3971187df2fe0066947b93
aesop            a7dbf0c63b694e47f425f3dcddbc0e178bb432d3
Qq                38d591e778f100aec9762bb582f9c7f55f50e9dc
batteries         023ce7d62a0531e22a5331e20b587817a80d49ff
Cli               88679d088c9720c27ebdf2ba4dafe17341747f94
```

No project `.olean` or other compiled output was copied into the extraction
before verification.

## Independent extraction and build

The complete build began with eight workers in the fresh extraction. It was
deliberately interrupted after completed job 4,176 of the original 5,577-job
plan solely to increase parallelism. The same extraction then resumed with
twelve workers, using only artifacts produced during this verification, and
completed all 5,569 jobs with Lean 4.32.1.

The following four paper gates were then rerun directly in the extracted
tree; each exited successfully:

```text
lake env lean BongTest/He2023ADCAudit.lean
lake env lean BongTest/He2023ADCQuaternaryBoundaryQ2.lean
lake env lean BongTest/He2023ADCExceptionalQuaternaryQ2.lean
lake env lean BongTest/PaperAxiomGate.lean
```

The standalone enforcing gate reported:

```text
AXIOM_GATE_PASS: 60683 declarations checked
```

The checked-in exact-arithmetic verifier was also rerun from this extraction:

```text
wolframscript -file scripts/verification/verify_he2023adc_table1.wl
```

It independently confirmed all 48 determinant values, symmetry, positive
definiteness, the literal selected rows
`1--15, 19, 25, 30--32, 44`, and selected count 21.

## Scope of this receipt

This closes local mechanical reproducibility for exact clean checkpoint
`8ead7f4` through Report 59 and supersedes Report 58 for that source closure.
It does not include the later non-dyadic Table 4.7, low-rank, Proposition
4.16, minimal-testing, Lemma 4.14, or Proposition 4.15 developments in
Reports 61--65.

It also does not certify GitHub-hosted exact-tag CI, a permanent release
asset, concrete instances of the remaining non-dyadic and global arithmetic
laws, the external catalogue and local-computation inputs, publisher
corrections, or independent human semantic sign-off. The paper therefore
remains Grade D and `NOT_COMPLETE`.
