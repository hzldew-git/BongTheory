# Exact Review Kit receipt through Report 57

This receipt fixes the independently extracted local Review Kit evidence for
commit `7d7a4d5e79a06015fa40ccba464f143d77b6f231`. That clean checkpoint
contains the completed number-field form of Lemma 2.2 and the internal proof
of O'Meara 63:9, together with every earlier He ADC result recorded through
Report 57.

## Archive identity

- generated archive:
  `BongTheory-He2023ADC-ci-7d7a4d5-review-kit.zip`;
- archive size: 6,214,243 bytes;
- SHA-256:
  `3FD3D6AA8294C67D7FC1719A349B0923B16AB2438A21CCE4AACF910690AC434C`;
- recorded source commit:
  `7d7a4d5e79a06015fa40ccba464f143d77b6f231`;
- recorded source-tree state: `clean`;
- recorded tracked local Lean sources: 1,982;
- recorded packaged files: 2,061.

The archive contains 2,060 payload hashes in `FILES.sha256`. A separate
structure-only extraction verified all payload hashes and found no packaged
`.lake` directory or compiled Lean artifact. The He classic formalization is
not present in this paper-specific package.

## Dependency acquisition

The official end-to-end verifier began by cloning every dependency from its
public upstream. Eight repositories completed, but GitHub reset the connection
while the final `Cli` repository was being cloned. A retry encountered the
same external network failure. The failed partial clone was preserved under a
different name, and `Cli` was copied from a clean local mirror at the exact
revision in `lake-manifest.json`.

Before building, every one of the nine dependency worktrees was checked to be
clean and to have a `HEAD` exactly equal to its locked manifest revision:

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

This fallback concerns dependency transport only: no compiled project output
or mismatched dependency revision was copied. Exact-tag GitHub CI remains the
independent public-network check.

## Independent extraction and build

The complete build began with four workers in the fresh extraction. It was
interrupted after job 2,480 solely to increase parallelism, then resumed with
eight workers in the same extraction. Every project artifact used by the
resumed process had been produced during this verification. The build
completed all `5,560` jobs with Lean 4.32.1.

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
AXIOM_GATE_PASS: 60594 declarations checked
```

At the exact clean source checkpoint, the comment-aware source scanner also
checked all 2,769 tracked Lean files and found no forbidden proof token outside
comments.

## Scope of this receipt

This closes local mechanical reproducibility for the exact clean source
checkpoint `7d7a4d5` through Reports 55--57, and supersedes Report 54 for the
current He ADC source closure. It does not certify GitHub-hosted CI, an
uploaded artifact, a tagged release, the remaining concrete non-dyadic and
global arithmetic laws, the external catalogue and local-computation inputs,
publisher corrections, or independent human semantic sign-off. The paper
therefore remains Grade D and `NOT_COMPLETE`.
